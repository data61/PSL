(*<*)
(*
 * Knowledge-based programs.
 * (C)opyright 2011, Peter Gammie, peteg42 at gmail.com.
 * License: BSD
 *)

theory SPRViewDet
imports
  SPRView
  KBPsAlg
  Eval
  List_local
  ODList Trie2
  "Transitive-Closure.Transitive_Closure_List_Impl"
  "HOL-Library.Mapping"
begin
(*>*)

subsection\<open>Perfect Recall in Deterministic Broadcast Environments\<close>

text\<open>

\label{sec:kbps-theory-spr-deterministic-protocols}

It is well known that simultaneous broadcast has the effect of making
information \emph{common knowledge}; roughly put, the agents all learn
the same things at the same time as the system evolves, so the
relation amongst the agents' states of knowledge never becomes more
complex than it is in the initial state
\citep[Chapter~6]{FHMV:1995}. For this reason we might hope to find
finite-state implementations of JKBPs in broadcast environments.

The broadcast assumption by itself is insufficient in general, however
\citep[\S7]{Ron:1996}, and so we need to further constrain the
scenario. Here we require that for each canonical trace the JKBP
prescribes at most one action. In practice this constraint is easier
to verify than the circularity would suggest; we return to this point
at the end of this section.

\<close>

text_raw\<open>
\begin{figure}[tb]
\begin{isabellebody}%
\<close>

record (overloaded) ('a, 'es, 'ps) BEState =
  es :: "'es"
  ps :: "('a \<times> 'ps) odlist"

locale FiniteDetBroadcastEnvironment =
  Environment jkbp envInit envAction envTrans envVal envObs
    for jkbp :: "'a \<Rightarrow> ('a :: {finite,linorder}, 'p, 'aAct) KBP"
    and envInit
         :: "('a, 'es :: {finite,linorder}, 'as :: {finite,linorder}) BEState list"
    and envAction :: "('a, 'es, 'as) BEState \<Rightarrow> 'eAct list"
    and envTrans :: "'eAct \<Rightarrow> ('a \<Rightarrow> 'aAct)
                     \<Rightarrow> ('a, 'es, 'as) BEState \<Rightarrow> ('a, 'es, 'as) BEState"
    and envVal :: "('a, 'es, 'as) BEState \<Rightarrow> 'p \<Rightarrow> bool"
    and envObs :: "'a \<Rightarrow> ('a, 'es, 'as) BEState \<Rightarrow> ('cobs \<times> 'as option)"

+ fixes agents :: "'a odlist"
  fixes envObsC :: "'es \<Rightarrow> 'cobs"
  defines "envObs a s \<equiv> (envObsC (es s), ODList.lookup (ps s) a)"
  assumes agents: "ODList.toSet agents = UNIV"
  assumes envTrans: "\<forall>s s' a eact eact' aact aact'.
            ODList.lookup (ps s) a = ODList.lookup (ps s') a \<and> aact a = aact' a
             \<longrightarrow> ODList.lookup (ps (envTrans eact aact s)) a
               = ODList.lookup (ps (envTrans eact' aact' s')) a"
  assumes jkbpDet: "\<forall>a. \<forall>t \<in> SPR.jkbpC. length (jAction SPR.MC t a) \<le> 1"
text_raw\<open>
  \end{isabellebody}%
  \caption{Finite broadcast environments with a deterministic JKBP.}
  \label{fig:kbps-theory-det-broadcast-envs}
\end{figure}
\<close>(*<*)

instantiation BEState_ext :: (linorder, linorder, linorder, linorder) linorder
begin

definition less_eq_BEState_ext
  where "x \<le> y \<equiv> es x < es y \<or> (es x = es y \<and> (ps x < ps y \<or> (ps x = ps y \<and> more x \<le> more y)))"

definition less_BEState_ext
  where "x < y \<equiv> es x < es y \<or> (es x = es y \<and> (ps x < ps y \<or> (ps x = ps y \<and> more x < more y)))"

instance
  apply intro_classes
  apply (unfold less_eq_BEState_ext_def less_BEState_ext_def)
  apply auto
  done

end

instance BEState_ext :: ("{finite, linorder}", finite, "{finite, linorder}", finite) finite
proof
 let ?U = "UNIV :: ('a, 'b, 'c, 'd) BEState_ext set"
 { fix x :: "('a, 'b, 'c, 'd) BEState_scheme"
   have "\<exists>a b c. x = BEState_ext a b c"
     by (cases x) simp
 } then have U:
   "?U = (\<lambda>((a, b), c). BEState_ext a b c) ` ((UNIV \<times> UNIV) \<times> UNIV)"
   by (auto simp add: Set.image_def)
 show "finite ?U" by (simp add: U)
qed

(*>*)
text\<open>

We encode our expectations of the scenario in the @{term
"FiniteBroadcastEnvironment"} locale of
Figure~\ref{fig:kbps-theory-det-broadcast-envs}. The broadcast is
modelled by having all agents make the same common observation of the
shared state of type @{typ "'es"}. We also allow each agent to
maintain a private state of type @{typ "'ps"}; that other agents
cannot influence it or directly observe it is enforced by the
constraint \<open>envTrans\<close> and the definition of @{term "envObs"}.

We do however allow the environment's protocol to be non-deterministic
and a function of the entire system state, including private states.

\<close>

context FiniteDetBroadcastEnvironment
begin
(*<*)

(* ouch *)
lemma envObs_def_raw:
  "envObs a = (\<lambda>s. (envObsC (es s), ODList.lookup (ps s) a))"
  apply (rule ext)+
  apply (simp add: envObs_def)
  done

(*>*)
text\<open>

We seek a suitable simulation space by considering what determines an
agent's knowledge. Intuitively any set of traces that is relevant to
the agents' states of knowledge with respect to @{term "t \<in> jkbpC"}
need include only those with the same common observation as @{term
"t"}:

\<close>

definition tObsC :: "('a, 'es, 'as) BEState Trace \<Rightarrow> 'cobs Trace" where
  "tObsC \<equiv> tMap (envObsC \<circ> es)"

text\<open>

Clearly this is an abstraction of the SPR jview of the given trace.

\<close>

lemma spr_jview_tObsC:
  assumes "spr_jview a t = spr_jview a t'"
  shows "tObsC t = tObsC t'"
(*<*)
  using SPR.sync[rule_format, OF assms] assms
  by (induct rule: trace_induct2) (auto simp: envObs_def tObsC_def)

lemma tObsC_tLength:
  "tObsC t = tObsC t' \<Longrightarrow> tLength t = tLength t'"
  unfolding tObsC_def by (rule tMap_eq_imp_tLength_eq)

lemma tObsC_tStep_eq_inv:
  "tObsC t' = tObsC (t \<leadsto> s) \<Longrightarrow> \<exists>t'' s'. t' = t'' \<leadsto> s'"
  unfolding tObsC_def by auto

lemma tObsC_prefix_closed[dest]:
  "tObsC (t \<leadsto> s) = tObsC (t' \<leadsto> s') \<Longrightarrow> tObsC t = tObsC t'"
  unfolding tObsC_def by simp

lemma tObsC_tLast[iff]:
  "tLast (tObsC t) = envObsC (es (tLast t))"
  unfolding tObsC_def by simp

lemma tObsC_initial[iff]:
  "tFirst (tObsC t) = envObsC (es (tFirst t))"
  "tObsC (tInit s) = tInit (envObsC (es s))"
  "tObsC t = tInit cobs \<longleftrightarrow> (\<exists>s. t = tInit s \<and> envObsC (es s) = cobs)"
  unfolding tObsC_def by simp_all

lemma spr_tObsC_trc_aux:
  assumes "(t, t') \<in> (\<Union>a. relations SPR.MC a)\<^sup>*"
  shows "tObsC t = tObsC t'"
  using assms
  apply (induct)
   apply simp
  apply clarsimp
  apply (rule_tac a=x in spr_jview_tObsC)
  apply simp
  done

lemma spr_jview_tObsC_trans:
  "\<lbrakk>spr_jview a t = spr_jview a t'; spr_jview a' t' = spr_jview a' t''\<rbrakk>
     \<Longrightarrow> tObsC t = tObsC t''"
  by (fastforce dest: spr_jview_tObsC)

(*>*)
text\<open>

Unlike the single-agent case of \S\ref{sec:kbps-spr-single-agent}, it
is not sufficient for a simulation to record only the final states; we
need to relate the initial private states of the agents with the final
states they consider possible, as the initial states may contain
information that is not common knowledge. This motivates the following
abstraction:

\<close>

definition
  tObsC_abs :: "('a, 'es, 'as) BEState Trace \<Rightarrow> ('a, 'es, 'as) BEState Relation"
where
  "tObsC_abs t \<equiv> { (tFirst t', tLast t')
                    |t'. t' \<in> SPR.jkbpC \<and> tObsC t' = tObsC t}"
(*<*)
lemma tObsC_abs_jview_eq[dest]:
  "spr_jview a t' = spr_jview a t
    \<Longrightarrow> tObsC_abs t = tObsC_abs t'"
  unfolding tObsC_abs_def by (fastforce dest: spr_jview_tObsC)

lemma tObsC_abs_tObsC_eq[dest]:
  "tObsC t' = tObsC t
    \<Longrightarrow> tObsC_abs t = tObsC_abs t'"
  unfolding tObsC_abs_def by (fastforce dest: spr_jview_tObsC)

lemma spr_jview_tObsCI:
  assumes tt': "tObsC t = tObsC t'"
      and first: "envObs a (tFirst t) = envObs a (tFirst t')"
      and "tMap (\<lambda>s. ODList.lookup (ps s) a) t = tMap (\<lambda>s. ODList.lookup (ps s) a) t'"
  shows "spr_jview a t = spr_jview a t'"
  using tObsC_tLength[OF tt'] assms
  by (induct rule: trace_induct2, auto iff: tObsC_def envObs_def spr_jview_def)

lemma tObsC_absI[intro]:
  "\<lbrakk> t' \<in> SPR.jkbpC; tObsC t' = tObsC t; u = tFirst t'; v = tLast t' \<rbrakk>
    \<Longrightarrow> (u, v) \<in> tObsC_abs t"
  unfolding tObsC_abs_def by blast

lemma tObsC_abs_conv:
  "(u, v) \<in> tObsC_abs t
    \<longleftrightarrow> (\<exists>t'. t' \<in> SPR.jkbpC \<and> tObsC t' = tObsC t \<and> u = tFirst t' \<and> v = tLast t')"
  unfolding tObsC_abs_def by blast

lemma tObsC_abs_tLast[simp]:
  "(u, v) \<in> tObsC_abs t \<Longrightarrow> envObsC (es v) = envObsC (es (tLast t))"
  unfolding tObsC_abs_def tObsC_def
  by (auto iff: o_def elim: tMap_tLast_inv)

lemma tObsC_abs_tInit[iff]:
  "tObsC_abs (tInit s)
 = { (s', s') |s'. s' \<in> set envInit \<and> envObsC (es s') = envObsC (es s) }"
  unfolding tObsC_abs_def
  apply auto
  apply (rule_tac x="tInit s'" in exI)
  apply simp
  done

(*>*)
text\<open>\<close>

end (* context FiniteDetBroadcastEnvironment *)

text\<open>

We use the following record to represent the worlds of the simulated
Kripke structure:

\<close>

record (overloaded) ('a, 'es, 'as) spr_simWorld =
  sprFst :: "('a, 'es, 'as) BEState"
  sprLst :: "('a, 'es, 'as) BEState"
  sprCRel :: "('a, 'es, 'as) BEState Relation"

(*<*)
instance spr_simWorld_ext :: ("{finite, linorder}", finite, "{finite, linorder}", finite) finite
proof
 let ?U = "UNIV :: ('a, 'b, 'c, 'd) spr_simWorld_ext set"
 { fix x :: "('a, 'b, 'c, 'd) spr_simWorld_scheme"
   have "\<exists>a b c d. x = spr_simWorld_ext a b c d"
     by (cases x) simp
 } then have U:
   "?U = (\<lambda>(a, (b, (c, d))). spr_simWorld_ext a b c d) ` (UNIV \<times> (UNIV \<times> (UNIV \<times> UNIV)))"
   by (auto simp add: Set.image_def)
 show "finite ?U" by (simp add: U)
qed

(*>*)

context FiniteDetBroadcastEnvironment
begin

text\<open>

The simulation of a trace @{term "t \<in> jkbpC"} records its initial and
final states, and the relation between initial and final states of all
commonly-plausible traces:

\<close>

definition
  spr_sim :: "('a, 'es, 'as) BEState Trace \<Rightarrow> ('a, 'es, 'as) spr_simWorld"
where
  "spr_sim \<equiv> \<lambda>t. \<lparr> sprFst = tFirst t, sprLst = tLast t, sprCRel = tObsC_abs t \<rparr>"

text\<open>

The associated Kripke structure relates two worlds for an agent if the
agent's observation on the the first and last states corresponds, and
the worlds have the same common observation relation. As always, we
evaluate propositions on the final state of the trace.

\<close>

definition
  spr_simRels :: "'a \<Rightarrow> ('a, 'es, 'as) spr_simWorld Relation"
where
  "spr_simRels \<equiv> \<lambda>a. { (s, s') |s s'.
                         envObs a (sprFst s) = envObs a (sprFst s')
                       \<and> envObs a (sprLst s) = envObs a (sprLst s')
                       \<and> sprCRel s = sprCRel s' }"

definition spr_simVal :: "('a, 'es, 'as) spr_simWorld \<Rightarrow> 'p \<Rightarrow> bool" where
  "spr_simVal \<equiv> envVal \<circ> sprLst"

abbreviation
  "spr_simMC \<equiv> mkKripke (spr_sim ` SPR.jkbpC) spr_simRels spr_simVal"
(*<*)

lemma spr_sim_tFirst_tLast:
  "\<lbrakk> spr_sim t = s; t \<in> SPR.jkbpC \<rbrakk> \<Longrightarrow> (sprFst s, sprLst s) \<in> sprCRel s"
  unfolding spr_sim_def by auto

lemma spr_sim_tObsC_abs:
  shows "tObsC_abs t = sprCRel (spr_sim t)"
  unfolding tObsC_abs_def spr_sim_def by simp

lemma spr_simVal_eq[iff]:
  "spr_simVal (spr_sim t) = envVal (tLast t)"
  unfolding spr_sim_def spr_simVal_def by simp

lemma spr_sim_range:
  "sim_range SPR.MC spr_simMC spr_sim"
  by (rule sim_rangeI) (simp_all add: spr_sim_def)

lemma spr_simVal:
  "sim_val SPR.MC spr_simMC spr_sim"
  by (rule sim_valI) simp

lemma spr_sim_f:
  "sim_f SPR.MC spr_simMC spr_sim"
  unfolding spr_simRels_def spr_sim_def mkKripke_def SPR.mkM_def
  by (rule sim_fI, auto)

lemma envDetJKBP':
  assumes tCn: "t \<in> SPR.jkbpCn n"
      and aact: "act \<in> set (jAction (SPR.MCn n) t a)"
  shows "jAction (SPR.MCn n) t a = [act]"
  using jkbpDet[rule_format, where t=t and a=a] assms
  apply -
  apply (cases "jAction SPR.MC t a")
   apply (auto iff: SPR.jkbpC_jkbpCn_jAction_eq[OF tCn] dest: SPR.jkbpCn_jkbpC_inc)
  done

(*>*)
text\<open>

All the properties of a simulation are easy to show for @{term
"spr_sim"} except for reverse simulation.

The critical lemma states that if we have two traces that yield the
same common observations, and an agent makes the same observation on
their initial states, then that agent's private states at each point
on the two traces are identical.

\<close>

lemma spr_jview_det_ps:
  assumes tt'C: "{t, t'} \<subseteq> SPR.jkbpC"
  assumes obsCtt': "tObsC t = tObsC t'"
  assumes first: "envObs a (tFirst t) = envObs a (tFirst t')"
  shows "tMap (\<lambda>s. ODList.lookup (ps s) a) t
       = tMap (\<lambda>s. ODList.lookup (ps s) a) t'"
(*<*)
using tObsC_tLength[OF obsCtt'] first tt'C obsCtt'
proof(induct rule: trace_induct2)
  case (tInit s s') thus ?case
    by (simp add: envObs_def)
next
  case (tStep s s' t t')
  from tStep
  have ts: "t \<leadsto> s \<in> SPR.jkbpCn (tLength (t \<leadsto> s))"
   and t's': "t' \<leadsto> s' \<in> SPR.jkbpCn (tLength (t' \<leadsto> s'))"
    by blast+
  from tStep have jvtt': "spr_jview a t = spr_jview a t'"
    by - (rule spr_jview_tObsCI, auto)
  with tStep have jatt':
    "jAction (SPR.MCn (tLength t)) t a
   = jAction (SPR.MCn (tLength t')) t' a"
    apply -
    apply simp
    apply (rule S5n_jAction_eq)
     apply blast
    unfolding SPR.mkM_def
    apply auto
    done
  from jvtt'
  have tt'Last: "ODList.lookup (ps (tLast t)) a
               = ODList.lookup (ps (tLast t')) a"
    by (auto simp: envObs_def)
  from ts obtain eact aact
    where aact: "\<forall>a. aact a \<in> set (jAction (SPR.MCn (tLength t)) t a)"
      and s: "s = envTrans eact aact (tLast t)"
    by (auto iff: Let_def)
  from t's' obtain eact' aact'
    where aact': "\<forall>a. aact' a \<in> set (jAction (SPR.MCn (tLength t')) t' a)"
      and s': "s' = envTrans eact' aact' (tLast t')"
    by (auto iff: Let_def)
  from tStep have tCn: "t \<in> SPR.jkbpCn (tLength t)" by auto
  from aact
  obtain act
    where act: "jAction (SPR.MCn (tLength t)) t a = [act]"
    using envDetJKBP'[OF tCn, where a=a and act="aact a"]
    by auto
  hence "jAction (SPR.MCn (tLength t')) t' a = [act]"
    by (simp only: jatt')
  with act aact aact'
  have "aact a = aact' a"
    by (auto elim!: allE[where x=a])
  with agents tt'Last s s'
  have "ODList.lookup (ps s) a = ODList.lookup (ps s') a"
    by (simp add: envTrans)
  moreover
  from tStep have "tMap (\<lambda>s. ODList.lookup (ps s) a) t = tMap (\<lambda>s. ODList.lookup (ps s) a) t'"
    by auto
  moreover
  from tStep have "envObsC (es s) = envObsC (es s')"
    unfolding tObsC_def by simp
  ultimately show ?case by simp
qed

lemma spr_sim_r:
  "sim_r SPR.MC spr_simMC spr_sim"
proof(rule sim_rI)
  fix a p q'
  assume pT: "p \<in> worlds SPR.MC"
     and fpq': "(spr_sim p, q') \<in> relations spr_simMC a"
  from fpq' obtain uq fq vq
    where q': "q' = \<lparr> sprFst = uq, sprLst = vq, sprCRel = tObsC_abs p \<rparr>"
      and uq: "envObs a (tFirst p) = envObs a uq"
      and vq: "envObs a (tLast p) = envObs a vq"
    unfolding mkKripke_def spr_sim_def spr_simRels_def
    by fastforce

  from fpq' have "q' \<in> worlds spr_simMC" by simp
  with q' have "(uq, vq) \<in> tObsC_abs p"
    using spr_sim_tFirst_tLast[where s=q']
    apply auto
    done
  then obtain t
    where tT: "t \<in> SPR.jkbpC"
      and tp: "tObsC t = tObsC p"
      and tuq: "tFirst t = uq"
      and tvq: "tLast t = vq"
    by (auto iff: tObsC_abs_conv)

  from pT tT tp tuq uq
  have "tMap (\<lambda>s. ODList.lookup (ps s) a) p = tMap (\<lambda>s. ODList.lookup (ps s) a) t"
    by (auto intro: spr_jview_det_ps)
  with tp tuq uq
  have "spr_jview a p = spr_jview a t"
    by (auto intro: spr_jview_tObsCI)

  with pT tT have pt: "(p, t) \<in> relations SPR.MC a"
    unfolding SPR.mkM_def by simp
  from q' uq vq tp tuq tvq have ftq': "spr_sim t = q'"
    unfolding spr_sim_def by auto
  from pt ftq'
  show "\<exists>q. (p, q) \<in> relations SPR.MC a \<and> spr_sim q = q'"
    by blast
qed

(*>*)
text\<open>

The proof proceeds by lock-step induction over @{term "t"} and @{term
"t'"}, appealing to the @{term "jkbpDet"} assumption, the definition
of @{term "envObs"} and the constraint @{term "envTrans"}.

It is then a short step to showing reverse simulation, and hence
simulation:

\<close>

lemma spr_sim: "sim SPR.MC spr_simMC spr_sim"
(*<*)
  using spr_sim_range spr_simVal spr_sim_f spr_sim_r
  unfolding sim_def
  by blast
(*>*)

end (* context FiniteDetBroadcastEnvironment *)

sublocale FiniteDetBroadcastEnvironment
        < SPRdet: SimIncrEnvironment jkbp envInit envAction envTrans envVal
                                     spr_jview envObs spr_jviewInit spr_jviewIncr
                                     spr_sim spr_simRels spr_simVal
(*<*)
  by standard (rule spr_sim)
(*>*)

(* **************************************** *)

subsubsection\<open>Representations\<close>

text\<open>

As before we canonically represent the quotient of the simulated
worlds @{typ "('a, 'es, 'as) spr_simWorld"} under @{term
"spr_simRels"} using ordered, distinct lists. In particular, we use
the type @{typ "('a \<times> 'a) odlist"} (abbreviated @{typ "'a
odrelation"}) to canonically represent relations.

\<close>

context FiniteDetBroadcastEnvironment
begin

type_synonym (in -) ('a, 'es, 'as) spr_simWorldsECRep
  = "('a, 'es, 'as) BEState odrelation"
type_synonym (in -) ('a, 'es, 'as) spr_simWorldsRep
  = "('a, 'es, 'as) spr_simWorldsECRep \<times> ('a, 'es, 'as) spr_simWorldsECRep"

text\<open>

We can abstract such a representation into a set of simulated
equivalence classes:

\<close>

definition
  spr_simAbs :: "('a, 'es, 'as) spr_simWorldsRep
              \<Rightarrow> ('a, 'es, 'as) spr_simWorld set"
where
  "spr_simAbs \<equiv> \<lambda>(cec, aec). { \<lparr> sprFst = s, sprLst = s', sprCRel = toSet cec \<rparr>
                                |s s'. (s, s') \<in> toSet aec }"

text\<open>

Assuming @{term "X"} represents a simulated equivalence class for
@{term "t \<in> jkbpC"}, we can decompose @{term "spr_simAbs X"} in terms
of @{term "tObsC_abs t"} and @{term "agent_abs t"}:

\<close>

definition
  agent_abs :: "'a \<Rightarrow> ('a, 'es, 'as) BEState Trace
             \<Rightarrow> ('a, 'es, 'as) BEState Relation"
where
  "agent_abs a t \<equiv> { (tFirst t', tLast t')
                     |t'. t' \<in> SPR.jkbpC \<and> spr_jview a t' = spr_jview a t }"
(*<*)

lemma agent_absI[intro]:
  "\<lbrakk> spr_jview a t' = spr_jview a t; t' \<in> SPR.jkbpC; t \<in> SPR.jkbpC \<rbrakk>
      \<Longrightarrow> (tFirst t', tLast t') \<in> agent_abs a t"
  unfolding agent_abs_def by auto

lemma spr_simAbs_refl:
  assumes tC: "t \<in> SPR.jkbpC"
      and ec: "spr_simAbs ec = SPRdet.sim_equiv_class a t"
  shows "spr_sim t \<in> spr_simAbs ec"
  using assms by simp

lemma spr_simAbs_tObsC_abs[simp]:
  assumes tC: "t \<in> SPR.jkbpC"
      and ec: "spr_simAbs ec = SPRdet.sim_equiv_class a t"
  shows "toSet (fst ec) = tObsC_abs t"
  using tC spr_simAbs_refl[OF tC ec]
  unfolding spr_sim_def spr_simAbs_def by auto

lemma spr_simAbs_agent_abs[simp]:
  assumes tC: "t \<in> SPR.jkbpC"
      and ec: "spr_simAbs ec = SPRdet.sim_equiv_class a t"
  shows "toSet (snd ec) = agent_abs a t"
  using tC ec
  unfolding spr_sim_def spr_simAbs_def agent_abs_def
  apply (cases ec)
  apply auto
  apply (subgoal_tac "\<lparr>sprFst = aaa, sprLst = ba, sprCRel = toSet aa\<rparr> \<in> {\<lparr>sprFst = s, sprLst = s', sprCRel = toSet aa\<rparr> |s s'. (s, s') \<in> toSet b}")
  apply auto
  done

(*>*)
text\<open>

This representation is canonical on the domain of interest (though not
in general):

\<close>

lemma spr_simAbs_inj_on:
  "inj_on spr_simAbs { x . spr_simAbs x \<in> SPRdet.jkbpSEC }"
(*<*)
proof(rule inj_onI)
  fix x y
  assume x: "x \<in> { x . spr_simAbs x \<in> SPRdet.jkbpSEC }"
     and y: "y \<in> { x . spr_simAbs x \<in> SPRdet.jkbpSEC }"
     and xy: "spr_simAbs x = spr_simAbs y"
  from x obtain a t
    where tC: "t \<in> SPR.jkbpC"
      and ec: "spr_simAbs x = SPRdet.sim_equiv_class a t"
    by auto
  from spr_simAbs_tObsC_abs[OF tC ec] spr_simAbs_tObsC_abs[OF tC trans[OF xy[symmetric] ec], symmetric]
  have "fst x = fst y" by (blast intro: injD[OF toSet_inj])
  moreover
  from spr_simAbs_agent_abs[OF tC ec] spr_simAbs_agent_abs[OF tC trans[OF xy[symmetric] ec], symmetric]
  have "snd x = snd y" by (blast intro: injD[OF toSet_inj])
  ultimately show "x = y" by (simp add: prod_eqI)
qed

(*>*)
text\<open>

The following sections make use of a Kripke structure constructed over
@{term "tObsC_abs t"} for some canonical trace @{term "t"}. Note that
we use the relation in the generated code.

\<close>

type_synonym (in -) ('a, 'es, 'as) spr_simWorlds
  = "('a, 'es, 'as) BEState \<times> ('a, 'es, 'as) BEState"

definition (in -)
  spr_repRels :: "('a \<Rightarrow> ('a, 'es, 'as) BEState \<Rightarrow> 'cobs \<times> 'as option)
                 \<Rightarrow> 'a \<Rightarrow> ('a, 'es, 'as) spr_simWorlds Relation"
where
  "spr_repRels envObs \<equiv> \<lambda>a. { ((u, v), (u', v')).
        envObs a u = envObs a u' \<and> envObs a v = envObs a v' }"

definition
  spr_repVal :: "('a, 'es, 'as) spr_simWorlds \<Rightarrow> 'p \<Rightarrow> bool"
where
  "spr_repVal \<equiv> envVal \<circ> snd"

abbreviation
  spr_repMC :: "('a, 'es, 'as) BEState Relation
               \<Rightarrow> ('a, 'p, ('a, 'es, 'as) spr_simWorlds) KripkeStructure"
where
  "spr_repMC \<equiv> \<lambda>tcobsR. mkKripke tcobsR (spr_repRels envObs) spr_repVal"
(*<*)

abbreviation
  spr_repRels :: "'a \<Rightarrow> ('a, 'es, 'as) spr_simWorlds Relation"
where
  "spr_repRels \<equiv> SPRViewDet.spr_repRels envObs"

lemma spr_repMC_kripke[intro, simp]: "kripke (spr_repMC X)"
  by (rule kripkeI) simp

lemma spr_repMC_S5n[intro, simp]: "S5n (spr_repMC X)"
  unfolding spr_repRels_def
  by (intro S5nI equivI refl_onI symI transI) auto

(*>*)
text\<open>

As before we can show that this Kripke structure is adequate for a
particular canonical trace @{term "t"} by showing that it simulates
@{term "spr_repMC"} We introduce an intermediate structure:

\<close>

abbreviation
  spr_jkbpCSt :: "('a, 'es, 'as) BEState Trace \<Rightarrow> ('a, 'es, 'as) spr_simWorld set"
where
  "spr_jkbpCSt t \<equiv> spr_sim ` { t' . t' \<in> SPR.jkbpC \<and> tObsC t = tObsC t' }"

abbreviation
  spr_simMCt :: "('a, 'es, 'as) BEState Trace
                \<Rightarrow> ('a, 'p, ('a, 'es, 'as) spr_simWorld) KripkeStructure"
where
  "spr_simMCt t \<equiv> mkKripke (spr_jkbpCSt t) spr_simRels spr_simVal"

definition
  spr_repSim :: "('a, 'es, 'as) spr_simWorld \<Rightarrow> ('a, 'es, 'as) spr_simWorlds"
where
  "spr_repSim \<equiv> \<lambda>s. (sprFst s, sprLst s)"
(*<*)

lemma spr_repSim_simps[simp]:
  "spr_repSim ` spr_sim ` T = (\<lambda>t. (tFirst t, tLast t)) ` T"
  "spr_repSim (spr_sim t) = (tFirst t, tLast t)"
  unfolding spr_repSim_def spr_sim_def
  apply auto
  apply (rule_tac x="\<lparr> sprFst = tFirst t, sprLst = tLast t, sprCRel = tObsC_abs t \<rparr>" in image_eqI)
  apply auto
  done

lemma jkbpCSt_jkbpCS_subset:
  "spr_jkbpCSt t \<subseteq> spr_sim ` SPR.jkbpC"
  by auto

(*>*)
text\<open>\<close>

lemma spr_repSim:
  assumes tC: "t \<in> SPR.jkbpC"
  shows "sim (spr_simMCt t)
             ((spr_repMC \<circ> sprCRel) (spr_sim t))
             spr_repSim"
(*<*) (is "sim ?M ?M' ?f")
proof
  show "sim_range ?M ?M' ?f"
  proof
    show "worlds ?M' = ?f ` worlds ?M"
      apply (simp add: spr_sim_def spr_repSim_def)
      apply (auto iff: tObsC_abs_def)
      apply (rule_tac x="\<lparr> sprFst = tFirst t', sprLst = tLast t', sprCRel = tObsC_abs t \<rparr>" in image_eqI)
       apply simp
      apply (rule_tac x=t' in image_eqI)
       apply (simp add: tObsC_abs_def)
      apply auto[1]
      done
  next
    fix a
    show "relations ?M' a \<subseteq> worlds ?M' \<times> worlds ?M'"
      by (simp add: spr_sim_def spr_repSim_def)
  qed
next
  show "sim_val ?M ?M' ?f"
    by rule (simp add: spr_sim_def spr_simVal_def spr_repSim_def spr_repVal_def split: prod.split)
next
  show "sim_f ?M ?M' ?f"
    by rule (auto iff: spr_sim_def simp: spr_simRels_def spr_repRels_def spr_repSim_def)
next
  show "sim_r ?M ?M' ?f"
    apply rule
    unfolding spr_repRels_def spr_repSim_def spr_simRels_def spr_sim_def
    apply clarsimp
    apply (rule_tac x="\<lparr> sprFst = aa, sprLst = b, sprCRel = tObsC_abs ta \<rparr>" in exI)
    apply (auto iff: tObsC_abs_def)
    apply (rule_tac x=t'a in image_eqI)
    apply auto
    done
qed
(*>*)
text\<open>

As before we define a set of constants that satisfy the \<open>Algorithm\<close> locale given the assumptions of the @{term
"FiniteDetBroadcastEnvironment"} locale.

\<close>

(* **************************************** *)

subsubsection\<open>Initial states\<close>

text\<open>

The initial states for agent @{term "a"} given an initial observation
@{term "iobs"} consist of the set of states that yield a common
observation consonant with @{term "iobs"} paired with the set of
states where @{term "a"} observes @{term "iobs"}:

\<close>

definition (in -)
  spr_simInit ::
        "('a, 'es, 'as) BEState list \<Rightarrow> ('es \<Rightarrow> 'cobs)
      \<Rightarrow> ('a \<Rightarrow> ('a, 'es, 'as) BEState \<Rightarrow> 'cobs \<times> 'obs)
       \<Rightarrow> 'a \<Rightarrow> ('cobs \<times> 'obs)
       \<Rightarrow> ('a :: linorder, 'es :: linorder, 'as :: linorder) spr_simWorldsRep"
where
  "spr_simInit envInit envObsC envObs \<equiv> \<lambda>a iobs.
    (ODList.fromList [ (s, s). s \<leftarrow> envInit, envObsC (es s) = fst iobs ],
     ODList.fromList [ (s, s). s \<leftarrow> envInit, envObs a s = iobs ])"
(*<*)

abbreviation
  spr_simInit :: "'a \<Rightarrow> ('cobs \<times> 'as option) \<Rightarrow> ('a, 'es, 'as) spr_simWorldsRep"
where
  "spr_simInit \<equiv> SPRViewDet.spr_simInit envInit envObsC envObs"

(*>*)
text\<open>\<close>

lemma spr_simInit:
  assumes "iobs \<in> envObs a ` set envInit"
  shows "spr_simAbs (spr_simInit a iobs)
       = spr_sim ` { t' \<in> SPR.jkbpC. spr_jview a t' = spr_jviewInit a iobs }"
(*<*)
  using assms
  unfolding spr_simInit_def spr_simAbs_def spr_sim_def [abs_def]
  apply (clarsimp simp: Let_def SPR.jviewInit split: prod.split)
  apply rule
   apply clarsimp
   apply (rule_tac x="tInit s" in image_eqI)
    apply (auto iff: spr_jview_def envObs_def)
  done
(*>*)

(* **************************************** *)

subsubsection\<open>Simulated observations\<close>

text\<open>

An observation can be made at any element of the representation of a
simulated equivalence class of a canonical trace:

\<close>

definition (in -)
  spr_simObs ::
        "('es \<Rightarrow> 'cobs)
      \<Rightarrow> 'a \<Rightarrow> ('a :: linorder, 'es :: linorder, 'as :: linorder) spr_simWorldsRep
      \<Rightarrow> 'cobs \<times> 'as option"
where
  "spr_simObs envObsC \<equiv> \<lambda>a. (\<lambda>s. (envObsC (es s), ODList.lookup (ps s) a))
                           \<circ> snd \<circ> ODList.hd \<circ> snd"
(*<*)

abbreviation
  spr_simObs :: "'a \<Rightarrow> ('a, 'es, 'as) spr_simWorldsRep \<Rightarrow> 'cobs \<times> 'as option"
where
  "spr_simObs \<equiv> SPRViewDet.spr_simObs envObsC"

(*>*)
text\<open>\<close>

lemma spr_simObs:
  assumes tC: "t \<in> SPR.jkbpC"
  assumes ec: "spr_simAbs ec = SPRdet.sim_equiv_class a t"
  shows "spr_simObs a ec = envObs a (tLast t)"
(*<*)
proof -
  have A: "\<forall>s \<in> set (toList (snd ec)). envObs a (snd s) = envObs a (tLast t)"
    using spr_simAbs_agent_abs[OF tC ec]
    apply (clarsimp simp: toSet_def)
    apply (auto simp: agent_abs_def)
    done
  from tC ec have B: "(tFirst t, tLast t) \<in> set (toList (snd ec))"
    by (auto iff: spr_simAbs_def spr_sim_def toSet_def split_def)
  show ?thesis
    unfolding spr_simObs_def
    using list_choose_hd[OF A B]
    by (simp add: ODList.hd_def envObs_def)
qed
(*>*)

(* **************************************** *)

subsubsection\<open>Evaluation\<close>

text\<open>

As for the clock semantics (\S\ref{sec:kbps-theory-clock-view-eval}),
we use the general evalation function @{term "evalS"}.

Once again we propositions are used to filter the set of possible
worlds @{term "X"}:

\<close>

abbreviation (in -)
  spr_evalProp ::
        "(('a::linorder, 'es::linorder, 'as::linorder) BEState \<Rightarrow> 'p \<Rightarrow> bool)
      \<Rightarrow> ('a, 'es, 'as) BEState odrelation
      \<Rightarrow> 'p \<Rightarrow> ('a, 'es, 'as) BEState odrelation"
where
  "spr_evalProp envVal \<equiv> \<lambda>X p. ODList.filter (\<lambda>s. envVal (snd s) p) X"

text\<open>

The knowledge operation computes the subset of possible worlds @{term
"cec"} that yield the same observation as @{term "s"} for agent @{term
"a"}:

\<close>

definition (in -)
  spr_knowledge ::
     "('a \<Rightarrow> ('a::linorder, 'es::linorder, 'as::linorder) BEState
          \<Rightarrow> 'cobs \<times> 'as option)
       \<Rightarrow> ('a, 'es, 'as) BEState odrelation
       \<Rightarrow> 'a \<Rightarrow> ('a, 'es, 'as) spr_simWorlds
       \<Rightarrow> ('a, 'es, 'as) spr_simWorldsECRep"
where
  "spr_knowledge envObs cec \<equiv> \<lambda>a s.
    ODList.fromList [ s' . s' \<leftarrow> toList cec, (s, s') \<in> spr_repRels envObs a ]"
(*<*)

(* We need to avoid the explicit enumeration of the set in spr_repRels. *)

declare (in -) spr_knowledge_def[code del]

lemma (in -) [code]:
  "spr_knowledge envObs cec = (\<lambda>a s.
     ODList.fromList [ s' . s' \<leftarrow> toList cec,
                               envObs a (fst s) = envObs a (fst s') \<and> envObs a (snd s) = envObs a (snd s') ])"
  unfolding spr_knowledge_def spr_repRels_def by (simp add: split_def)

(*>*)
text\<open>

Similarly the common knowledge operation computes the transitive
closure \citep{AFP:TRANCL} of the union of the knowledge relations for
the agents \<open>as\<close>:

\<close>

definition (in -)
  spr_commonKnowledge ::
     "('a \<Rightarrow> ('a::linorder, 'es::linorder, 'as::linorder) BEState
          \<Rightarrow> 'cobs \<times> 'as option)
        \<Rightarrow> ('a, 'es, 'as) BEState odrelation
        \<Rightarrow> 'a list
        \<Rightarrow> ('a, 'es, 'as) spr_simWorlds
        \<Rightarrow> ('a, 'es, 'as) spr_simWorldsECRep"
where
  "spr_commonKnowledge envObs cec \<equiv> \<lambda>as s.
    let r = \<lambda>a. ODList.fromList
               [ (s', s'') . s' \<leftarrow> toList cec, s'' \<leftarrow> toList cec,
                             (s', s'') \<in> spr_repRels envObs a ];
        R = toList (ODList.big_union r as)
     in ODList.fromList (memo_list_trancl R s)"
(*<*)

(* We need to avoid the explicit enumeration of the set in spr_repRels. *)

declare (in -) spr_commonKnowledge_def[code del]

lemma (in -) [code]:
  "spr_commonKnowledge envObs cec = (\<lambda>as s.
    let r = \<lambda>a. ODList.fromList
               [ (s', s'') . s' \<leftarrow> toList cec, s'' \<leftarrow> toList cec,
                             envObs a (fst s') = envObs a (fst s'') \<and> envObs a (snd s') = envObs a (snd s'') ];
        R = toList (ODList.big_union r as)
     in ODList.fromList (memo_list_trancl R s))"
  unfolding spr_commonKnowledge_def spr_repRels_def by (simp add: split_def)

(*>*)
text\<open>

The evaluation function evaluates a subjective knowledge formula on
the representation of an equivalence class:

\<close>

definition (in -)
  "eval envVal envObs \<equiv> \<lambda>(cec, X).
     evalS (spr_evalProp envVal)
           (spr_knowledge envObs cec)
           (spr_commonKnowledge envObs cec)
           X"
(*<*)

lemma spr_knowledge:
  "s \<in> toSet cec
    \<Longrightarrow> toSet (spr_knowledge envObs cec a s) = relations (spr_repMC (toSet cec)) a `` {s}"
  unfolding spr_knowledge_def spr_repRels_def by (auto simp: toSet_def[symmetric])

lemma spr_commonKnowledge_relation_image:
  "s \<in> toSet cec
    \<Longrightarrow> toSet (spr_commonKnowledge envObs cec as s) = (\<Union>a \<in> set as. relations (spr_repMC (toSet cec)) a)\<^sup>+ `` {s}"
  unfolding spr_commonKnowledge_def Let_def
  apply (simp add: memo_list_trancl toSet_def[symmetric] Image_def split_def)
  apply (rule Collect_cong)
  apply (rule_tac f="\<lambda>x. (s, b) \<in> x" in arg_cong)
  apply (rule arg_cong[where f=trancl])
  apply fastforce
  done

lemma eval_rec_models:
  assumes XY: "toSet X \<subseteq> toSet Y"
      and s: "s \<in> toSet X"
  shows "s \<in> toSet (eval_rec (spr_evalProp envVal) (spr_knowledge envObs Y) (spr_commonKnowledge envObs Y) X \<phi>)
     \<longleftrightarrow> spr_repMC (toSet Y), s \<Turnstile> \<phi>"
using XY s
proof(induct \<phi> arbitrary: X s)
  case (Kknows a' \<phi> X s)
  from \<open>s \<in> toSet X\<close> spr_knowledge[OF subsetD[OF Kknows(2) Kknows(3)], where a=a']
  show ?case
    apply simp
    apply rule
     apply (drule arg_cong[where f="toSet"])
     apply (clarsimp simp: odlist_all_iff)
     apply (cut_tac s1="(a, b)" and X1="spr_knowledge envObs Y a' (aa, ba)" in Kknows.hyps)
      using Kknows(2) Kknows(3)
      apply (auto simp add: S5n_rels_closed[OF spr_repMC_S5n])[3]

    apply (clarsimp simp: toSet_eq_iff odlist_all_iff)
    apply (subst Kknows.hyps)
      using Kknows(2) Kknows(3)
      apply (auto simp add: S5n_rels_closed[OF spr_repMC_S5n] o_def)
    done
next
  case (Kcknows as \<phi> X s)
  show ?case
  proof(cases "as = Nil")
    case True with \<open>s \<in> toSet X\<close> show ?thesis by clarsimp
  next
    case False
    with \<open>s \<in> toSet X\<close> spr_commonKnowledge_relation_image[OF subsetD[OF Kcknows(2) Kcknows(3)], where as=as]
    show ?thesis
      apply simp
      apply rule
       apply (drule arg_cong[where f="toSet"])
       apply (clarsimp simp: odlist_all_iff)
       apply (cut_tac s1="(a, b)" and X1="spr_commonKnowledge envObs Y as (aa, ba)" in Kcknows.hyps)
        using Kcknows(2) Kcknows(3)
        apply (auto simp add: S5n_rels_closed[OF spr_repMC_S5n])[2]
        apply (subst (asm) trancl_unfold) back back back (* FIXME clunky, why did this break? *)
        apply (auto simp add: S5n_rels_closed[OF spr_repMC_S5n])[2]

      apply (clarsimp simp: toSet_eq_iff odlist_all_iff)
      apply (subst Kcknows.hyps)
       using Kcknows(2) Kcknows(3)
       apply (auto simp add: S5n_rels_closed[OF spr_repMC_S5n] o_def)
       apply (subst (asm) trancl_unfold) back back back (* FIXME clunky, why did this break? *)
       apply blast
      done
  qed
qed (simp_all add: spr_repVal_def)

lemma agent_abs_tObsC_abs_subset:
  "tObsC t' = tObsC t \<Longrightarrow> agent_abs a t \<subseteq> tObsC_abs t'"
  unfolding agent_abs_def tObsC_abs_def
  by (auto intro: spr_jview_tObsC)

lemma spr_simAbs_fst_snd:
  assumes tC: "t \<in> SPR.jkbpC"
      and ec: "spr_simAbs ec = SPRdet.sim_equiv_class a t"
  shows "toSet (snd ec) \<subseteq> toSet (fst ec)"
  using assms by (simp add: agent_abs_tObsC_abs_subset)

lemma tObsC_abs_rel:
  assumes tC: "t \<in> SPR.jkbpC"
      and ec: "spr_simAbs ec = SPRdet.sim_equiv_class a t"
      and r: "(x, y) \<in> (\<Union> (relations (spr_repMC (tObsC_abs t)) ` set as))\<^sup>+"
  shows "x \<in> tObsC_abs t \<longleftrightarrow>y \<in> tObsC_abs t"
  using assms
  apply -
  apply rule
   apply (erule trancl_induct, auto)+
  done

lemma spr_simAbs_fst_snd_trc:
  assumes tC: "t \<in> SPR.jkbpC"
      and ec: "spr_simAbs ec = SPRdet.sim_equiv_class a t"
  shows "toSet (big_union (spr_commonKnowledge envObs (fst ec) as) (toList (snd ec))) \<subseteq> toSet (fst ec)"
  using assms
  apply clarsimp
  apply (simp only: toSet_def[symmetric])
  apply (subgoal_tac "(ab,ba) \<in> toSet (fst ec)")
   apply (simp add: spr_commonKnowledge_relation_image tObsC_abs_rel[OF tC ec])
  apply (simp add: subsetD[OF agent_abs_tObsC_abs_subset[OF refl]])
  done

lemma agent_abs_rel_inv:
  assumes tC: "t \<in> SPR.jkbpC"
      and ec: "spr_simAbs ec = SPRdet.sim_equiv_class a t"
      and x: "x \<in> agent_abs a t"
      and xy: "(x, y) \<in> relations (spr_repMC (toSet (fst ec))) a"
  shows "y \<in> agent_abs a t"
  using assms
  apply simp
  unfolding agent_abs_def tObsC_abs_def spr_repRels_def
  apply auto
  apply (rule_tac x=t'b in exI)
  apply clarsimp
  apply (rule spr_jview_tObsCI)
   apply simp
  apply auto[1]
  apply (rule spr_jview_det_ps)
  using tC
  apply auto
  done

lemma agent_abs_tObsC_abs:
  assumes tC: "t \<in> SPR.jkbpC"
      and x: "x \<in> agent_abs a t"
      and y: "y \<in> agent_abs a t"
  shows "(x, y) \<in> relations (spr_repMC (tObsC_abs t)) a"
  using assms
  unfolding agent_abs_def spr_repRels_def
  apply clarsimp
  apply safe
  prefer 3
  apply (erule tObsC_absI) back
   apply simp_all
   apply (erule spr_jview_tObsC)
  prefer 3
  apply (erule tObsC_absI) back back
   apply simp_all
   apply (erule spr_jview_tObsC)
  apply (rule spr_tFirst)
   apply simp
  apply (rule spr_tLast)
   apply simp
  done

lemma agent_abs_spr_repRels:
  assumes tC: "t \<in> SPR.jkbpC"
      and x: "x \<in> agent_abs a t"
      and y: "y \<in> agent_abs a t"
  shows "(x, y) \<in> spr_repRels a"
  using assms
  unfolding agent_abs_def spr_repRels_def
  by (auto elim!: spr_tFirst spr_tLast)

lemma evalS_models:
  assumes tC: "t \<in> SPR.jkbpC"
      and ec: "spr_simAbs ec = SPRdet.sim_equiv_class a t"
      and subj_phi: "subjective a \<phi>"
      and s: "s \<in> toSet (snd ec)"
  shows "evalS (spr_evalProp envVal) (spr_knowledge envObs (fst ec)) (spr_commonKnowledge envObs (fst ec)) (snd ec) \<phi>
     \<longleftrightarrow> spr_repMC (toSet (fst ec)), s \<Turnstile> \<phi>" (is "?lhs \<phi> = ?rhs \<phi>")
using subj_phi s ec
proof(induct \<phi> rule: subjective.induct[case_names Kprop Knot Kand Kknows Kcknows])
  case (Kknows a a' \<psi>) thus ?case
    apply (clarsimp simp: toSet_eq_iff)
    apply rule
     apply clarsimp
     apply (subgoal_tac "(a, b) \<in> toSet (snd ec)")
      apply (drule (1) subsetD) back
      apply (simp only: eval_rec_models[OF spr_simAbs_fst_snd[OF tC ec]])
      using tC Kknows
      apply simp
       using tC ec
       apply -
       apply (erule (1) agent_abs_rel_inv[OF tC])
       apply simp

    apply clarsimp
    apply (subst eval_rec_models[OF spr_simAbs_fst_snd[OF tC ec]])
     apply simp
    using agent_abs_tObsC_abs[OF tC]
    apply auto
    done
next
  case (Kcknows a as \<psi>)
  have "?lhs (Kcknows as \<psi>)
      = (\<forall>y\<in>agent_abs a t.
           \<forall>x\<in>((\<Union>a\<in>set as. relations (spr_repMC (toSet (fst ec))) a)\<^sup>+ `` {y}).
              x \<in> toSet (eval_rec (spr_evalProp envVal) (spr_knowledge envObs (fst ec)) (spr_commonKnowledge envObs (fst ec))
                       (big_union (spr_commonKnowledge envObs (fst ec) as) (toList (snd ec))) \<psi>))"
    (* FIXME dreaming of a cong rule here. *)
    using toSet_def[symmetric] spr_simAbs_agent_abs[OF tC Kcknows(3)] spr_simAbs_tObsC_abs[OF tC Kcknows(3)]
    apply (clarsimp simp: toSet_eq_iff toSet_def[symmetric] subset_eq)
    apply (rule ball_cong[OF refl])
    apply (rule ball_cong)
    apply (subst spr_commonKnowledge_relation_image)
    apply (simp_all add: subsetD[OF agent_abs_tObsC_abs_subset[OF refl]])
    done
  also have "... = (\<forall>s\<in>agent_abs a t. spr_repMC (toSet (fst ec)), s \<Turnstile> Kcknows as \<psi>)"
    apply (rule ball_cong[OF refl])
    apply simp
    apply (rule ball_cong[OF refl])
    apply (subst eval_rec_models[OF spr_simAbs_fst_snd_trc[OF tC Kcknows(3), where as=as], symmetric])
     using spr_simAbs_agent_abs[OF tC Kcknows(3)] spr_simAbs_tObsC_abs[OF tC Kcknows(3)]
     apply (simp add: toSet_def[symmetric])
     apply (rule_tac x=y in bexI)
      apply (subst spr_commonKnowledge_relation_image)
       apply (auto elim: subsetD[OF agent_abs_tObsC_abs_subset[OF refl]])[1]
      apply simp
     apply assumption
    apply (rule refl)
    done
  also have "... = spr_repMC (toSet (fst ec)), s \<Turnstile> Kknows a (Kcknows as \<psi>)"
    using spr_simAbs_agent_abs[OF tC Kcknows(3)] spr_simAbs_tObsC_abs[OF tC Kcknows(3)]
          Kcknows(2) tC
    apply simp
    apply (rule ball_cong[OF _ refl])
    apply rule
     apply (clarsimp simp: subsetD[OF agent_abs_tObsC_abs_subset] agent_abs_spr_repRels[OF tC])
    apply (clarsimp elim!: agent_abs_rel_inv[OF tC Kcknows(3)])
    done

  also have "... = spr_repMC (toSet (fst ec)), s \<Turnstile> Kcknows as \<psi>"
    apply (rule S5n_common_knowledge_fixed_point_simpler[symmetric])
    using spr_simAbs_agent_abs[OF tC Kcknows(3)] spr_simAbs_tObsC_abs[OF tC Kcknows(3)]
          Kcknows(1) Kcknows(2)
      apply (auto elim: subsetD[OF agent_abs_tObsC_abs_subset[OF refl]])
    done
  finally show ?case .
qed simp_all

(*>*)
text\<open>

This function corresponds with the standard semantics:

\<close>

lemma eval_models:
  assumes tC: "t \<in> SPR.jkbpC"
  assumes ec: "spr_simAbs ec = SPRdet.sim_equiv_class a t"
  assumes subj_phi: "subjective a \<phi>"
  assumes s: "s \<in> toSet (snd ec)"
  shows "eval envVal envObs ec \<phi> \<longleftrightarrow> spr_repMC (toSet (fst ec)), s \<Turnstile> \<phi>"
(*<*)
  unfolding eval_def
  using evalS_models[OF tC ec subj_phi s]
  apply auto
  done
(*>*)

(* **************************************** *)

subsubsection\<open>Simulated actions\<close>

text\<open>

From a common equivalence class and a subjective equivalence class for
agent @{term "a"}, we can compute the actions enabled for @{term "a"}:

\<close>

definition (in -)
  spr_simAction ::
       "('a, 'p, 'aAct) JKBP \<Rightarrow> (('a, 'es, 'as) BEState \<Rightarrow> 'p \<Rightarrow> bool)
     \<Rightarrow> ('a \<Rightarrow> ('a, 'es, 'as) BEState \<Rightarrow> 'cobs \<times> 'as option)
     \<Rightarrow> 'a
     \<Rightarrow> ('a::linorder, 'es::linorder, 'as::linorder) spr_simWorldsRep
     \<Rightarrow> 'aAct list"
where
  "spr_simAction jkbp envVal envObs \<equiv> \<lambda>a ec.
    [ action gc. gc \<leftarrow> jkbp a, eval envVal envObs ec (guard gc) ]"
(*<*)

abbreviation
  spr_simAction :: "'a \<Rightarrow> ('a, 'es, 'as) spr_simWorldsRep \<Rightarrow> 'aAct list"
where
  "spr_simAction \<equiv> SPRViewDet.spr_simAction jkbp envVal envObs"

(*>*)
text\<open>

Using the above result about evaluation, we can relate \<open>spr_simAction\<close> to @{term "jAction"}. Firstly, \<open>spr_simAction\<close> behaves the same as @{term "jAction"} using the
@{term "spr_repMC"} structure:

\<close>

lemma spr_action_jaction:
  assumes tC: "t \<in> SPR.jkbpC"
  assumes ec: "spr_simAbs ec = SPRdet.sim_equiv_class a t"
  shows "set (spr_simAction a ec)
       = set (jAction (spr_repMC (toSet (fst ec))) (tFirst t, tLast t) a)"
(*<*)
  unfolding spr_simAction_def jAction_def
  apply clarsimp
  apply rule
   apply clarsimp
   apply (rule_tac x=xa in bexI)
    apply simp
   apply clarsimp
   apply (subst eval_models[OF tC ec, symmetric])
    using tC ec subj
    apply simp_all
    apply (rule agent_absI)
    apply simp_all
  apply clarsimp
  apply (rule_tac x=xa in bexI)
   apply simp
  apply clarsimp
  apply (subst eval_models[OF tC ec])
   using tC ec subj
   apply simp_all
  apply (rule agent_absI)
   apply simp_all
  done

lemma spr_submodel_aux:
  assumes tC: "t \<in> SPR.jkbpC"
      and s: "s \<in> worlds (spr_simMCt t)"
  shows "gen_model SPRdet.MCS s = gen_model (spr_simMCt t) s"
proof(rule gen_model_subset[where T="spr_jkbpCSt t"])
  fix a
  let ?X = "spr_sim ` { t' . t' \<in> SPR.jkbpC \<and> tObsC t = tObsC t' }"
  show "relations SPRdet.MCS a \<inter> ?X \<times> ?X
      = relations (spr_simMCt t) a \<inter> ?X \<times> ?X"
    by (simp add: Int_ac Int_absorb1
                  relation_mono[OF jkbpCSt_jkbpCS_subset jkbpCSt_jkbpCS_subset])
next
  let ?X = "spr_sim ` { t' . t' \<in> SPR.jkbpC \<and> tObsC t = tObsC t' }"
  from s show "(\<Union>a. relations (spr_simMCt t) a)\<^sup>* `` {s} \<subseteq> ?X"
    apply (clarsimp simp del: mkKripke_simps)
    apply (erule (1) kripke_rels_trc_worlds)
    apply auto
    done
next
  let ?Y = "{ t' . t' \<in> SPR.jkbpC \<and> tObsC t = tObsC t' }"
  let ?X = "spr_sim ` ?Y"
  from s obtain t'
    where st': "s = spr_sim t'"
      and t'C: "t' \<in> SPR.jkbpC"
      and t'O: "tObsC t = tObsC t'"
    by fastforce
  { fix t''
    assume tt': "(t', t'') \<in> (\<Union>a. relations SPR.MC a)\<^sup>*"
    from t'C tt' have t''C: "t'' \<in> SPR.jkbpC"
      by - (erule kripke_rels_trc_worlds, simp_all)
    from t'O tt' have t''O: "tObsC t = tObsC t''"
      by (simp add: spr_tObsC_trc_aux)
    from t''C t''O have "t'' \<in> ?Y" by simp }
  hence "(\<Union>a. relations SPR.MC a)\<^sup>* `` {t'} \<subseteq> ?Y"
    by clarsimp
  hence "spr_sim ` ((\<Union>a. relations SPR.MC a)\<^sup>* `` {t'}) \<subseteq> ?X"
    by (rule image_mono)
  with st' t'C
  show "(\<Union>a. relations SPRdet.MCS a)\<^sup>* `` {s} \<subseteq> ?X"
    using sim_trc_commute[OF SPR.mkM_kripke spr_sim, where t=t'] by simp
qed (insert s, auto)

(*>*)
text\<open>

We can connect the agent's choice of actions on the \<open>spr_repMC\<close> structure to those on the \<open>SPR.MC\<close> structure
using our earlier results about actions being preserved by generated
models and simulations.

\<close>

lemma spr_simAction:
  assumes tC: "t \<in> SPR.jkbpC"
  assumes ec: "spr_simAbs ec = SPRdet.sim_equiv_class a t"
  shows "set (spr_simAction a ec) = set (jAction SPR.MC t a)"
(*<*) (is "?lhs = ?rhs")
proof -
  from tC ec
  have "?lhs = set (jAction (spr_repMC (toSet (fst ec))) (tFirst t, tLast t) a)"
    by (rule spr_action_jaction)
  also from tC ec have "... = set (jAction (spr_simMCt t) (spr_sim t) a)"
    by (simp add: simulation_jAction_eq[OF _ spr_repSim] spr_sim_tObsC_abs)
  also from tC have "... = set (jAction SPRdet.MCS (spr_sim t) a)"
    using gen_model_jAction_eq[OF spr_submodel_aux[OF tC, where s="spr_sim t"], where w'="spr_sim t"]
          gen_model_world_refl[where w="spr_sim t" and M="spr_simMCt t"]
    by simp
  also from tC have "... = set (jAction SPR.MC t a)"
    by (simp add: simulation_jAction_eq[OF _ spr_sim])
  finally show ?thesis .
qed
(*>*)

(* **************************************** *)

subsubsection\<open>Simulated transitions\<close>

text\<open>

The story of simulated transitions takes some doing. We begin by
computing the successor relation of a given equivalence class @{term
"X"} with respect to the common equivalence class @{term "cec"}:

\<close>

abbreviation (in -)
  "spr_jAction jkbp envVal envObs cec s \<equiv> \<lambda>a.
     spr_simAction jkbp envVal envObs a (cec, spr_knowledge envObs cec a s)"

definition (in -)
  spr_trans :: "'a odlist
              \<Rightarrow> ('a, 'p, 'aAct) JKBP
              \<Rightarrow> (('a::linorder, 'es::linorder, 'as::linorder) BEState \<Rightarrow> 'eAct list)
              \<Rightarrow> ('eAct \<Rightarrow> ('a \<Rightarrow> 'aAct)
                  \<Rightarrow> ('a, 'es, 'as) BEState \<Rightarrow> ('a, 'es, 'as) BEState)
              \<Rightarrow> (('a, 'es, 'as) BEState \<Rightarrow> 'p \<Rightarrow> bool)
              \<Rightarrow> ('a \<Rightarrow> ('a, 'es, 'as) BEState \<Rightarrow> 'cobs \<times> 'as option)
                \<Rightarrow> ('a, 'es, 'as) spr_simWorldsECRep
                \<Rightarrow> ('a, 'es, 'as) spr_simWorldsECRep
                  \<Rightarrow> (('a, 'es, 'as) BEState \<times> ('a, 'es, 'as) BEState) list"
where
  "spr_trans agents jkbp envAction envTrans envVal envObs \<equiv> \<lambda>cec X.
    [ (initialS, succS) .
       (initialS, finalS) \<leftarrow> toList X,
       eact \<leftarrow> envAction finalS,
       succS \<leftarrow> [ envTrans eact aact finalS .
                   aact \<leftarrow> listToFuns (spr_jAction jkbp envVal envObs cec
                                                (initialS, finalS))
                                   (toList agents) ] ]"

text\<open>

We will split the result of this function according to the common
observation and also agent @{term "a"}'s observation, where @{term
"a"} is the agent we are constructing the automaton for.

\<close>

definition (in -)
  spr_simObsC :: "('es \<Rightarrow> 'cobs)
               \<Rightarrow> (('a::linorder, 'es::linorder, 'as::linorder) BEState
                 \<times> ('a, 'es, 'as) BEState) odlist
               \<Rightarrow> 'cobs"
where
  "spr_simObsC envObsC \<equiv> envObsC \<circ> es \<circ> snd \<circ> ODList.hd"

abbreviation (in -)
  envObs_rel :: "(('a, 'es, 'as) BEState \<Rightarrow> 'cobs \<times> 'as option)
              \<Rightarrow> ('a, 'es, 'as) spr_simWorlds \<times> ('a, 'es, 'as) spr_simWorlds \<Rightarrow> bool"
where
  "envObs_rel envObs \<equiv> \<lambda>(s, s'). envObs (snd s') = envObs (snd s)"

text\<open>

The above combine to yield the successor equivalence classes like so:

\<close>

definition (in -)
  spr_simTrans :: "'a odlist
              \<Rightarrow> ('a, 'p, 'aAct) JKBP
              \<Rightarrow> (('a::linorder, 'es::linorder, 'as::linorder) BEState \<Rightarrow> 'eAct list)
              \<Rightarrow> ('eAct \<Rightarrow> ('a \<Rightarrow> 'aAct)
                  \<Rightarrow> ('a, 'es, 'as) BEState \<Rightarrow> ('a, 'es, 'as) BEState)
              \<Rightarrow> (('a, 'es, 'as) BEState \<Rightarrow> 'p \<Rightarrow> bool)
              \<Rightarrow> ('es \<Rightarrow> 'cobs)
              \<Rightarrow> ('a \<Rightarrow> ('a, 'es, 'as) BEState \<Rightarrow> 'cobs \<times> 'as option)
               \<Rightarrow> 'a
               \<Rightarrow> ('a, 'es, 'as) spr_simWorldsRep
               \<Rightarrow> ('a, 'es, 'as) spr_simWorldsRep list"
where
  "spr_simTrans agents jkbp envAction envTrans envVal envObsC envObs \<equiv> \<lambda>a ec.
    let aSuccs = spr_trans agents jkbp envAction envTrans envVal envObs
                           (fst ec) (snd ec);
        cec' = ODList.fromList
                 (spr_trans agents jkbp envAction envTrans envVal envObs
                            (fst ec) (fst ec))
     in [ (ODList.filter (\<lambda>s. envObsC (es (snd s)) = spr_simObsC envObsC aec') cec',
           aec') .
          aec' \<leftarrow> map ODList.fromList (partition (envObs_rel (envObs a)) aSuccs) ]"
(*<*)

abbreviation
  spr_trans :: "('a, 'es, 'as) spr_simWorldsECRep
              \<Rightarrow> ('a, 'es, 'as) spr_simWorldsECRep
              \<Rightarrow> (('a, 'es, 'as) spr_simWorlds) list"
where
  "spr_trans \<equiv> SPRViewDet.spr_trans agents jkbp envAction envTrans envVal envObs"

abbreviation
  spr_simTrans :: "'a \<Rightarrow> ('a, 'es, 'as) spr_simWorldsRep \<Rightarrow> ('a, 'es, 'as) spr_simWorldsRep list"
where
  "spr_simTrans \<equiv> SPRViewDet.spr_simTrans agents jkbp envAction envTrans envVal envObsC envObs"

lemma spr_trans_aec:
  assumes tC: "t \<in> SPR.jkbpC"
      and ec: "spr_simAbs ec = SPRdet.sim_equiv_class a t"
  shows "set (spr_trans (fst ec) (snd ec))
       = { (tFirst t', s) |t' s. t' \<leadsto> s \<in> SPR.jkbpC \<and> spr_jview a t' = spr_jview a t }" (is "?lhs = ?rhs")
proof
  show "?lhs \<subseteq> ?rhs"
  proof
    fix x assume x: "x \<in> ?lhs"
    with assms show "x \<in> ?rhs"
      unfolding spr_trans_def
      apply (clarsimp simp del: split_paired_Ex split_paired_All simp add: toSet_def[symmetric] agent_abs_def)
      apply (rule_tac x=t' in exI)
      apply simp
      apply (rule_tac n="Suc (tLength t')" in SPR.jkbpCn_jkbpC_inc)
      apply (auto iff: Let_def simp del: split_paired_Ex split_paired_All)
      apply (simp add: listToFuns_ext[OF agents[unfolded toSet_def]])

      apply (rule_tac x=xa in exI)
      apply simp
      apply (subst (asm) spr_simAction)
        apply assumption
        apply rule
         apply clarsimp
         apply (clarsimp simp: spr_simAbs_def)
         apply (subst (asm) spr_knowledge)
          apply (simp add: ec)
          apply (erule tObsC_absI)
           apply simp_all
          apply (erule spr_jview_tObsC)
         using ec
         apply clarsimp (* FIXME *)

         apply (clarsimp simp: spr_repRels_def tObsC_abs_conv)
         apply (rule_tac x=t'b in image_eqI)
          apply (auto iff: spr_sim_def)[1]
         apply clarsimp
         apply (rule spr_jview_tObsCI[OF _ _ spr_jview_det_ps])
           apply simp_all
          apply (erule spr_jview_tObsC[symmetric])
          apply (erule spr_jview_tObsC[symmetric])
       apply clarsimp
       apply (clarsimp simp: spr_simAbs_def)
       apply (subst spr_knowledge)
        apply (simp_all add: ec)
        apply (erule tObsC_absI)
         apply (erule spr_jview_tObsC)
        apply simp_all
       apply (rule_tac x="tFirst xc" in exI)
       apply (rule_tac x="tLast xc" in exI)
       apply (simp add: spr_sim_def)
       apply rule
        apply (drule tObsC_abs_jview_eq)
        apply simp
        apply (erule tObsC_abs_jview_eq[symmetric])
       apply (clarsimp simp: spr_repRels_def tObsC_abs_conv)
       apply rule
        apply (rule spr_tFirst)
        apply simp
       apply rule
        apply (rule spr_tLast)
        apply simp
       apply rule
        apply (rule_tac x=t' in exI)
        apply simp
        apply (erule spr_jview_tObsC)
       apply (rule_tac x=xc in exI)
       apply simp
       apply (drule spr_jview_tObsC)
       apply (drule spr_jview_tObsC)
       apply simp
      apply (subst SPR.jkbpC_jkbpCn_jAction_eq[symmetric])
      apply auto
      done
  qed
  show "?rhs \<subseteq> ?lhs"
  proof
    fix x assume x: "x \<in> ?rhs"
    then obtain t' s
      where x': "x = (tFirst t', s)"
        and t'sC: "t' \<leadsto> s \<in> SPR.jkbpC"
        and F: "spr_jview a t' = spr_jview a t"
      by blast
    from t'sC have t'Cn: "t' \<in> SPR.jkbpCn (tLength t')" by blast
    from t'sC obtain eact aact
      where eact: "eact \<in> set (envAction (tLast t'))"
        and aact: "\<forall>a. aact a \<in> set (jAction (SPR.mkM (SPR.jkbpCn (tLength t'))) t' a)"
        and s: "s = envTrans eact aact (tLast t')"
      using SPR.jkbpC_tLength_inv[where t="t' \<leadsto> s" and n="Suc (tLength t')"]
      by (auto iff: Let_def)
    from tC t'sC ec F x' s eact aact
    show "x \<in> ?lhs"
      unfolding spr_trans_def
      apply (clarsimp simp del: split_paired_Ex split_paired_All simp: toSet_def[symmetric])
      apply (rule bexI[where x="(tFirst t', tLast t')"])
      apply simp
      apply (rule bexI[where x="eact"])
      apply (rule_tac x="aact" in image_eqI)
      apply simp_all
      apply (simp add: listToFuns_ext[OF agents[unfolded toSet_def]])
      defer
      apply blast
      apply (subst spr_simAction[where t=t'])
      apply blast
      defer
      apply (auto iff: SPR.jkbpC_jkbpCn_jAction_eq[OF t'Cn])[1]

      apply (clarsimp simp: spr_simAbs_def)
      apply (subst spr_knowledge)
      apply (simp_all add: ec)
      apply (rule tObsC_absI[where t=t and t'=t'])
       apply simp_all
       apply blast
       apply (blast intro: spr_jview_tObsC)
      apply (clarsimp simp: spr_repRels_def tObsC_abs_conv)
      apply rule
       apply clarsimp
       apply (rule_tac x=t'aa in image_eqI)
        apply (auto iff: spr_sim_def)[1]
       apply simp
       apply (rule spr_jview_tObsCI[OF _ _ spr_jview_det_ps])
       apply simp_all
       apply (erule spr_jview_tObsC[symmetric])
       apply blast
       apply (erule spr_jview_tObsC[symmetric])
      apply (clarsimp simp: spr_sim_def)
      apply rule
       apply (drule tObsC_abs_jview_eq)
       apply (drule tObsC_abs_jview_eq)
       apply simp
      apply rule
      apply (rule spr_tFirst)
       apply simp
      apply rule
      apply (rule spr_tLast)
       apply simp
      apply rule
       apply (rule_tac x=t' in exI)
       apply (auto dest: spr_jview_tObsC intro: spr_jview_tObsC_trans)
      done
  qed
qed

lemma spr_trans_cec:
  assumes tC: "t \<in> SPR.jkbpC"
      and ec: "spr_simAbs ec = SPRdet.sim_equiv_class a t"
  shows "set (spr_trans (fst ec) (fst ec))
       = { (tFirst t', s) |t' s. t' \<leadsto> s \<in> SPR.jkbpC \<and> tObsC t' = tObsC t }" (is "?lhs = ?rhs")
proof
  show "?lhs \<subseteq> ?rhs"
  proof
    fix x assume x: "x \<in> ?lhs"
    with assms show "x \<in> ?rhs"
      unfolding spr_trans_def
      apply (clarsimp simp del: split_paired_Ex split_paired_All simp add: toSet_def[symmetric] tObsC_abs_def)
      apply (rule_tac x=t' in exI)
      apply simp
      apply (rule_tac n="Suc (tLength t')" in SPR.jkbpCn_jkbpC_inc)
      apply (auto iff: Let_def simp del: split_paired_Ex split_paired_All)
      apply (simp add: listToFuns_ext[OF agents[unfolded toSet_def]])

      apply (rule_tac x=xa in exI)
      apply simp
      apply (subst (asm) spr_simAction)
        apply assumption
       apply rule
        apply clarsimp
        apply (clarsimp simp: spr_simAbs_def)
        apply (subst (asm) spr_knowledge)
         apply (simp add: ec)
         apply (erule tObsC_absI)
          apply simp_all
        apply (clarsimp simp: spr_repRels_def tObsC_abs_conv ec)
        apply (rule_tac x=t'b in image_eqI)
         apply (auto iff: spr_sim_def ec)[1]
        apply clarsimp
        apply (rule spr_jview_tObsCI[OF _ _ spr_jview_det_ps])
         apply simp_all
       apply (clarsimp simp: spr_simAbs_def)
       apply (subst spr_knowledge)
        apply (simp_all add: ec)
        apply (erule tObsC_absI)
        apply simp_all
       apply (rule_tac x="tFirst xc" in exI)
       apply (rule_tac x="tLast xc" in exI)
       apply (simp add: spr_sim_def)
       apply rule
        apply (drule tObsC_abs_jview_eq)
        apply auto[1]
       apply (clarsimp simp: spr_repRels_def tObsC_abs_conv)
       apply rule
        apply (rule spr_tFirst)
        apply simp
       apply rule
        apply (rule spr_tLast)
        apply simp
       apply rule
        apply (rule_tac x=t' in exI)
        apply simp
       apply (rule_tac x=xc in exI)
       apply simp
       apply (drule spr_jview_tObsC)
       apply simp
      apply (subst SPR.jkbpC_jkbpCn_jAction_eq[symmetric])
      apply auto
      done
  qed
  show "?rhs \<subseteq> ?lhs"
  proof
    fix x assume x: "x \<in> ?rhs"
    then obtain t' s
      where x': "x = (tFirst t', s)"
        and t'sC: "t' \<leadsto> s \<in> SPR.jkbpC"
        and F: "tObsC t' = tObsC t"
      by blast
    from t'sC have t'Cn: "t' \<in> SPR.jkbpCn (tLength t')" by blast
    from t'sC obtain eact aact
      where eact: "eact \<in> set (envAction (tLast t'))"
        and aact: "\<forall>a. aact a \<in> set (jAction (SPR.mkM (SPR.jkbpCn (tLength t'))) t' a)"
        and s: "s = envTrans eact aact (tLast t')"
      using SPR.jkbpC_tLength_inv[where t="t' \<leadsto> s" and n="Suc (tLength t')"]
      by (auto iff: Let_def)
    from tC t'sC ec F x' s eact aact
    show "x \<in> ?lhs"
      unfolding spr_trans_def
      apply (clarsimp simp del: split_paired_Ex split_paired_All simp: toSet_def[symmetric])
      apply (rule bexI[where x="(tFirst t', tLast t')"])
      apply simp
      apply (rule bexI[where x="eact"])
      apply (rule_tac x="aact" in image_eqI)
      apply simp_all
      apply (simp add: listToFuns_ext[OF agents[unfolded toSet_def]])
      defer
      apply blast
      apply (subst spr_simAction[where t=t'])
      apply blast
      defer
      apply (auto iff: SPR.jkbpC_jkbpCn_jAction_eq[OF t'Cn])[1]

      apply (clarsimp simp: spr_simAbs_def)
      apply (subst spr_knowledge)
      apply (simp_all add: ec)
      apply (rule tObsC_absI[where t=t and t'=t'])
       apply simp_all
       apply blast
      apply (clarsimp simp: spr_repRels_def tObsC_abs_conv)
      apply rule
       apply clarsimp
       apply (rule_tac x=t'aa in image_eqI)
        apply (auto iff: spr_sim_def [abs_def])[1]
       apply simp
       apply (rule spr_jview_tObsCI[OF _ _ spr_jview_det_ps])
       apply simp_all
       apply blast
      apply (clarsimp simp: spr_sim_def [abs_def])
      apply (rule conjI)
       apply (auto dest!: tObsC_abs_jview_eq intro: spr_tFirst spr_tLast)[1]
      apply (rule conjI)
      apply (auto intro: spr_tFirst)[1]
      apply (rule conjI)
       apply (auto intro: spr_tLast)[1]
      apply (rule conjI)
       apply (auto intro: spr_tLast)[1]
      apply (rule_tac x=xb in exI)
      apply (auto dest: spr_jview_tObsC intro: spr_jview_tObsC_trans)[1]
      done
  qed
qed

lemma spr_simObsC:
    assumes t'sC: "t \<leadsto> s \<in> SPR.jkbpC"
        and aec': "toSet aec = (rel_ext (envObs_rel (envObs a)) \<inter> X \<times> X) `` {(tFirst t, s)}"
        and X: "X = {(tFirst t', s) |t' s. t' \<leadsto> s \<in> SPR.jkbpC \<and> spr_jview a t' = spr_jview a t}"
    shows "spr_simObsC envObsC aec = envObsC (es s)"
  unfolding spr_simObsC_def
  apply (cases aec)
   using assms
   apply auto[1]
  using assms
  apply (simp add: ODList.hd_def toList_fromList)
  apply (subgoal_tac "x \<in> insert x (set xs)")
   apply (auto iff: envObs_def)[1]
  apply blast
  done

lemma envObs_rel_equiv:
  "equiv UNIV (rel_ext (envObs_rel (envObs a)))"
  by (intro equivI refl_onI symI transI) auto

(*>*)
text\<open>

Showing that \<open>spr_simTrans\<close> works requires a series of
auxiliary lemmas that show we do in fact compute the correct successor
equivalence classes. We elide the unedifying details, skipping
straight to the lemma that the @{term "Algorithm"} locale expects:

\<close>

lemma spr_simTrans:
  assumes tC: "t \<in> SPR.jkbpC"
  assumes ec: "spr_simAbs ec = SPRdet.sim_equiv_class a t"
  shows "spr_simAbs ` set (spr_simTrans a ec)
      = { SPRdet.sim_equiv_class a (t' \<leadsto> s)
          |t' s. t' \<leadsto> s \<in> SPR.jkbpC \<and> spr_jview a t' = spr_jview a t}"
(*<*)(is "?lhs = ?rhs")
proof
  show "?lhs \<subseteq> ?rhs"
  proof
    fix x assume x: "x \<in> ?lhs"
    then obtain rx
      where xrx: "x = spr_simAbs rx"
        and rx: "rx \<in> set (spr_simTrans a ec)" by blast
    with tC ec obtain cec' aec' UV' t' s
      where rxp: "rx = (cec', aec')"
        and t'sC: "t' \<leadsto> s \<in> SPR.jkbpC"
        and tt': "spr_jview a t' = spr_jview a t"
        and aec': "toSet aec' = (rel_ext (envObs_rel (envObs a)) \<inter> set (spr_trans (fst ec) (snd ec))
                                                       \<times> set (spr_trans (fst ec) (snd ec))) `` {(tFirst t', s)}"
        and cec': "cec' = ODList.filter (\<lambda>s. envObsC (es (snd s)) = spr_simObsC envObsC aec') (fromList (spr_trans (fst ec) (fst ec)))"
      unfolding spr_simTrans_def
      using spr_trans_aec[OF assms]
      apply (auto split: prod.split_asm)
      apply (drule imageI[where f=set])
      apply (simp add: partition[OF envObs_rel_equiv subset_UNIV])
      apply (erule quotientE)
      apply fastforce
      done
    from t'sC tt' aec' cec'
    have "spr_simAbs (cec', aec') = SPRdet.sim_equiv_class a (t' \<leadsto> s)"
      unfolding spr_simAbs_def
      apply clarsimp
      apply rule
       using spr_trans_aec[OF assms] spr_trans_cec[OF assms]
       apply clarsimp
       apply (rule_tac x="t'aa \<leadsto> s'" in image_eqI)
        apply (simp add: spr_sim_def)
        apply (cut_tac aec=aec' and t=t' and s=s in spr_simObsC[where a=a])
        apply simp_all
        apply rule
         apply clarsimp
         apply (erule_tac t'="t'b \<leadsto> sa" in tObsC_absI)
          apply simp_all
          apply (auto dest: spr_jview_tObsC iff: tObsC_def envObs_def_raw)[1]
        apply (clarsimp simp: envObs_def_raw tObsC_abs_conv)
        apply (case_tac t'b)
         apply (simp add: tObsC_def)
        apply clarsimp
        apply (rename_tac Trace State)
        apply (rule_tac x=Trace in exI)
        apply (auto dest: spr_jview_tObsC simp: tObsC_def)[1]
       apply (simp add: spr_jview_def)
      using spr_trans_aec[OF assms] spr_trans_cec[OF assms]
      apply (clarsimp simp: spr_sim_def)
      apply (cut_tac aec=aec' and t=t' and s=s in spr_simObsC[where a=a])
       apply simp_all
      apply (frule spr_jview_tStep_eq_inv)
      apply clarsimp
      apply safe
       apply (clarsimp simp: tObsC_abs_conv)
       apply (case_tac t'a)
        apply (simp add: tObsC_def)
       apply clarsimp
       apply (rename_tac Trace State)
       apply (rule_tac x="Trace" in exI)
       apply (drule spr_jview_prefix_closed)
       apply (auto dest: spr_jview_tObsC simp: tObsC_def)[1]

       apply (auto simp: spr_jview_def Let_def envObs_def_raw)[1]

       apply (erule_tac t'="t'a \<leadsto> sa" in tObsC_absI)
        apply simp_all

        apply (drule spr_jview_tObsC[symmetric])
        apply (frule spr_jview_prefix_closed)
        apply (auto dest: spr_jview_tObsC simp: tObsC_def)[1]

        apply (simp add: spr_jview_def)
        apply auto[1]
        apply (rule_tac x="t''" in exI)
        apply (drule spr_jview_prefix_closed)
        apply simp
        done
    with xrx rxp t'sC tt'
    show "x \<in> ?rhs"
      apply simp
      apply (rule_tac x=t' in exI)
      apply (rule_tac x=s in exI)
      apply simp
      done
  qed
next
  note image_cong_simp [cong del]
  show "?rhs \<subseteq> ?lhs"
  proof
    fix x assume x: "x \<in> ?rhs"
    then obtain t' s
      where t'sC: "t' \<leadsto> s \<in> SPR.jkbpC"
        and tt': "spr_jview a t' = spr_jview a t"
        and xt's: "x = SPRdet.sim_equiv_class a (t' \<leadsto> s)"
      by auto
    then have "(\<lambda>s. (sprFst s, sprLst s)) ` x \<in> set ` set (partition (envObs_rel (envObs a)) (spr_trans (fst ec) (snd ec)))"
      apply (simp add: partition[OF envObs_rel_equiv] spr_trans_aec[OF assms] spr_sim_def [abs_def])
      apply (rule_tac x="(tFirst t', s)" in quotientI2)
       apply auto[1]
      apply (auto dest: spr_jview_tStep_eq_inv)
       apply (frule spr_jview_tStep_eq_inv)
       apply clarsimp
       apply (drule spr_jview_prefix_closed)
       apply auto[1]
      apply (rule_tac x="\<lparr>sprFst = tFirst t'aa, sprLst = sa, sprCRel = tObsC_abs (t'aa \<leadsto> sa)\<rparr>" in image_eqI)
       apply simp
      apply (rule_tac x="t'aa \<leadsto> sa" in image_eqI)
       apply simp
      apply (simp add: spr_jview_def)
      done
    then obtain rx
      where "rx \<in> set (partition (envObs_rel (envObs a)) (spr_trans (fst ec) (snd ec)))"
        and "set rx = (\<lambda>s. (sprFst s, sprLst s)) ` x"
      by auto
    with t'sC tt' xt's show "x \<in> ?lhs"
      unfolding spr_simTrans_def
      apply clarsimp
      apply (rule_tac x="(ODList.filter (\<lambda>s. envObsC (es (snd s)) = spr_simObsC envObsC (fromList rx)) (fromList (spr_trans (fst ec) (fst ec))), fromList rx)" in image_eqI)
       prefer 2
       apply (rule_tac x="rx" in image_eqI)
        apply simp
       apply simp

       apply (subst spr_simObsC[where a=a and t=t' and s=s, OF _ _ refl])
        apply simp_all
        apply rule
         apply clarsimp
         apply (frule spr_jview_tStep_eq_inv)
         apply (auto simp: spr_jview_def spr_sim_def [abs_def])[1]
        apply clarsimp
        apply (rule_tac x="spr_sim (t'aa \<leadsto> sa)" in image_eqI)
         apply (simp add: spr_sim_def [abs_def])
        apply (rule_tac x="t'aa \<leadsto> sa" in image_eqI)
         apply simp
        apply (simp add: spr_jview_def)

       apply (clarsimp simp: spr_trans_cec[OF assms] spr_sim_def [abs_def] spr_simAbs_def)
       apply rule
        apply (auto iff: tObsC_abs_conv)[1]
         apply (frule spr_jview_tStep_eq_inv)
         apply clarsimp
         apply (frule tObsC_tStep_eq_inv)
         apply clarsimp
         apply (drule spr_jview_prefix_closed)
         apply (drule spr_jview_tObsC)
         apply (drule spr_jview_tObsC)
         apply (drule tObsC_prefix_closed)
         apply (rule_tac x=t''a in exI)
         apply simp

         apply (frule spr_jview_tStep_eq_inv)
         apply clarsimp
         apply (frule tObsC_tStep_eq_inv)
         apply clarsimp
         apply (drule spr_jview_tObsC) back
         apply (simp add: tObsC_def)

         apply (rule_tac x="t'a \<leadsto> sa" in exI)
         apply simp
         apply (frule spr_jview_tStep_eq_inv)
         apply clarsimp
         apply (drule spr_jview_tObsC)
         apply (frule spr_jview_tObsC)
         apply (simp add: tObsC_def)

         apply (rule_tac x="spr_sim ta" in image_eqI)
          apply (simp add: spr_sim_def [abs_def])
         apply (rule_tac x=ta in image_eqI)
          apply (simp add: spr_sim_def [abs_def])
         apply simp
       apply clarsimp
       apply (rule_tac x=ta in image_eqI)
        prefer 2
        apply simp
        apply (clarsimp simp: tObsC_abs_def)
        apply auto[1]

        apply (rule_tac x="t'a \<leadsto> sa" in exI)
        apply simp
        apply (frule spr_jview_tStep_eq_inv)
        apply clarsimp
        apply (drule spr_jview_tObsC)
        apply (frule spr_jview_tObsC)
        apply (simp add: tObsC_def)

        apply (frule spr_jview_tStep_eq_inv)
        apply clarsimp
        apply (frule tObsC_tStep_eq_inv)
        apply clarsimp
        apply (rule_tac x="t''a" in exI)
        apply (drule spr_jview_tObsC)
        apply (frule spr_jview_tObsC)
        apply (simp add: tObsC_def)

        apply (frule spr_jview_tStep_eq_inv)
        apply clarsimp
        apply (frule tObsC_tStep_eq_inv)
        apply clarsimp
        apply (drule spr_jview_tObsC) back
        apply (simp add: tObsC_def)
        done
  qed
qed

(*>*)
text\<open>

The explicit-state approach sketched above is quite inefficient, and
also some distance from the symbolic techniques we use in
\S\ref{sec:kbps-prag-algorithmics}. However it does suffice to
demonstrate the theory on the muddy children example in
\S\ref{sec:kbps-theory-mc}.

\<close>

end (* context FiniteDetBroadcastEnvironment *)

subsubsection\<open>Maps\<close>

text\<open>

As always we use a pair of tries. The domain of these maps is the pair
of relations.

\<close>

type_synonym ('a, 'es, 'obs, 'as) trans_trie
    = "(('a, 'es, 'as) BEState,
        (('a, 'es, 'as) BEState,
          (('a, 'es, 'as) BEState,
           (('a, 'es, 'as) BEState,
            ('obs, ('a, 'es, 'as) spr_simWorldsRep) mapping) trie) trie) trie) trie"

type_synonym
  ('a, 'es, 'aAct, 'as) acts_trie
    = "(('a, 'es, 'as) BEState,
        (('a, 'es, 'as) BEState,
          (('a, 'es, 'as) BEState,
           (('a, 'es, 'as) BEState, 'aAct) trie) trie) trie) trie"
(*<*)

definition
  trans_MapOps_lookup :: "('a :: linorder, 'es :: linorder, 'obs, 'as :: linorder) trans_trie
                        \<Rightarrow> ('a, 'es, 'as) spr_simWorldsRep \<times> 'obs
                        \<rightharpoonup> ('a, 'es, 'as) spr_simWorldsRep"
where
  "trans_MapOps_lookup \<equiv> \<lambda>m ((cec, aec), obs).
     Option.bind (lookup_trie m (map fst (toList cec)))
      (\<lambda>m. Option.bind (lookup_trie m (map snd (toList cec)))
       (\<lambda>m. Option.bind (lookup_trie m (map fst (toList aec)))
        (\<lambda>m. Option.bind (lookup_trie m (map snd (toList aec)))
         (\<lambda>m. Mapping.lookup m obs))))"

definition
  trans_MapOps_update :: "('a, 'es, 'as) spr_simWorldsRep \<times> 'obs
                        \<Rightarrow> ('a, 'es, 'as) spr_simWorldsRep
                        \<Rightarrow> ('a :: linorder, 'es :: linorder, 'obs, 'as :: linorder) trans_trie
                        \<Rightarrow> ('a, 'es, 'obs, 'as) trans_trie"
where
  "trans_MapOps_update \<equiv> \<lambda>((cec, aec), obs) v m.
     trie_update_with' (map fst (toList cec)) m empty_trie
      (\<lambda>m. trie_update_with' (map snd (toList cec)) m empty_trie
       (\<lambda>m. trie_update_with' (map fst (toList aec)) m empty_trie
        (\<lambda>m. trie_update_with' (map snd (toList aec)) m Mapping.empty
         (\<lambda>m. Mapping.update obs v m))))"

definition
  trans_MapOps :: "(('a :: linorder, 'es :: linorder, 'obs, 'as :: linorder) trans_trie,
                    ('a, 'es, 'as) spr_simWorldsRep \<times> 'obs,
                    ('a, 'es, 'as) spr_simWorldsRep) MapOps"
where
  "trans_MapOps \<equiv>
     \<lparr> MapOps.empty = empty_trie,
       lookup = trans_MapOps_lookup,
       update = trans_MapOps_update \<rparr>"

lemma (in FiniteDetBroadcastEnvironment) trans_MapOps[intro, simp]:
  "MapOps (\<lambda>k. (spr_simAbs (fst k), snd k)) (SPRdet.jkbpSEC \<times> UNIV) trans_MapOps"
proof
  fix k show "MapOps.lookup trans_MapOps (MapOps.empty trans_MapOps) k = None"
    unfolding trans_MapOps_def trans_MapOps_lookup_def
    by (auto split: prod.split)
next
  fix e k k' M
  assume k: "(spr_simAbs (fst k), snd k) \<in> SPRdet.jkbpSEC \<times> (UNIV :: 'z set)"
     and k': "(spr_simAbs (fst k'), snd k') \<in> SPRdet.jkbpSEC \<times> (UNIV :: 'z set)"
  show "MapOps.lookup trans_MapOps (MapOps.update trans_MapOps k e M) k'
         = (if (spr_simAbs (fst k'), snd k') = (spr_simAbs (fst k), snd k)
             then Some e else MapOps.lookup trans_MapOps M k')"
  proof(cases "(spr_simAbs (fst k'), snd k') = (spr_simAbs (fst k), snd k)")
    case True hence "k = k'"
      using inj_onD[OF spr_simAbs_inj_on] k k' by (auto iff: prod_eqI)
    thus ?thesis
      unfolding trans_MapOps_def trans_MapOps_lookup_def trans_MapOps_update_def
      by (auto simp: lookup_update lookup_trie_update_with split: option.split prod.split)
  next
    have *: "\<And> y ya. y \<noteq> ya \<Longrightarrow> Mapping.lookup (Mapping.update y e Mapping.empty) ya = None" by transfer simp
    case False thus ?thesis
      unfolding trans_MapOps_def trans_MapOps_lookup_def trans_MapOps_update_def
      by (auto dest: map_prod_eq simp: lookup_trie_update_with split: option.split prod.split intro!: lookup_update_neq *)
  qed
qed

(* A map for the agent actions. *)

definition
  acts_MapOps_lookup :: "('a :: linorder, 'es :: linorder, 'aAct, 'as :: linorder) acts_trie
                       \<Rightarrow> ('a, 'es, 'as) spr_simWorldsRep
                       \<rightharpoonup> 'aAct"
where
  "acts_MapOps_lookup \<equiv> \<lambda>m (cec, aec).
     Option.bind (lookup_trie m (map fst (toList cec)))
      (\<lambda>m. Option.bind (lookup_trie m (map snd (toList cec)))
       (\<lambda>m. Option.bind (lookup_trie m (map fst (toList aec)))
        (\<lambda>m. lookup_trie m (map snd (toList aec)))))"

definition
  acts_MapOps_update :: "('a, 'es, 'as) spr_simWorldsRep
                       \<Rightarrow> 'aAct
                       \<Rightarrow> ('a :: linorder, 'es :: linorder, 'aAct, 'as :: linorder) acts_trie
                       \<Rightarrow> ('a, 'es, 'aAct, 'as) acts_trie"
where
  "acts_MapOps_update \<equiv> \<lambda>(cec, aec) pAct m.
     trie_update_with' (map fst (toList cec)) m empty_trie
      (\<lambda>m. trie_update_with' (map snd (toList cec)) m empty_trie
       (\<lambda>m. trie_update_with' (map fst (toList aec)) m empty_trie
        (\<lambda>m. trie_update (map snd (toList aec)) pAct m)))"

definition
  acts_MapOps :: "(('a :: linorder, 'es :: linorder, 'aAct, 'as :: linorder) acts_trie,
                   ('a, 'es, 'as) spr_simWorldsRep,
                   'aAct) MapOps"
where
  "acts_MapOps \<equiv>
     \<lparr> MapOps.empty = empty_trie,
       lookup = acts_MapOps_lookup,
       update = acts_MapOps_update \<rparr>"

lemma (in FiniteDetBroadcastEnvironment) acts_MapOps[intro, simp]:
  "MapOps spr_simAbs SPRdet.jkbpSEC acts_MapOps"
proof
  fix k show "MapOps.lookup acts_MapOps (MapOps.empty acts_MapOps) k = None"
    unfolding acts_MapOps_def acts_MapOps_lookup_def by auto
next
  fix e k k' M
  assume k: "spr_simAbs k \<in> SPRdet.jkbpSEC"
     and k': "spr_simAbs k' \<in> SPRdet.jkbpSEC"
  show "MapOps.lookup acts_MapOps (MapOps.update acts_MapOps k e M) k'
         = (if spr_simAbs k' = spr_simAbs k
             then Some e else MapOps.lookup acts_MapOps M k')"
  proof(cases "spr_simAbs k' = spr_simAbs k")
    case True hence "k = k'"
      using inj_onD[OF spr_simAbs_inj_on] k k' by (auto iff: prod_eqI)
    thus ?thesis
      unfolding acts_MapOps_def acts_MapOps_lookup_def acts_MapOps_update_def
      by (auto simp: lookup_trie_update_with lookup_trie_update split: option.split prod.split)
  next
    case False thus ?thesis
      unfolding acts_MapOps_def acts_MapOps_lookup_def acts_MapOps_update_def
      by (auto dest: map_prod_eq simp: lookup_trie_update_with lookup_trie_update split: option.split prod.split)
  qed
qed

(*>*)
text\<open>

This suffices to placate the @{term "Algorithm"} locale.

\<close>

sublocale FiniteDetBroadcastEnvironment
        < SPRdet: Algorithm
            jkbp envInit envAction envTrans envVal
            spr_jview envObs spr_jviewInit spr_jviewIncr
            spr_sim spr_simRels spr_simVal
            spr_simAbs spr_simObs spr_simInit spr_simTrans spr_simAction
            acts_MapOps trans_MapOps
(*<*)
  apply (unfold_locales)

  using spr_simInit
  apply auto[1]

  using spr_simObs
  apply auto[1]

  using spr_simAction
  apply auto[1]

  using spr_simTrans
  apply auto[1]

  apply (rule acts_MapOps)
  apply (rule trans_MapOps)

  done

definition
  "mkSPRDetAuto \<equiv> \<lambda>agents jkbp envInit envAction envTrans envVal envObsC envObs.
    mkAlgAuto acts_MapOps
              trans_MapOps
              (spr_simObs envObsC)
              (spr_simInit envInit envObsC envObs)
              (spr_simTrans agents jkbp envAction envTrans envVal envObsC envObs)
              (spr_simAction jkbp envVal envObs)
              (\<lambda>a. map (spr_simInit envInit envObsC envObs a \<circ> envObs a) envInit)"

lemma (in FiniteDetBroadcastEnvironment) mkSPRDetAuto_implements:
  "SPR.implements (mkSPRDetAuto agents jkbp envInit envAction envTrans envVal envObsC envObs)"
  using SPRdet.k_mkAlgAuto_implements
  unfolding mkSPRDetAuto_def mkAlgAuto_def SPRdet.k_frontier_def
  by simp

(*

We actually run this unfolding of the algorithm. The lemma is keeping
us honest.

*)

definition
  "SPRDetAutoDFS \<equiv> \<lambda>agents jkbp envInit envAction envTrans envVal envObsC envObs. \<lambda>a.
    alg_dfs acts_MapOps
            trans_MapOps
            (spr_simObs envObsC a)
            (spr_simTrans agents jkbp envAction envTrans envVal envObsC envObs a)
            (spr_simAction jkbp envVal envObs a)
            (map (spr_simInit envInit envObsC envObs a \<circ> envObs a) envInit)"

lemma (in FiniteDetBroadcastEnvironment)
  "mkSPRDetAuto agents jkbp envInit envAction envTrans envVal envObsC envObs
 = (\<lambda>a. alg_mk_auto acts_MapOps trans_MapOps
           (spr_simInit a)
           (SPRDetAutoDFS agents jkbp envInit envAction envTrans envVal envObsC envObs a))"
  unfolding mkSPRDetAuto_def mkAlgAuto_def SPRDetAutoDFS_def alg_mk_auto_def by (simp add: Let_def)

(*>*)
text\<open>

As we remarked earlier in this section, in general it may be difficult
to establish the determinacy of a KBP as it is a function of the
environment. However in many cases determinism is syntactically
manifest as the guards are logically disjoint, independently of the
knowledge subformulas. The following lemma generates the required
proof obligations for this case:

\<close>

lemma (in PreEnvironmentJView) jkbpDetI:
  assumes tC: "t \<in> jkbpC"
  assumes jkbpSynDet: "\<forall>a. distinct (map guard (jkbp a))"
  assumes jkbpSemDet: "\<forall>a gc gc'.
        gc \<in> set (jkbp a) \<and> gc' \<in> set (jkbp a) \<and> t \<in> jkbpC
    \<longrightarrow> guard gc = guard gc' \<or> \<not>(MC, t \<Turnstile> guard gc \<and> MC, t \<Turnstile> guard gc')"
  shows "length (jAction MC t a) \<le> 1"
(*<*)
proof -
  { fix a X
    assume "set X \<subseteq> set (jkbp a)"
       and "distinct (map guard X)"
    with tC have "length [ action gc . gc \<leftarrow> X, MC, t \<Turnstile> guard gc ] \<le> 1"
      apply (induct X)
      using jkbpSemDet[rule_format, where a=a]
      apply auto
      done }
  from this[OF subset_refl jkbpSynDet[rule_format]] show ?thesis
    unfolding jAction_def by simp
qed

(*>*)
text\<open>

The scenario presented here is a variant of the broadcast environments
treated by \citet{Ron:1996}, which we cover in the next section.

\FloatBarrier

\<close>
(*<*)
end
(*>*)
