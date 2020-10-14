(*<*)
theory SPRViewNonDet
imports
  SPRView
  KBPsAuto
begin
(*>*)

subsection\<open>Perfect Recall in Non-deterministic Broadcast Environments\<close>

text_raw\<open>
\begin{figure}[ht]
\begin{isabellebody}%
\<close>
record ('a, 'ePubAct, 'es, 'pPubAct, 'ps) BEState =
  es :: "'es"
  ps :: "'a \<Rightarrow> 'ps"
  pubActs :: "'ePubAct \<times> ('a \<Rightarrow> 'pPubAct)"

locale FiniteBroadcastEnvironment =
  Environment jkbp envInit envAction envTrans envVal envObs
    for jkbp :: "('a :: finite, 'p, ('pPubAct :: finite \<times> 'ps :: finite)) JKBP"
    and envInit
         :: "('a, 'ePubAct :: finite, 'es :: finite, 'pPubAct, 'ps) BEState list"
    and envAction :: "('a, 'ePubAct, 'es, 'pPubAct, 'ps) BEState
                   \<Rightarrow> ('ePubAct \<times> 'ePrivAct) list"
    and envTrans :: "('ePubAct \<times> 'ePrivAct)
                  \<Rightarrow> ('a \<Rightarrow> ('pPubAct \<times> 'ps))
                  \<Rightarrow> ('a, 'ePubAct, 'es, 'pPubAct, 'ps) BEState
                  \<Rightarrow> ('a, 'ePubAct, 'es, 'pPubAct, 'ps) BEState"
    and envVal :: "('a, 'ePubAct, 'es, 'pPubAct, 'ps) BEState \<Rightarrow> 'p \<Rightarrow> bool"
    and envObs :: "'a \<Rightarrow> ('a, 'ePubAct, 'es, 'pPubAct, 'ps) BEState
                \<Rightarrow> ('cobs \<times> 'ps \<times> ('ePubAct \<times> ('a \<Rightarrow> 'pPubAct)))"

+ fixes envObsC :: "'es \<Rightarrow> 'cobs"
    and envActionES :: "'es \<Rightarrow> ('ePubAct \<times> ('a \<Rightarrow> 'pPubAct))
                            \<Rightarrow> ('ePubAct \<times> 'ePrivAct) list"
    and envTransES :: "('ePubAct \<times> 'ePrivAct) \<Rightarrow> ('a \<Rightarrow> 'pPubAct)
                    \<Rightarrow> 'es \<Rightarrow> 'es"
  defines envObs_def: "envObs a \<equiv> (\<lambda>s. (envObsC (es s), ps s a, pubActs s))"
      and envAction_def: "envAction s \<equiv> envActionES (es s) (pubActs s)"
      and envTrans_def:
           "envTrans eact aact s \<equiv> \<lparr> es = envTransES eact (fst \<circ> aact) (es s)
                                    , ps = snd \<circ> aact
                                    , pubActs = (fst eact, fst \<circ> aact) \<rparr>"
text_raw\<open>
  \end{isabellebody}%
  \caption{Finite broadcast environments with non-deterministic KBPs.}
  \label{fig:kbps-theory-broadcast-envs}
\end{figure}
\<close>

(*<*)
instance BEState_ext :: (finite, finite, finite, finite, finite, finite) finite
proof
 let ?U = "UNIV :: ('a, 'b, 'c, 'd, 'e, 'f) BEState_ext set"
 { fix x :: "('a, 'b, 'c, 'd, 'e, 'f) BEState_scheme"
   have "\<exists>a b c d. x = BEState_ext a b c d"
     by (cases x) simp
 } then have U:
   "?U = (\<lambda>(((a, b), c), d). BEState_ext a b c d) ` (((UNIV \<times> UNIV) \<times> UNIV) \<times> UNIV)"
     by (auto simp add: image_def)
 show "finite ?U" by (simp add: U)
qed

(*>*)
text\<open>

\label{sec:kbps-theory-spr-non-deterministic-protocols}

For completeness we reproduce the results of \citet{Ron:1996}
regarding non-deterministic KBPs in broadcast environments.

The determinism requirement is replaced by the constraint that actions
be split into public and private components, where the private part
influences the agents' private states, and the public part is
broadcast and recorded in the system state. Moreover the protocol of
the environment is only a function of the environment state, and not
the agents' private states. Once again an agent's view consists of the
common observation and their private state. The situation is described
by the locale in Figure~\ref{fig:kbps-theory-broadcast-envs}. Note
that as we do not intend to generate code for this case, we adopt more
transparent but less effective representations.

Our goal in the following is to instantiate the @{term
"SimIncrEnvironment"} locale with respect to the assumptions made in
the @{term "FiniteBroadcastEnvironment"} locale. We begin by defining
similar simulation machinery to the previous section.

\<close>

context FiniteBroadcastEnvironment
begin

text\<open>

As for the deterministic variant, we abstract traces using the common
observation. Note that this now includes the public part of the
agents' actions.

\<close>

definition
  tObsC :: "('a, 'ePubAct, 'es, 'pPubAct, 'ps) BEState Trace
         \<Rightarrow> ('cobs \<times> 'ePubAct \<times> ('a \<Rightarrow> 'pPubAct)) Trace"
where
  "tObsC \<equiv> tMap (\<lambda>s. (envObsC (es s), pubActs s))"
(*<*)

lemma spr_jview_tObsC:
  assumes "spr_jview a t = spr_jview a t'"
  shows "tObsC t = tObsC t'"
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
  "tLast (tObsC t) = (envObsC (es (tLast t)), pubActs (tLast t))"
  unfolding tObsC_def by simp

lemma tObsC_tStep:
  "tObsC (t \<leadsto> s) = tObsC t \<leadsto> (envObsC (es s), pubActs s)"
  unfolding tObsC_def by simp

lemma tObsC_initial[iff]:
  "tFirst (tObsC t) = (envObsC (es (tFirst t)), pubActs (tFirst t))"
  "tObsC (tInit s) = tInit (envObsC (es s), pubActs s)"
  "tObsC t = tInit cobs \<longleftrightarrow> (\<exists>s. t = tInit s \<and> envObsC (es s) = fst cobs \<and> pubActs s = snd cobs)"
  unfolding tObsC_def by auto

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

(*>*)
text\<open>

Similarly we introduce common and agent-specific abstraction functions:

\<close>

definition
  tObsC_abs :: "('a, 'ePubAct, 'es, 'pPubAct, 'ps) BEState Trace
             \<Rightarrow> ('a, 'ePubAct, 'es, 'pPubAct, 'ps) BEState Relation"
where
  "tObsC_abs t \<equiv> { (tFirst t', tLast t')
                   |t'. t' \<in> SPR.jkbpC \<and> tObsC t' = tObsC t }"

definition
  agent_abs :: "'a \<Rightarrow> ('a, 'ePubAct, 'es, 'pPubAct, 'ps) BEState Trace
             \<Rightarrow> ('a, 'ePubAct, 'es, 'pPubAct, 'ps) BEState Relation"
where
  "agent_abs a t \<equiv> { (tFirst t', tLast t')
                     |t'. t' \<in> SPR.jkbpC \<and> spr_jview a t' = spr_jview a t }"
(*<*)

lemma tObsC_abs_jview_eq[dest, intro]:
  "spr_jview a t' = spr_jview a t
    \<Longrightarrow> tObsC_abs t = tObsC_abs t'"
  unfolding tObsC_abs_def by (fastforce dest: spr_jview_tObsC)

lemma tObsC_absI[intro]:
  "\<lbrakk> t' \<in> SPR.jkbpC; tObsC t' = tObsC t; u = tFirst t'; v = tLast t' \<rbrakk>
    \<Longrightarrow> (u, v) \<in> tObsC_abs t"
  unfolding tObsC_abs_def by blast

lemma tObsC_abs_conv:
  "(u, v) \<in> tObsC_abs t
    \<longleftrightarrow> (\<exists>t'. t' \<in> SPR.jkbpC \<and> tObsC t' = tObsC t \<and> u = tFirst t' \<and> v = tLast t')"
  unfolding tObsC_abs_def by blast

lemma agent_absI[elim]:
  "\<lbrakk> t' \<in> SPR.jkbpC; spr_jview a t' = spr_jview a t; u = tFirst t'; v = tLast t' \<rbrakk>
    \<Longrightarrow> (u, v) \<in> agent_abs a t"
  unfolding agent_abs_def by blast

lemma agent_abs_tLastD[simp]:
  "(u, v) \<in> agent_abs a t \<Longrightarrow> envObs a v = envObs a (tLast t)"
  unfolding agent_abs_def by auto

lemma agent_abs_inv[dest]:
  "(u, v) \<in> agent_abs a t
    \<Longrightarrow> \<exists>t'. t' \<in> SPR.jkbpC \<and> spr_jview a t' = spr_jview a t
           \<and> u = tFirst t' \<and> v = tLast t'"
  unfolding agent_abs_def by blast

(*>*)

end (* context FiniteBroadcastEnvironment *)

text\<open>

The simulation is identical to that in the previous section:

\<close>

record ('a, 'ePubAct, 'es, 'pPubAct, 'ps) SPRstate =
  sprFst :: "('a, 'ePubAct, 'es, 'pPubAct, 'ps) BEState"
  sprLst :: "('a, 'ePubAct, 'es, 'pPubAct, 'ps) BEState"
  sprCRel :: "('a, 'ePubAct, 'es, 'pPubAct, 'ps) BEState Relation"

context FiniteBroadcastEnvironment
begin

definition
  spr_sim :: "('a, 'ePubAct, 'es, 'pPubAct, 'ps) BEState Trace
           \<Rightarrow> ('a, 'ePubAct, 'es, 'pPubAct, 'ps) SPRstate"
where
  "spr_sim \<equiv> \<lambda>t. \<lparr> sprFst = tFirst t, sprLst = tLast t, sprCRel = tObsC_abs t \<rparr>"
(*<*)

lemma spr_sim_tFirst_tLast:
  "\<lbrakk> spr_sim t = s; t \<in> SPR.jkbpC \<rbrakk> \<Longrightarrow> (sprFst s, sprLst s) \<in> sprCRel s"
  unfolding spr_sim_def by auto

(*>*)
text\<open>

The Kripke structure over simulated traces is also the same:

\<close>

definition
  spr_simRels :: "'a \<Rightarrow> ('a, 'ePubAct, 'es, 'pPubAct, 'ps) SPRstate Relation"
where
  "spr_simRels \<equiv> \<lambda>a. { (s, s') |s s'.
                         envObs a (sprFst s) = envObs a (sprFst s')
                       \<and> envObs a (sprLst s) = envObs a (sprLst s')
                       \<and> sprCRel s = sprCRel s' }"

definition
  spr_simVal :: "('a, 'ePubAct, 'es, 'pPubAct, 'ps) SPRstate \<Rightarrow> 'p \<Rightarrow> bool"
where
  "spr_simVal \<equiv> envVal \<circ> sprLst"

abbreviation
  "spr_simMC \<equiv> mkKripke (spr_sim ` SPR.jkbpC) spr_simRels spr_simVal"
(*<*)

lemma spr_simVal_def2[iff]:
  "spr_simVal (spr_sim t) = envVal (tLast t)"
  unfolding spr_sim_def spr_simVal_def by simp


(*>*)
text\<open>

As usual, showing that @{term "spr_sim"} is in fact a simulation is
routine for all properties except for reverse simulation. For that we
use proof techniques similar to those of
\citet{DBLP:journals/tocl/LomuscioMR00}: the goal is to show that,
given @{term "t \<in> jkbpC"}, we can construct a trace @{term "t' \<in>
jkbpC"} indistinguishable from @{term "t"} by agent @{term "a"}, based
on the public actions, the common observation and @{term "a"}'s
private and initial states.

To do this we define a splicing operation:

\<close>

definition
  sSplice :: "'a
           \<Rightarrow> ('a, 'ePubAct, 'es, 'pPubAct, 'ps) BEState
           \<Rightarrow> ('a, 'ePubAct, 'es, 'pPubAct, 'ps) BEState
           \<Rightarrow> ('a, 'ePubAct, 'es, 'pPubAct, 'ps) BEState"
where
  "sSplice a s s' \<equiv> s\<lparr> ps := (ps s)(a := ps s' a) \<rparr>"
(*<*)

lemma sSplice_es[simp]:
  "es (sSplice a s s') = es s"
  unfolding sSplice_def by simp

lemma sSplice_pubActs[simp]:
  "pubActs (sSplice a s s') = pubActs s"
  unfolding sSplice_def by simp

lemma sSplice_envObs[simp]:
  assumes init: "envObs a s = envObs a s'"
  shows "sSplice a s s' = s"
proof -
  from init have "ps s a = ps s' a"
    by (auto simp: envObs_def)
  thus ?thesis
    unfolding sSplice_def by (simp add: fun_upd_idem_iff)
qed

lemma sSplice_envObs_a:
  assumes "envObsC (es s) = envObsC (es s')"
  assumes "pubActs s = pubActs s'"
  shows "envObs a (sSplice a s s') = envObs a s'"
  using assms
  unfolding sSplice_def envObs_def by simp

lemma sSplice_envObs_not_a:
  assumes "a' \<noteq> a"
  shows "envObs a' (sSplice a s s') = envObs a' s"
  using assms
  unfolding sSplice_def envObs_def by simp

(*>*)
text\<open>

The effect of @{term "sSplice a s s'"} is to update @{term "s"} with
@{term "a"}'s private state in @{term "s'"}. The key properties are
that provided the common observation on @{term "s"} and @{term "s'"}
are the same, then agent @{term "a"}'s observation on @{term "sSplice
a s s'"} is the same as
 at @{term "s'"}, while everyone else's is the
same as at @{term "s"}.

We hoist this operation pointwise to traces:

\<close>

abbreviation
  tSplice :: "('a, 'ePubAct, 'es, 'pPubAct, 'ps) BEState Trace
            \<Rightarrow> 'a
            \<Rightarrow> ('a, 'ePubAct, 'es, 'pPubAct, 'ps) BEState Trace
            \<Rightarrow> ('a, 'ePubAct, 'es, 'pPubAct, 'ps) BEState Trace"
      ("_ \<^bsub>\<^esub>\<bowtie>\<^bsub>_\<^esub> _" [55, 1000, 56] 55)
where
  "t \<^bsub>\<^esub>\<bowtie>\<^bsub>a\<^esub> t' \<equiv> tZip (sSplice a) t t'"
(*<*)

declare sSplice_envObs_a[simp] sSplice_envObs_not_a[simp]

lemma tSplice_tObsC:
  assumes tObsC: "tObsC t = tObsC t'"
  shows "tObsC (t \<^bsub>\<^esub>\<bowtie>\<^bsub>a\<^esub> t') = tObsC t"
  using tObsC_tLength[OF tObsC] tObsC
  by (induct rule: trace_induct2) (simp_all add: tObsC_tStep)

lemma tSplice_spr_jview_a:
  assumes tObsC: "tObsC t = tObsC t'"
  shows "spr_jview a (t \<^bsub>\<^esub>\<bowtie>\<^bsub>a\<^esub> t') = spr_jview a t'"
  using tObsC_tLength[OF tObsC] tObsC
  by (induct rule: trace_induct2) (simp_all add: tObsC_tStep spr_jview_def)

lemma tSplice_spr_jview_not_a:
  assumes tObsC: "tObsC t = tObsC t'"
  assumes aa': "a \<noteq> a'"
  shows "spr_jview a' (t \<^bsub>\<^esub>\<bowtie>\<^bsub>a\<^esub> t') = spr_jview a' t"
  using tObsC_tLength[OF tObsC] tObsC aa'
  by (induct rule: trace_induct2) (simp_all add: tObsC_tStep spr_jview_def)

lemma tSplice_es:
  assumes tLen: "tLength t = tLength t'"
  shows "es (tLast (t \<^bsub>\<^esub>\<bowtie>\<^bsub>a\<^esub> t')) = es (tLast t)"
  using tLen by (induct rule: trace_induct2) simp_all

lemma tSplice_pubActs:
  assumes tLen: "tLength t = tLength t'"
  shows "pubActs (tLast (t \<^bsub>\<^esub>\<bowtie>\<^bsub>a\<^esub> t')) = pubActs (tLast t)"
  using tLen by (induct rule: trace_induct2) simp_all

lemma tSplice_envAction:
  assumes tLen: "tLength t = tLength t'"
  shows "envAction (tLast (t \<^bsub>\<^esub>\<bowtie>\<^bsub>a\<^esub> t')) = envAction (tLast t)"
  unfolding envAction_def
  using tSplice_es[OF tLen] tSplice_pubActs[OF tLen]
  by simp

lemma tSplice_tFirst[simp]:
  assumes tLen: "tLength t = tLength t'"
  assumes init: "envObs a (tFirst t) = envObs a (tFirst t')"
  shows "tFirst (t \<^bsub>\<^esub>\<bowtie>\<^bsub>a\<^esub> t') = tFirst t"
  using tLen init by (induct rule: trace_induct2) simp_all

lemma tSplice_tLast[simp]:
  assumes tLen: "tLength t = tLength t'"
  assumes last: "envObs a (tLast t) = envObs a (tLast t')"
  shows "tLast (t \<^bsub>\<^esub>\<bowtie>\<^bsub>a\<^esub> t') = tLast t"
  using tLen last
  unfolding envObs_def
  apply (induct rule: trace_induct2)
  apply (auto iff: sSplice_def fun_upd_idem_iff)
  done

(*>*)
text\<open>

The key properties are that after splicing, if @{term "t"} and @{term
"t'"} have the same common observation, then so does @{term "t \<^bsub>\<^esub>\<bowtie>\<^bsub>a\<^esub>
t'"}, and for all agents @{term "a' \<noteq> a"}, the view @{term "a'"} has
of @{term "t \<^bsub>\<^esub>\<bowtie>\<^bsub>a\<^esub> t'"} is the same as it has of @{term "t"}, while for
@{term "a"} it is the same as @{term "t'"}.

We can conclude that provided the two traces are initially
indistinguishable to @{term "a"}, and not commonly distinguishable,
then @{term "t \<^bsub>\<^esub>\<bowtie>\<^bsub>a\<^esub> t'"} is a canonical trace:

\<close>

lemma tSplice_jkbpC:
  assumes tt': "{t, t'} \<subseteq> SPR.jkbpC"
  assumes init: "envObs a (tFirst t) = envObs a (tFirst t')"
  assumes tObsC: "tObsC t = tObsC t'"
  shows "t \<^bsub>\<^esub>\<bowtie>\<^bsub>a\<^esub> t' \<in> SPR.jkbpC"
(*<*)
using tObsC_tLength[OF tObsC] tt' init tObsC
proof(induct rule: trace_induct2)
  case (tInit s s') thus ?case by simp
next
  case (tStep s s' t t')

  hence tt': "t \<^bsub>\<^esub>\<bowtie>\<^bsub>a\<^esub> t' \<in> SPR.jkbpC"
    and tLen: "tLength t' = tLength t"
    and tObsC: "tObsC (t \<leadsto> s) = tObsC (t' \<leadsto> s')"
    by auto

  hence tt'n: "t \<^bsub>\<^esub>\<bowtie>\<^bsub>a\<^esub> t' \<in> SPR.jkbpCn (tLength t)"
    by auto

  from tStep
  have ts: "t \<leadsto> s \<in> SPR.jkbpCn (Suc (tLength t))"
   and t's': "t' \<leadsto> s' \<in> SPR.jkbpCn (Suc (tLength t'))"
    apply -
     apply ((rule SPR.jkbpC_tLength_inv, simp_all)[1])+
    done

  from ts obtain eact aact
    where eact: "eact \<in> set (envAction (tLast t))"
      and aact: "\<forall>a. aact a \<in> set (jAction (SPR.mkM (SPR.jkbpCn (tLength t))) t a)"
      and trans: "envTrans eact aact (tLast t) = s"
    apply (auto iff: Let_def)
    done

  from t's' obtain eact' aact'
    where eact': "eact' \<in> set (envAction (tLast t'))"
      and aact': "\<forall>a. aact' a \<in> set (jAction (SPR.mkM (SPR.jkbpCn (tLength t'))) t' a)"
      and trans': "envTrans eact' aact' (tLast t') = s'"
    apply (auto iff: Let_def)
    done

  define aact'' where "aact'' = aact (a := aact' a)"

  from tObsC trans trans'
  have aact''_fst: "fst \<circ> aact'' = fst \<circ> aact"
    unfolding envTrans_def aact''_def
    apply -
    apply (rule ext)
    apply (auto iff: tObsC_tStep)
    apply (erule o_eq_elim)
    apply simp
    done

  from tObsC trans trans'
  have aact''_snd: "snd \<circ> aact'' = (snd \<circ> aact)(a := ps s' a)"
    unfolding envTrans_def aact''_def
    apply -
    apply (rule ext)
    apply auto
    done

  have "envTrans eact aact'' (tLast (t \<^bsub>\<^esub>\<bowtie>\<^bsub>a\<^esub> t'))
      = sSplice a (envTrans eact aact (tLast t)) s'"
    apply (simp only: envTrans_def sSplice_def)
    using tSplice_es[OF tLen[symmetric]] aact''_fst aact''_snd
    apply clarsimp
    done

  moreover

  { fix a'
    have "aact'' a' \<in> set (jAction (SPR.mkM (SPR.jkbpCn (tLength t))) (t \<^bsub>\<^esub>\<bowtie>\<^bsub>a\<^esub> t') a')"
    proof(cases "a' = a")
      case False
      with tStep have "jAction (SPR.mkM (SPR.jkbpCn (tLength t))) (t \<^bsub>\<^esub>\<bowtie>\<^bsub>a\<^esub> t') a'
                     = jAction (SPR.mkM (SPR.jkbpCn (tLength t))) t a'"
        apply -
        apply (rule S5n_jAction_eq)
         apply simp
        unfolding SPR.mkM_def
        using tSplice_spr_jview_not_a tt'
        apply auto
        done
      with False aact show ?thesis
        unfolding aact''_def by simp
    next
      case True
      with tStep have "jAction (SPR.mkM (SPR.jkbpCn (tLength t))) (t \<^bsub>\<^esub>\<bowtie>\<^bsub>a\<^esub> t') a
                     = jAction (SPR.mkM (SPR.jkbpCn (tLength t))) t' a"
        apply -
        apply (rule S5n_jAction_eq)
         apply simp
        unfolding SPR.mkM_def
        using tSplice_spr_jview_a tt'
        apply auto
        done
      with True aact' tLen show ?thesis
        unfolding aact''_def by simp
    qed }

  moreover

  from tStep have "envAction (tLast (t \<^bsub>\<^esub>\<bowtie>\<^bsub>a\<^esub> t')) = envAction (tLast t)"
    using tSplice_envAction by blast

  moreover note eact trans tt'n

  ultimately have "(t \<^bsub>\<^esub>\<bowtie>\<^bsub>a\<^esub> t') \<leadsto> sSplice a s s' \<in> SPR.jkbpCn (Suc (tLength t))"
    apply (simp add: Let_def del: split_paired_Ex)
    apply (rule exI[where x="eact"])
    apply (rule exI[where x="aact''"])
    apply simp
    done

  thus ?case
    apply (simp only: tZip.simps)
    apply blast
    done
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

  define q where "q = t \<^bsub>\<^esub>\<bowtie>\<^bsub>a\<^esub> p"

  from tp tuq uq
  have "spr_jview a p = spr_jview a q"
    unfolding q_def by (simp add: tSplice_spr_jview_a)

  with pT tT tp tuq uq
  have pt: "(p, q) \<in> relations SPR.MC a"
    unfolding SPR.mkM_def q_def by (simp add: tSplice_jkbpC)
  from q' uq vq tp tuq tvq
  have ftq': "spr_sim q = q'"
    unfolding spr_sim_def q_def
    using tSplice_tObsC[where a=a and t=t and t'=p]
    apply clarsimp
    apply (intro conjI)
      apply (auto dest: tObsC_tLength)[2]
    unfolding tObsC_abs_def (* FIXME abstract *)
    apply simp
    done
  from pt ftq'
  show "\<exists>q. (p, q) \<in> relations SPR.MC a \<and> spr_sim q = q'"
    by blast
qed

(*>*)
text\<open>

The proof is by induction over @{term "t"} and @{term "t'"}, and
depends crucially on the public actions being recorded in the state
and commonly observed. Showing the reverse simulation property is then
straightforward.

\<close>

lemma spr_sim: "sim SPR.MC spr_simMC spr_sim"
(*<*)
proof
  show "sim_range SPR.MC spr_simMC spr_sim"
    by (rule sim_rangeI) (simp_all add: spr_sim_def)
next
  show "sim_val SPR.MC spr_simMC spr_sim"
    by (rule sim_valI) simp
next
  show "sim_f SPR.MC spr_simMC spr_sim"
    unfolding spr_simRels_def spr_sim_def mkKripke_def SPR.mkM_def
    by (rule sim_fI, auto simp del: split_paired_Ex)
next
  show "sim_r SPR.MC spr_simMC spr_sim"
    by (rule spr_sim_r)
qed

(*>*)
end (* context FiniteBroadcastEnvironment *)

sublocale FiniteBroadcastEnvironment
        < SPR: SimIncrEnvironment jkbp envInit envAction envTrans envVal
                                       spr_jview envObs spr_jviewInit spr_jviewIncr
                                       spr_sim spr_simRels spr_simVal
(*<*)
  by standard (simp add: spr_sim)

(*>*)
text\<open>

The algorithmic representations and machinery of the deterministic
JKBP case suffice for this one too, and so we omit the details.

\FloatBarrier

\<close>
(*<*)

end
(*>*)
