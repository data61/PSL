(*<*)
(*
 * Knowledge-based programs.
 * (C)opyright 2011, Peter Gammie, peteg42 at gmail.com.
 * License: BSD
 *)

theory SPRViewNonDetIndInit
imports
  SPRView
  KBPsAuto
  SPRViewNonDet
begin
(*>*)

subsubsection\<open>Perfect Recall in Independently-Initialised Non-deterministic Broadcast Environments\<close>

text\<open>

\label{sec:kbps-theory-spr-non-deterministic-protocols-ind-init}

If the private and environment parts of the initial states are
independent we can simplify the construction of the previous section
and consider only sets of states rather than relations. This greatly
reduces the state space that the algorithm traverses.

We capture this independence by adding some assumptions to the @{term
"FiniteBroadcastEnvironment"} locale of
Figure~\ref{fig:kbps-theory-broadcast-envs}; the result is the @{term
"FiniteBroadcastEnvironmentIndependentInit"} locale shown in
Figure~\ref{fig:kbps-theory-broadcast-envs-ind-init}. We ask that the
initial states be the Cartesian product of possible private and
environment states; in other words there is nothing for the agents to
learn about correlations amongst the initial states. As there are
initially no public actions from the previous round, we use the @{term
"default"} class to indicate that there is a fixed but arbitrary
choice to be made here.

Again we introduce common and agent-specific abstraction functions:


\<close>

text_raw\<open>
\begin{figure}[ht]
\begin{isabellebody}%
\<close>
locale FiniteBroadcastEnvironmentIndependentInit =
  FiniteBroadcastEnvironment jkbp envInit envAction envTrans envVal envObs
                             envObsC envActionES envTransES
    for jkbp :: "('a::finite, 'p, ('pPubAct::{default,finite} \<times> 'ps::finite)) JKBP"
    and envInit :: "('a, 'ePubAct :: {default, finite}, 'es :: finite,
                     'pPubAct, 'ps) BEState list"
    and envAction :: "('a, 'ePubAct, 'es, 'pPubAct, 'ps) BEState
                   \<Rightarrow> ('ePubAct \<times> 'ePrivAct) list"
    and envTrans :: "('ePubAct \<times> 'ePrivAct)
                  \<Rightarrow> ('a \<Rightarrow> ('pPubAct \<times> 'ps))
                  \<Rightarrow> ('a, 'ePubAct, 'es, 'pPubAct, 'ps) BEState
                  \<Rightarrow> ('a, 'ePubAct, 'es, 'pPubAct, 'ps) BEState"
    and envVal :: "('a, 'ePubAct, 'es, 'pPubAct, 'ps) BEState \<Rightarrow> 'p \<Rightarrow> bool"
    and envObs :: "'a \<Rightarrow> ('a, 'ePubAct, 'es, 'pPubAct, 'ps) BEState
                \<Rightarrow> ('cobs \<times> 'ps \<times> ('ePubAct \<times> ('a \<Rightarrow> 'pPubAct)))"
    and envObsC :: "'es \<Rightarrow> 'cobs"
    and envActionES :: "'es \<Rightarrow> ('ePubAct \<times> ('a \<Rightarrow> 'pPubAct))
                            \<Rightarrow> ('ePubAct \<times> 'ePrivAct) list"
    and envTransES :: "('ePubAct \<times> 'ePrivAct) \<Rightarrow> ('a \<Rightarrow> 'pPubAct)
                    \<Rightarrow> 'es \<Rightarrow> 'es"

+ fixes agents :: "'a list"
  fixes envInitBits :: "'es list \<times> ('a \<Rightarrow> 'ps list)"
  defines envInit_def:
     "envInit \<equiv> [ \<lparr> es = esf, ps = psf, pubActs = (default, \<lambda>_. default) \<rparr>
                 . psf \<leftarrow> listToFuns (snd envInitBits) agents
                 , esf \<leftarrow> fst envInitBits ]"
  assumes agents: "set agents = UNIV" "distinct agents"

text_raw\<open>
  \end{isabellebody}%
  \caption{Finite broadcast environments with non-deterministic
  KBPs, where the initial private and environment states are
  independent.}
  \label{fig:kbps-theory-broadcast-envs-ind-init}
\end{figure}
\<close>

context FiniteBroadcastEnvironmentIndependentInit
begin

definition
  tObsC_ii_abs :: "('a, 'ePubAct, 'es, 'pPubAct, 'ps) BEState Trace
             \<Rightarrow> ('a, 'ePubAct, 'es, 'pPubAct, 'ps) BEState set"
where "tObsC_ii_abs t \<equiv>
  { tLast t' |t'. t' \<in> SPR.jkbpC \<and> tObsC t' = tObsC t }"

definition
  agent_ii_abs :: "'a \<Rightarrow> ('a, 'ePubAct, 'es, 'pPubAct, 'ps) BEState Trace
             \<Rightarrow> ('a, 'ePubAct, 'es, 'pPubAct, 'ps) BEState set"
where "agent_ii_abs a t \<equiv>
  { tLast t' |t'. t' \<in> SPR.jkbpC \<and> spr_jview a t' = spr_jview a t }"
(*<*)

lemma tObsC_ii_abs_jview_eq[dest, intro]:
  "spr_jview a t' = spr_jview a t
    \<Longrightarrow> tObsC_ii_abs t = tObsC_ii_abs t'"
  unfolding tObsC_ii_abs_def by (fastforce dest: spr_jview_tObsC)

lemma tObsC_ii_absI[intro]:
  "\<lbrakk> t' \<in> SPR.jkbpC; tObsC t' = tObsC t; v = tLast t' \<rbrakk>
    \<Longrightarrow> v \<in> tObsC_ii_abs t"
  unfolding tObsC_ii_abs_def by blast

lemma tObsC_ii_abs_conv:
  " v \<in> tObsC_ii_abs t
    \<longleftrightarrow> (\<exists>t'. t' \<in> SPR.jkbpC \<and> tObsC t' = tObsC t \<and> v = tLast t')"
  unfolding tObsC_ii_abs_def by blast

lemma agent_ii_absI[elim]:
  "\<lbrakk> t' \<in> SPR.jkbpC; spr_jview a t' = spr_jview a t; v = tLast t' \<rbrakk>
    \<Longrightarrow> v \<in> agent_ii_abs a t"
  unfolding agent_ii_abs_def by blast

lemma agent_ii_abs_tLastD[simp]:
  "v \<in> agent_ii_abs a t \<Longrightarrow> envObs a v = envObs a (tLast t)"
  unfolding agent_ii_abs_def by auto

lemma agent_ii_abs_inv[dest]:
  "v \<in> agent_ii_abs a t
    \<Longrightarrow> \<exists>t'. t' \<in> SPR.jkbpC \<and> spr_jview a t' = spr_jview a t
           \<and> v = tLast t'"
  unfolding agent_ii_abs_def by blast

(*>*)
text\<open>

The simulation is similar to the single-agent case
(\S\ref{sec:kbps-spr-single-agent}); for a given canonical trace
@{term "t"} it pairs the set of worlds that any agent considers
possible with the final state of @{term "t"}:

\<close>

type_synonym (in -) ('a, 'ePubAct, 'es, 'pPubAct, 'ps) SPRstate =
  "('a, 'ePubAct, 'es, 'pPubAct, 'ps) BEState set
 \<times> ('a, 'ePubAct, 'es, 'pPubAct, 'ps) BEState"

definition
  spr_ii_sim :: "('a, 'ePubAct, 'es, 'pPubAct, 'ps) BEState Trace
           \<Rightarrow> ('a, 'ePubAct, 'es, 'pPubAct, 'ps) SPRstate"
where "spr_ii_sim \<equiv> \<lambda>t. (tObsC_ii_abs t, tLast t)"
(*<*)

lemma spr_ii_sim_tFirst_tLast:
  "\<lbrakk> spr_ii_sim t = s; t \<in> SPR.jkbpC \<rbrakk> \<Longrightarrow> snd s \<in> fst s"
  unfolding spr_ii_sim_def by auto

(*>*)
text\<open>

The Kripke structure over simulated traces is also quite similar:

\<close>

definition
  spr_ii_simRels :: "'a \<Rightarrow> ('a, 'ePubAct, 'es, 'pPubAct, 'ps) SPRstate Relation"
where "spr_ii_simRels \<equiv> \<lambda>a.
  { (s, s') |s s'. envObs a (snd s) = envObs a (snd s') \<and> fst s = fst s' }"

definition
  spr_ii_simVal :: "('a, 'ePubAct, 'es, 'pPubAct, 'ps) SPRstate \<Rightarrow> 'p \<Rightarrow> bool"
where "spr_ii_simVal \<equiv> envVal \<circ> snd"

abbreviation
  "spr_ii_simMC \<equiv> mkKripke (spr_ii_sim ` SPR.jkbpC) spr_ii_simRels spr_ii_simVal"
(*<*)

lemma spr_ii_simVal_def2[iff]:
  "spr_ii_simVal (spr_ii_sim t) = envVal (tLast t)"
  unfolding spr_ii_sim_def spr_ii_simVal_def by simp

(* Same as for SPRViewNonDet but different base case. *)

lemma tSplice_jkbpC:
  assumes tt': "{t, t'} \<subseteq> SPR.jkbpC"
  assumes tObsC: "tObsC t = tObsC t'"
  shows "t \<^bsub>\<^esub>\<bowtie>\<^bsub>a\<^esub> t' \<in> SPR.jkbpC"
using tObsC_tLength[OF tObsC] tt' tObsC
proof(induct rule: trace_induct2)
  case (tInit s s') thus ?case
    apply clarsimp
    unfolding envInit_def sSplice_def
    apply clarsimp
    apply (rule_tac x="x(a := xa a)" in bexI)
    using listToFun_splice[OF agents]
    apply auto
    done
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

lemma spr_ii_sim_r:
  "sim_r SPR.MC spr_ii_simMC spr_ii_sim"
proof(rule sim_rI)
  fix a p q'
  assume pT: "p \<in> worlds SPR.MC"
     and fpq': "(spr_ii_sim p, q') \<in> relations spr_ii_simMC a"
  from fpq' obtain vq
    where q': "q' = (tObsC_ii_abs p, vq)"
      and vq: "envObs a (tLast p) = envObs a vq"
    unfolding mkKripke_def spr_ii_sim_def spr_ii_simRels_def
    by fastforce

  from fpq' have "q' \<in> worlds spr_ii_simMC" by simp
  with q' have "vq \<in> tObsC_ii_abs p"
    using spr_ii_sim_tFirst_tLast[where s=q']
    apply auto
    done

  then obtain t
    where tT: "t \<in> SPR.jkbpC"
      and tp: "tObsC t = tObsC p"
      and tvq: "tLast t = vq"
    by (auto iff: tObsC_ii_abs_conv)

  define q where "q = t \<^bsub>\<^esub>\<bowtie>\<^bsub>a\<^esub> p"

  from tp
  have "spr_jview a p = spr_jview a q"
    unfolding q_def by (simp add: tSplice_spr_jview_a)

  with pT tT tp
  have pt: "(p, q) \<in> relations SPR.MC a"
    unfolding SPR.mkM_def q_def by (simp add: tSplice_jkbpC)
  from q' vq tp tvq
  have ftq': "spr_ii_sim q = q'"
    unfolding spr_ii_sim_def q_def
    using tSplice_tObsC[where a=a and t=t and t'=p]
    apply clarsimp
    apply (intro conjI)
      apply (auto dest: tObsC_tLength)[2]
    unfolding tObsC_ii_abs_def (* FIXME abstract *)
    apply auto
    done
  from pt ftq'
  show "\<exists>q. (p, q) \<in> relations SPR.MC a \<and> spr_ii_sim q = q'"
    by blast
qed

(*>*)
text\<open>

The proofs that this simulation is adequate are similar to those in
the previous section. We elide the details.

\<close>

lemma spr_ii_sim: "sim SPR.MC spr_ii_simMC spr_ii_sim"
(*<*)
proof
  show "sim_range SPR.MC spr_ii_simMC spr_ii_sim"
    by (rule sim_rangeI) (simp_all add: spr_ii_sim_def)
next
  show "sim_val SPR.MC spr_ii_simMC spr_ii_sim"
    by (rule sim_valI) simp
next
  show "sim_f SPR.MC spr_ii_simMC spr_ii_sim"
    unfolding spr_ii_simRels_def spr_ii_sim_def mkKripke_def SPR.mkM_def
    by (rule sim_fI, auto simp del: split_paired_Ex)
next
  show "sim_r SPR.MC spr_ii_simMC spr_ii_sim"
    by (rule spr_ii_sim_r)
qed
(*>*)

end (* context FiniteBroadcastEnvironment *)

sublocale FiniteBroadcastEnvironmentIndependentInit
        < SPRii: SimIncrEnvironment jkbp envInit envAction envTrans envVal
                                       spr_jview envObs spr_jviewInit spr_jviewIncr
                                       spr_ii_sim spr_ii_simRels spr_ii_simVal
(*<*)
  by standard (simp add: spr_ii_sim)

end
(*>*)
