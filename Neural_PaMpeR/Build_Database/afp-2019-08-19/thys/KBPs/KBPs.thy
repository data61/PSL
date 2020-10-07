(*<*)
(*
 * Knowledge-based programs.
 * (C)opyright 2011, Peter Gammie, peteg42 at gmail.com.
 * License: BSD
 *)

theory KBPs
imports Kripke Traces
begin
(*>*)

section\<open>Knowledge-based Programs\<close>

text \<open>

\label{sec:kbps-theory-kbps-semantics}

A knowledge-based programs (KBPs) encodes the dependency of action on
knowledge by a sequence of guarded commands, and a \emph{joint
knowledge-based program} (JKBP) assigns a KBP to each agent:

\<close>

record ('a, 'p, 'aAct) GC =
  guard  :: "('a, 'p) Kform"
  action :: "'aAct"

type_synonym ('a, 'p, 'aAct) KBP = "('a, 'p, 'aAct) GC list"
type_synonym ('a, 'p, 'aAct) JKBP = "'a \<Rightarrow> ('a, 'p, 'aAct) KBP"

text\<open>

We use a list of guarded commands just so we can reuse this definition
and others in algorithmic contexts; we would otherwise use a set as
there is no problem with infinite programs or actions, and we always
ignore the sequential structure.

Intuitively a KBP for an agent cannot directly evaluate the truth of
an arbitrary formula as it may depend on propositions that the agent
has no certainty about. For example, a card-playing agent cannot
determine which cards are in the deck, despite being sure that those
in her hand are not. Conversely agent $a$ can evaluate formulas of the
form @{term "\<^bold>K\<^sub>a \<phi>"} as these depend only on the worlds the agent thinks
is possible.

Thus we restrict the guards of the JKBP to be boolean combinations of
\emph{subjective} formulas:

\<close>

fun subjective :: "'a \<Rightarrow> ('a, 'p) Kform \<Rightarrow> bool" where
  "subjective a (Kprop p)      = False"
| "subjective a (Knot f)       = subjective a f"
| "subjective a (Kand f g)     = (subjective a f \<and> subjective a g)"
| "subjective a (Kknows a' f)  = (a = a')"
| "subjective a (Kcknows as f) = (a \<in> set as)"

text\<open>

All JKBPs in the following sections are assumed to be subjective.

This syntactic restriction implies the desired semantic property, that
we can evaluate a guard at an arbitrary world that is compatible with
a given observation \citep[\S3]{DBLP:journals/dc/FaginHMV97}.

\<close>

lemma S5n_subjective_eq:
  assumes S5n: "S5n M"
  assumes subj: "subjective a \<phi>"
  assumes ww': "(w, w') \<in> relations M a"
  shows "M, w \<Turnstile> \<phi> \<longleftrightarrow> M, w' \<Turnstile> \<phi>"
(*<*)
using subj ww'
proof(induct \<phi> rule: subjective.induct[case_names Kprop Knot Kand Kknows Kcknows])
  case (Kcknows a as \<phi>)
  hence "(w, w') \<in> (\<Union>a\<in>set as. relations M a)\<^sup>+" by auto
  with Kcknows S5n show ?case by (auto dest: S5n_tc_rels_eq)
qed (auto dest: S5n_rels_eq[OF S5n])

(*>*)
text\<open>

The proof is by induction over the formula @{term "\<phi>"}, using the
properties of $S5_n$ Kripke structures in the knowledge cases.

We capture the fixed but arbitrary JKBP using a locale, and work in
this context for the rest of this section.

\<close>

locale JKBP =
  fixes jkbp :: "('a, 'p, 'aAct) JKBP"
  assumes subj: "\<forall>a gc. gc \<in> set (jkbp a) \<longrightarrow> subjective a (guard gc)"

context JKBP
begin

text\<open>

The action of the JKBP at a world is the list of all actions that are
enabled at that world:

\<close>

definition jAction :: "('a, 'p, 'w) KripkeStructure \<Rightarrow> 'w \<Rightarrow> 'a \<Rightarrow> 'aAct list"
where "jAction \<equiv> \<lambda>M w a. [ action gc. gc \<leftarrow> jkbp a, M, w \<Turnstile> guard gc ]"

text\<open>

All of our machinery on Kripke structures lifts from the models
relation of \S\ref{sec:kbps-logic-of-knowledge} through @{term
"jAction"}, due to the subjectivity requirement. In particular, the
KBP for agent $a$ behaves the same at worlds that $a$ cannot
distinguish amongst:

\<close>

lemma S5n_jAction_eq:
  assumes S5n: "S5n M"
  assumes ww': "(w, w') \<in> relations M a"
  shows "jAction M w a = jAction M w' a"
(*<*)
proof -
  { fix gc assume "gc \<in> set (jkbp a)"
    with subj have "subjective a (guard gc)" by auto
    with S5n ww' have "M, w \<Turnstile> guard gc = M, w' \<Turnstile> guard gc"
      by - (rule S5n_subjective_eq, simp_all) }
  thus ?thesis
    unfolding jAction_def
    by - (rule arg_cong[where f=concat], simp)
qed
(*>*)

text\<open>

Also the JKBP behaves the same on relevant generated models for all
agents:

\<close>

lemma gen_model_jAction_eq:
  assumes S: "gen_model M w = gen_model M' w"
  assumes w': "w' \<in> worlds (gen_model M' w)"
  assumes M: "kripke M"
  assumes M': "kripke M'"
  shows "jAction M w' = jAction M' w'"
(*<*)
  unfolding jAction_def
  by (auto iff: gen_model_eq[OF M M' S w'])
(*>*)

text\<open>

Finally, @{term "jAction"} is invariant under simulations:

\<close>

lemma simulation_jAction_eq:
  assumes M: "kripke M"
  assumes sim: "sim M M' f"
  assumes w: "w \<in> worlds M"
  shows "jAction M w = jAction M' (f w)"
(*<*)
  unfolding jAction_def
  using assms by (auto iff: sim_semantic_equivalence)
(*>*)

end

section\<open>Environments and Views\<close>

text\<open>

\label{sec:kbps-theory-environments}

The previous section showed how a JKBP can be interpreted statically,
with respect to a fixed Kripke structure. As we also wish to capture
how agents interact, we adopt the \emph{interpreted systems} and
\emph{contexts} of \cite{FHMV:1995}, which we term \emph{environments}
following \cite{Ron:1996}.

A \emph{pre-environment} consists of the following:
\begin{itemize}

\item @{term "envInit"}, an arbitrary set of initial states;

\item The protocol of the environment @{term "envAction"}, which
  depends on the current state;

\item A transition function @{term "envTrans"}, which incorporates the
  environment's action and agents' behaviour into a state change; and

\item A propositional evaluation function @{term "envVal"}.

\end{itemize}
We extend the @{term "JKBP"} locale with these constants:

\<close>

locale PreEnvironment = JKBP jkbp for jkbp :: "('a, 'p, 'aAct) JKBP"
+ fixes envInit :: "'s list"
    and envAction :: "'s \<Rightarrow> 'eAct list"
    and envTrans :: "'eAct \<Rightarrow> ('a \<Rightarrow> 'aAct) \<Rightarrow> 's \<Rightarrow> 's"
    and envVal :: "'s \<Rightarrow> 'p \<Rightarrow> bool"

text\<open>

\label{sec:kbps-views}

We represent the possible evolutions of the system as finite sequences
of states, represented by a left-recursive type @{typ "'s Trace"} with
constructors @{term "tInit s"} and @{term "t \<leadsto> s"}, equipped with
@{term "tFirst"}, @{term "tLast"}, @{term "tLength"} and @{term
"tMap"} functions.

Constructing these traces requires us to determine the agents' actions
at a given state. To do so we need to find an appropriate S$5_n$
structure for interpreting @{term "jkbp"}.

Given that we want the agents to make optimal use of the information
they have access to, we allow these structures to depend on the entire
history of the system, suitably conditioned by what the agents can
observe. We capture this notion of observation with a \emph{view}
\citep{Ron:1996}, which is an arbitrary function of a trace:

\<close>

type_synonym ('s, 'tview) View = "'s Trace \<Rightarrow> 'tview"
type_synonym ('a, 's, 'tview) JointView = "'a \<Rightarrow> 's Trace \<Rightarrow> 'tview"

text\<open>

\label{sec:kbps-synchrony}

We require views to be \emph{synchronous}, i.e. that agents be able to
tell the time using their view by distinguishing two traces of
different lengths. As we will see in the next section, this guarantees
that the JKBP has an essentially unique implementation.

We extend the @{term "PreEnvironment"} locale with a view:

\<close>

locale PreEnvironmentJView =
  PreEnvironment jkbp envInit envAction envTrans envVal
    for jkbp :: "('a, 'p, 'aAct) JKBP"
    and envInit :: "'s list"
    and envAction :: "'s \<Rightarrow> 'eAct list"
    and envTrans :: "'eAct \<Rightarrow> ('a \<Rightarrow> 'aAct) \<Rightarrow> 's \<Rightarrow> 's"
    and envVal :: "'s \<Rightarrow> 'p \<Rightarrow> bool"
+ fixes jview :: "('a, 's, 'tview) JointView"
  assumes sync: "\<forall>a t t'. jview a t = jview a t' \<longrightarrow> tLength t = tLength t'"

text\<open>

The two principle synchronous views are the clock view and the
perfect-recall view which we discuss further in
\S\ref{sec:kbps-theory-views}. We will later derive an agent's
concrete view from an instantaneous observation of the global state in
\S\ref{sec:kbps-environments}.

We build a Kripke structure from a set of traces by relating traces
that yield the same view. To obtain an S$5_n$ structure we also need a
way to evaluate propositions: we apply @{term "envVal"} to the final
state of a trace:

\<close>

definition (in PreEnvironmentJView)
  mkM :: "'s Trace set \<Rightarrow> ('a, 'p, 's Trace) KripkeStructure"
where
  "mkM T \<equiv>
      \<lparr> worlds = T,
        relations = \<lambda>a. { (t, t') . {t, t'} \<subseteq> T \<and> jview a t = jview a t' },
        valuation = envVal \<circ> tLast \<rparr>"
(*<*)

context PreEnvironmentJView
begin

lemma mkM_kripke[intro, simp]: "kripke (mkM T)"
  unfolding mkM_def by (rule kripkeI) fastforce

lemma mkM_S5n[intro, simp]: "S5n (mkM T)"
  unfolding mkM_def
  by (intro S5nI equivI)
     (bestsimp intro: equivI refl_onI symI transI)+

lemma mkM_simps[simp]:
  "worlds (mkM T) = T"
  "\<lbrakk> (t, t') \<in> relations (mkM T) a \<rbrakk> \<Longrightarrow> jview a t = jview a t'"
  "\<lbrakk> (t, t') \<in> relations (mkM T) a \<rbrakk> \<Longrightarrow> t \<in> T"
  "\<lbrakk> (t, t') \<in> relations (mkM T) a \<rbrakk> \<Longrightarrow> t' \<in> T"
  "valuation (mkM T) = envVal \<circ> tLast"
  unfolding mkM_def by simp_all

lemma mkM_rel_length[simp]:
  assumes tt': "(t, t') \<in> relations (mkM T) a"
  shows "tLength t' = tLength t"
proof -
  from tt' have "jview a t = jview a t'" by simp
  thus ?thesis by (bestsimp dest: sync[rule_format])
qed

(*>*)
text\<open>

This construction supplants the role of the \emph{local states} of
\citet{FHMV:1995}.

The following section shows how we can canonically interpret the JKBP
with respect to this structure.

\<close>

section\<open>Canonical Structures\<close>

text\<open>

\label{sec:kbps-canonical-kripke}

Our goal in this section is to find the canonical set of traces for a
given JKBP in a particular environment. As we will see, this always
exists with respect to synchronous views.

We inductively define an \emph{interpretation} of a JKBP with respect
to an arbitrary set of traces @{term "T"} by constructing a sequence
of sets of traces of increasing length:

\<close>

fun jkbpTn :: "nat \<Rightarrow> 's Trace set \<Rightarrow> 's Trace set"(*<*)("jkbpT\<^bsub>_\<^esub>")(*>*) where
  "jkbpT\<^bsub>0\<^esub> T     = { tInit s |s. s \<in> set envInit }"
| "jkbpT\<^bsub>Suc n\<^esub> T = { t \<leadsto> envTrans eact aact (tLast t) |t eact aact.
                             t \<in> jkbpT\<^bsub>n\<^esub> T \<and> eact \<in> set (envAction (tLast t))
                          \<and> (\<forall>a. aact a \<in> set (jAction (mkM T) t a)) }"

text\<open>

This model reflects the failure of any agent to provide an action as
failure of the entire system. In general @{term "envTrans"} may
incorporate a scheduler and communication failure models.

The union of this sequence gives us a closure property:

\<close>

definition jkbpT :: "'s Trace set \<Rightarrow> 's Trace set" where
  "jkbpT T \<equiv> \<Union>n. jkbpT\<^bsub>n\<^esub> T"
(*<*)

lemma jkbpTn_length:
  "t \<in> jkbpTn n T \<Longrightarrow> tLength t = n"
  by (induct n arbitrary: t, auto)

lemma jkbpT_tLength_inv:
  "\<lbrakk> t \<in> jkbpT T; tLength t = n \<rbrakk> \<Longrightarrow> t \<in> jkbpTn n T"
  unfolding jkbpT_def
  by (induct n arbitrary: t) (fastforce simp: jkbpTn_length)+

lemma jkbpT_traces_of_length:
   "{ t \<in> jkbpT T . tLength t = n } = jkbpTn n T"
  using jkbpT_tLength_inv
  unfolding jkbpT_def by (bestsimp simp: jkbpTn_length)

(*>*)
text\<open>

We say that a set of traces @{term "T"} \emph{represents} a JKBP if it
is closed under @{term "jkbpT"}:

\<close>

definition represents :: "'s Trace set \<Rightarrow> bool" where
  "represents T \<equiv> jkbpT T = T"
(*<*)

lemma representsI:
  "jkbpT T = T \<Longrightarrow> represents T"
  unfolding represents_def by simp

lemma representsD:
  "represents T \<Longrightarrow> jkbpT T = T"
  unfolding represents_def by simp

(*>*)
text\<open>

This is the vicious cycle that we break using our assumption that the
view is synchronous. The key property of such views is that the
satisfaction of an epistemic formula is determined by the set of
traces in the model that have the same length. Lifted to @{term
"jAction"}, we have:

\<close>

(*<*)
lemma sync_tLength_eq_trc:
  assumes "(t, t') \<in> (\<Union>a\<in>as. relations (mkM T) a)\<^sup>*"
  shows "tLength t = tLength t'"
  using assms by (induct rule: rtrancl_induct) auto

lemma sync_gen_model_tLength:
  assumes traces: "{ t \<in> T . tLength t = n } = { t \<in> T' . tLength t = n }"
      and tT: "t \<in> { t \<in> T . tLength t = n }"
  shows "gen_model (mkM T) t = gen_model (mkM T') t"
  apply(rule gen_model_subset[where T="{ t \<in> T . tLength t = n }"])
  apply simp_all

  (* t \<in> T and t \<in> T' *)
  prefer 4
  using tT
  apply simp
  prefer 4
  using tT traces
  apply simp

  apply (unfold mkM_def)[1]
  using tT traces
  apply (auto)[1]

  using tT
  apply (auto dest: sync_tLength_eq_trc[where as=UNIV] kripke_rels_trc_worlds)[1]

  using tT traces
  apply (auto dest: sync_tLength_eq_trc[where as=UNIV] kripke_rels_trc_worlds)[1]

  done

(*>*)
lemma sync_jview_jAction_eq:
  assumes traces: "{ t \<in> T . tLength t = n } = { t \<in> T' . tLength t = n }"
  assumes tT: "t \<in> { t \<in> T . tLength t = n }"
  shows "jAction (mkM T) t = jAction (mkM T') t"
(*<*)
  apply (rule gen_model_jAction_eq[where w=t])
  apply (rule sync_gen_model_tLength)
  using assms
  apply (auto intro: gen_model_world_refl)
  done

(*>*)
text\<open>

This implies that for a synchronous view we can inductively define the
\emph{canonical traces} of a JKBP. These are the traces that a JKBP
generates when it is interpreted with respect to those very same
traces. We do this by constructing the sequence \<open>jkbpC\<^sub>n\<close> of
\emph{(canonical) temporal slices} similarly to @{term "jkbpT\<^bsub>n\<^esub>"}:

\<close>

fun jkbpCn :: "nat \<Rightarrow> 's Trace set"(*<*)("jkbpC\<^bsub>_\<^esub>")(*>*) where
  "jkbpC\<^bsub>0\<^esub>      = { tInit s |s. s \<in> set envInit }"
| "jkbpC\<^bsub>Suc n\<^esub> = { t \<leadsto> envTrans eact aact (tLast t) |t eact aact.
                             t \<in> jkbpC\<^bsub>n\<^esub> \<and> eact \<in> set (envAction (tLast t))
                          \<and> (\<forall>a. aact a \<in> set (jAction (mkM jkbpC\<^bsub>n\<^esub>) t a)) }"

abbreviation MCn :: "nat \<Rightarrow> ('a, 'p, 's Trace) KripkeStructure"(*<*)("MC\<^bsub>_\<^esub>")(*>*) where
  "MC\<^bsub>n\<^esub> \<equiv> mkM jkbpC\<^bsub>n\<^esub>"
(*<*)

lemma jkbpCn_step_inv:
  "t \<leadsto> s \<in> jkbpCn (Suc n) \<Longrightarrow> t \<in> jkbpCn n"
  by (induct n arbitrary: t, (fastforce simp add: Let_def)+)

lemma jkbpCn_length[simp]:
  "t \<in> jkbpCn n \<Longrightarrow> tLength t = n"
  by (induct n arbitrary: t, (fastforce simp add: Let_def)+)

lemma jkbpCn_init_inv[intro]:
  "tInit s \<in> jkbpCn n \<Longrightarrow> s \<in> set envInit"
   by (frule jkbpCn_length) auto

lemma jkbpCn_tFirst_init_inv[intro]:
 "t \<in> jkbpCn n \<Longrightarrow> tFirst t \<in> set envInit"
  by (induct n arbitrary: t) (auto iff: Let_def)

(*>*)
text\<open>

The canonical set of traces for a JKBP with respect to a joint view is
the set of canonical traces of all lengths.

\<close>

definition jkbpC :: "'s Trace set" where
  "jkbpC \<equiv> \<Union>n. jkbpC\<^bsub>n\<^esub>"

abbreviation MC :: "('a, 'p, 's Trace) KripkeStructure" where
  "MC \<equiv> mkM jkbpC"
(*<*)

lemma jkbpCn_jkbpC_subset:
  "jkbpCn n \<subseteq> jkbpC"
  unfolding jkbpC_def by blast

lemma jkbpCn_jkbpC_inc[intro]:
  "t \<in> jkbpCn n \<Longrightarrow> t \<in> jkbpC"
  unfolding jkbpC_def by best

lemma jkbpC_tLength_inv[intro]:
  "\<lbrakk> t \<in> jkbpC; tLength t = n \<rbrakk> \<Longrightarrow> t \<in> jkbpCn n"
  unfolding jkbpC_def
  by (induct n arbitrary: t, (fastforce simp add: Let_def)+)

lemma jkbpC_traces_of_length:
   "{ t \<in> jkbpC . tLength t = n } = jkbpCn n"
  unfolding jkbpC_def by bestsimp

lemma jkbpC_prefix_closed[dest]:
  "t \<leadsto> s \<in> jkbpC \<Longrightarrow> t \<in> jkbpC"
  apply (drule jkbpC_tLength_inv)
   apply simp
  apply (auto iff: Let_def jkbpC_def)
  done

lemma jkbpC_init[iff]:
  "tInit s \<in> jkbpC \<longleftrightarrow> s \<in> set envInit"
  unfolding jkbpC_def
  apply rule
   apply fast
  apply (subgoal_tac "tInit s \<in> jkbpCn 0")
   apply simp
  apply (rule_tac x=0 in exI)
  apply simp_all
  done

lemma jkbpC_jkbpCn_rels:
  "\<lbrakk> (u, v) \<in> relations MC a; tLength u = n \<rbrakk>
    \<Longrightarrow> (u, v) \<in> relations (MC\<^bsub>n\<^esub>) a"
  unfolding mkM_def by (fastforce dest: sync[rule_format])

lemma jkbpC_tFirst_init_inv[intro]:
  "t \<in> jkbpC \<Longrightarrow> tFirst t \<in> set envInit"
  unfolding jkbpC_def by blast

(*>*)
text\<open>

We can show that @{term "jkbpC"} represents the joint knowledge-based
program @{term "jkbp"} with respect to @{term "jview"}:

\<close>

lemma jkbpC_jkbpCn_jAction_eq:
  assumes tCn: "t \<in> jkbpC\<^bsub>n\<^esub>"
  shows "jAction MC t = jAction MC\<^bsub>n\<^esub> t"
(*<*)
  using assms
  by - (rule sync_jview_jAction_eq, auto iff: jkbpC_traces_of_length)

(*>*)
text\<open>\<close>

lemma jkbpTn_jkbpCn_represents: "jkbpT\<^bsub>n\<^esub> jkbpC = jkbpC\<^bsub>n\<^esub>"
  by (induct n) (fastforce simp: Let_def jkbpC_jkbpCn_jAction_eq)+

text\<open>\<close>

theorem jkbpC_represents: "represents jkbpC"
(*<*)
  using jkbpTn_jkbpCn_represents
  by (simp add: representsI jkbpC_def jkbpT_def)

(*>*)
text\<open>

We can show uniqueness too, by a similar argument:

\<close>

theorem jkbpC_represents_uniquely:
  assumes repT: "represents T"
  shows "T = jkbpC"
(*<*)
proof -
  { fix n
    have "{ t \<in> T . tLength t = n } = { t \<in> jkbpC . tLength t = n }"
    proof(induct n)
      case 0
      from repT have F: "{t \<in> T. tLength t = 0} = jkbpTn 0 T"
        by - (subst jkbpT_traces_of_length[symmetric], simp add: representsD)
      thus ?case by (simp add: jkbpC_traces_of_length)
    next
      case (Suc n)
      hence indhyp: "{t \<in> T. tLength t = n} = jkbpCn n"
        by (simp add: jkbpC_traces_of_length)

        (* F and H are very similar. *)
      from repT have F: "\<And>n. jkbpTn n T = {t \<in> T. tLength t = n}"
        by - (subst jkbpT_traces_of_length[symmetric], simp add: representsD)
      from indhyp F have G: "jkbpTn n T = jkbpCn n"
        by simp
      from repT have H: "\<And>n. {t \<in> T. tLength t = n} = {t \<in> jkbpTn n T. tLength t = n}"
        by (subst representsD[OF repT, symmetric], auto iff: jkbpT_traces_of_length jkbpTn_length)
      from F indhyp have ACTS:
        "\<And>t. t \<in> jkbpTn n T
          \<Longrightarrow> jAction (mkM T) t = jAction (MCn n) t"
        by - (rule sync_jview_jAction_eq[where n="n"], auto)
      show ?case
        apply (auto iff: Let_def ACTS G H jkbpC_traces_of_length)
        apply blast+
        done
    qed }
  thus ?thesis by auto
qed
(*>*)

end (* context PreEnvironmentJView *)

text\<open>

Thus, at least with synchronous views, we are justified in talking
about \emph{the} representation of a JKBP in a given environment. More
generally these results are also valid for the more general notion of
\emph{provides witnesses} as shown by \citet[Lemma 7.2.4]{FHMV:1995}
and \citet{DBLP:journals/dc/FaginHMV97}: it requires only that if a
subjective knowledge formula is false on a trace then there is a trace
of the same length or less that bears witness to that effect. This is
a useful generalisation in asynchronous settings.

The next section shows how we can construct canonical representations
of JKBPs using automata.

\<close>

(*<*)
end
(*>*)
