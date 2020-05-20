(*<*)
(*
 * Copyright 2015, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory CIMP_lang
imports
  CIMP_pred
begin

(*>*)
section\<open>CIMP syntax and semantics\<close>

text\<open>

\label{sec:cimp-syntax-semantics}

We define a small sequential programming language with synchronous
message passing primitives for describing the individual
processes. This has the advantage over raw transition systems in that
it is programmer-readable, includes sequential composition, supports a
program logic and VCG (\S\ref{sec:cimp-vcg}), etc. These processes are
composed in parallel at the top-level.

CIMP is inspired by IMP, as presented by @{cite [cite_macro=citet]
"Winskel:1993"} and @{cite [cite_macro=citet]
"ConcreteSemantics:2014"}, and the classical process algebras CCS
@{cite [cite_macro=citep] "Milner:1980" and "Milner:1989"} and CSP
@{cite [cite_macro=citep] "Hoare:1985"}. Note that the algebraic
properties of this language have not been developed.

As we operate in a concurrent setting, we need to provide a small-step
semantics (\S\ref{sec:cimp-semantics}), which we give in the style of
\emph{structural operational semantics} (SOS) as popularised by @{cite
[cite_macro=citet] "DBLP:journals/jlp/Plotkin04"}. The semantics of a
complete system (\S\ref{sec:cimp-system-steps}) is presently taken
simply to be the states reachable by interleaving the enabled steps of
the individual processes, subject to message passing rendezvous. We
leave a trace or branching semantics to future work.

\<close>

subsection\<open>Syntax\<close>

text\<open>

Programs are represented using an explicit (deep embedding) of their
syntax, as the semantics needs to track the progress of multiple
threads of control. Each (atomic) \emph{basic command}
(\S\ref{sec:cimp-decompose}) is annotated with a @{typ "'location"},
which we use in our assertions (\S\ref{sec:cimp-control-predicates}).
These locations need not be unique, though in practice they likely
will be.

Processes maintain \emph{local states} of type @{typ "'state"}. These
can be updated with arbitrary relations of @{typ "'state \<Rightarrow> 'state
set"} with \<open>LocalOp\<close>, and conditions of type @{typ "'s \<Rightarrow>
bool"} are similarly shallowly embedded. This arrangement allows the
end-user to select their own level of atomicity.

The sequential composition operator and control constructs are
standard. We add the infinite looping construct \<open>Loop\<close> so we
can construct single-state reactive systems; this has implications for
fairness assertions.

\<close>

type_synonym 's bexp = "'s \<Rightarrow> bool"

datatype ('answer, 'location, 'question, 'state) com
  = Request  "'location" "'state \<Rightarrow> 'question" "'answer \<Rightarrow> 'state \<Rightarrow> 'state set"        ("\<lbrace>_\<rbrace> Request _ _"  [0, 70, 70] 71)
  | Response "'location" "'question \<Rightarrow> 'state \<Rightarrow> ('state \<times> 'answer) set"               ("\<lbrace>_\<rbrace> Response _"  [0, 70] 71)
  | LocalOp  "'location" "'state \<Rightarrow> 'state set"                                       ("\<lbrace>_\<rbrace> LocalOp _" [0, 70] 71)
  | Cond1    "'location" "'state bexp" "('answer, 'location, 'question, 'state) com" ("\<lbrace>_\<rbrace> IF _ THEN _ FI" [0, 0] 71)
  | Cond2    "'location" "'state bexp" "('answer, 'location, 'question, 'state) com"
                           "('answer, 'location, 'question, 'state) com"             ("\<lbrace>_\<rbrace> IF _/ THEN _/ ELSE _/ FI"  [0, 0, 0] 71)
  | Loop     "('answer, 'location, 'question, 'state) com"                           ("LOOP DO _/ OD"  [0] 71)
  | While    "'location" "'state bexp" "('answer, 'location, 'question, 'state) com" ("\<lbrace>_\<rbrace> WHILE _/ DO _/ OD"  [0, 0, 0] 71)
  | Seq      "('answer, 'location, 'question, 'state) com"
              "('answer, 'location, 'question, 'state) com"                           (infixr ";;" 69)
  | Choose   "('answer, 'location, 'question, 'state) com"
              "('answer, 'location, 'question, 'state) com"                           (infixl "\<squnion>" 68)

text\<open>

We provide a one-armed conditional as it is the common form and avoids
the need to discover a label for an internal \<open>SKIP\<close> and/or
trickier proofs about the VCG.

In contrast to classical process algebras, we have local state and
distinct send and receive actions. These provide an interface to
Isabelle/HOL's datatypes that avoids the need for binding (ala the
$\pi$-calculus of @{cite [cite_macro=citet] "Milner:1989"}) or large
non-deterministic sums (ala CCS @{cite [cite_macro=citep] \<open>\S2.8\<close>
"Milner:1980"}). Intuitively the sender asks a @{typ "'question"} with
a \<open>Request\<close> command, which upon rendezvous with a
receiver's \<open>Response\<close> command receives an @{typ
"'answer"}. The @{typ "'question"} is a deterministic function of the
sender's local state, whereas a receiver can respond
non-deterministically. Note that CIMP does not provide a notion of
channel; these can be modelled by a judicious choice of @{typ
"'question"}.

We also provide a binary external choice operator. Internal choice can
be recovered in combination with local operations (see @{cite
[cite_macro=citet] \<open>\S2.3\<close> "Milner:1980"}).

We abbreviate some common commands: \<open>SKIP\<close> is a local
operation that does nothing, and the floor brackets simplify
deterministic \<open>LocalOp\<close>s. We also adopt some syntax magic from
Makarius's Hoare and Multiquote theories in the Isabelle/HOL
distribution.

\<close>

abbreviation SKIP_syn ("\<lbrace>_\<rbrace>/ SKIP" 70) where
  "\<lbrace>l\<rbrace> SKIP \<equiv> \<lbrace>l\<rbrace> LocalOp (\<lambda>s. {s})"

abbreviation (input) DetLocalOp :: "'location \<Rightarrow> ('state \<Rightarrow> 'state)
                                  \<Rightarrow> ('answer, 'location, 'question, 'state) com" ("\<lbrace>_\<rbrace> \<lfloor>_\<rfloor>") where
  "\<lbrace>l\<rbrace> \<lfloor>f\<rfloor> \<equiv> \<lbrace>l\<rbrace> LocalOp (\<lambda>s. {f s})"

syntax
  "_quote"        :: "'b \<Rightarrow> ('a \<Rightarrow> 'b)" ("\<guillemotleft>_\<guillemotright>" [0] 1000)
  "_antiquote"    :: "('a \<Rightarrow> 'b) \<Rightarrow> 'b" ("\<acute>_" [1000] 1000)
  "_Assign"       :: "'location \<Rightarrow> idt \<Rightarrow> 'b \<Rightarrow> ('answer, 'location, 'question, 'state) com" ("(\<lbrace>_\<rbrace> \<acute>_ :=/ _)" [0, 0, 70] 71) (* FIXME precedence -- see massive ambiguities in the GC model *)
  "_NonDetAssign" :: "'location \<Rightarrow> idt \<Rightarrow> 'b set \<Rightarrow> ('answer, 'location, 'question, 'state) com" ("(\<lbrace>_\<rbrace> \<acute>_ :\<in>/ _)" [0, 0, 70] 71)

abbreviation (input) NonDetAssign :: "'location \<Rightarrow> (('val \<Rightarrow> 'val) \<Rightarrow> 'state \<Rightarrow> 'state) \<Rightarrow> ('state \<Rightarrow> 'val set)
                                   \<Rightarrow> ('answer, 'location, 'question, 'state) com" where
  "NonDetAssign l upd es \<equiv> \<lbrace>l\<rbrace> LocalOp (\<lambda>s. { upd \<langle>e\<rangle> s |e. e \<in> es s })"

translations
  "\<lbrace>l\<rbrace> \<acute>x := e" => "CONST DetLocalOp l \<guillemotleft>\<acute>(_update_name x (\<lambda>_. e))\<guillemotright>"
  "\<lbrace>l\<rbrace> \<acute>x :\<in> es" => "CONST NonDetAssign l (_update_name x) \<guillemotleft>es\<guillemotright>"

parse_translation \<open>
  let
    fun antiquote_tr i (Const (@{syntax_const "_antiquote"}, _) $
          (t as Const (@{syntax_const "_antiquote"}, _) $ _)) = skip_antiquote_tr i t
      | antiquote_tr i (Const (@{syntax_const "_antiquote"}, _) $ t) =
          antiquote_tr i t $ Bound i
      | antiquote_tr i (t $ u) = antiquote_tr i t $ antiquote_tr i u
      | antiquote_tr i (Abs (x, T, t)) = Abs (x, T, antiquote_tr (i + 1) t)
      | antiquote_tr _ a = a
    and skip_antiquote_tr i ((c as Const (@{syntax_const "_antiquote"}, _)) $ t) =
          c $ skip_antiquote_tr i t
      | skip_antiquote_tr i t = antiquote_tr i t;

    fun quote_tr [t] = Abs ("s", dummyT, antiquote_tr 0 (Term.incr_boundvars 1 t))
      | quote_tr ts = raise TERM ("quote_tr", ts);
  in [(@{syntax_const "_quote"}, K quote_tr)] end
\<close>


subsection\<open>Process semantics\<close>

text\<open>

\label{sec:cimp-semantics}

Here we define the semantics of a single process's program. We begin
by defining the type of externally-visible behaviour:

\<close>

datatype ('answer, 'question) seq_label
  = sl_Internal ("\<tau>")
  | sl_Send 'question 'answer ("\<guillemotleft>_, _\<guillemotright>")
  | sl_Receive 'question 'answer ("\<guillemotright>_, _\<guillemotleft>")

text\<open>

We define a \emph{labelled transition system} (an LTS) using an
execution-stack style of semantics that avoids special treatment of
the \<open>SKIP\<close>s introduced by a traditional small step
semantics (such as @{cite [cite_macro=citet] \<open>Chapter~14\<close>
"Winskel:1993"}) when a basic command is executed. This was suggested
by Thomas Sewell; @{cite [cite_macro=citet] "PittsAM:opespe"} gave a
semantics to an ML-like language using this approach.

\<close>

type_synonym ('answer, 'location, 'question, 'state) local_state
  = "('answer, 'location, 'question, 'state) com list \<times> 'state"

inductive
  small_step :: "('answer, 'location, 'question, 'state) local_state
               \<Rightarrow> ('answer, 'question) seq_label
               \<Rightarrow> ('answer, 'location, 'question, 'state) local_state \<Rightarrow> bool" ("_ \<rightarrow>\<^bsub>_\<^esub> _" [55, 0, 56] 55)
where
  Request:  "\<lbrakk> \<alpha> = action s; s' \<in> val \<beta> s \<rbrakk> \<Longrightarrow> (\<lbrace>l\<rbrace> Request action val # cs, s) \<rightarrow>\<^bsub>\<guillemotleft>\<alpha>, \<beta>\<guillemotright>\<^esub> (cs, s')"
| Response: "(s', \<beta>) \<in> action \<alpha> s \<Longrightarrow> (\<lbrace>l\<rbrace> Response action # cs, s) \<rightarrow>\<^bsub>\<guillemotright>\<alpha>, \<beta>\<guillemotleft>\<^esub> (cs, s')"

| LocalOp: "s' \<in> R s \<Longrightarrow> (\<lbrace>l\<rbrace> LocalOp R # cs, s) \<rightarrow>\<^bsub>\<tau>\<^esub> (cs, s')"

| Cond1True:  "b s \<Longrightarrow> (\<lbrace>l\<rbrace> IF b THEN c FI # cs, s) \<rightarrow>\<^bsub>\<tau>\<^esub> (c # cs, s)"
| Cond1False: "\<not>b s \<Longrightarrow> (\<lbrace>l\<rbrace> IF b THEN c FI # cs, s) \<rightarrow>\<^bsub>\<tau>\<^esub> (cs, s)"

| Cond2True:  "b s \<Longrightarrow> (\<lbrace>l\<rbrace> IF b THEN c1 ELSE c2 FI # cs, s) \<rightarrow>\<^bsub>\<tau>\<^esub> (c1 # cs, s)"
| Cond2False: "\<not>b s \<Longrightarrow> (\<lbrace>l\<rbrace> IF b THEN c1 ELSE c2 FI # cs, s) \<rightarrow>\<^bsub>\<tau>\<^esub> (c2 # cs, s)"

| Loop:       "(c # LOOP DO c OD # cs, s) \<rightarrow>\<^bsub>\<alpha>\<^esub> (cs', s') \<Longrightarrow> (LOOP DO c OD # cs, s) \<rightarrow>\<^bsub>\<alpha>\<^esub> (cs', s')"

| While:      "b s \<Longrightarrow> (\<lbrace>l\<rbrace> WHILE b DO c OD # cs, s) \<rightarrow>\<^bsub>\<tau>\<^esub> (c # \<lbrace>l\<rbrace> WHILE b DO c OD # cs, s)"
| WhileFalse: "\<not> b s \<Longrightarrow> (\<lbrace>l\<rbrace> WHILE b DO c OD # cs, s) \<rightarrow>\<^bsub>\<tau>\<^esub> (cs, s)"

| Seq:     "(c1 # c2 # cs, s) \<rightarrow>\<^bsub>\<alpha>\<^esub> (cs', s') \<Longrightarrow> (c1;; c2 # cs, s) \<rightarrow>\<^bsub>\<alpha>\<^esub> (cs', s')"

| Choose1: "(c1 # cs, s) \<rightarrow>\<^bsub>\<alpha>\<^esub> (cs', s') \<Longrightarrow> (c1 \<squnion> c2 # cs, s) \<rightarrow>\<^bsub>\<alpha>\<^esub> (cs', s')"
| Choose2: "(c2 # cs, s) \<rightarrow>\<^bsub>\<alpha>\<^esub> (cs', s') \<Longrightarrow> (c1 \<squnion> c2 # cs, s) \<rightarrow>\<^bsub>\<alpha>\<^esub> (cs', s')"

text\<open>

The following projections operate on local states. These are internal
to CIMP and should not appear to the end-user.

\<close>

abbreviation cPGM :: "('answer, 'location, 'question, 'state) local_state \<Rightarrow> ('answer, 'location, 'question, 'state) com list" where
  "cPGM \<equiv> fst"

abbreviation cLST :: "('answer, 'location, 'question, 'state) local_state \<Rightarrow> 'state" where
  "cLST s \<equiv> snd s"
(*<*)

declare small_step.intros[intro]

inductive_cases small_step_inv[elim]:
  "(\<lbrace>l\<rbrace> Request action val # cs, ls) \<rightarrow>\<^bsub>a\<^esub> s'"
  "(\<lbrace>l\<rbrace> Response action # cs, ls) \<rightarrow>\<^bsub>a\<^esub> s'"
  "(\<lbrace>l\<rbrace> LocalOp R # cs, ls) \<rightarrow>\<^bsub>a\<^esub> s'"
  "(\<lbrace>l\<rbrace> IF b THEN c FI # cs, ls) \<rightarrow>\<^bsub>a\<^esub> s'"
  "(\<lbrace>l\<rbrace> IF b THEN c1 ELSE c2 FI # cs, ls) \<rightarrow>\<^bsub>a\<^esub> s'"
  "(\<lbrace>l\<rbrace> WHILE b DO c OD # cs, ls) \<rightarrow>\<^bsub>a\<^esub> s'"
  "(LOOP DO c OD # cs, ls) \<rightarrow>\<^bsub>a\<^esub> s'"

lemma small_step_impossible[iff]:
  "\<not>(\<lbrace>l\<rbrace> Request action val # cs, ls) \<rightarrow>\<^bsub>\<tau>\<^esub> s'"
  "\<not>(\<lbrace>l\<rbrace> Request action val # cs, ls) \<rightarrow>\<^bsub>\<guillemotright>\<alpha>, \<beta>\<guillemotleft>\<^esub> s'"
  "\<not>(\<lbrace>l\<rbrace> Response action' # cs, ls) \<rightarrow>\<^bsub>\<tau>\<^esub> s'"
  "\<not>(\<lbrace>l\<rbrace> Response action' # cs, ls) \<rightarrow>\<^bsub>\<guillemotleft>\<alpha>, \<beta>\<guillemotright>\<^esub> s'"
  "\<not>(\<lbrace>l\<rbrace> LocalOp R # cs, ls) \<rightarrow>\<^bsub>\<guillemotright>\<alpha>, \<beta>\<guillemotleft>\<^esub> s'"
  "\<not>(\<lbrace>l\<rbrace> LocalOp R # cs, ls) \<rightarrow>\<^bsub>\<guillemotleft>\<alpha>, \<beta>\<guillemotright>\<^esub> s'"
  "\<not>(\<lbrace>l\<rbrace> IF b THEN c FI # cs, ls) \<rightarrow>\<^bsub>\<guillemotright>\<alpha>, \<beta>\<guillemotleft>\<^esub> s'"
  "\<not>(\<lbrace>l\<rbrace> IF b THEN c FI # cs, ls) \<rightarrow>\<^bsub>\<guillemotleft>\<alpha>, \<beta>\<guillemotright>\<^esub> s'"
  "\<not>(\<lbrace>l\<rbrace> IF b THEN c1 ELSE c2 FI # cs, ls) \<rightarrow>\<^bsub>\<guillemotright>\<alpha>, \<beta>\<guillemotleft>\<^esub> s'"
  "\<not>(\<lbrace>l\<rbrace> IF b THEN c1 ELSE c2 FI # cs, ls) \<rightarrow>\<^bsub>\<guillemotleft>\<alpha>, \<beta>\<guillemotright>\<^esub> s'"
  "\<not>(\<lbrace>l\<rbrace> WHILE b DO c OD # cs, ls) \<rightarrow>\<^bsub>\<guillemotright>\<alpha>, \<beta>\<guillemotleft>\<^esub> s'"
  "\<not>(\<lbrace>l\<rbrace> WHILE b DO c OD # cs, ls) \<rightarrow>\<^bsub>\<guillemotleft>\<alpha>, \<beta>\<guillemotright>\<^esub> s'"
by (auto elim: small_step.cases)

lemma small_step_stuck[iff]:
  "\<not> ([], l, s) \<rightarrow>\<^bsub>\<alpha>\<^esub> c'"
by (auto elim: small_step.cases)

(*>*)
text\<open>

\label{sec:cimp-decompose}

To reason about system transitions we need to identify which basic
statement gets executed next. To that end we factor out the recursive
cases of the @{term "small_step"} semantics into \emph{contexts},
which identify the \<open>basic_com\<close> commands with immediate
externally-visible behaviour. Note that non-determinism means that
more than one \<open>basic_com\<close> can be enabled at a time.

The representation of evaluation contexts follows @{cite
[cite_macro=citet] "DBLP:journals/jar/Berghofer12"}. This style of
operational semantics was originated by @{cite [cite_macro=citet]
"DBLP:journals/tcs/FelleisenH92"}.

\<close>

type_synonym ('answer, 'location, 'question, 'state) ctxt
  = "('answer, 'location, 'question, 'state) com \<Rightarrow> ('answer, 'location, 'question, 'state) com"

inductive_set
  ctxt :: "( ('answer, 'location, 'question, 'state) ctxt
           \<times> (('answer, 'location, 'question, 'state) com \<Rightarrow> ('answer, 'location, 'question, 'state) com list) ) set"
where
  C_Hole: "(id, \<langle>[]\<rangle>) \<in> ctxt"
| C_Loop: "(E, fctxt) \<in> ctxt \<Longrightarrow> (\<lambda>t. LOOP DO E t OD, \<lambda>t. fctxt t @ [LOOP DO E t OD]) \<in> ctxt"
| C_Seq: "(E, fctxt) \<in> ctxt \<Longrightarrow> (\<lambda>t. E t;; u, \<lambda>t. fctxt t @ [u]) \<in> ctxt"
| C_Choose1: "(E, fctxt) \<in> ctxt \<Longrightarrow> (\<lambda>t. E t \<squnion> u, fctxt) \<in> ctxt"
| C_Choose2: "(E, fctxt) \<in> ctxt \<Longrightarrow> (\<lambda>t. u \<squnion> E t, fctxt) \<in> ctxt"

inductive
  basic_com :: "('answer, 'location, 'question, 'state) com \<Rightarrow> bool"
where
  "basic_com (\<lbrace>l\<rbrace> Request action val)"
| "basic_com (\<lbrace>l\<rbrace> Response action)"
| "basic_com (\<lbrace>l\<rbrace> LocalOp R)"
| "basic_com (\<lbrace>l\<rbrace> IF b THEN c FI)"
| "basic_com (\<lbrace>l\<rbrace> IF b THEN c1 ELSE c2 FI)"
| "basic_com (\<lbrace>l\<rbrace> WHILE b DO c OD)"
(*<*)

declare basic_com.intros[intro!] basic_com.cases[elim]

(*>*)
text\<open>

We can decompose a small step into a context and a @{term
"basic_com"}.

\<close>

fun
  decompose_com :: "('answer, 'location, 'question, 'state) com
                      \<Rightarrow> ( ('answer, 'location, 'question, 'state) com
                        \<times> ('answer, 'location, 'question, 'state) ctxt
                        \<times> (('answer, 'location, 'question, 'state) com \<Rightarrow> ('answer, 'location, 'question, 'state) com list) ) set"
where
  "decompose_com (LOOP DO c1 OD) = { (c, \<lambda>t. LOOP DO ictxt t OD, \<lambda>t. fctxt t @ [LOOP DO ictxt t OD]) |c fctxt ictxt. (c, ictxt, fctxt) \<in> decompose_com c1 }"
| "decompose_com (c1;; c2) = { (c, \<lambda>t. ictxt t;; c2, \<lambda>t. fctxt t @ [c2]) |c fctxt ictxt. (c, ictxt, fctxt) \<in> decompose_com c1 }"
| "decompose_com (c1 \<squnion> c2) = { (c, \<lambda>t. ictxt t \<squnion> c2, fctxt) |c fctxt ictxt. (c, ictxt, fctxt) \<in> decompose_com c1 }
                           \<union> { (c, \<lambda>t. c1 \<squnion> ictxt t, fctxt) |c fctxt ictxt. (c, ictxt, fctxt) \<in> decompose_com c2 }"
| "decompose_com c = {(c, id, \<langle>[]\<rangle>)}"

definition
  decomposeLS :: "('answer, 'location, 'question, 'state) local_state
               \<Rightarrow> ( ('answer, 'location, 'question, 'state) com
                 \<times> (('answer, 'location, 'question, 'state) com \<Rightarrow> ('answer, 'location, 'question, 'state) com)
                 \<times> (('answer, 'location, 'question, 'state) com \<Rightarrow> ('answer, 'location, 'question, 'state) com list) ) set"
where
  "decomposeLS s \<equiv> case cPGM s of c # _ \<Rightarrow> decompose_com c | _ \<Rightarrow> {}"

(*<*)
declare ctxt.intros[intro!]

lemma ctxt_inj:
  assumes "(E, fctxt) \<in> ctxt"
  assumes "E x = E y"
  shows "x = y"
using assms by (induct set: ctxt) auto

lemma decompose_ctxt:
  assumes "(c', ictxt, fctxt) \<in> decompose_com c"
  shows "(ictxt, fctxt) \<in> ctxt"
using assms by (induct c arbitrary: c' ictxt fctxt) auto

lemma decompose_ictxt:
  assumes "(c', ictxt, fctxt) \<in> decompose_com c"
  shows "c = ictxt c'"
using assms by (induct c arbitrary: c' ictxt fctxt) auto
(*>*)

theorem context_decompose:
  "s \<rightarrow>\<^bsub>\<alpha>\<^esub> s' \<longleftrightarrow> (\<exists>(c, ictxt, fctxt) \<in> decomposeLS s.
                     cPGM s = ictxt c # tl (cPGM s)
                   \<and> basic_com c
                   \<and> (c # fctxt c @ tl (cPGM s), cLST s) \<rightarrow>\<^bsub>\<alpha>\<^esub> s')"
(*<*)(is "?lhs = ?rhs")
proof
  assume ?lhs then show ?rhs
    by (induct rule: small_step.induct)
       (fastforce simp: decomposeLS_def)+
next
  have gen: "(c0 # cs, s) \<rightarrow>\<^bsub>\<alpha>\<^esub> s'"
    if as: "(c # fctxt c @ cs, s) \<rightarrow>\<^bsub>\<alpha>\<^esub> s'"
   and ds: "(c, ictxt, fctxt) \<in> decompose_com c0"
   for cs c c0 ictxt fctxt l s s'
  proof -
    from ds have ic: "(ictxt, fctxt) \<in> ctxt"
      unfolding decomposeLS_def by (auto intro: decompose_ctxt split: list.splits)
    from ic as decompose_ictxt[OF ds]
    show "(c0 # cs, s) \<rightarrow>\<^bsub>\<alpha>\<^esub> s'"
      by (induct ictxt fctxt arbitrary: c0 cs set: ctxt)
         (cases s', fastforce simp: fun_eq_iff dest: ctxt_inj)+
  qed
  assume ?rhs then show ?lhs
    by (cases s)
       (auto simp: decomposeLS_def split: list.splits dest!: gen)
qed

(*>*)
text\<open>

While we only use this result left-to-right (to decompose a small step
into a basic one), this equivalence shows that we lose no information
in doing so.

\<close>

subsection\<open>System steps\<close>

text\<open>

\label{sec:cimp-system-steps}

A global state maps process names to process' local states. One might
hope to allow processes to have distinct types of local state, but
there remains no good solution yet in a simply-typed setting; see
@{cite [cite_macro=citet] "DBLP:journals/entcs/SchirmerW09"}.

\<close>

type_synonym ('answer, 'location, 'proc, 'question, 'state) global_state
  = "'proc \<Rightarrow> ('answer, 'location, 'question, 'state) local_state"

type_synonym ('proc, 'state) local_states
  = "'proc \<Rightarrow> 'state"

text\<open>

An execution step of the overall system is either any enabled internal
@{term "\<tau>"} step of any process, or a communication rendezvous between
two processes. For the latter to occur, a @{const "Request"} action
must be enabled in process @{term "p1"}, and a @{const "Response"}
action in (distinct) process @{term "p2"}, where the request/response
labels @{term "\<alpha>"} and @{term "\<beta>"} (semantically) match.

We also track global communication history here to support assertional
reasoning (see \S\ref{sec:cimp-assertions}).

\<close>

type_synonym ('answer, 'question) event = "'question \<times> 'answer"
type_synonym ('answer, 'question) history = "('answer, 'question) event list"

type_synonym ('answer, 'location, 'proc, 'question, 'state) system_state
  = "('answer, 'location, 'proc, 'question, 'state) global_state
   \<times> ('answer, 'question) history"

inductive_set
  system_step :: "( ('answer, 'ls, 'proc, 'question, 'state) system_state
                  \<times> ('answer, 'ls, 'proc, 'question, 'state) system_state ) set"
where
  LocalStep: "\<lbrakk> s p \<rightarrow>\<^bsub>\<tau>\<^esub> ls'; s' = s(p := ls'); h' = h \<rbrakk> \<Longrightarrow> ((s, h), (s', h')) \<in> system_step"
| CommunicationStep: "\<lbrakk> s p1 \<rightarrow>\<^bsub>\<guillemotleft>\<alpha>, \<beta>\<guillemotright>\<^esub> ls1'; s p2 \<rightarrow>\<^bsub>\<guillemotright>\<alpha>, \<beta>\<guillemotleft>\<^esub> ls2'; p1 \<noteq> p2;
                        s' = s(p1 := ls1', p2 := ls2'); h' = h @ [(\<alpha>, \<beta>)] \<rbrakk> \<Longrightarrow> ((s, h), (s', h')) \<in> system_step"

abbreviation
  system_step_syn :: "('answer, 'ls, 'proc, 'question, 'state) system_state
                    \<Rightarrow> ('answer, 'ls, 'proc, 'question, 'state) system_state \<Rightarrow> bool" ("_ s\<Rightarrow> _" [55, 56] 55)
where
  "sh s\<Rightarrow> sh' \<equiv> (sh, sh') \<in> system_step"

abbreviation
  system_steps_syn :: "('answer, 'ls, 'proc, 'question, 'state) system_state
                     \<Rightarrow> ('answer, 'ls, 'proc, 'question, 'state) system_state \<Rightarrow> bool" ("_ s\<Rightarrow>\<^sup>* _" [55, 56] 55)
where
  "sh s\<Rightarrow>\<^sup>* sh' \<equiv> (sh, sh') \<in> system_step\<^sup>*"
(*<*)

(*>*)
text\<open>

In classical process algebras matching communication actions yield
\<open>\<tau>\<close> steps, which aids nested parallel composition
and the restriction operation @{cite [cite_macro=citep]
\<open>\S2.2\<close> "Milner:1980"}. As CIMP does not provide either
we do not need to hide communication labels. In CCS/CSP it is not
clear how one reasons about the communication history, and it seems
that assertional reasoning about these languages is not well
developed.

\<close>

subsection\<open>Assertions\<close>

text\<open>

\label{sec:cimp-assertions}

We now develop a technique for showing that a CIMP system satisfies a
single global invariant, following @{cite [cite_macro=citet]
"DBLP:journals/acta/Lamport80" and "DBLP:journals/toplas/LamportS84"}
(and the later @{cite [cite_macro=citet] "DBLP:books/aw/Lamport2002"})
and closely related work by @{cite [cite_macro=citet]
"AptFrancezDeRoever:1980"}, @{cite [cite_macro=citet]
"CousotCousot:1980"} and @{cite [cite_macro=citet]
"DBLP:journals/acta/LevinG81"}, which suggest the incorporation of a
history variable. @{cite [cite_macro=citet] "CousotCousot:1980"}
apparently contains a completeness proof.  Lamport mentions that this
technique was well-known in the mid-80s when he proposed the use of
prophecy variables (see his webpage bibliography). See also @{cite
[cite_macro=citet] "DBLP:books/cu/RoeverBH2001"} for an extended
discussion of some of this.

Achieving the right level of abstraction is a bit fiddly; we want to
avoid revealing too much of the program text as it
executes. Intuitively we wish to expose the processes's present
control locations and local states only. @{cite [cite_macro=citet]
"DBLP:journals/acta/Lamport80"} avoids these issues by only providing
an axiomatic semantics for his language.

\<close>

subsubsection\<open>Control predicates\<close>

text\<open>

\label{sec:cimp-control-predicates}

Following @{cite [cite_macro=citet]
"DBLP:journals/acta/Lamport80"}\footnote{@{cite [cite_macro=citet]
"MannaPnueli:1995"} also develop a theory of locations. I think
Lamport attributes control predicates to Owicki in her PhD thesis
(under Gries). I did not find a treatment of procedures. @{cite
[cite_macro=citet] "MannaPnueli:1991"} observe that a set notation for
spreading assertions over sets of locations reduces clutter
significantly.}, we define the \<open>at\<close> predicate, which
holds of a process when control resides at that location. Due to
non-determinism processes can be \<open>at\<close> a set of locations;
it is more like ``a statement with this location is enabled'', which
incidentally handles non-unique locations. Lamport's language is
deterministic, so he doesn't have this problem. This also allows him
to develop a stronger theory about his control predicates.

\<close>

primrec
  atC :: "('answer, 'location, 'question, 'state) com \<Rightarrow> 'location \<Rightarrow> bool"
where
  "atC (\<lbrace>l'\<rbrace> Request action val) = (\<lambda>l. l = l')"
| "atC (\<lbrace>l'\<rbrace> Response action) = (\<lambda>l. l = l')"
| "atC (\<lbrace>l'\<rbrace> LocalOp f) = (\<lambda>l. l = l')"
| "atC (\<lbrace>l'\<rbrace> IF _ THEN _ FI) = (\<lambda>l. l = l')"
| "atC (\<lbrace>l'\<rbrace> IF _ THEN _ ELSE _ FI) = (\<lambda>l. l = l')"
| "atC (\<lbrace>l'\<rbrace> WHILE _ DO _ OD) = (\<lambda>l. l = l')"
| "atC (LOOP DO c OD) = atC c"
| "atC (c1;; c2) = atC c1"
| "atC (c1 \<squnion> c2) = (atC c1 \<^bold>\<or> atC c2)"

primrec atL :: "('answer, 'location, 'question, 'state) com list \<Rightarrow> 'location \<Rightarrow> bool" where
  "atL [] = \<langle>False\<rangle>"
| "atL (c # _) = atC c"

abbreviation atLS :: "('answer, 'location, 'question, 'state) local_state \<Rightarrow> 'location \<Rightarrow> bool" where
  "atLS \<equiv> \<lambda>s. atL (cPGM s)"
(*<*)

lemma at_decompose:
  "(c, ictxt, fctxt) \<in> decompose_com c0 \<Longrightarrow> (\<forall>l. atC c l \<longrightarrow> atC c0 l)"
by (induct c0 arbitrary: c ictxt fctxt) fastforce+

lemma at_decomposeLS:
  "(c, ictxt, fctxt) \<in> decomposeLS s \<Longrightarrow> (\<forall>l. atC c l \<longrightarrow> atLS s l)"
by (auto simp: decomposeLS_def at_decompose split: list.splits)

(*>*)
text\<open>

We define predicates over communication histories and a projection of
global states. These are uncurried to ease composition.

\<close>

type_synonym ('location, 'proc, 'state) pred_local_state
  = "'proc \<Rightarrow> (('location \<Rightarrow> bool) \<times> 'state)"

record ('answer, 'location, 'proc, 'question, 'state) pred_state =
  local_states :: "('location, 'proc, 'state) pred_local_state"
  hist :: "('answer, 'question) history"

type_synonym ('answer, 'location, 'proc, 'question, 'state) pred
  = "('answer, 'location, 'proc, 'question, 'state) pred_state \<Rightarrow> bool"

definition mkP :: "('answer, 'location, 'proc, 'question, 'state) system_state \<Rightarrow> ('answer, 'location, 'proc, 'question, 'state) pred_state" where
  "mkP \<equiv> \<lambda>(s, h). \<lparr> local_states = \<lambda>p. case s p of (cs, ps) \<Rightarrow> (atL cs, ps), hist = h \<rparr>"
(*<*)

lemma hist_mkP[iff]:
  "hist (mkP (s, h)) = h"
by (simp add: mkP_def)

(*>*)
text\<open>

We provide the following definitions to the end-user.

\<open>AT\<close> maps process names to a predicate that is true of
locations where control for that process resides. The abbreviation
\<open>at\<close> shuffles its parameters; the former is
simplifier-friendly and eta-reduced, while the latter is convenient
for writing assertions.

\<close>

definition AT :: "('answer, 'location, 'proc, 'question, 'state) pred_state \<Rightarrow> 'proc \<Rightarrow> 'location \<Rightarrow> bool" where
  "AT \<equiv> \<lambda>s p l. fst (local_states s p) l"

abbreviation at :: "'proc \<Rightarrow> 'location \<Rightarrow> ('answer, 'location, 'proc, 'question, 'state) pred" where
  "at p l s \<equiv> AT s p l"

text\<open>

Often we wish to talk about control residing at one of a set of
locations. This stands in for, and generalises, the \<open>in\<close>
predicate of @{cite [cite_macro=citet]
"DBLP:journals/acta/Lamport80"}.

\<close>

definition atS :: "'proc \<Rightarrow> 'location set \<Rightarrow> ('answer, 'location, 'proc, 'question, 'state) pred" where
  "atS \<equiv> \<lambda>p ls s. \<exists>l\<in>ls. at p l s"

text\<open>

A process is terminated if it not at any control location.

\<close>

abbreviation terminated :: "'proc \<Rightarrow> ('answer, 'location, 'proc, 'question, 'state) pred" where
  "terminated p s \<equiv> \<forall>l. \<not>at p l s"

text\<open>

The \<open>LST\<close> operator (written as a postfix \<open>\<down>\<close>) projects
the local states of the processes from a \<open>pred_state\<close>, i.e. it
discards control location information.

Conversely the \<open>LSTP\<close> operator lifts predicates over
local states into predicates over \<open>pred_state\<close>.  @{cite
[cite_macro=citet] \<open>\S3.6\<close> "DBLP:journals/acta/LevinG81"}
call such predicates \emph{universal assertions}.

\<close>

type_synonym ('proc, 'state) state_pred
  = "('proc, 'state) local_states \<Rightarrow> bool"

definition LST :: "('answer, 'location, 'proc, 'question, 'state) pred_state
                 \<Rightarrow> ('proc, 'state) local_states" ("_\<down>" [1000] 1000) where
  "s\<down> \<equiv> snd \<circ> local_states s"

abbreviation (input) LSTP :: "('proc, 'state) state_pred
                            \<Rightarrow> ('answer, 'location, 'proc, 'question, 'state) pred" where
  "LSTP P \<equiv> \<lambda>s. P (LST s)"

text\<open>

By default we ask the simplifier to rewrite @{const "atS"} using
ambient @{const "AT"} information.

\<close>

lemma atS_state_cong[cong]:
  "\<lbrakk> AT s p = AT s' p \<rbrakk> \<Longrightarrow> atS p ls s \<longleftrightarrow> atS p ls s'"
by (auto simp: atS_def)

text\<open>

We provide an incomplete set of basic rules for label sets.

\<close>

lemma atS_simps:
  "\<not>atS p {} s"
  "atS p {l} s \<longleftrightarrow> at p l s"
  "\<lbrakk> at p l s; l \<in> ls \<rbrakk> \<Longrightarrow> atS p ls s \<longleftrightarrow> True"
  "(\<forall>l. at p l s \<longrightarrow> l \<notin> ls) \<Longrightarrow> atS p ls s \<longleftrightarrow> False"
by (auto simp: atS_def)

lemma atS_mono:
  "\<lbrakk> atS p ls s; ls \<subseteq> ls' \<rbrakk> \<Longrightarrow> atS p ls' s"
by (auto simp: atS_def)

lemma atS_un:
  "atS p (l \<union> l') s \<longleftrightarrow> atS p l s \<or> atS p l' s"
by (auto simp: atS_def)

subsubsection\<open>Invariants\<close>

text\<open>

\label{sec:cimp-invariants}

A complete system consists of one program per process, and a (global)
constraint on their initial local states. From these we can construct
the set of initial global states and all those reachable by system
steps (\S\ref{sec:cimp-system-steps}).

\<close>

type_synonym ('answer, 'location, 'proc, 'question, 'state) programs
  = "'proc \<Rightarrow> ('answer, 'location, 'question, 'state) com"

type_synonym ('answer, 'location, 'proc, 'question, 'state) system
  = "('answer, 'location, 'proc, 'question, 'state) programs
   \<times> ('proc, 'state) state_pred"

definition
  initial_states :: "('answer, 'location, 'proc, 'question, 'state) system
                   \<Rightarrow> ('answer, 'location, 'proc, 'question, 'state) global_state set"
where
  "initial_states sys \<equiv>
     { f . (\<forall>p. cPGM (f p) = [fst sys p]) \<and> snd sys (cLST \<circ> f) }"

definition
  reachable_states :: "('answer, 'location, 'proc, 'question, 'state) system
                     \<Rightarrow> ('answer, 'location, 'proc, 'question, 'state) system_state set"
where
  "reachable_states sys \<equiv> system_step\<^sup>* `` (initial_states sys \<times> {[]})"

text\<open>

The following is a slightly more convenient induction rule for the set
of reachable states.

\<close>

lemma reachable_states_system_step_induct[consumes 1,
                                          case_names init LocalStep CommunicationStep]:
  assumes r: "(s, h) \<in> reachable_states sys"
  assumes i: "\<And>s. s \<in> initial_states sys \<Longrightarrow> P s []"
  assumes l: "\<And>s h ls' p. \<lbrakk> (s, h) \<in> reachable_states sys; P s h; s p \<rightarrow>\<^bsub>\<tau>\<^esub> ls' \<rbrakk>
                    \<Longrightarrow> P (s(p := ls')) h"
  assumes c: "\<And>s h ls1' ls2' p1 p2 \<alpha> \<beta>.
                 \<lbrakk> (s, h) \<in> reachable_states sys; P s h;
                 s p1 \<rightarrow>\<^bsub>\<guillemotleft>\<alpha>, \<beta>\<guillemotright>\<^esub> ls1'; s p2 \<rightarrow>\<^bsub>\<guillemotright>\<alpha>, \<beta>\<guillemotleft>\<^esub> ls2'; p1 \<noteq> p2 \<rbrakk>
                    \<Longrightarrow> P (s(p1 := ls1', p2 := ls2')) (h @ [(\<alpha>, \<beta>)])"
  shows "P s h"
(*<*)
proof -
  have "P s' h'" if "(s, []) s\<Rightarrow>\<^sup>* (s', h')" "s \<in> initial_states sys" for s s' h'
    using that
    by (induct rule: rtrancl_induct2)
       (fastforce simp: reachable_states_def elim: system_step.cases intro: i l c)+
  with r show ?thesis by (clarsimp simp: reachable_states_def)
qed

lemma initial_statesD:
  "s \<in> initial_states sys \<Longrightarrow> AT (mkP (s, [])) = atC \<circ> fst sys \<and> snd sys (mkP (s, []))\<down>"
by (simp add: initial_states_def mkP_def split_def o_def LST_def AT_def)

lemma initial_states_mkP[iff]:
  "s \<in> initial_states sys \<Longrightarrow> at p l (mkP (s, [])) \<longleftrightarrow> atC (fst sys p) l"
by (simp add: initial_states_def mkP_def split_def AT_def)

(*>*)
subsubsection\<open>Relating reachable states to the initial programs\<close>

text\<open>

\label{sec:cimp-decompose-small-step}

To usefully reason about the control locations presumably embedded in
the single global invariant, we need to link the programs we have in
reachable state \<open>s\<close> to the programs in the initial states. The
\<open>fragments\<close> function decomposes the program into statements
that can be directly executed (\S\ref{sec:cimp-decompose}). We also
compute the locations we could be at after executing that statement as
a function of the process's local state.

We could support Lamport's \<open>after\<close> control predicate with more
syntactic analysis of this kind.

\<close>

fun
  extract_cond :: "('answer, 'location, 'question, 'state) com \<Rightarrow> 'state bexp"
where
  "extract_cond (\<lbrace>l\<rbrace> IF b THEN c FI) = b"
| "extract_cond (\<lbrace>l\<rbrace> IF b THEN c1 ELSE c2 FI) = b"
| "extract_cond (\<lbrace>l\<rbrace> WHILE b DO c OD) = b"
| "extract_cond c = \<langle>False\<rangle>"

type_synonym  ('answer, 'location, 'question, 'state) loc_comp
  = "('answer, 'location, 'question, 'state) com
   \<Rightarrow> 'state \<Rightarrow> 'location \<Rightarrow> bool"

fun lconst :: "('location \<Rightarrow> bool) \<Rightarrow> ('answer, 'location, 'question, 'state) loc_comp" where
  "lconst lp b s = lp"

definition lcond :: "('location \<Rightarrow> bool) \<Rightarrow> ('location \<Rightarrow> bool)
                   \<Rightarrow> ('answer, 'location, 'question, 'state) loc_comp" where
  "lcond lp lp' c s \<equiv> if extract_cond c s then lp else lp'"
(*<*)

lemma lcond_split:
  "Q (lcond lp lp' c s) \<longleftrightarrow> (extract_cond c s \<longrightarrow> Q lp) \<and> (\<not>extract_cond c s \<longrightarrow> Q lp')"
by (simp add: lcond_def split: if_splits)

lemma lcond_split_asm:
  "Q (lcond lp lp' c s) \<longleftrightarrow> \<not> ((extract_cond c s \<and> \<not>Q lp) \<or> (\<not>extract_cond c s \<and> \<not> Q lp'))"
by (simp add: lcond_def split: if_splits)

lemmas lcond_splits = lcond_split lcond_split_asm
(*>*)

fun
  fragments :: "('answer, 'location, 'question, 'state) com
              \<Rightarrow> ('location \<Rightarrow> bool)
              \<Rightarrow> ( ('answer, 'location, 'question, 'state) com
               \<times> ('answer, 'location, 'question, 'state) loc_comp ) set"
where
  "fragments (\<lbrace>l\<rbrace> IF b THEN c FI) ls
       = { (\<lbrace>l\<rbrace> IF b THEN c' FI, lcond (atC c) ls) |c'. True }
        \<union> fragments c ls"
| "fragments (\<lbrace>l\<rbrace> IF b THEN c1 ELSE c2 FI) ls
       = { (\<lbrace>l\<rbrace> IF b THEN c1' ELSE c2' FI, lcond (atC c1) (atC c2)) |c1' c2'. True }
        \<union> fragments c1 ls \<union> fragments c2 ls"
| "fragments (LOOP DO c OD) ls = fragments c (atC c)"
| "fragments (\<lbrace>l'\<rbrace> WHILE b DO c OD) ls
       = { (\<lbrace>l'\<rbrace> WHILE b DO c' OD, lcond (atC c) ls) |c'. True } \<union> fragments c (\<lambda>l. l = l')"
| "fragments (c1;; c2) ls = fragments c1 (atC c2) \<union> fragments c2 ls"
| "fragments (c1 \<squnion> c2) ls = fragments c1 ls \<union> fragments c2 ls"
| "fragments c ls = { (c, lconst ls) }"

fun
  fragmentsL :: "('answer, 'location, 'question, 'state) com list
               \<Rightarrow> ( ('answer, 'location, 'question, 'state) com
                 \<times> ('answer, 'location, 'question, 'state) loc_comp ) set"
where
  "fragmentsL [] = {}"
| "fragmentsL [c] = fragments c \<langle>False\<rangle>"
| "fragmentsL (c # c' # cs) = fragments c (atC c') \<union> fragmentsL (c' # cs)"

abbreviation
  fragmentsLS :: "('answer, 'location, 'question, 'state) local_state
               \<Rightarrow> ( ('answer, 'location, 'question, 'state) com
                 \<times> ('answer, 'location, 'question, 'state) loc_comp ) set"
where
  "fragmentsLS s \<equiv> fragmentsL (cPGM s)"
(*<*)

lemma fragmentsL_mono_Cons[iff]:
  "fragmentsL cs \<subseteq> fragmentsL (c # cs)"
by (induct cs) auto

lemma small_step_fragmentsLS:
  assumes "s \<rightarrow>\<^bsub>\<alpha>\<^esub> s'"
  shows "fragmentsLS s' \<subseteq> fragmentsLS s"
using assms by (induct rule: small_step.induct) (case_tac [!] cs, auto)

lemmas small_step_fragmentsLS_mem = subsetD[OF small_step_fragmentsLS]

(*>*)
text\<open>

Eliding the bodies of \<open>IF\<close> and \<open>WHILE\<close> statements
yields smaller (but equivalent) proof obligations.

We show that taking system steps preserves fragments.

\<close>

lemma reachable_states_fragmentsLS:
  assumes "(s, h) \<in> reachable_states sys"
  shows "fragmentsLS (s p) \<subseteq> fragments (fst sys p) \<langle>False\<rangle>"
(*<*)
using assms
by (induct rule: reachable_states_system_step_induct)
   (auto simp: initial_states_def dest: small_step_fragmentsLS_mem)
(*>*)

text\<open>

Decomposing a compound command preserves fragments too.

\<close>

fun
  extract_inner_locations :: "('answer, 'location, 'question, 'state) com
                            \<Rightarrow> ('answer, 'location, 'question, 'state) com list
                            \<Rightarrow> ('answer, 'location, 'question, 'state) loc_comp"
where
  "extract_inner_locations (\<lbrace>l\<rbrace> IF b THEN c FI) cs = lcond (atC c) (atL cs)"
| "extract_inner_locations (\<lbrace>l\<rbrace> IF b THEN c1 ELSE c2 FI) cs = lcond (atC c1) (atC c2)"
| "extract_inner_locations (LOOP DO c OD) cs = lconst (atC c)"
| "extract_inner_locations (\<lbrace>l\<rbrace> WHILE b DO c OD) cs = lcond (atC c) (atL cs)"
| "extract_inner_locations c cs = lconst (atL cs)"

(*<*)

lemma decompose_fragments:
  assumes "(c, ictxt, fctxt) \<in> decompose_com c0"
  shows "(c, extract_inner_locations c (fctxt c @ cs)) \<in> fragments c0 (atL cs)"
using assms
proof(induct c0 arbitrary: c ictxt fctxt cs)
  case (Loop c01 c ictxt fctxt cs)
  from Loop.prems Loop.hyps(1)[where cs="ictxt c # cs"] show ?case by (auto simp: decompose_ictxt[symmetric])
next
  case (Seq c01 c02 c ictxt fctxt cs)
  from Seq.prems Seq.hyps(1)[where cs="c02 # cs"] show ?case by auto
qed auto

lemma decomposeLS_fragmentsLS:
  assumes "(c, ictxt, fctxt) \<in> decomposeLS s"
  shows "(c, extract_inner_locations c (fctxt c @ tl (cPGM s))) \<in> fragmentsLS s"
using assms
proof(cases "cPGM s")
  case (Cons d ds)
  with assms decompose_fragments[where cs="ds"]
  show ?thesis by (cases ds) (auto simp: decomposeLS_def)
qed (simp add: decomposeLS_def)
(*>*)

lemma small_step_extract_inner_locations:
  assumes "basic_com c"
  assumes "(c # cs, ls) \<rightarrow>\<^bsub>\<alpha>\<^esub> ls'"
  shows "extract_inner_locations c cs c ls = atLS ls'"
using assms by (fastforce split: lcond_splits)

text\<open>

The headline result allows us to constrain the initial and final states
of a given small step in terms of the original programs, provided the
initial state is reachable.

\<close>

theorem decompose_small_step:
  assumes "s p \<rightarrow>\<^bsub>\<alpha>\<^esub> ps'"
  assumes "(s, h) \<in> reachable_states sys"
  obtains c cs ls'
    where "(c, ls') \<in> fragments (fst sys p) \<langle>False\<rangle>"
      and "basic_com c"
      and "\<forall>l. atC c l \<longrightarrow> atLS (s p) l"
      and "ls' c (cLST (s p)) = atLS ps'"
      and "(c # cs, cLST (s p)) \<rightarrow>\<^bsub>\<alpha>\<^esub> ps'"
(*<*)
using assms
apply -
apply (frule iffD1[OF context_decompose])
apply clarsimp
apply (frule decomposeLS_fragmentsLS)
apply (frule at_decomposeLS)
apply (frule (1) subsetD[OF reachable_states_fragmentsLS, rotated])
apply (frule (1) small_step_extract_inner_locations[rotated])
apply auto
done

(*>*)
text\<open>

Reasoning with @{thm [source] "reachable_states_system_step_induct"}
and @{thm [source] "decompose_small_step"} is quite tedious. We
provide a very simple VCG that generates friendlier local proof
obligations.

\<close>
(*<*)

end
(*>*)
