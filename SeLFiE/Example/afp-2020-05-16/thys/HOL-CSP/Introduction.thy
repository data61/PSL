(*<*)
\<comment>\<open> ********************************************************************
 * Project         : HOL-CSP - A Shallow Embedding of CSP in  Isabelle/HOL
 * Version         : 2.0
 *
 * Author          : Burkhart Wolff, Safouan Taha, Lina Ye.
 *                   (Based on HOL-CSP 1.0 by Haykal Tej and Burkhart Wolff)
 *
 * This file       : A Combined CSP Theory
 *
 * Copyright (c) 2009 Université Paris-Sud, France
 *
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are
 * met:
 *
 *     * Redistributions of source code must retain the above copyright
 *       notice, this list of conditions and the following disclaimer.
 *
 *     * Redistributions in binary form must reproduce the above
 *       copyright notice, this list of conditions and the following
 *       disclaimer in the documentation and/or other materials provided
 *       with the distribution.
 *
 *     * Neither the name of the copyright holders nor the names of its
 *       contributors may be used to endorse or promote products derived
 *       from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 * "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 * LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
 * A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
 * OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
 * SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 * DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 * THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 ******************************************************************************\<close>
(*>*)

chapter\<open>Context\<close>
(*<*)
theory Introduction
  imports HOLCF
begin
(*>*)

section\<open>Preface\<close>
text\<open>
   This is a formalization in Isabelle/HOL of the work of Hoare and Roscoe
   on the denotational semantics of the Failure/Divergence Model of CSP. 
   It follows essentially the presentation of CSP in Roscoe's
   Book "Theory and Practice of Concurrency" @{cite "roscoe:csp:1998" }
   and the semantic details in a joint Paper of Roscoe and Brooks
   "An improved failures model for communicating processes"
   @{cite "brookes-roscoe85"}.

   The original version of this formalization, called HOL-CSP 1.0 
   @{cite "tej.ea:corrected:1997"}, revealed minor, but omnipresent foundational errors
   in key concepts like the process invariant. A correction was
   proposed slightly before the apparition of Roscoe's book (all three authors  were
   in e-mail contact at that time).
\<close>

text\<open>
  In recent years, a team of authors undertook the task to port HOL-CSP 1.0
  to modern Isabelle/HOL and structured proof techniques. This results in the
  present version are called HOL-CSP 2.0.
 
  The effort is motivated by the following assets of CSP:
  \<^item> the theory is interesting in itself, and reworking its formal
    structure might help to make it more widely accessible, given
    that it is a particularly advanced example of the shallow embedding
    technique using the denotational semantics of a language,
  \<^item> it is interesting to \<^emph>\<open>compare\<close> the ancient, imperative, ML-heavy 
    proof style to the more recent declarative one in Isabelle/Isar;
    this comparison (not presented here) gives a source of empirical
    evidence that such proofs are more stable wrt. the constant
    changes in the Isabelle itself,
  \<^item> the \<^emph>\<open>semantic\<close> presentation of CSP lends itself to a semantically
    clean and well-understood \<^emph>\<open>combination\<close> of specification languages,
    which represents a major step to our longterm goal of heterogenuous,
    yet semantically clean system specifications consisting of
    different formalisms describing components or system aspects separately,
  \<^item> the resulting HOL-CSP environment could one day be used as a tool that 
    certifies traces of other CSP model-checkers such as FDR4 or PAT.
\<close>

text\<open> 
  In contrast to HOL-CSP 1.0, which came with
  an own fixpoint theory partly inspired by previous work of Alberto Camilieri under 
  HOL4 @{cite"Camilleri91"}, it is the goal of the redesign of HOL-CSP 2.0  to reuse 
  the HOLCF theory  that emmerged from Franz Regensburgers work and was substantially 
  extended by Brian Huffman. Thus, the footprint of the HOL-CSP 2.0
  theory should be reduced drastically. Moreover, all proofs
  have been heavily revised or re-constructed to reflect the
  drastically improved state of the art of interactive
  theory development with Isabelle. \<close>

section\<open>Introduction\<close>
text\<open>DRAWN FROM THE PAPER @{cite "tej.ea:corrected:1997"}\<close>
text\<open>
  In his invited lecture at FME'96, C.A.R. Hoare presented his view on the status 
  quo of formal methods in industry. With respect to formal proof methods, he ruled 
  that they "are now sufficiently advanced that a [...] formal methodologist could 
  occasionally detect [...] obscure latent errors before they occur in practice" 
  and asked for their publication as a possible "milestone in the acceptance of formal 
  methods" in industry.
  
  In this paper, we report of a larger verification effort as part of the  UniForM project 
  @{cite "KriegBrueckner95"}. It revealed an obscure latent error that was not detected 
  within a decade. It cannot be said that the object of interest is a "large software 
  system" whose failure may "cost millions", but it is a well-known subject in the center 
  of academic interest considered foundational for several formal methods tools: the 
  theory of the failure- divergence model of CSP (@{cite "Hoare:1985:CSP:3921"}, 
  @{cite "brookes-roscoe85"}). And indeed we hope that this work may further encourage the use 
  of formal proof methods at least in the academic community working on formal methods.
  
  Implementations of proof support for a formal method can roughly be divided into two 
  categories. In direct tools like FDR @{cite "FDRTutorial2000"}, the logical rules of a 
  method (possibly integrated into complex proof techniques) are hard-wired into the code of 
  their implementation. Such tools tend to be difficult to modify and to formally reason 
  about, but can possess enviable automatic proof power in specific problem domains 
  and comfortable user interfaces. 

  The other category can be labelled as logical embeddings. Formal methods such as CSP 
  or Z can be logically embedded into an LCF-style tactical theorem prover such as HOL 
  @{cite "gordon.ea:hol:1993"} or Isabelle@{cite "nipkow.ea:isabelle:2002"}. Coming with 
  an open system design going back to Milner, these provers allow for user-programmed 
  extensions in a logically sound way. Their  strength is flexibility, generality and 
  expressiveness that makes them to symbolic programming environments.
  
  In this paper we present a tool of the latter category (as a step towards a future 
  combination with the former). After a brief introduction into the failure divergence 
  semantics in the traditional CSP-literature, we will discuss the revealed problems 
  and present a correction. Although the error is not "mathematically deep", it stings 
  since its correction affects many definitions. It is shown that the corrected CSP 
  still fulfils the desired algebraic laws. The addition of fixpoint-theory and 
  specialised tactics extends the embedding in Isabelle/HOL to a formally proven 
  consistent proof environment for CSP. Its use is demonstrated in a final example.
\<close>

section\<open>An Outline of Failure-Divergence Semantics\<close>

text\<open> 
  A very first approach to give denotational semantics to CSP is to view it as a kind 
  of a regular expression. This way, it can be understood as an automata and the 
  denotations are just the language of the automaton; this way, synchronization 
  and concurrency can be basically understood as the construction of a product automaton 
  with potential interleaving. The semantics becomes compositional, and internal communication
  between sub-components of a component can be modeled by the concealment operator. 

  Hoares work @{cite "Hoare:1985:CSP:3921"} was strongly inspired by this initial idea.
  However, it became quickly clear that the simplistic automata vision is not a satisfying
  paradigm for all aspects of concurrency. Particularly regarding the nature of communication,
  where one "sends" actively information and the other "receives" it, the bi-directional 
  product construction seems to be misleading. Furthermore, it is an obvious difference
  if a group of processes remains in a passive deadlock because all possible communications 
  contradict each other, or if a group of processes is too busy with internal chatter and
  never reaches the point where this component is again ready for communication. 
  
  Hoare solved these apparent problems by presenting a multi-layer approach, in which the
  denotational models were refined more and more allowing to distinguish the above 
  critical situations. An ingenious concept in the overall scheme is to distinguish
  \<^emph>\<open>non-deterministic\<close> choice from \<^emph>\<open>deterministic\<close> one \<^footnote>\<open>which in itself produces
  problems with recursion which had to be overcome by some restrictions on its use.\<close> in order to 
  solve the sender/receiver problem. 

  Hoare proposed 3 denotational semantics for CSP:
  \<^item> the \<^emph>\<open>trace\<close> model, which is basically the above naive automata model not allowing
    to distinguish non-deterministic choice from deterministic one, neither to distinguish deadlock 
    from infinite internal chatter,
  \<^item> the \<^emph>\<open>failure\<close> model is able to distinguish non-deterministic choice from deterministic one by 
    different maximum refusal sets, which is however cannot differentiate deadlock from infinite 
    internal chatter,   
  \<^item> the \<^emph>\<open>failure-divergence\<close> model overcomes additionally the unresolved problem of failure model.


In the sequel, we explain these two problems in more detail, giving some
motivation for the daunting complexity of the latter model.
It is this complexity which finally raises general interest in a 
formal verification.
\<close>

subsection\<open>Non-Determinism\<close>
(*<*)
consts dummyPrefix :: "'a::cpo \<Rightarrow> 'b::cpo \<Rightarrow> 'b::cpo"
consts dummyDet :: "'a::cpo \<Rightarrow> 'b::cpo \<Rightarrow> 'b::cpo"
consts dummyNDet :: "'a::cpo \<Rightarrow> 'b::cpo \<Rightarrow> 'b::cpo"
consts dummyHide :: "'b::cpo \<Rightarrow> 'a \<Rightarrow> 'b::cpo"

notation dummyPrefix (infixr  "\<rightarrow>" 50)
notation dummyDet    (infixr  "\<box>" 50)
notation dummyNDet   (infixr  "\<sqinter>" 50)
notation dummyHide   (infixr  "\<setminus>" 50)
(*>*)

text\<open>
   Let a and b be any two events in some set of events @{term "\<Sigma>"}. The two processes

   \<^descr>    @{term   "(a \<rightarrow> Stop) \<box> (b \<rightarrow> Stop)"}   \hspace{7cm}            (1)

   and

   \<^descr>    @{term   "(a \<rightarrow> Stop) \<sqinter> (b \<rightarrow> Stop)"}  \hspace{7cm}            (2)


\<close>
text\<open>
   cannot be distinguished under the trace semantics, in which both processes 
   are capable of performing the same sequences of events, i.e. both have the 
   same set of traces @{term "{{},{a},{b}}"}. This is because both processes can either 
   engage in @{term "a"} and then @{term "Stop"}, or engage in @{term "b"} and 
   then @{term "Stop"}. We would, however, like to distinguish between @{term "a"} 
   \<^emph>\<open>deterministic\<close> choice of @{term "a"} or @{term "b"} (1) and @{term "a"} 
   \<^emph>\<open>non-deterministic\<close> choice of @{term "a"} or @{term "b"} (2).
   
   
   This can be done by considering the events that a process can refuse to engage 
   in when these events are offered by the environment; it cannot refuse either, 
   so we say its maximal refusal set is the set containing all elements of @{term "\<Sigma>"} other 
   than @{term "a"} and @{term "b"}, written @{term "\<Sigma>-{a,b}"}, i.e. it can 
   refuse all elements in @{term "\<Sigma>"} other than @{term "a"} or @{term "b"}. In the case 
   of the non-deterministic process (2), however, we wish to express that if the environment 
   offers the event @{term "a"} say, the process non-deterministically chooses either to engage in 
   @{term "a"}, to refuse it and engage in @{term "b"} (likewise for @{term "b"}). We say 
   therefore, that process (2) has two maximal refusal sets, @{term "\<Sigma>-{a}"} and 
   @{term "\<Sigma>-{b}"}, because it can refuse to engage in either @{term "a"} or 
   @{term "b"}, but not both. The notion of refusal sets is in this way used to distinguish 
   non-determinism from determinism in choices.
\<close>

subsection\<open>Infinite Chatter\<close>

text\<open>
   Consider the infinite process @{term "\<mu> X. a \<rightarrow> X"}
   which performs an infinite stream of @{term "a"}'s. If one now conceals the event a in 
   this process by writing
   \<^descr>      @{term "(\<mu> X. a \<rightarrow> X) \<setminus> a"}    \hspace{7.8cm}            (3)
\<close>   
text\<open>
   it no longer becomes possible to distinguish the behaviour of this process 
   from that of the deadlock process Stop. We would like to be able to make such 
   a distinction, since the former process has clearly not stopped but is engaging 
   in an unbounded sequence of internal actions invisible to the environment. We say 
   the process has diverged, and introduce the notion of a divergence set to denote 
   all sequences events that can cause a process to diverge. Hence, the process Stop 
   is assigned the divergence set @{term "{}"}, since it can not diverge, whereas the process 
   (3) above diverges on any sequence of events since the process begins to diverge 
   immediately, i.e. its divergence set is @{term "\<Sigma>\<^sup>*"} , where @{term "\<Sigma>\<^sup>*"} denotes the 
   set of all  sequences with elements in @{term "\<Sigma>"}. Divergence is undesirable and so 
   it is essential to be able to express it to ensure that it is avoided.
\<close>

subsection\<open>The Global Architecture of HOL-CSP 2.0\<close>
text\<open>
   The global architecture of HOL-CSP 2.0 has been substantially simplified compared 
   to HOL-CSP 1.0: the fixpoint reasoning is now entirely based on HOLCF (which meant that
   the continuity proofs for CSP operators had basically been re-done).\<close>

text\<open>
   The theory \<^verbatim>\<open>Process\<close> establishes the basic common notions for events, traces, ticks and
   tickfree-ness, the type definitions for failures and divergences as well as the
   global constraints on them (called the "axioms" in Hoare's Book.) captured in a 
   predicate \<^verbatim>\<open>is_process\<close>. On this basis, the set of failures and divergences satisfying
   \<^verbatim>\<open>is_process\<close> is turned into the type \<^verbatim>\<open>'a process\<close> via a type-definition 
   (making \<^verbatim>\<open>is_process\<close> as the central data invariant). In the sequel, it is shown that
   \<^verbatim>\<open>'a process\<close> belongs to the type-class @{class "cpo"} stemming from @{theory HOLCF} which 
   makes  the concepts of complete partial order, continuity, fixpoint-induction and general 
   recursion available to all expressions of type \<^verbatim>\<open>'a process\<close>. \<close>

text\<open> 
   The theory \<^verbatim>\<open>Process\<close> also establishes the two partial orderings @{term "P \<le> P'"} for 
   refinements and @{term "P \<sqsubseteq> P'"} for the approximation on processes used to give semantics
   to recursion. The latter is well-known to be logically weaker than the former.
   Note that, unfortunately, the use of these two symbols in HOL-CSP 2.0, where the 
   latter is already used in the @{theory HOLCF}-theory, is just the other way round as 
   in the literature. \<close>

text\<open>
   Each CSP operator is described in an own theory which comprises:
   \<^item> The denotational core definition in terms of a pair of Failures and Divergences
   \<^item> The establishment of  \<^verbatim>\<open>is_process\<close> for the  Failures and Divergences in the
     range of the given operator (thus, the invariance of  \<^verbatim>\<open>is_process\<close> for this operator)
   \<^item> The proof of the projections \<^verbatim>\<open>T\<close> and  \<^verbatim>\<open>F\<close> and \<^verbatim>\<open>D\<close> for this operator
   \<^item> The proof of continuity of the operator (which is always possible except for
     hide if applied to infinite hide-sets).\<close>

text\<open>
   Finally, the theory CSP contains the "Laws" of CSP, i.e. the derived rules 
   allowing abstractly to reason over CSP processes. The overall dependency graph 
   is shown in \autoref{fig:fig1}.\<close>

text\<open>
   \begin{figure}[ht]
   	\centering
     \includegraphics[width=0.9\textwidth]{session_graph}
   	\caption{The HOL-CSP 2.0 Theory Graph}
   	\label{fig:fig1}
   \end{figure}\<close>

(*<*)
no_notation dummyPrefix  (infixr  "\<rightarrow>" 50)
no_notation dummyDet     (infixr  "\<box>" 50)
no_notation dummyNDet    (infixr  "\<sqinter>" 50)
no_notation dummyHide    (infixr  "\<setminus>" 50)

end
(*>*)
