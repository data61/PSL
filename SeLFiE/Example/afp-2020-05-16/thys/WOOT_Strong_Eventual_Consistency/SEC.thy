section \<open>Strong Eventual Consistency \label{sec:strong_eventual_consistency}\<close>

theory SEC
  imports StrongConvergence
begin

text \<open>In the following theorem we establish that all reached states are successful. This
implies with the unconditional termination property (Section \ref{sec:integrate_term}) of it that 
the integration algorithm never fails.\<close>

theorem (in dist_execution) no_failure:
  fixes i
  assumes "is_valid_state_id i"
  shows "isOK (state i)"
  apply (cases "state i")
  by (metis assms state_is_associated_string is_certified_associated_string.simps(2), simp)

text \<open>The following theorem establishes that any pair of peers having received the same
set of updates, will be in the same state.\<close>

theorem (in dist_execution) strong_convergence:
  assumes "is_valid_state_id i"
  assumes "is_valid_state_id j"
  assumes "set (received_messages i) = set (received_messages j)"
  shows "state i = state j"
  using state_is_associated_string is_certified_associated_string_unique by (metis assms)

text \<open>As we noted in Section~\ref{sec:networkModel}, we have not assumed eventual delivery, but
  a corollary of this theorem with the eventual delivery assumption implies eventual consistency.
  Since finally all peer would have received all messages, i.e., an equal set.\<close>

section \<open>Code generation\<close>

export_code integrate create_insert create_delete in Haskell
  module_name WOOT file_prefix "code"

section \<open>Proof Outline\label{sec:proof_outline}\<close>

text \<open>
  In this section we outline and motivate the approach we took to prove the strong eventual
  consistency of WOOT.

  While introducing operation-based CRDTs Shapiro et al. also establish
  \cite{shapiro2011conflict}[Theorem 2.2]. If the following two conditions are met:
  \begin{itemize}
    \item
      Concurrent operations commute, i.e., if a pair of operations @{text "m\<^sub>1"},
      @{text "m\<^sub>2"} is concurrent with respect to the order induced by the happened-before
      relation, and they are both applicable to a state @{text "s"}, then the message
      @{text "m\<^sub>1"} (resp. @{text "m\<^sub>2"}) is still applicable on the state reached by
      applying  @{text "m\<^sub>2"} (resp. @{text "m\<^sub>1"}) on @{text "s"} and the resulting
      states are equal.
    \item Assuming causal delivery, the messages are applicable.
  \end{itemize}
  Then the CRDT has strong convergence.
  The same authors extend the above result in \cite[Proposition 2.2]{shapiro:inria-00555588}
  to more general delivery orders $\xrightarrow{d}$ (weaker than the one induced by the
  happened-before relation), i.e., two messages may be causally dependent but concurrent with
  respect to $\xrightarrow{d}$. Assuming operations that are concurrent with respect to
  $\xrightarrow{d}$ commute, and messages are applicable, when the
  delivery order respects $\xrightarrow{d}$ then again the CRDT has strong convergence.

  A key difficulty of the consistency proof of the WOOT framework is that the applicability
  condition for the WOOT framework has three constraints:
  \begin{enumerate}
    \item \label{en:proof:deps_are_met} Dependencies must be met.
    \item \label{en:proof:id_distinct} Identifiers must be distinct.
    \item The order must be consistent, i.e. the predecessor W-character must appear before the
      successor W-character in the state an insert message is being integrated.
  \end{enumerate}

  The first constraint is a direct consequence of the semantic causal delivery order. The uniqueness
  of identifiers can be directly established by analyzing the implementation of the message creation
  algorithms. Alternatively, Gomes et al.~\cite{gomes2017verifying} use an axiomatic approach, where
  they require the underlying network protocol to deliver messages with unique identifiers. They
  provide a formal framework in Isabelle/HOL that can be used to show consistency of arbitrary
  CRDTs. Their results could be used to establish constraints \ref{en:proof:deps_are_met} and
  \ref{en:proof:id_distinct}.

  The last constraint is the most intricate one, and forces us to use a different method to
  establish the strong eventual consistency. The fact that the order constraint is fulfilled is a
  consequence of the consistency property. But the current fundamental lemmas require applicability
  of the operations in the first place to establish consistency, which would result in a circular
  argument.

  Zeller et. al. actually predict the above circumstance in the context of state-based CRDTs
  \cite{DBLP:conf/forte/ZellerBP14}:
  \begin{displayquote}
  In theory it could even be the case that there are two reachable states for which the merge
  operation does not yield the correct result, but where the two states can never be reached in the
  same execution.
  \end{displayquote}

  Because of the above, we treat WOOT as a distributed message passing algorithm and show
  convergence by establishing a global invariant, which is maintained during the execution of the
  framework. The invariant captures that the W-characters appear in the same order on all peers.
  It has strong convergence as a consequence, in the special case, when peers have received
  the same set of updates. It also implies that the generated messages will be applicable.

  \begin{figure}
    \centering
    \begin{tikzpicture}[
      statenode/.style={circle, draw=black, fill=black!20, thick, minimum size=5mm},
      curstatenode/.style={circle, draw=black, fill=black!60, thick, minimum size=5mm},
      peernode/.style={rectangle, draw=black, thick, minimum size=5mm},
    ]
    %Nodes
    \node[peernode] (peerA) at (1.5cm, 3cm) {Peer A};
    \node[peernode] (peerB) at (1.5cm, 2cm) {Peer B};
    \node[peernode] (peerC) at (1.5cm, 1cm) {Peer C};
    \node[statenode] (stateA2) at (4cm, 3cm) {};
    \node[curstatenode] (stateB2) at (5cm, 2cm) {};
    \node[statenode] (stateC2) at (3.5cm, 1cm) {};
    \node[statenode] (stateA3) at (5.5cm, 3cm) {};
    \node[statenode] (stateB3) at (7cm, 2cm) {};
    \node[statenode] (stateC3) at (6.5cm, 1cm) {};
    \node[statenode] (stateA4) at (7.5cm, 3cm) {};
    \draw[->] (peerA.east) -- (stateA2.west);
    \draw[->] (peerB.east) -- (stateB2.west);
    \draw[->] (peerC.east) -- (stateC2.west);
    \draw[->] (stateA2.east) -- (stateA3.west);
    \draw[->] (stateB2.east) -- (stateB3.west);
    \draw[->] (stateC2.east) -- (stateC3.west);
    \draw[->] (stateC2) -- (stateA2);
    \draw[->] (stateC2) -- (stateB2);
    \draw[->] (stateA3) -- (stateC3);
    \draw[->] (stateA3) -- (stateB3);
    \draw[->] (stateA3) -- (stateA4);
    \draw (5cm,3.5cm) to[bend right] (4.8cm,0.5cm);
    \end{tikzpicture}
    \caption{Example state graph, where the consistency is established left of the bend curve.}
    \label{fig:state_graph}
  \end{figure}

  In Figure~\ref{fig:state_graph}, we exemplify an induction step in a proof over the execution
  of the framework. The invariant is established for all states left of the dashed lines, and we
  show that it remains true if we include the state, drawn in dark gray. Note that induction
  proceeds in an order consistent with the happened-before relation.

  The technique we are using is to define a relation @{term is_associated_string} from a set of
  messages to the final state their application leads to. Crucially, that relation can be defined
  in a message-order independent way. We show that it correctly models the behaviour of Algorithm
  @{term "integrate"} by establishing that applying the integration algorithm to the associated
  string of a set @{term "M"} leads to the associated string of the set @{term "M \<union> {m}"}
  in Proposition @{thm [source] integrate_insert_commute}.

  We also show that at most one @{text s} fulfills @{term "is_associated_string M s"},
  which automatically implies commutativity (cf. Lemma @{thm [source] "associated_string_unique"}).

  Note that the domain of the relation @{term "is_associated_string"} consists of the sets of
  messages that we call @{term "consistent"}. We show that, in every state of a peer, the set of
  received messages will be consistent.
  The main ingredient required for the definition of a consistent set of messages as the relation
  @{term "is_associated_string"} are \emph{sort keys} associated to the W-characters, which we will
  explain in the following Section.
\<close>

subsection \<open> Sort Keys \<close>

text \<open>
  There is an implicit sort key, which is deterministically computable, using the immutable data
  associated to a W-character and the data of the W-characters it (transitively) depends on.

  We show that Algorithm @{term "integrate"} effectively maintains the W-characters ordered with
  respect to that sort key, which is the reason we can construct the mapping
  @{term "is_associated_string"} in a message-order
  independent way. An alternative viewpoint would be to see Algorithm @{term "integrate_insert"} as
  an optimized version of a more mundane algorithm, that just inserts the W-characters using this
  implicit sort key.

  Since the sort key is deterministically computable using the immutable data associated to a
  W-character and the data of the W-characters it (transitively) depends on, all peers could
  perform this computation independently, which leads to the conclusion that the W-characters
  will be ordered consistently across all peers.

  The construction relies on a combinator @{term "\<Psi>"} that computes the sort key for a
  W-character, and which requires as input:
  \begin{itemize}
    \item The unique identifier associated to a W-character.
    \item The sort keys of the predecessor/successor W-characters.
  \end{itemize}
  Its values are elements of a totally ordered space.

  Note that the predecessor (resp. successor) W-character of a W-character is the W-character that
  was immediately before (resp. after) it at the time it was inserted. Like its unique identifier,
  it is immutable data associated with that W-character. Sometimes a W-character is inserted at the
  beginning (resp. end) of the string. For those W-characters, we use the special smallest
  (resp. largest) sort keys, denoted by @{term "\<turnstile>"} (resp. @{term "\<stileturn>"}) as predecessor
  (resp. successor). These keys themselves are never associated to a W-character.

  We will write @{term "\<Psi> (l,u) i"} for the value computed by the combinator for a W-character
  with identifier @{term "i"}, assuming the sort key of its predecessor (resp. successor) is
  @{term "l"} (resp. @{term "u"}).

  For example, the sort key for a W-character with identifier @{term "i"} inserted in an empty
  string (hence its predecessor is @{term "\<turnstile>"} and its successor is @{term "\<stileturn>"}) 
  will be  @{term "\<Psi> (\<turnstile>,\<stileturn>) i"}. A W-character
  inserted between that character and the end of the string, with identifier j, would be assigned
  the sort key @{term "\<Psi> (\<lbrakk>\<Psi> (\<turnstile>,\<stileturn>) i\<rbrakk>,\<stileturn>) j"}.

  The sort key needs to fulfill a couple of properties, to be useful:

  There should never be a pair of W-characters with the same sort key. Note, if this happens, even
  if those W-characters were equal or ordered consistently, we would not be able to insert a new
  W-character between those W-characters.

  Since the W-characters have themselves unique identifiers, a method to insure the above property
  is to require that @{term "\<Psi>"} be injective with respect to the identifier of the W-character
  it computes a sort key for, i.e.,
  @{term "\<Psi> (l,u) i = \<Psi> (l',u') i' \<Longrightarrow> i = i'"}.

  Another essential property is that the W-characters with predecessor having the sort key
  @{term "l"} and successor having the sort key @{term "u"}  should have a sort key that is between
  @{term "l"} and @{term "u"}, such that the W-character is inserted between the preceding and
  succeeding W-character, i.e., @{text "l < \<Psi> (l,u) i < u"}.

  This latter property ensures intention preservation, i.e. the inserted W-character will be placed
  at the place the user intended.

  If we review function @{term "concurrent"}, then we see that the algorithm compares W-characters
  by identifier, in the special case, when the inserted W-character is compared to a W-character
  whose predecessor and successor are outside of the range it is to be inserted in. A careful
  investigation, leads to the conclusion that:

  If @{text "l \<le> l' < \<Psi> (l,u) i < u' \<le> u"} then @{text "\<Psi>(l,u) i"} can be compared
  with @{text "\<Psi>(l',u') i'"} by comparing @{text "i"} with @{text "i'"}, i.e.:
  \begin{itemize}
    \item @{text "i < i' \<Longrightarrow> \<Psi> (l,u) i < \<Psi>(l',u') i'"}
  \end{itemize}

  In Section \ref{sec:psi} we show that a combinator @{term "\<Psi>"} with the above properties can
  be constructed (cf. Propositions @{thm [source] psi_narrow psi_mono psi_elem}).
  Using the sort keys we can define the notion of a consistent set of messages as well as the
  relation @{term "is_associated_string"} in a message-order independent way.\<close>

subsection \<open> Induction \<close>

text \<open>
  We have a couple of criteria that define a consistent set of messages:

  \begin{itemize}
    \item Each insert message in the set has a unique identifier.
    \item If a message depends on another message identifier, a message with that identifier will
      be present. Note that for insert messages, these are the predecessor/successor W-characters
      if present. For delete messages it is the corresponding insert message.
    \item The dependencies form a well-order, i.e., there is no dependency cycle.
    \item It is possible to assign sort keys to each insert message, such that
      the assigned sort key for each insert message is equal to the value returned by the
      @{term "\<Psi>"} for it, using the associated sort keys of its predecessor and successors,
      i.e.,
      @{term "a (P m) < a (S m) \<and>
              a \<lbrakk>I m\<rbrakk> = \<lbrakk>\<Psi> (a (P m), a (S m)) (I m)\<rbrakk>"}.
      Note that we also require that sort key of the predecessor is smaller than the sort key of the
      successor.
  \end{itemize}

  The relation @{term "is_associated_string"} is then defined by ordering the insert messages
  according to the assigned sort keys above and marking W-characters, for which there are delete
  messages as deleted.

  The induction proof (Lemma @{thm [source] dist_execution.sent_messages_consistent}) over the
  states of the framework is straight forward: Using Lemma @{thm [source] top_sort} we find a
  possible order of the states consistent with the happened before relation. The induction invariant
  is that the set of generated messages by all peers is
  consistent (independent of whether they have been received by all peers (yet)). The latter also
  implies that the subset a peer has received in any of those states is consistent, using the
  additional fact that each messages dependencies will be delivered before the message itself
  (see also Lemma @{thm [source] consistent_subset} and
  Proposition @{thm [source] integrate_insert_commute'}).
  For the induction step, we rely on the results from Section \ref{sec:create_consistent} that any
  additional created messages will keep the set of messages consistent and that the peers' states
  will be consistent with the (consistent subset of) messages they received (Lemma @{thm [source]
  dist_execution.state_is_associated_string'}).\<close>
end

