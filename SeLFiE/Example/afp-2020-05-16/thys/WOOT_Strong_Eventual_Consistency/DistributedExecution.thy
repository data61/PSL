subsection \<open>Network Model \label{sec:networkModel}\<close>

text \<open>In the past subsections, we described the algorithms each peer uses to integrate received
  messages and broadcast new messages when an edit operation has been made on that peer.

  In this section, we model the WOOT Framework as a distributed application and set the
  basis for the consistency properties, we want to establish.

  We assume a finite set of peers starting with the same initial state of an empty W-string, each
  peer reaches a finite set of subsequent states, caused by the integration of received (or locally
  generated messages). A message is always generated from a concrete state of a peer, using the
  algorithms described in Section \ref{sec:edit}. Moreover, we assume that the same message will only
  be delivered once to a peer. Finally, we assume that the happened before relation, formed by
  \begin{itemize}
  \item Subsequent states of the same peer
  \item States following the reception and states that were the generation sites
  \end{itemize}
  do not contain loops. (Equivalently that the transitive closure of the relation is a strict
  partial order.)

  The latter is a standard assumption in the modelling of distributed systems (compare e.g.
  \cite[Chapter 6.1]{raynal2013}) effectively implied by the fact that there are no physical causal
  loops.

  Additionally, we assume that a message will be only received by a peer, when the antecedent
  messages have already been received by the peer. This is a somewhat technical assumption to
  simplify the description of the system. In a practical implementation a peer would buffer the set
  of messages that cannot yet be integrated. Note that this assumption is automatically implied if
  causal delivery is assumed.

  We establish two properties under the above assumptions
  \begin{itemize}
  \item The integration algorithm never fails.
  \item Two peers having received the same set of messages will be in the same state.
  \end{itemize}

  The model assumptions are derived from Gomes et al.\cite{gomes2017verifying} and
  Shapiro et al.\cite{shapiro:inria-00555588} with minor modifications required for WOOT.\<close>

theory DistributedExecution
  imports IntegrateAlgorithm CreateAlgorithms "HOL-Library.Product_Lexorder"
begin

type_synonym 'p event_id = "'p \<times> nat"

datatype ('p,'s) event =
  Send "('p event_id, 's) message" |
  Receive "'p event_id" "('p event_id, 's) message"

text \<open>The type variable @{typ "'p"} denotes a unique identifier identifying a peer.
  We model each peer's history as a finite sequence of events, where each event is either
  the reception or broadcast of a message.
  The index of the event in a peer's history and its identifier form a pair uniquely identifying
  an event in a distributed execution of the framework.
  In the case of a reception, @{term "Receive s m"} indicated the reception of the message @{term m}
  sent at event @{term "s"}.

  In the following we introduce the locale @{text "dist_execution_preliminary"} from which the
  @{text "dist_execution"} locale will inherit. The reason for the introduction of two
  locales is technical - in particular, it is not possible to interleave definitions and assumptions
  within the definition of a locale. The preliminary locale only introduces the assumption that the
  set of participating peers is finite.\<close>

locale dist_execution_preliminary =
  fixes events :: "('p :: linorder) \<Rightarrow> ('p,'s) event list"
  \<comment> \<open>We introduce a locale fixing the sequence of events per peer.\<close>

  assumes fin_peers: "finite (UNIV :: 'p set)"
  \<comment> \<open>We are assuming a finite set of peers.\<close>

begin

fun is_valid_event_id
  where "is_valid_event_id (i,j) = (j < length (events i))"

fun event_pred
  where "event_pred (i,j) p  = (is_valid_event_id (i,j) \<and> p (events i ! j))"

fun event_at
  where "event_at i m = event_pred i ((=) m)"

fun is_reception
  where
    "is_reception i j = event_pred j (\<lambda>e. case e of Receive s _ \<Rightarrow> s = i | _ \<Rightarrow> False)"

fun happened_immediately_before where
  "happened_immediately_before i j = (
     is_valid_event_id i \<and>
     is_valid_event_id j \<and>
     ((fst i = fst j \<and> Suc (snd i) = snd j) \<or> is_reception i j))"

text \<open>
  The @{term happened_immediately_before} describes immediate causal precedence:
  \begin{itemize}
    \item An events causally precedes the following event on the same peer.
    \item A message broadcast event causally precedes the reception event of it.
  \end{itemize}

  The transitive closure of this relation is the famous happened before relation introduced
  by Lamport\cite{Lamport1978}.

  In the @{text "dist_execution"} we will assume that the relation is acyclic - which implies that
  the transitive closure @{term "happened_immediately_before\<^sup>+\<^sup>+"} is a strict partial
  order.
\<close>

text \<open>Each peer passes through a sequence of states, which may change after receiving a message.
  We denote the initial state of peer $p$ as $(p,0)$ and the state after
  event $(p,i)$ as $(p,i+1)$. Note that there is one more state per peer than events, since we
  are count both the initial and terminal state of a peer.\<close>

fun is_valid_state_id
  where "is_valid_state_id (i,j) = (j \<le> length (events i))"

fun received_messages
  where
    "received_messages (i,j) = [m. (Receive _ m) \<leftarrow> (take j (events i))]"

fun state where "state i = foldM integrate [] (received_messages i)"

text \<open>Everytime a peer receives a message its state is updated by integrating the message. The
  function @{term state} returns the state for a given state id.\<close>

end

text \<open> The function @{text deps} computes the identifiers a message depends on. \<close>

fun extended_to_set :: "'a extended \<Rightarrow> 'a set"
  where
    "extended_to_set \<lbrakk>i\<rbrakk> = {i}" |
    "extended_to_set _ = {}"

fun deps :: "('id, 's) message \<Rightarrow> 'id set"
  where
    "deps (Insert (InsertMessage l _ u _)) = extended_to_set l \<union> extended_to_set u" |
    "deps (Delete (DeleteMessage i)) = {i}"

locale dist_execution = dist_execution_preliminary +
  assumes no_data_corruption:
    "\<And>i s m. event_at i (Receive s m) \<Longrightarrow> event_at s (Send m)"
  \<comment> \<open>A received message must also have been actually broadcast. Note that, we do not
  assume that a broadcast message will be received by all peers, similar to the modelling made by
  \cite[Section 5.2]{gomes2017verifying}.\<close>

  assumes at_most_once:
    "\<And>i j s m.
    event_at i (Receive s m) \<Longrightarrow>
    event_at j (Receive s m) \<Longrightarrow>
    fst i = fst j \<Longrightarrow> i = j"
  \<comment> \<open>A peer will never receive the same message twice. Note that this is something
  that can be easily implemented in the application layer, if the underlying transport mechanism
  does not guarantee it.\<close>

  assumes acyclic_happened_before:
    "acyclicP happened_immediately_before"
  \<comment> \<open>The immediate causal precendence relation is acyclic, which implies that its
  closure, the \emph{happened before} relation is a strict partial order.\<close>

  assumes semantic_causal_delivery:
    "\<And>m s i j i'. event_at (i,j) (Receive s m) \<Longrightarrow> i' \<in> deps m \<Longrightarrow>
      \<exists>s' j' m'. event_at (i,j') (Receive s' (Insert m')) \<and> j' < j \<and> I m' = i'"
  \<comment> \<open>A message will only be delivered to a peer, if its
  antecedents have already been delivered. (See beginning of this Section for the reason of this
  assumption).\<close>

  assumes send_correct:
    "\<And>m i. event_at i (Send m) \<Longrightarrow>
    (\<exists>n \<sigma>. return m = state i \<bind> (\<lambda>s. create_insert s n \<sigma> i)) \<or>
    (\<exists>n. return m = state i \<bind> (\<lambda>s. create_delete s n))"
  \<comment> \<open>A peer broadcasts messages by running the @{term create_insert} or @{term create_delete}
     algorithm on its current state. In the case of an insertion the new character is assigned
     the event id as its identifier. Note that, it would be possible to assume, a different choice
     for allocating unique identifiers to new W-characters. We choose the event id since it is
     automatically unique.\<close>

begin

text \<open>Based on the assumptions above we show in Section \ref{sec:strong_eventual_consistency}:
  \begin{itemize}
    \item \emph{Progress}: All reached states @{term "state i"} will be successful, i.e., the
          algorithm @{term integrate} terminates and does not fail.
    \item \emph{Strong Eventual Consistency}: Any pair of states  @{term "state i"}
          and @{term "state j"} which have been reached after receiving the same set of messages,
          i.e., @{term "set (received_messages i) = set (received_messages j)"} will be equal.
  \end{itemize}\<close>

end

end
