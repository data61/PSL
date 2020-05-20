section \<open>The WOOT Framework \label{sec:wootFramework}\<close>

theory Data
  imports Main Datatype_Order_Generator.Order_Generator
begin

text \<open>%
  \begin{figure}[t]
    \centering
    \begin{tikzpicture}[
      peernode/.style={rectangle, draw=black, thick, scale=0.8},
      eventnode/.style={rectangle, draw=black, fill=black!20, thick,rounded corners=.1cm,
      scale=0.8},
      statenode/.style={rectangle, draw=black, thick,rounded corners=.1cm,
      scale=0.8},
    ]
    % Nodes.
    \node[peernode] (peerA) at (0, 0) {Peer A};
    \node[peernode] (peerB) at (4, 0) {Peer B};
    \node[peernode] (peerC) at (8, 0) {Peer C};
    \node[statenode] (stateA1) at (0, -1) {$[]$};
    \node[statenode] (stateB1) at (4, -1) {$[]$};
    \node[statenode] (stateC1) at (8, -1) {$[]$};
    \node[eventnode] (eventA1) at (0, -2) {\emph{Send} (InsM $\vdash (A,0) \dashv I)$};
    \node[eventnode] (eventB1) at (4, -2) {\emph{Send} (InsM $\vdash (B,0) \dashv N)$};
    \node[eventnode] (eventB2) at (4, -3) {\emph{Recv} $(B,0)$};
        % Lines.
    \node[statenode] (stateB2) at (4, -4) {$[N_{(B,0)}]$};
    \node[eventnode] (eventB3) at (4, -6) {\emph{Recv} $(A,0)$};
        % Lines
    \node[statenode] (stateB3) at (4, -7) {$[I_{(A,0)} N_{(B,0)}]$};
     \node[eventnode] (eventB4) at (4, -8) {\emph{Recv} $(C,1)$};
        % Lines.
    \node[statenode] (stateB4) at (4, -9) {$[I_{(A,0)} N_{(B,0)} K_{(C,1)}]$};
    \node[eventnode] (eventA2) at (0, -3) {\emph{Recv} $(A,0)$};
    \node[statenode] (stateA2) at (0, -4) {$[I_{(A,0)}]$};
    \node[eventnode] (eventA3) at (0, -6) {\emph{Recv} $(B,0)$};
    \node[statenode] (stateA3) at (0, -7) {$[I_{(A,0)}  N_{(B,0)}]$};
    \node[eventnode] (eventA4) at (0, -8) {\emph{Recv} $(C,1)$};
    \node[statenode] (stateA4) at (0, -9) {$[I_{(A,0)} N_{(B,0)} K_{(C,1)}]$};
    \node[eventnode] (eventC1) at (8, -3) {\emph{Recv} $(A,0)$};
    \node[statenode] (stateC2) at (8, -4) {$[I_{(A,0)}]$};
    \node[eventnode] (eventC2) at (8, -5) {\emph{Send} $InsM (A,0)  (C,1) \dashv K$};
    \node[eventnode] (eventC3) at (8, -6) {\emph{Recv} $(C,1)$};
    \node[statenode] (stateC3) at (8, -7) {$[I_{(A,0)} K_{(C,1)}]$};
    \node[eventnode] (eventC4) at (8, -8) {\emph{Recv} $(B,0)$};
    \node[statenode] (stateC4) at (8, -9) {$[I_{(A,0)} N_{(B,0)} K_{(C,1)}]$};
        % Lines.
    \draw[->] (peerA.south) -- (stateA1.north);
    \draw[->] (peerB.south) -- (stateB1.north);
    \draw[->] (peerC.south) -- (stateC1.north);
    \draw[->] (stateA1.south) -- (eventA1.north);
    \draw[->] (eventA1.south) -- (eventA2.north);
    \draw[->] (eventA2.south) -- (stateA2.north);
    \draw[->] (stateA2.south) -- (eventA3.north);
    \draw[->] (eventA3.south) -- (stateA3.north);
    \draw[->] (stateA3.south) -- (eventA4.north);
    \draw[->] (eventA4.south) -- (stateA4.north);
    \draw[->] (stateB1.south) -- (eventB1.north);
    \draw[->] (eventB1.south) -- (eventB2.north);
    \draw[->] (eventB2.south) -- (stateB2.north);
    \draw[->] (stateB2.south) -- (eventB3.north);
    \draw[->] (eventB3.south) -- (stateB3.north);
    \draw[->] (stateB3.south) -- (eventB4.north);
    \draw[->] (eventB4.south) -- (stateB4.north);
    \draw[->] (stateC1.south) -- (eventC1.north);
    \draw[->] (eventC1.south) -- (stateC2.north);
    \draw[->] (stateC2.south) -- (eventC2.north);
    \draw[->] (eventC2.south) -- (eventC3.north);
    \draw[->] (eventC3.south) -- (stateC3.north);
    \draw[->] (stateC3.south) -- (eventC4.north);
    \draw[->] (eventC4.south) -- (stateC4.north);
    \end{tikzpicture}%
    \caption{Example session with 3 peers. Each peer creates an update message and sends a copy of
      it to the other two peers. Each peer integrates the messages in a different order.
    The white rounded boxes represent states, for brevity we only show the W-character's symbol and
    identifier. Although a W-character's data structure stores the identifiers of its predecessor
    and successor from its original creation event. The gray round boxes represent events,
    we abbreviate the reception events, with the identifier of the W-character, although the peer
    receives the full insert message.}%
    \label{fig:session}%
  \end{figure}
  Following the presentation by Oster et al.~\cite{oster2006data} we describe the WOOT framework as
  an operation-based CRDT~\cite{shapiro2011conflict}.

  In WOOT, the shared data type is a string over an alphabet @{text "'\<Sigma>"}.
  Each peer starts with a prescribed initial state representing the empty string.
  Users can perform two types of edit operations on the string at their peer:
  \begin{itemize}
    \item Insert a new character.
    \item Delete an existing character.
  \end{itemize}

  Whenever a user performs one of these operations, their peer will create an update message (see
  Section~\ref{sec:edit}), integrate it immediately into its state, and send it to every other peer.

  An update message created at a peer may depend on at most two of the previously integrated
  messages at that peer.
  A message cannot be delivered to a peer if its antecedents have not been delivered to it yet.
  In Section~\ref{sec:networkModel} we describe a few possible methods to implement this
  requirement, as there is a trade-off between causal consistency and scalability.

  Once delivered to a remote peer, an update message will be integrated to the peers' state.
  The integration algorithm for an update message is the same whether the message originated at the
  same or at a different peer (see Section~\ref{sec:integrate}).

  The interaction of the WOOT Framework can be visualized using a space-time
  diagram~\cite{kshemkalyani2011distributed}.
  An example session between 3 peers is shown in Figure~\ref{fig:session}.
  Note that, each peer sees the edit operations in a different order.\<close>

subsection \<open>Symbol Identifiers \label{sec:symbolIdentifiers}\<close>

text \<open>The WOOT Framework requires a unique identifier for each insert operation, which it keeps
  associated with the inserted symbol.
  The identifier may not be used for another insertion operation on the same or any other peer.
  Moreover the set of identifiers must be endowed with a total linear order.
  We will denote the set of identifiers by @{text "'\<I> :: linorder" }.

  Note that the order on the identifiers is not directly used as a global order over the inserted
  symbols, in contrast to the sort-key based approaches: LSEQ, LOGOOT, or TreeDoc. In particular,
  this means we do not require the identifier space to be dense.

  In the modelling in Section \ref{sec:networkModel}, we will use the pair consisting of a unique
  identifier for the peer and the count of messages integrated or sent by that peer, with the
  lexicographic order induced by the Cartesian product of the peer identifier and the counter.

  It is however possible to use other methods to generate unique identifiers, as long as the above
  requirements are fulfilled.\<close>

subsubsection \<open>Extended Identifiers\<close>

datatype '\<I> extended
  = Begin ("\<turnstile>")
  | InString '\<I> ("(1\<lbrakk>_\<rbrakk>)")
  | End ("\<stileturn>")
derive linorder extended

text \<open>We embed the set of identifiers in an extension containing two additional elements
  denoting the smallest (resp. largest) element of the extension. The order of identifiers with
  respect to each other is preserved. The extended set is used in the corner cases, where a
  W-character is inserted at the beginning or end of the string - and there is no preceeding resp.
  succeeding W-character to reference. See also the following section.\<close>

subsection \<open>Messages \label{sec:messages}\<close>

datatype ('\<I>, '\<Sigma>) insert_message =
  InsertMessage (P:"'\<I> extended") (I:'\<I>) (S:"'\<I> extended") (\<Sigma>:'\<Sigma>)

datatype '\<I> delete_message = DeleteMessage '\<I>

datatype ('\<I>, '\<Sigma>) message =
  Insert "('\<I>, '\<Sigma>) insert_message" |
  Delete "'\<I> delete_message"

text \<open>Two kinds of update messages are exchanged in the WOOT Framework, indicating
  respectively an insertion or a deletion of a character. Thus the set of messages is a sum
  type @{type "message"}.

  An insert message @{term "Insert m"} has the following four components:
  \begin{itemize}
  \item @{term "P m"} and @{term "S m"} denote the identifiers  of the character immediately
     preceding (resp. succeeding) the character at the time of its insertion.
     The special value @{term "\<turnstile>"} (resp. @{term "\<stileturn>"}) indicates that there
     was no such character, i.e., that it was inserted at the beginning (resp. end) of the string.
  \item @{term "I m"} denotes the unique identifier associated to the character (as described in
     Subsection~\ref{sec:symbolIdentifiers}).
  \item @{term "\<Sigma> m"} denotes the inserted character.
  \end{itemize}\<close>

subsection \<open>States \label{sec:states}\<close>

type_synonym ('\<I>, '\<Sigma>) woot_character = "('\<I>, '\<Sigma> option) insert_message"

text \<open>A W-character @{term "w"} is the representation of an inserted character in the state of a
  peer. It has the same semantics and notation for its components as an insert message, with the
  difference that @{term "\<Sigma> w"} can be @{term "Some \<sigma>"} denoting an inserted character, or
  @{term "None"} if the character has already been deleted.
  Because of this overlap in semantics, we define the type of W-characters as a type synonym.

  The state of a peer is then a string of W-characters
  @{text "s :: ('\<I>, '\<Sigma>) woot_character list"}.
  The initial state is the empty string @{term "[]"}.
  The string the user sees is the sequence of symbols omitting @{term "None"}s, i.e., the sequence:
  @{text "[\<sigma>. Some \<sigma> \<leftarrow> map \<Sigma> s]"}.\<close>

fun to_woot_char :: "('\<I>, '\<Sigma>) insert_message \<Rightarrow> ('\<I>, '\<Sigma>) woot_character"
  where
    "to_woot_char (InsertMessage p i s \<sigma>) = InsertMessage p i s (Some \<sigma>)"

text \<open>An insert message can be converted into a W-character by applying @{term Some} to the symbol
  component.\<close>

end
