(*  Title:      A state based hotel key card system

    Author:     Tobias Nipkow, TU Muenchen
*)

(*<*)
theory State
imports Basis
begin

declare if_split_asm[split]
(*>*)

section\<open>A state based model\<close>

text\<open>The model is based on three opaque types @{typ guest},
@{typ key} and @{typ room}. Type @{typ card} is just an abbreviation
for @{typ"key \<times> key"}.

The state of the system is modelled as a record which combines the
information about the front desk, the rooms and the guests.
\<close>

record state =
 owns :: "room \<Rightarrow> guest option"
 currk :: "room \<Rightarrow> key"
 issued :: "key set"
 cards :: "guest \<Rightarrow> card set"
 roomk :: "room \<Rightarrow> key"
 isin :: "room \<Rightarrow> guest set"
 safe :: "room \<Rightarrow> bool"

text\<open>\noindent Reception records who @{const owns} a room (if anybody, hence
@{typ"guest option"}), the current key @{const currk} that has been
issued for a room, and which keys have been @{const issued} so
far. Each guest has a set of @{const cards}. Each room has a key
@{const roomk} recorded in the lock and a set @{const isin} of
occupants. The auxiliary variable @{const safe} is explained further
below; we ignore it for now.

In specification languages like Z, VDM and B we would now define a
number of operations on this state space. Since they are the only
permissible operations on the state, this defines a set of
\emph{reachable} states. In a purely logical environment like
Isabelle/HOL this set can be defined directly by an inductive
definition. Each clause of the definition corresponds to a
transition/operation/event. This is the standard approach to modelling
state machines in theorem provers.

The set of reachable states of the system (called \<open>reach\<close>) is
defined by four transitions: initialization, checking in, entering a room,
and leaving a room:\<close>

(*<*)
inductive_set reach :: "state set"
where
(*>*)
init:
"inj initk \<Longrightarrow>
\<lparr> owns = (\<lambda>r. None), currk = initk, issued = range initk,
  cards = (\<lambda>g. {}), roomk = initk, isin = (\<lambda>r. {}),
  safe = (\<lambda>r. True) \<rparr> \<in> reach"

| check_in:
"\<lbrakk> s \<in> reach; k \<notin> issued s \<rbrakk> \<Longrightarrow>
s\<lparr> currk := (currk s)(r := k), issued := issued s \<union> {k},
   cards := (cards s)(g := cards s g \<union> {(currk s r, k)}),
   owns :=  (owns s)(r := Some g),
   safe := (safe s)(r := False) \<rparr> \<in> reach"

| enter_room:
"\<lbrakk> s \<in> reach; (k,k') \<in> cards s g; roomk s r \<in> {k,k'} \<rbrakk> \<Longrightarrow>
s\<lparr> isin := (isin s)(r := isin s r \<union> {g}),
   roomk := (roomk s)(r := k'),
   safe := (safe s)(r := owns s r = \<lfloor>g\<rfloor> \<and> isin s r = {} \<and> k' = currk s r
                              \<or> safe s r)
  \<rparr> \<in> reach"

| exit_room:
"\<lbrakk> s \<in> reach;  g \<in> isin s r \<rbrakk> \<Longrightarrow>
s\<lparr> isin := (isin s)(r := isin s r - {g}) \<rparr> \<in> reach"

text\<open>\bigskip There is no check-out event because it is implicit in the next
check-in for that room: this covers the cases where a guest leaves without checking out (in which case the room should not be blocked forever) or where
the hotel decides to rent out a room prematurely, probably by accident.
Neither do guests have to return their cards at any point because they may
loose cards or may pretended to have lost them.
We will now explain the events.
\begin{description}
\item[\<open>init\<close>]
Initialization requires that every room has a different key, i.e.\
that @{const currk} is injective. Nobody
owns a room, the keys of all rooms are recorded as issued, nobody has
a card, and all rooms are empty.
\item[@{thm[source] enter_room}]
A guest may enter if either of the two keys on his card equal the room key.
Then \<open>g\<close> is added to the occupants of \<open>r\<close> and
the room key is set to the second key on the card.
Normally this has no effect because the second key is already the room key.
But when entering for the first time, the first key on the card equals
the room key and then the lock is actually recoded.
\item[\<open>exit_room\<close>]
removes an occupant from the occupants of a room.
\item[\<open>check_in\<close>] for room \<open>r\<close> and guest \<open>g\<close>
issues the card @{term"(currk s r, k)"}
to \<open>g\<close>, where \<open>k\<close> is new, makes \<open>g\<close> the owner of the room,
and sets @{term"currk s r"} to the new key \<open>k\<close>.
\end{description}

The reader can easily check that our specification allows the intended
distributed implementation: entering only reads and writes the key in
that lock, and check-in only reads and writes the information at
reception.

In contrast to Jackson we require that initially distinct rooms have
distinct keys. This protects the hotel from its guests: otherwise a
guest may be able to enter rooms he does not own, potentially stealing
objects from those rooms. Of course he can also steal objects from his
own room, but in that case it is easier to hold him responsible. In
general, the hotel may just want to minimize the opportunity for
theft.

The main difference to Jackson's model is that his can talk about
transitions between states rather than merely about reachable
states. This means that he can specify that unauthorized entry into a
room should not occur. Because our specification does not formalize
the transition relation itself, we need to include the \<open>isin\<close>
component in order to
express the same requirement. In the end, we would like to establish
that the system is \emph{safe}: only the owner of a room can be in a
room:
\begin{center}
@{prop"s \<in> reach \<Longrightarrow> g \<in> isin s r \<Longrightarrow> owns s r = Some g"}
\end{center}
Unfortunately, this is just not true. It does not take a PhD in
computer science to come up with the following scenario: because
guests can retain their cards, there is nothing to stop a guest from
reentering his old room after he has checked out (in our model: after
the next guest has checked in), but before the next guest has entered
his room. Hence the best we can do is to prove a conditional safety
property: under certain conditions, the above safety property
holds. The question is: which conditions? It is clear that the room
must be empty when its owner enters it, or all bets
are off. But is that sufficient? Unfortunately not. Jackson's Alloy tool
took 2 seconds~\cite[p.~303]{Jackson06}
to find the following ``guest-in-the-middle'' attack:

\begin{enumerate}

\item Guest 1 checks in and obtains a card $(k_1,k_2)$ for room 1 (whose key
in the lock is $k_1$). Guest 1 does not enter room 1.

\item Guest 2 checks in, obtains a card $(k_2,k_3)$ for room 1, but
does not enter room 1 either.

\item Guest 1 checks in again, obtains a card $(k_3,k_4)$, goes to
room 1, opens it with his old card $(k_1,k_2)$, finds the room empty,
and feels safe \ldots

\end{enumerate}
After Guest~1 has left his room, Guest~2 enters and makes off with the
luggage.

Jackson now assumes that guests return their cards upon
check-out, which can be modelled as follows: upon check-in, the new card
is not added to the guest's set of cards but it replaces his previous
set of cards, i.e.\ guests return old cards the next time they check
in.  Under this assumption, Alloy finds no more counterexamples to
safety --- at least not up to 6 cards and keys and 3 guests and
rooms. This is not a proof but a strong indication that the given
assumptions suffice for safety. We prove that this is indeed the case.

It should be noted that the system also suffers from a liveness
problem: if a guest never enters the room he checked in to, that room
is forever blocked. In practice this is dealt with by a master key. We
ignore liveness.

\subsection{Formalizing safety}
\label{sec:formalizing-safety}

It should be clear that one cannot force guests to always return their
cards (or, equivalently, never to use an old card). We can only prove that if
they do, their room is safe. However, we do not follow Jackson's
approach of globally assuming everybody returns their old cards upon
check-in. Instead we would like to take a local approach where it is up
to each guest whether he follows this safety policy. We allow
guests to keep their cards but make safety dependent on how they use
them.  This generality requires a finer grained model: we need to
record if a guest has entered his room in a safe manner,
i.e.\ if it was empty and if he used the latest key for the room, the
one stored at reception.
The auxiliary variable @{const safe} records for each room if this
was the case at some point between his last check-in and now.
The main theorem will be that if a room is safe in this
manner, then only the owner can be in the room.
Now we explain how @{const safe} is modified with each event:

\begin{description}
\item[\<open>init\<close>] sets @{const safe} to @{const True} for every room.
\item[\<open>check_in\<close>] for room \<open>r\<close> resets @{prop"safe s r"}
because it is not safe for the new owner yet.
\item[@{thm[source] enter_room}] for room \<open>r\<close> sets @{prop"safe s r"} if
the owner entered an empty room using the latest card issued for that room
by reception, or if the room was already safe.
\item[\<open>exit_room\<close>] does not modify @{const safe}.
\end{description}

The reader should convince his or herself that @{const safe}
corresponds to the informal safety policy set out above.  Note that a
guest may find his room non-empty the first time he enters, and
@{const safe} will not be set, but he may come back later, find the
room empty, and then @{const safe} will be set. Furthermore, it is
important that @{thm[source] enter_room} cannot reset @{const safe}
due to the disjunct \<open>\<or> safe s r\<close>.  Hence \<open>check_in\<close> is
the only event that can reset @{const safe}.  That is, a room stays
safe until the next \<open>check_in\<close>.  Additionally @{const safe} is
initially @{const True}, which is fine because initially injectivity
of \<open>initk\<close> prohibits illegal entries by non-owners.

Note that because none of the other state components depend on @{const
safe}, it is truly auxiliary: it can be deleted from the system and
the same set of reachable states is obtained, modulo the absence of
@{const safe}.

We have formalized a very general safety policy of always using the
latest card. A special case of this policy is the one called
\emph{NoIntervening} by Jackson~\cite[p.~200]{Jackson06}: every \<open>check_in\<close> must immediately be followed by the corresponding @{thm[source]
enter_room}.
\<close>

(*<*)
lemma currk_issued[simp]: "s : reach \<Longrightarrow> currk s r : issued s"
by (induct set: reach) auto

lemma key1_issued[simp]: "s : reach \<Longrightarrow> (k,k') : cards s g \<Longrightarrow> k : issued s"
by (induct set: reach) auto

lemma key2_issued[simp]: "s : reach \<Longrightarrow> (k,k') : cards s g \<Longrightarrow> k' : issued s"
by (induct set: reach) auto

lemma roomk_issued[simp]: "s : reach \<Longrightarrow> roomk s k : issued s"
by (induct set: reach) auto

lemma currk_inj[simp]:
 "s : reach \<Longrightarrow> \<forall>r r'. (currk s r = currk s r') = (r = r')"
by (induct set: reach) (auto simp:inj_on_def)

lemma key1_not_currk[simp]:
 "s : reach \<Longrightarrow> (currk s r,k') \<notin> cards s g"
by (induct set: reach) auto

lemma guest_key2_disj[simp]: 
 "\<lbrakk> s : reach; (k\<^sub>1,k) \<in> cards s g\<^sub>1; (k\<^sub>2,k) \<in> cards s g\<^sub>2 \<rbrakk> \<Longrightarrow> g\<^sub>1=g\<^sub>2"
by (induct set: reach) auto

lemma safe_roomk_currk[simp]:
 "s : reach \<Longrightarrow> safe s r \<Longrightarrow> roomk s r = currk s r"
by (induct set: reach) auto


lemma safe_only_owner_enter_normal_aux[simp]:
 "\<lbrakk> s : reach; safe s r; (k',roomk s r) \<in> cards s g \<rbrakk> \<Longrightarrow> owns s r = Some g"
by (induct set: reach) (auto)

lemma safe_only_owner_enter_normal:
assumes "s : reach"
shows "\<lbrakk> safe s r; (k',roomk s r) \<in> cards s g \<rbrakk> \<Longrightarrow> owns s r = Some g"
using assms
proof induct
  case (enter_room s k k1 g1 r1)
  let ?s' = "s\<lparr>isin := (isin s)(r1 := isin s r1 \<union> {g1}),
               roomk := (roomk s)(r1 := k1),
               safe := (safe s)
                 (r1 :=
                    owns s r1 = Some g1 \<and> isin s r1 = {} \<and> k1 = currk s r1 \<or>
                    safe s r1)\<rparr>"
  note s = \<open>s \<in> reach\<close>
  and IH = \<open>\<lbrakk> safe s r; (k', roomk s r) \<in> cards s g \<rbrakk> \<Longrightarrow> owns s r = Some g\<close>
  and card_g1 = \<open>(k,k1) \<in> cards s g1\<close> and safe = \<open>safe ?s' r\<close>
  and card_g = \<open>(k',roomk ?s' r) \<in> cards ?s' g\<close>
  have "roomk s r1 = k \<or> roomk s r1 = k1" using \<open>roomk s r1 \<in> {k,k1}\<close> by simp
  thus ?case
  proof
    assume [symmetric,simp]: "roomk s r1 = k"
    show ?thesis
    proof (cases "r1 = r")
      assume "r1 \<noteq> r" with IH safe card_g show ?thesis by simp
    next
      assume [simp]: "r1 = r"
      hence safe': "owns s r = Some g1 \<or> safe s r"
        using safe by auto
      thus ?thesis
      proof
        assume "safe s r"
        with s card_g1 have False by simp
        thus ?thesis ..
      next
        assume [simp]: "owns s r = Some g1"
        thus "owns ?s' r = Some g"
          using s card_g card_g1 by simp
      qed
    qed
  next
    assume "roomk s r1 = k1"
    with enter_room show ?case by auto
  qed
qed auto

theorem "s : reach \<Longrightarrow> safe s r \<Longrightarrow> g : isin s r \<Longrightarrow> owns s r = Some g"
by (induct set: reach) auto

theorem safe: assumes "s : reach"
shows "safe s r \<Longrightarrow> g : isin s r \<Longrightarrow> owns s r = Some g"
using assms
proof induct
  case (enter_room s k1 k2 g1 r1)
  let ?s' = "s\<lparr>isin := (isin s)(r1 := isin s r1 \<union> {g1}),
               roomk := (roomk s)(r1 := k2),
               safe := (safe s)
                 (r1 :=
                    owns s r1 = Some g1 \<and> isin s r1 = {} \<and> k2 = currk s r1 \<or>
                    safe s r1)\<rparr>"
  note s = \<open>s \<in> reach\<close>
  and IH = \<open>\<lbrakk> safe s r; g \<in> isin s r \<rbrakk> \<Longrightarrow> owns s r = Some g\<close>
  and card_g1 = \<open>(k1,k2) \<in> cards s g1\<close> and safe = \<open>safe ?s' r\<close>
  and isin = \<open>g \<in> isin ?s' r\<close>
  show ?case
    proof (cases "r1 = r")
      assume "r1 \<noteq> r" with IH isin safe show ?thesis by simp
    next
      assume [simp]: "r1 = r"
      have "g \<in> isin s r \<or> g = g1" using isin by auto
      thus ?thesis
      proof
        assume g: "g \<in> isin s r"
        then have "safe s r" using safe by auto
        with g show ?thesis using IH by simp
      next
        assume [simp]: "g = g1"
        have "k2 = roomk s r1 \<or> k1 = roomk s r1"
          using \<open>roomk s r1 \<in> {k1,k2}\<close> by auto
        thus ?thesis
        proof
          assume "k2 = roomk s r1"
          with card_g1 s safe show ?thesis
            by auto
      next
        assume [simp]: "k1 = roomk s r1"
        have "owns s r = Some g1 \<or> safe s r" using safe by auto
        thus ?thesis
        proof
          assume "owns s r = Some g1" thus ?thesis by simp
        next
          assume "safe s r"
          hence False using s card_g1 by auto
          thus ?thesis ..
        qed
      qed
    qed
  qed
qed auto
(*>*)

text\<open>

\subsection{Verifying safety}
\label{sec:verisafe}

All of our lemmas are invariants of @{const reach}.
The complete list, culminating in the main theorem, is this:
\begin{lemma}\label{state-lemmas}
\begin{enumerate}
\item @{thm currk_issued}
\item @{thm key1_issued}
\item @{thm key2_issued}
\item @{thm roomk_issued}
\item \label{currk_inj} @{thm currk_inj}
\item \label{key1_not_currk} @{thm key1_not_currk}
\item @{thm guest_key2_disj}
\item \label{safe_roomk_currk} @{thm[display] safe_roomk_currk}
\item \label{safe_only_owner_enter_normal} @{thm safe_only_owner_enter_normal}
\end{enumerate}
\end{lemma}
\begin{theorem}\label{safe-state}
@{thm[mode=IfThen] safe}
\end{theorem}
The lemmas and the theorem are proved in this order, each one is marked as a
simplification rule, and each proof is a one-liner: induction on
@{prop"s \<in> reach"} followed by \<open>auto\<close>.

Although, or maybe even because these proofs work so smoothly one may
like to understand why. Hence we examine the proof of
Theorem~\ref{safe-state} in more detail. The only interesting case is
@{thm[source] enter_room}. We assume that guest \<open>g\<^sub>1\<close> enters room
\<open>r\<^sub>1\<close> with card @{term"(k\<^sub>1,k\<^sub>2)"} and call the new state \<open>t\<close>.
We assume @{prop"safe t r"} and @{prop"g \<in> isin t r"} and prove
@{prop"owns t r = \<lfloor>g\<rfloor>"} by case distinction.
If @{prop"r\<^sub>1 \<noteq> r"}, the claim follows directly from the induction hypothesis
using \mbox{@{prop"safe s r"}} and @{prop"g \<in> isin t r"}
because @{prop"owns t r = owns s r"} and @{prop"safe t r = safe s r"}.
If @{prop"r\<^sub>1 = r"} then @{prop"g \<in> isin t r"} is equivalent with
@{prop"g \<in> isin s r \<or> g = g\<^sub>1"}. If @{prop"g \<in> isin s r"} then
\mbox{@{prop"safe s r"}} follows from @{prop"safe t r"} by
definition of @{thm[source]enter_room} because @{prop"g \<in> isin s r"}
implies @{prop"isin s r \<noteq> {}"}. Hence the induction hypothesis implies the
claim.  If @{prop"g = g\<^sub>1"} we make another case distinction.
If @{prop"k\<^sub>2 = roomk s r"}, the claim follows immediately from
Lemma~\ref{state-lemmas}.\ref{safe_only_owner_enter_normal} above:
only the owner of a room can possess a card where the second
key is the room key.
If @{prop"k\<^sub>1 = roomk s r"} then, by definition of @{thm[source]enter_room},
@{prop"safe t r"} implies @{prop"owns s r = \<lfloor>g\<rfloor> \<or> safe s r"}.
In the first case the claim is immediate. If @{prop"safe s r"}
then @{prop"roomk s r = currk s r"}
(by Lemma~\ref{state-lemmas}.\ref{safe_roomk_currk})
and thus @{prop"(currk s r, k\<^sub>2) \<in> cards s g"} by assumption
@{prop"(k\<^sub>1,k\<^sub>2) \<in> cards s g\<^sub>1"}, thus contradicting
Lemma~\ref{state-lemmas}.\ref{key1_not_currk}.

This detailed proof shows that a number of case distinctions are
required. Luckily, they all suggest themselves to Isabelle via the
definition of function update (\<open>:=\<close>) or via disjunctions that
arise automatically.
\<close>

(*<*)
end
(*>*)
