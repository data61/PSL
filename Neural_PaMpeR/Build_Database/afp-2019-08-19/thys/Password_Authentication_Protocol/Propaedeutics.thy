(*  Title:       Verification of a Diffie-Hellman Password-based Authentication Protocol by Extending the Inductive Method
    Author:      Pasquale Noce
                 Security Certification Specialist at Arjo Systems, Italy
                 pasquale dot noce dot lavoro at gmail dot com
                 pasquale dot noce at arjosystems dot com
*)

section "Propaedeutic definitions and lemmas"

theory Propaedeutics
imports Complex_Main "HOL-Library.Countable"
begin

declare [[goals_limit = 20]]

text \<open>
\null

\emph{This paper is an achievement of the whole OS Development and Certification team of the Arjo
Systems site at Arzano, Italy, because it would have never been born without the contributions of my
colleagues, the discussions we had, the ideas they shared with me. Particularly, the intuition that
the use of Chip Authentication Mapping makes the secrecy of the PACE authentication key unnecessary
is not mine. I am very grateful to all the team members for these essential contributions, and even
more for these unforgettable years of work together.}
\<close>


subsection "Introduction"

text \<open>
Password-based authentication in an insecure environment -- such as password-based authentication
between a user and a smart card, which is the subject of this paper -- requires that the password be
exchanged on a secure channel, so as to prevent it from falling into the hands of an eavesdropper.
A possible method to establish such a channel is Password Authenticated Connection Establishment
(PACE), which itself is a password-based Diffie-Hellman key agreement protocol, specified in the
form of a smart card protocol in \cite{R4}. Thus, in addition to the user's password, another
password is needed if PACE is used, namely the one from which the PACE authentication key is
derived.

A simple choice allowing to reduce the number of the passwords that the user has to manage would be
to employ the same password both as key derivation password, verified implicitly by means of the
PACE protocol, and as direct use password, verified explicitly by comparison. However, this approach
has the following shortcomings:

\begin{itemize}

\item
A usual countermeasure against trial-and-error attacks aimed at disclosing the user's password
consists of blocking its use after a number of consecutive verification failures exceeding a given
threshold. If the PACE authentication key is derived from the user's password, such key has to be
blocked as well. Thus, an additional PACE authentication key would be needed for any user's
operation not requiring to be preceded by the verification of the user's password, but only to be
performed on a secure channel, such as the verification of a Personal Unblocking Code (PUC) by means
of command RESET RETRY COUNTER \cite{R5} to unblock the password. On the contrary, a single PACE
authentication key is sufficient for all user's operations provided it is independent of the user's
password, which leads to a simpler system.

\item
The user is typically allowed to change her password, e.g. by means of command CHANGE REFERENCE DATA
\cite{R5}. If the PACE authentication key is derived from the user's password, such key has to be
changed as well. This gives rise to additional functional requirements which can be nontrivial to
meet, particularly in the case of a preexisting implementation having to be adapted. For instance,
if the key itself is stored on the smart card rather than being derived at run time from the user's
password, which improves performance and prevents side channel attacks, the update of the password
and the key must be performed as an atomic operation to ensure their consistency. On the contrary,
the PACE authentication key can remain unchanged provided it is independent of the user's password,
which leads to a simpler system.

\end{itemize}

Therefore, a PACE password distinct from the user's password seems to be preferable. As the user's
password is a secret known by the user only, the derivation of the PACE authentication key from the
user's password would guarantee the secrecy of the key as well. If the PACE authentication key is
rather derived from an independent password, then a new question arises: is this key required to be
secret?

In order to find the answer, it is useful to schematize the protocol applying the informal notation
used in \cite{R1}. If Generic Mapping is employed as mapping method (cf. \cite{R4}), the protocol
takes the following form, where agents $U$ and $C$ stand for a given user and her own smart card,
step C$n$ for the $n$th command APDU, and step R$n$ for the $n$th response APDU (for further
information, cf. \cite{R4} and \cite{R5}).

\null

\qquad R1. $C \rightarrow U : \{s\}_K$

\qquad C2. $U \rightarrow C : PK_{Map,PCD}$

\qquad R2. $C \rightarrow U : PK_{Map,IC}$

\qquad C3. $U \rightarrow C : PK_{DH,PCD}$

\qquad R3. $C \rightarrow U : PK_{DH,IC}$

\qquad C4. $U \rightarrow C : \{PK_{DH,IC}\}_{KS}$

\qquad R4. $C \rightarrow U : \{PK_{DH,PCD}\}_{KS}$

\qquad C5. $U \rightarrow C : \{$\emph{User's password}$\}_{KS}$

\qquad R5. $C \rightarrow U : \{$\emph{Success code}$\}_{KS}$

\null

Being irrelevant for the security analysis of the protocol, the initial MANAGE SECURITY ENVIRONMENT:
SET AT command/response pair, as well as the first GENERAL AUTHENTICATE command requesting nonce
$s$, are not included in the scheme.

In the response to the first GENERAL AUTHENTICATE command (step R1), the card returns nonce $s$
encrypted with the PACE authentication key $K$.

In the second GENERAL AUTHENTICATE command/response pair (steps C2 and R2), the user and the card
exchange the respective ephemeral public keys $PK_{Map,PCD} = [SK_{Map,PCD}]G$ and $PK_{Map,IC} =
[SK_{Map,IC}]G$, where $G$ is the static cryptographic group generator (the notation used in
\cite{R6} is applied). Then, both parties compute the ephemeral generator $G' = [s + SK_{Map,PCD}
\times SK_{Map,IC}]G$.

In the third GENERAL AUTHENTICATE command/response pair (steps C3 and R3), the user and the card
exchange another pair of ephemeral public keys $PK_{DH,PCD} = [SK_{DH,PCD}]G'$ and $PK_{DH,IC} =
[SK_{DH,IC}]G'$, and then compute the shared secret $[SK_{DH,PCD} \times SK_{DH,IC}]G'$, from which
session keys $KS_{Enc}$ and $KS_{MAC}$ are derived. In order to abstract from unnecessary details,
the above scheme considers a single session key $KS$.

In the last GENERAL AUTHENTICATE command/response pair (steps C4 and R4), the user and the card
exchange the respective authentication tokens, obtained by computing a Message Authentication Code
(MAC) of the ephemeral public keys $PK_{DH,IC}$ and $PK_{DH,PCD}$ with session key $KS_{MAC}$. In
order to abstract from unnecessary details, the above scheme represents these MACs as cryptograms
generated using the single session key $KS$.

Finally, in steps C5 and R5, the user sends her password to the card on the secure messaging channel
established by session keys $KS_{Enc}$ and $KS_{MAC}$, e.g. via command VERIFY \cite{R5}, and the
card returns the success status word 0x9000 \cite{R5} over the same channel. In order to abstract
from unnecessary details, the above scheme represents both messages as cryptograms generated using
the single session key $KS$.

So, what if the PACE authentication key $K$ were stolen by an attacker -- henceforth called
\emph{spy} as done in \cite{R1}? In this case, even if the user's terminal were protected from
attacks, the spy could get hold of the user's password by replacing the user's smart card with a
fake one capable of performing a remote data transmission, so as to pull off a \emph{grandmaster
chess attack} \cite{R2}. In this way, the following scenario would occur, where agents $F$ and $S$
stand for the fake card and the spy.

\null

\qquad R1. $F \rightarrow U : \{s\}_K$

\qquad C2. $U \rightarrow F : PK_{Map,PCD}$

\qquad R2. $F \rightarrow U : PK_{Map,IC}$

\qquad C3. $U \rightarrow F : PK_{DH,PCD}$

\qquad R3. $F \rightarrow U : PK_{DH,IC}$

\qquad C4. $U \rightarrow F : \{PK_{DH,IC}\}_{KS}$

\qquad R4. $F \rightarrow U : \{PK_{DH,PCD}\}_{KS}$

\qquad C5. $U \rightarrow F : \{$\emph{User's password}$\}_{KS}$

\qquad C5'. $F \rightarrow S : $ \emph{User's password}

\null

Since the spy has stored key $K$ in its memory, the fake card can encrypt nonce $s$ with $K$, so
that it computes the same session keys as the user in step R3. As a result, the user receives a
correct authentication token in step R4, and then agrees to send her password to the fake card in
step C5. At this point, in order to accomplish the attack, the fake card has to do nothing but
decrypt the user's password and send it to the spy on a remote communication channel, which is what
happens in the final step C5'.

This argument demonstrates that the answer to the pending question is affirmative, namely the PACE
authentication key is indeed required to be secret, if Generic Mapping is used. Moreover, the same
conclusion can be drawn on the basis of a similar argument in case the mapping method being used is
Integrated Mapping (cf. \cite{R4}). Therefore, the PACE password from which the key is derived must
be secret as well.

This requirement has a significant impact on both the security and the usability of the system. In
fact, the only way to prevent the user from having to input the PACE password in addition to the
direct use one is providing such password to the user's terminal by other means. In the case of a
stand-alone application, this implies that either the PACE password itself or data allowing its
computation must be stored somewhere in the user's terminal, which gives rise to a risk of leakage.
The alternative is to have the PACE password typed in by the user, which renders longer the overall
credentials that the user is in charge of managing securely. Furthermore, any operation having to be
performed on a secure messaging channel before the user types in her password -- such as identifying
the user in case the smart card is endowed with an identity application compliant with \cite{R3} and
\cite{R4} -- would require an additional PACE password independent of the user's one. Hence, such
preliminary operations and the subsequent user's password verification would have to be performed on
distinct secure messaging channels, which would cause a deterioration in the system performance.

In case Chip Authentication Mapping is used as mapping method instead (cf. \cite{R4}), the resulting
protocol can be schematized as follows.

\null

\qquad R1. $C \rightarrow U : \{s\}_K$

\qquad C2. $U \rightarrow C : PK_{Map,PCD}$

\qquad R2. $C \rightarrow U : PK_{Map,IC}$

\qquad C3. $U \rightarrow C : PK_{DH,PCD}$

\qquad R3. $C \rightarrow U : PK_{DH,IC}$

\qquad C4. $U \rightarrow C : \{PK_{DH,IC}\}_{KS}$

\qquad R4. $C \rightarrow U : \{PK_{DH,PCD}$, $(SK_{IC})^{-1} \times SK_{Map,IC}$ \emph{mod n},

\qquad \qquad $PK_{IC}$, $PK_{IC}$ \emph{signature}$\}_{KS}$

\qquad C5. $U \rightarrow C : \{$\emph{User's password}$\}_{KS}$

\qquad R5. $C \rightarrow U : \{$\emph{Success code}$\}_{KS}$

\null

In the response to the last GENERAL AUTHENTICATE command (step R4), in addition to the MAC of
$PK_{DH,PCD}$ computed with session key $KS_{MAC}$, the smart card returns also the \emph{Encrypted
Chip Authentication Data} ($A_{IC}$) if Chip Authentication Mapping is used. These data result from
the encryption with session key $KS_{Enc}$ of the \emph{Chip Authentication Data} ($CA_{IC}$), which
consist of the product modulo $n$, where $n$ is the group order, of the inverse modulo $n$ of the
static private key $SK_{IC}$ with the ephemeral private key $SK_{Map,IC}$.

The user can then verify the authenticity of the chip applying the following procedure.

\begin{enumerate}

\item
Read the static public key $PK_{IC} = [SK_{IC}]G$ from a dedicated file of the smart card, named
\emph{EF.CardSecurity}.
\\Because of the read access conditions to be enforced by this file, it must be read over the secure
messaging channel established by session keys $KS_{Enc}$ and $KS_{MAC}$ (cf. \cite{R3}).

\item
Verify the signature contained in file EF.CardSecurity, generated over the contents of the file by a
trusted Certification Authority (CA).
\\To perform this operation, the user's terminal is supposed to be provided by secure means with the
public key corresponding to the private key used by the CA for signature generation.

\item
Decrypt the received $A_{IC}$ to recover $CA_{IC}$ and verify that $[CA_{IC}]PK_{IC} = PK_{Map,IC}$.
\\Since this happens just in case $CA_{IC} = (SK_{IC})^{-1} \times SK_{Map,IC}$ \emph{mod n}, the
success of such verification proves that the chip knows the private key $SK_{IC}$ corresponding to
the certified public key $PK_{IC}$, and thus is authentic.

\end{enumerate}

The reading of file EF.CardSecurity is performed next to the last GENERAL AUTHENTICATE command as a
separate operation, by sending one or more READ BINARY commands on the secure messaging channel
established by session keys $KS_{Enc}$ and $KS_{MAC}$ (cf. \cite{R3}, \cite{R4}, and \cite{R5}). The
above scheme represents this operation by inserting the public key $PK_{IC}$ and its signature into
the cryptogram returned by the last GENERAL AUTHENTICATE command, so as to abstract from unnecessary
details once again.

A successful verification of Chip Authentication Data provides the user with a proof of the fact
that the party knowing private key $SK_{Map,IC}$, and then sharing the same session keys $KS_{Enc}$
and $KS_{MAC}$, is an authentic chip. Thus, the protocol ensures that the user accepts to send her
password to an authentic chip only. As a result, the grandmaster chess attack described previously
is not applicable, so that the user's password cannot be stolen by the spy any longer. What is more,
this is true independently of the secrecy of the PACE authentication key. Therefore, this key is no
longer required to be secret, which solves all the problems ensuing from such requirement.

The purpose of this paper is indeed to construct a formal model of the above protocol in the Chip
Authentication Mapping case and prove its security, applying Paulson's Inductive Method as described
in \cite{R1}. In more detail, the formal development is aimed at proving that such protocol enforces
the following security properties.

\begin{itemize}

\item
Secrecy theorem \<open>pr_key_secrecy\<close>: if a user other than the spy sends her password to some
smart card (not necessarily her own one), then the spy cannot disclose the session key used to
encrypt the password. This property ensures that the protocol is successful in establishing
trustworthy secure messaging channels between users and smart cards.

\item
Secrecy theorem \<open>pr_passwd_secrecy\<close>: the spy cannot disclose the passwords of other users.
This property ensures that the protocol is successful in preserving the secrecy of users' passwords.

\item
Authenticity theorem \<open>pr_user_authenticity\<close>: if a smart card receives the password of a user
(not necessarily the cardholder), then the message must have been originally sent by that user. This
property ensures that the protocol enables users to authenticate themselves to their smart cards,
viz. provides an \emph{external authentication} service (cf. \cite{R5}).

\item
Authenticity theorem \<open>pr_card_authenticity\<close>: if a user sends her password to a smart card and
receives a success code as response, then the card is her own one and the response must have been
originally sent by that card. This property ensures that the protocol enables smart cards to
authenticate themselves to their cardholders, viz. provides an \emph{internal authentication}
service (cf. \cite{R5}).

\end{itemize}

Remarkably, none of these theorems turns out to require the secrecy of the PACE authentication key
as an assumption, so that all of them are valid independently of whether this key is secret or not.

The main technical difficulties arising from this formal development are the following ones.

\begin{itemize}

\item
Data such as private keys for Diffie-Hellman key agreement and session keys do not necessarily occur
as components of exchanged messages, viz. they may be computed by some agent without being ever sent
to any other agent. In this case, whichever protocol trace \<open>evs\<close> is given, any such key
\<open>x\<close> will not be contained in either set \<open>analz (spies evs)\<close> or \<open>used evs\<close>, so
that statements such as \<open>x \<in> analz (spies evs)\<close> or \<open>x \<in> used evs\<close> will be vacuously
false. Thus, some way must be found to formalize a state of affairs where \<open>x\<close> is known by the
spy or has already been used in some protocol run.

\item
As private keys for Diffie-Hellman key agreement do not necessarily occur as components of exchanged
messages, some way must be found to record the private keys that each agent has either generated or
accepted from some other agent (possibly implicitly, in the form of the corresponding public keys)
in each protocol run.

\item
The public keys for Diffie-Hellman key agreement being used are comprised of the elements of a
cryptographic cyclic group of prime order $n$, and the private keys are the elements of the finite
field comprised of the integers from 0 to $n$ - 1 (cf. \cite{R4}, \cite{R6}). Hence, the operations
defined in these algebraic structures, as well as the generation of public keys from known private
keys, correspond to additional ways in which the spy can generate fake messages starting from known
ones. A possible option to reflect this in the formal model would be to extend the inductive
definition of set \<open>synth H\<close> with rules enabling to obtain new Diffie-Hellman private and
public keys from those contained in set \<open>H\<close>, but the result would be an overly complex
definition. Thus, an alternative formalization ought to be found.

\end{itemize}

These difficulties are solved by extending the Inductive Method, with respect to the form specified
in \cite{R1}, as follows.

\begin{itemize}

\item
The protocol is no longer defined as a set of event lists, but rather as a set of 4-tuples
@{term "(evs, S, A, U)"} where \<open>evs\<close> is an event list, \<open>S\<close> is the current protocol
\emph{state} -- viz. a function that maps each agent to the private keys for Diffie-Hellman key
agreement generated or accepted in each protocol run --, \<open>A\<close> is the set of the Diffie-Hellman
private keys and session keys currently known by the spy, and \<open>U\<close> is the set of the
Diffie-Hellman private keys and session keys which have already been used in some protocol run.
\\In this way, the first two difficulties are solved. Particularly, the full set of the messages
currently known by the spy can be formalized as the set \<open>analz (A \<union> spies evs)\<close>.

\item
The inductive definition of the protocol does not contain a single \emph{fake} rule any longer, but
rather one \emph{fake} rule for each protocol step. Each \emph{fake} rule is denoted by adding
letter "F" to the identifier of the corresponding protocol step, e.g. the \emph{fake} rules
associated to steps C2 and R5 are given the names \emph{FC2} and \emph{FR5}, respectively.
\\In this way, the third difficulty is solved, too. In fact, for each protocol step, the related
\emph{fake} rule extends the spy's capabilities to generate fake messages with the operations on
known Diffie-Hellman private and public keys relevant for that step, which makes an augmentation of
set \<open>synth H\<close> with such operations unnecessary.

\end{itemize}

Throughout this paper, the salient points of definitions and proofs are commented; for additional
information, cf. Isabelle documentation, particularly \cite{R7}, \cite{R8}, \cite{R9}, and
\cite{R10}.

Paulson's Inductive Method is described in \cite{R1}, and further information is provided in
\cite{R7} as a case study. The formal developments described in \cite{R1} and \cite{R7} are included
in the Isabelle distribution.

Additional information on the involved cryptography can be found in \cite{R4} and \cite{R6}.
\<close>


subsection "Propaedeutic definitions"

text \<open>
First of all, the data types of encryption/signature keys, Diffie-Hellman private keys, and
Diffie-Hellman public keys are defined. Following \cite{R7}, encryption/signature keys are
identified with natural numbers, whereas Diffie-Hellman private keys and public keys are represented
as rational and integer numbers in order to model the algebraic structures that they form (a field
and a group, respectively; cf. above).

\null
\<close>

type_synonym key = nat

type_synonym pri_agrk = rat

type_synonym pub_agrk = int

text \<open>
\null

Agents are comprised of an infinite quantity of users and smart cards, plus the Certification
Authority (CA) signing public key $PK_{IC}$. For each \<open>n\<close>, \<open>User n\<close> is the cardholder
of smart card \<open>Card n\<close>.

\null
\<close>

datatype agent = CA | Card nat | User nat

text \<open>
\null

In addition to the kinds of messages considered in \cite{R1}, the data type of messages comprises
also users' passwords, Diffie-Hellman private and public keys, and Chip Authentication Data.
Particularly, for each \<open>n\<close>, \<open>Passwd n\<close> is the password of @{term "User n"}, accepted
as being the correct one by @{term "Card n"}.

\null
\<close>

datatype msg =
  Agent     agent |
  Number    nat |
  Nonce     nat |
  Key       key |
  Hash      msg |
  Passwd    nat |
  Pri_AgrK  pri_agrk |
  Pub_AgrK  pub_agrk |
  Auth_Data pri_agrk pri_agrk |
  Crypt     key msg |
  MPair     msg msg

syntax
  "_MTuple" :: "['a, args] \<Rightarrow> 'a * 'b"  ("(2\<lbrace>_,/ _\<rbrace>)")

translations
  "\<lbrace>x, y, z\<rbrace>" \<rightleftharpoons> "\<lbrace>x, \<lbrace>y, z\<rbrace>\<rbrace>"
  "\<lbrace>x, y\<rbrace>" \<rightleftharpoons> "CONST MPair x y"

text \<open>
\null

As regards data type \<open>event\<close>, constructor \<open>Says\<close> is extended with three additional
parameters of type @{typ nat}, respectively identifying the communication channel, the protocol run,
and the protocol step (ranging from 1 to 5) in which the message is exchanged. Communication
channels are associated to smart cards, so that if a user receives an encrypted nonce $s$ on channel
$n$, she will answer by sending her ephemeral public key $PK_{Map,PCD}$ for generator mapping to
smart card @{term "Card n"}.

\null
\<close>

datatype event = Says nat nat nat agent agent msg

text \<open>
\null

The record data type \<open>session\<close> is used to store the Diffie-Hellman private keys that each
agent has generated or accepted in each protocol run. In more detail:

\begin{itemize}

\item
Field \<open>NonceS\<close> is deputed to contain the nonce $s$, if any, having been generated internally
(in the case of a smart card) or accepted from the external world (in the case of a user).

\item
Field \<open>IntMapK\<close> is deputed to contain the ephemeral private key for generator mapping, if any,
having been generated internally.

\item
Field \<open>ExtMapK\<close> is deputed to contain the ephemeral private key for generator mapping, if any,
having been implicitly accepted from the external world in the form of the corresponding public key.

\item
Field \<open>IntAgrK\<close> is deputed to contain the ephemeral private key for key agreement, if any,
having been generated internally.

\item
Field \<open>ExtAgrK\<close> is deputed to contain the ephemeral private key for key agreement, if any,
having been implicitly accepted from the external world in the form of the corresponding public key.

\end{itemize}

\null
\<close>

record session =
  NonceS   :: "pri_agrk option"
  IntMapK :: "pri_agrk option"
  ExtMapK :: "pri_agrk option"
  IntAgrK :: "pri_agrk option"
  ExtAgrK :: "pri_agrk option"

text \<open>
\null

Then, the data type of protocol states is defined as the type of the functions that map any 3-tuple
@{term "(X, n, run)"}, where \<open>X\<close> is an agent, \<open>n\<close> identifies a communication channel,
and \<open>run\<close> identifies a protocol run taking place on that communication channel, to a record of
type @{typ session}.

\null
\<close>

type_synonym state = "agent \<times> nat \<times> nat \<Rightarrow> session"

text \<open>
\null

Set \<open>bad\<close> collects the numerical identifiers of the PACE authentication keys known by the spy,
viz. for each \<open>n\<close>, @{term "n \<in> bad"} just in case the spy knows the PACE authentication key
shared by agents @{term "User n"} and @{term "Card n"}.

\null
\<close>

consts bad :: "nat set"

text \<open>
\null

Function \<open>invK\<close> maps each encryption/signature key to the corresponding inverse key, matching
the original key just in case it is symmetric.

\null
\<close>

consts invK :: "key \<Rightarrow> key"

text \<open>
\null

Function \<open>agrK\<close> maps each Diffie-Hellman private key $x$ to the corresponding public key
$[x]G$, where $G$ is the static cryptographic group generator being used.

\null
\<close>

consts agrK :: "pri_agrk \<Rightarrow> pub_agrk"

text \<open>
\null

Function \<open>sesK\<close> maps each Diffie-Hellman private key $x$ to the session key resulting from
shared secret $[x]G$, where $G$ is the static cryptographic group generator being used.

\null
\<close>

consts sesK :: "pri_agrk \<Rightarrow> key"

text \<open>
\null

Function \<open>symK\<close> maps each natural number \<open>n\<close> to the PACE authentication key shared by
agents @{term "User n"} and @{term "Card n"}.

\null
\<close>

consts symK :: "nat \<Rightarrow> key"

text \<open>
\null

Function \<open>priAK\<close> maps each natural number \<open>n\<close> to the static Diffie-Hellman private key
$SK_{IC}$ assigned to smart card @{term "Card n"} for Chip Authentication.

\null
\<close>

consts priAK :: "nat \<Rightarrow> pri_agrk"

text \<open>
\null

Function \<open>priSK\<close> maps each agent to her own private key for digital signature generation, even
if the only such key being actually significant for the model is the Certification Authority's one,
i.e. @{term "priSK CA"}.

\null
\<close>

consts priSK :: "agent \<Rightarrow> key"

text \<open>
\null

The spy is modeled as a user, specifically the one identified by number 0, i.e. @{term "User 0"}.
In this way, in addition to the peculiar privilege of being able to generate fake messages, the spy
is endowed with the capability of performing any operation that a generic user can do.

\null
\<close>

abbreviation Spy :: agent where
"Spy \<equiv> User 0"

text \<open>
\null

Functions \<open>pubAK\<close> and \<open>pubSK\<close> are abbreviations useful to make the formal development
more readable. The former function maps each Diffie-Hellman private key \<open>x\<close> to the message
comprised of the corresponding public key @{term "agrK x"}, whereas the latter maps each agent to
the corresponding public key for digital signature verification.

\null
\<close>

abbreviation pubAK :: "pri_agrk \<Rightarrow> msg" where
"pubAK a \<equiv> Pub_AgrK (agrK a)"

abbreviation pubSK :: "agent \<Rightarrow> key" where
"pubSK X \<equiv> invK (priSK X)"

text \<open>
\null

Function \<open>start_S\<close> represents the initial protocol state, i.e. the one in which no ephemeral
Diffie-Hellman private key has been generated or accepted by any agent yet.

\null
\<close>

abbreviation start_S :: state where
"start_S \<equiv> \<lambda>x. \<lparr>NonceS = None, IntMapK = None, ExtMapK = None,
  IntAgrK = None, ExtAgrK = None\<rparr>"

text \<open>
\null

Set \<open>start_A\<close> is comprised of the messages initially known by the spy, namely:

\begin{itemize}

\item
her own password as a user,

\item
the compromised PACE authentication keys,

\item
the public keys for digital signature verification, and

\item
the static Diffie-Hellman public keys assigned to smart cards for Chip Authentication.

\end{itemize}

\null
\<close>

abbreviation start_A :: "msg set" where
"start_A \<equiv> insert (Passwd 0) (Key ` symK ` bad \<union> Key ` range pubSK \<union> pubAK ` range priAK)"

text \<open>
\null

Set \<open>start_U\<close> is comprised of the messages which have already been used before the execution
of the protocol starts, namely:

\begin{itemize}

\item
all users' passwords,

\item
all PACE authentication keys,

\item
the private and public keys for digital signature generation/verification, and

\item
the static Diffie-Hellman private and public keys assigned to smart cards for Chip Authentication.

\end{itemize}

\null
\<close>

abbreviation start_U :: "msg set" where
"start_U \<equiv> range Passwd \<union> Key ` range symK \<union> Key ` range priSK \<union> Key ` range pubSK \<union>
  Pri_AgrK ` range priAK \<union> pubAK ` range priAK"

text \<open>
\null

As in \cite{R1}, function \<open>spies\<close> models the set of the messages that the spy can see in a
protocol trace. However, it is no longer necessary to identify \<open>spies []\<close> with the initial
knowledge of the spy, since her current knowledge in correspondence with protocol state
@{term "(evs, S, A, U)"} is represented as set \<open>analz (A \<union> spies evs)\<close>, where
@{term "start_A \<subseteq> A"}. Therefore, this formal development defines \<open>spies []\<close> as the empty
set.

\null
\<close>

fun spies :: "event list \<Rightarrow> msg set" where
"spies [] = {}" |
"spies (Says i j k A B X # evs) = insert X (spies evs)"

text \<open>
\null

Here below is the specification of the axioms about the constants defined previously which are used
in the formal proofs. A model of the constants satisfying the axioms is also provided in order to
ensure the consistency of the formal development. In more detail:

\begin{enumerate}

\item
Axiom \<open>agrK_inj\<close> states that function @{term agrK} is injective, and formalizes the fact that
distinct Diffie-Hellman private keys generate distinct public keys.
\\Since the former keys are represented as rational numbers and the latter as integer numbers (cf.
above), a model of function @{term agrK} satisfying the axiom is built by means of the injective
function @{term "inv nat_to_rat_surj"} provided by the Isabelle distribution, which maps rational
numbers to natural numbers.

\item
Axiom \<open>sesK_inj\<close> states that function @{term sesK} is injective, and formalizes the fact that
the key derivation function specified in \cite{R4} for deriving session keys from shared secrets
makes use of robust hash functions, so that collisions are negligible.
\\Since Diffie-Hellman private keys are represented as rational numbers and encryption/signature
keys as natural numbers (cf. above), a model of function @{term sesK} satisfying the axiom is built
by means of the injective function @{term "inv nat_to_rat_surj"}, too.

\item
Axiom \<open>priSK_pubSK\<close> formalizes the fact that every private key for signature generation is
distinct from whichever public key for signature verification. For example, in the case of the RSA
algorithm, small fixed values are typically used as public exponents to make signature verification
more efficient, whereas the corresponding private exponents are of the same order of magnitude as
the modulus.

\item
Axiom \<open>priSK_symK\<close> formalizes the fact that private keys for signature generation are
distinct from PACE authentication keys, which is obviously true since the former keys are asymmetric
whereas the latter are symmetric.

\item
Axiom \<open>pubSK_symK\<close> formalizes the fact that public keys for signature verification are
distinct from PACE authentication keys, which is obviously true since the former keys are asymmetric
whereas the latter are symmetric.

\item
Axiom \<open>invK_sesK\<close> formalizes the fact that session keys are symmetric.

\item
Axiom \<open>invK_symK\<close> formalizes the fact that PACE authentication keys are symmetric.

\item
Axiom \<open>symK_bad\<close> states that set @{term bad} is closed with respect to the identity of PACE
authentication keys, viz. if a compromised user has the same PACE authentication key as another
user, then the latter user is compromised as well.

\end{enumerate}

It is worth remarking that there is no axiom stating that distinct PACE authentication keys are
assigned to distinct users. As a result, the formal development does not depend on the enforcement
of this condition.

\null
\<close>

specification (bad invK agrK sesK symK priSK)
agrK_inj:     "inj agrK"
sesK_inj:     "inj sesK"
priSK_pubSK:  "priSK X \<noteq> pubSK X'"
priSK_symK:   "priSK X \<noteq> symK n"
pubSK_symK:   "pubSK X \<noteq> symK n"
invK_sesK:    "invK (sesK a) = sesK a"
invK_symK:    "invK (symK n) = symK n"
symK_bad:     "m \<in> bad \<Longrightarrow> symK n = symK m \<Longrightarrow> n \<in> bad"
apply (rule_tac x = "{}" in exI)
apply (rule_tac x = "\<lambda>n. if even n then n else Suc n" in exI)
apply (rule_tac x = "\<lambda>x. int (inv nat_to_rat_surj x)" in exI)
apply (rule_tac x = "\<lambda>x. 2 * inv nat_to_rat_surj x" in exI)
apply (rule_tac x = "\<lambda>n. 0" in exI)
apply (rule_tac x = "\<lambda>X. Suc 0" in exI)
proof (simp add: inj_on_def, (rule allI)+, rule impI)
  fix x y
  have "surj nat_to_rat_surj"
   by (rule surj_nat_to_rat_surj)
  hence "inj (inv nat_to_rat_surj)"
   by (rule surj_imp_inj_inv)
  moreover assume "inv nat_to_rat_surj x = inv nat_to_rat_surj y"
  ultimately show "x = y"
   by (rule injD)
qed

text \<open>
\null

Here below are the inductive definitions of sets \<open>parts\<close>, \<open>analz\<close>, and \<open>synth\<close>.
With respect to the definitions given in the protocol library included in the Isabelle distribution,
those of \<open>parts\<close> and \<open>analz\<close> are extended with rules extracting Diffie-Hellman private
keys from Chip Authentication Data, whereas the definition of \<open>synth\<close> contains a further rule
that models the inverse operation, i.e. the construction of Chip Authentication Data starting from
private keys. Particularly, the additional \<open>analz\<close> rules formalize the fact that, for any two
private keys $x$ and $y$, if $x \times y$ \emph{mod n} and $x$ are known, where $n$ is the group
order, then $y$ can be obtained by computing $x \times y \times x^{-1}$ \emph{mod n}, and similarly,
$x$ can be obtained if $y$ is known.

An additional set, named \<open>items\<close>, is also defined inductively in what follows. This set is a
hybrid of \<open>parts\<close> and \<open>analz\<close>, as it shares with \<open>parts\<close> the rule applying to
cryptograms and with \<open>analz\<close> the rules applying to Chip Authentication Data. Since the former
rule is less strict than the corresponding one in the definition of \<open>analz\<close>, it turns out that
@{term "analz H \<subseteq> items H"} for any message set \<open>H\<close>. As a result, for any message \<open>X\<close>,
@{term "X \<notin> items (A \<union> spies evs)"} implies @{term "X \<notin> analz (A \<union> spies evs)"}. Therefore, set
\<open>items\<close> is useful to prove the secrecy of the Diffie-Hellman private keys utilized to compute
Chip Authentication Data without bothering with case distinctions concerning the secrecy of
encryption keys, as would happen if set \<open>analz\<close> were directly employed instead.

\null
\<close>

inductive_set parts :: "msg set \<Rightarrow> msg set" for H :: "msg set" where
Inj:      "X \<in> H \<Longrightarrow> X \<in> parts H" |
Fst:      "\<lbrace>X, Y\<rbrace> \<in> parts H \<Longrightarrow> X \<in> parts H" |
Snd:      "\<lbrace>X, Y\<rbrace> \<in> parts H \<Longrightarrow> Y \<in> parts H" |
Body:     "Crypt K X \<in> parts H \<Longrightarrow> X \<in> parts H" |
Auth_Fst: "Auth_Data x y \<in> parts H \<Longrightarrow> Pri_AgrK x \<in> parts H" |
Auth_Snd: "Auth_Data x y \<in> parts H \<Longrightarrow> Pri_AgrK y \<in> parts H"

inductive_set items :: "msg set \<Rightarrow> msg set" for H :: "msg set" where
Inj:      "X \<in> H \<Longrightarrow> X \<in> items H" |
Fst:      "\<lbrace>X, Y\<rbrace> \<in> items H \<Longrightarrow> X \<in> items H" |
Snd:      "\<lbrace>X, Y\<rbrace> \<in> items H \<Longrightarrow> Y \<in> items H" |
Body:     "Crypt K X \<in> items H \<Longrightarrow> X \<in> items H" |
Auth_Fst: "\<lbrakk>Auth_Data x y \<in> items H; Pri_AgrK y \<in> items H\<rbrakk> \<Longrightarrow> Pri_AgrK x \<in> items H" |
Auth_Snd: "\<lbrakk>Auth_Data x y \<in> items H; Pri_AgrK x \<in> items H\<rbrakk> \<Longrightarrow> Pri_AgrK y \<in> items H"

inductive_set analz :: "msg set \<Rightarrow> msg set" for H :: "msg set" where
Inj:      "X \<in> H \<Longrightarrow> X \<in> analz H" |
Fst:      "\<lbrace>X, Y\<rbrace> \<in> analz H \<Longrightarrow> X \<in> analz H" |
Snd:      "\<lbrace>X, Y\<rbrace> \<in> analz H \<Longrightarrow> Y \<in> analz H" |
Decrypt:  "\<lbrakk>Crypt K X \<in> analz H; Key (invK K) \<in> analz H\<rbrakk> \<Longrightarrow> X \<in> analz H" |
Auth_Fst: "\<lbrakk>Auth_Data x y \<in> analz H; Pri_AgrK y \<in> analz H\<rbrakk> \<Longrightarrow> Pri_AgrK x \<in> analz H" |
Auth_Snd: "\<lbrakk>Auth_Data x y \<in> analz H; Pri_AgrK x \<in> analz H\<rbrakk> \<Longrightarrow> Pri_AgrK y \<in> analz H"

inductive_set synth :: "msg set \<Rightarrow> msg set" for H :: "msg set" where
Inj:      "X \<in> H \<Longrightarrow> X \<in> synth H" |
Agent:    "Agent X \<in> synth H" |
Number:   "Number n \<in> synth H" |
Hash:     "X \<in> synth H \<Longrightarrow> Hash X \<in> synth H" |
MPair:    "\<lbrakk>X \<in> synth H; Y \<in> synth H\<rbrakk> \<Longrightarrow> \<lbrace>X, Y\<rbrace> \<in> synth H" |
Crypt:    "\<lbrakk>X \<in> synth H; Key K \<in> H\<rbrakk> \<Longrightarrow> Crypt K X \<in> synth H" |
Auth:     "\<lbrakk>Pri_AgrK x \<in> H; Pri_AgrK y \<in> H\<rbrakk> \<Longrightarrow> Auth_Data x y \<in> synth H"


subsection "Propaedeutic lemmas"

text \<open>
This section contains the lemmas about sets @{term parts}, @{term items}, @{term analz}, and
@{term synth} required for protocol verification. Since their proofs mainly consist of initial rule
inductions followed by sequences of rule applications and simplifications, \emph{apply}-style is
used.

\null
\<close>

lemma set_spies [rule_format]:
 "Says i j k A B X \<in> set evs \<longrightarrow> X \<in> spies evs"
apply (induction evs rule: spies.induct)
 apply simp_all
done

lemma parts_subset:
 "H \<subseteq> parts H"
by (rule subsetI, rule parts.Inj)

lemma parts_idem:
 "parts (parts H) = parts H"
apply (rule equalityI)
 apply (rule subsetI)
 apply (erule parts.induct)
      apply assumption
     apply (erule parts.Fst)
    apply (erule parts.Snd)
   apply (erule parts.Body)
  apply (erule parts.Auth_Fst)
 apply (erule parts.Auth_Snd)
apply (rule parts_subset)
done

lemma parts_simp:
 "H \<subseteq> range Agent \<union>
    range Number \<union>
    range Nonce \<union>
    range Key \<union>
    range Hash \<union>
    range Passwd \<union>
    range Pri_AgrK \<union>
    range Pub_AgrK \<Longrightarrow>
  parts H = H"
apply (rule equalityI [OF _ parts_subset])
apply (rule subsetI)
apply (erule parts.induct)
     apply blast+
done

lemma parts_mono:
 "G \<subseteq> H \<Longrightarrow> parts G \<subseteq> parts H"
apply (rule subsetI)
apply (erule parts.induct)
     apply (drule subsetD)
      apply assumption
     apply (erule parts.Inj)
    apply (erule parts.Fst)
   apply (erule parts.Snd)
  apply (erule parts.Body)
 apply (erule parts.Auth_Fst)
apply (erule parts.Auth_Snd)
done

lemma parts_insert:
 "insert X (parts H) \<subseteq> parts (insert X H)"
apply (rule subsetI)
apply simp
apply (erule disjE)
 apply simp
 apply (rule parts.Inj)
 apply simp
apply (erule rev_subsetD)
apply (rule parts_mono)
apply blast
done

lemma parts_simp_insert:
 "X \<in> range Agent \<union>
    range Number \<union>
    range Nonce \<union>
    range Key \<union>
    range Hash \<union>
    range Passwd \<union>
    range Pri_AgrK \<union>
    range Pub_AgrK \<Longrightarrow>
  parts (insert X H) = insert X (parts H)"
apply (rule equalityI [OF _ parts_insert])
apply (rule subsetI)
apply (erule parts.induct)
     apply simp_all
     apply (rotate_tac [!])
     apply (erule disjE)
      apply simp
     apply (rule disjI2)
     apply (erule parts.Inj)
    apply (erule disjE)
     apply blast
    apply (rule disjI2)
    apply (erule parts.Fst)
   apply (erule disjE)
    apply blast
   apply (rule disjI2)
   apply (erule parts.Snd)
  apply (erule disjE)
   apply blast
  apply (rule disjI2)
  apply (erule parts.Body)
 apply (erule disjE)
  apply blast
 apply (rule disjI2)
 apply (erule parts.Auth_Fst)
apply (erule disjE)
 apply blast
apply (rule disjI2)
apply (erule parts.Auth_Snd)
done

lemma parts_auth_data_1:
 "parts (insert (Auth_Data x y) H) \<subseteq>
    {Pri_AgrK x, Pri_AgrK y, Auth_Data x y} \<union> parts H"
apply (rule subsetI)
apply (erule parts.induct)
     apply simp_all
     apply (erule disjE)
      apply simp
     apply (rule_tac [1-4] disjI2)+
     apply (erule parts.Inj)
    apply (erule parts.Fst)
   apply (erule parts.Snd)
  apply (erule parts.Body)
 apply (erule disjE)
  apply simp
 apply (rule disjI2)+
 apply (erule parts.Auth_Fst)
apply (erule disjE)
 apply simp
apply (rule disjI2)+
apply (erule parts.Auth_Snd)
done

lemma parts_auth_data_2:
 "{Pri_AgrK x, Pri_AgrK y, Auth_Data x y} \<union> parts H \<subseteq>
    parts (insert (Auth_Data x y) H)"
apply (rule subsetI)
apply simp
apply (erule disjE)
 apply simp
 apply (rule parts.Auth_Fst [of _ y])
 apply (rule parts.Inj)
 apply simp
apply (erule disjE)
 apply simp
 apply (rule parts.Auth_Snd [of x])
 apply (rule parts.Inj)
 apply simp
apply (erule disjE)
 apply simp
 apply (rule parts.Inj)
 apply simp
apply (erule rev_subsetD)
apply (rule parts_mono)
apply blast
done

lemma parts_auth_data:
 "parts (insert (Auth_Data x y) H) =
    {Pri_AgrK x, Pri_AgrK y, Auth_Data x y} \<union> parts H"
by (rule equalityI, rule parts_auth_data_1, rule parts_auth_data_2)

lemma parts_crypt_1:
 "parts (insert (Crypt K X) H) \<subseteq> insert (Crypt K X) (parts (insert X H))"
apply (rule subsetI)
apply (erule parts.induct)
     apply simp_all
     apply (erule disjE)
      apply simp
     apply (rule_tac [1-3] disjI2)
     apply (rule parts.Inj)
     apply simp
    apply (erule parts.Fst)
   apply (erule parts.Snd)
  apply (erule disjE)
   apply simp
   apply (rule disjI2)
   apply (rule parts.Inj)
   apply simp
  apply (rule disjI2)
  apply (erule parts.Body)
 apply (erule parts.Auth_Fst)
apply (erule parts.Auth_Snd)
done

lemma parts_crypt_2:
 "insert (Crypt K X) (parts (insert X H)) \<subseteq> parts (insert (Crypt K X) H)"
apply (rule subsetI)
apply simp
apply (erule disjE)
 apply simp
 apply (rule parts.Inj)
 apply simp
apply (subst parts_idem [symmetric])
apply (erule rev_subsetD)
apply (rule parts_mono)
apply (rule subsetI)
apply simp
apply (erule disjE)
 apply simp
 apply (rule parts.Body [of K])
 apply (rule parts.Inj)
 apply simp
apply (rule parts.Inj)
apply simp
done

lemma parts_crypt:
 "parts (insert (Crypt K X) H) = insert (Crypt K X) (parts (insert X H))"
by (rule equalityI, rule parts_crypt_1, rule parts_crypt_2)

lemma parts_mpair_1:
 "parts (insert \<lbrace>X, Y\<rbrace> H) \<subseteq> insert \<lbrace>X, Y\<rbrace> (parts ({X, Y} \<union> H))"
apply (rule subsetI)
apply (erule parts.induct)
     apply simp_all
     apply (erule disjE)
      apply simp
     apply (rule_tac [1-4] disjI2)
     apply (rule parts.Inj)
     apply simp
    apply (erule disjE)
     apply simp
     apply (rule parts.Inj)
     apply simp
    apply (erule parts.Fst)
   apply (erule disjE)
    apply simp
    apply (rule parts.Inj)
    apply simp
   apply (erule parts.Snd)
  apply (erule parts.Body)
 apply (erule parts.Auth_Fst)
apply (erule parts.Auth_Snd)
done

lemma parts_mpair_2:
 "insert \<lbrace>X, Y\<rbrace> (parts ({X, Y} \<union> H)) \<subseteq> parts (insert \<lbrace>X, Y\<rbrace> H)"
apply (rule subsetI)
apply simp
apply (erule disjE)
 apply (rule parts.Inj)
 apply simp
apply (subst parts_idem [symmetric])
apply (erule rev_subsetD)
apply (rule parts_mono)
apply (rule subsetI)
apply simp
apply (erule disjE)
 apply simp
 apply (rule parts.Fst [of _ Y])
 apply (rule parts.Inj)
 apply simp
apply (erule disjE)
 apply simp
 apply (rule parts.Snd [of X])
 apply (rule parts.Inj)
 apply simp
apply (rule parts.Inj)
apply simp
done

lemma parts_mpair:
 "parts (insert \<lbrace>X, Y\<rbrace> H) = insert \<lbrace>X, Y\<rbrace> (parts ({X, Y} \<union> H))"
by (rule equalityI, rule parts_mpair_1, rule parts_mpair_2)

lemma items_subset:
 "H \<subseteq> items H"
by (rule subsetI, rule items.Inj)

lemma items_idem:
 "items (items H) = items H"
apply (rule equalityI)
 apply (rule subsetI)
 apply (erule items.induct)
      apply assumption
     apply (erule items.Fst)
    apply (erule items.Snd)
   apply (erule items.Body)
  apply (erule items.Auth_Fst)
  apply assumption
 apply (erule items.Auth_Snd)
 apply assumption
apply (rule items_subset)
done

lemma items_parts_subset:
 "items H \<subseteq> parts H"
apply (rule subsetI)
apply (erule items.induct)
     apply (erule parts.Inj)
    apply (erule parts.Fst)
   apply (erule parts.Snd)
  apply (erule parts.Body)
 apply (erule parts.Auth_Fst)
apply (erule parts.Auth_Snd)
done

lemma items_simp:
 "H \<subseteq> range Agent \<union>
    range Number \<union>
    range Nonce \<union>
    range Key \<union>
    range Hash \<union>
    range Passwd \<union>
    range Pri_AgrK \<union>
    range Pub_AgrK \<Longrightarrow>
  items H = H"
apply (rule equalityI)
 apply (subst (3) parts_simp [symmetric])
  apply assumption
 apply (rule items_parts_subset)
apply (rule items_subset)
done

lemma items_mono:
 "G \<subseteq> H \<Longrightarrow> items G \<subseteq> items H"
apply (rule subsetI)
apply (erule items.induct)
     apply (drule subsetD)
      apply assumption
     apply (erule items.Inj)
    apply (erule items.Fst)
   apply (erule items.Snd)
  apply (erule items.Body)
 apply (erule items.Auth_Fst)
 apply assumption
apply (erule items.Auth_Snd)
apply assumption
done

lemma items_insert:
 "insert X (items H) \<subseteq> items (insert X H)"
apply (rule subsetI)
apply simp
apply (erule disjE)
 apply simp
 apply (rule items.Inj)
 apply simp
apply (erule rev_subsetD)
apply (rule items_mono)
apply blast
done

lemma items_simp_insert_1:
 "X \<in> items H \<Longrightarrow> items (insert X H) = items H"
apply (rule equalityI)
 apply (rule subsetI)
 apply (erule items.induct [of _ "insert X H"])
      apply simp
      apply (erule disjE)
       apply simp
      apply (erule items.Inj)
     apply (erule items.Fst)
    apply (erule items.Snd)
   apply (erule items.Body)
  apply (erule items.Auth_Fst)
  apply assumption
 apply (erule items.Auth_Snd)
 apply assumption
apply (rule items_mono)
apply blast
done

lemma items_simp_insert_2:
 "X \<in> range Agent \<union>
    range Number \<union>
    range Nonce \<union>
    range Key \<union>
    range Hash \<union>
    range Passwd \<union>
    range Pub_AgrK \<Longrightarrow>
  items (insert X H) = insert X (items H)"
apply (rule equalityI [OF _ items_insert])
apply (rule subsetI)
apply (erule items.induct)
     apply simp_all
     apply (rotate_tac [!])
     apply (erule disjE)
      apply simp
     apply (rule disjI2)
     apply (erule items.Inj)
    apply (erule disjE)
     apply blast
    apply (rule disjI2)
    apply (erule items.Fst)
   apply (erule disjE)
    apply blast
   apply (rule disjI2)
   apply (erule items.Snd)
  apply (erule disjE)
   apply blast
  apply (rule disjI2)
  apply (erule items.Body)
 apply (erule disjE)
  apply blast
 apply (erule disjE)
  apply blast
 apply (rule disjI2)
 apply (erule items.Auth_Fst)
 apply assumption
apply (erule disjE)
 apply blast
apply (erule disjE)
 apply blast
apply (rule disjI2)
apply (erule items.Auth_Snd)
apply assumption
done

lemma items_pri_agrk_out:
 "Pri_AgrK x \<notin> parts H \<Longrightarrow>
    items (insert (Pri_AgrK x) H) = insert (Pri_AgrK x) (items H)"
apply (rule equalityI [OF _ items_insert])
apply (rule subsetI)
apply (erule items.induct)
     apply simp_all
     apply (erule disjE)
      apply simp
     apply (rule_tac [1-4] disjI2)
     apply (erule items.Inj)
    apply (erule items.Fst)
   apply (erule items.Snd)
  apply (erule items.Body)
 apply (erule disjE)
  apply simp
  apply (drule subsetD [OF items_parts_subset [of H]])
  apply (drule parts.Auth_Snd)
  apply simp
 apply (rule disjI2)
 apply (erule items.Auth_Fst)
 apply assumption
apply (erule disjE)
 apply simp
 apply (drule subsetD [OF items_parts_subset [of H]])
 apply (drule parts.Auth_Fst)
 apply simp
apply (rule disjI2)
apply (erule items.Auth_Snd)
apply assumption
done

lemma items_auth_data_in_1:
 "items (insert (Auth_Data x y) H) \<subseteq>
    insert (Auth_Data x y) (items ({Pri_AgrK x, Pri_AgrK y} \<union> H))"
apply (rule subsetI)
apply (erule items.induct)
     apply simp_all
     apply (erule disjE)
      apply simp
     apply (rule_tac [1-4] disjI2)
     apply (rule items.Inj)
     apply simp
    apply (erule items.Fst)
   apply (erule items.Snd)
  apply (erule items.Body)
 apply (erule disjE)
  apply simp
  apply (rule items.Inj)
  apply simp
 apply (erule items.Auth_Fst)
 apply assumption
apply (erule disjE)
 apply simp
 apply (rule items.Inj)
 apply simp
apply (erule items.Auth_Snd)
apply assumption
done

lemma items_auth_data_in_2:
 "Pri_AgrK x \<in> items H \<or> Pri_AgrK y \<in> items H \<Longrightarrow>
    insert (Auth_Data x y) (items ({Pri_AgrK x, Pri_AgrK y} \<union> H)) \<subseteq>
      items (insert (Auth_Data x y) H)"
apply (rule subsetI)
apply simp
apply rotate_tac
apply (erule disjE)
 apply (rule items.Inj)
 apply simp
apply (subst items_idem [symmetric])
apply (erule rev_subsetD)
apply (rule items_mono)
apply (rule subsetI)
apply simp
apply rotate_tac
apply (erule disjE)
 apply simp
 apply (erule disjE)
  apply (erule rev_subsetD)
  apply (rule items_mono)
  apply blast
 apply (rule items.Auth_Fst [of _ y])
  apply (rule items.Inj)
  apply simp
 apply (erule rev_subsetD)
 apply (rule items_mono)
 apply blast
apply rotate_tac
apply (erule disjE)
 apply simp
 apply (erule disjE)
  apply (rule items.Auth_Snd [of x])
   apply (rule items.Inj)
   apply simp
  apply (erule rev_subsetD)
  apply (rule items_mono)
  apply blast
 apply (erule rev_subsetD)
 apply (rule items_mono)
 apply blast
apply (rule items.Inj)
apply simp
done

lemma items_auth_data_in:
 "Pri_AgrK x \<in> items H \<or> Pri_AgrK y \<in> items H \<Longrightarrow>
    items (insert (Auth_Data x y) H) =
      insert (Auth_Data x y) (items ({Pri_AgrK x, Pri_AgrK y} \<union> H))"
by (rule equalityI, rule items_auth_data_in_1, rule items_auth_data_in_2)

lemma items_auth_data_out:
 "\<lbrakk>Pri_AgrK x \<notin> items H; Pri_AgrK y \<notin> items H\<rbrakk> \<Longrightarrow>
    items (insert (Auth_Data x y) H) = insert (Auth_Data x y) (items H)"
apply (rule equalityI [OF _ items_insert])
apply (rule subsetI)
apply (erule items.induct)
     apply simp_all
     apply (erule disjE)
      apply simp
     apply (rule_tac [1-4] disjI2)
     apply (erule items.Inj)
    apply (erule items.Fst)
   apply (erule items.Snd)
  apply (erule items.Body)
 apply (erule disjE)
  apply simp
 apply (erule items.Auth_Fst)
 apply assumption
apply (erule disjE)
 apply simp
apply (erule items.Auth_Snd)
apply assumption
done

lemma items_crypt_1:
 "items (insert (Crypt K X) H) \<subseteq> insert (Crypt K X) (items (insert X H))"
apply (rule subsetI)
apply (erule items.induct)
     apply simp_all
     apply (erule disjE)
      apply simp
     apply (rule_tac [1-4] disjI2)
     apply (rule items.Inj)
     apply simp
    apply (erule items.Fst)
   apply (erule items.Snd)
  apply (erule disjE)
   apply simp
   apply (rule items.Inj)
   apply simp
  apply (erule items.Body)
 apply (erule items.Auth_Fst)
 apply assumption
apply (erule items.Auth_Snd)
apply assumption
done

lemma items_crypt_2:
 "insert (Crypt K X) (items (insert X H)) \<subseteq> items (insert (Crypt K X) H)"
apply (rule subsetI)
apply simp
apply (erule disjE)
 apply simp
 apply (rule items.Inj)
 apply simp
apply (erule items.induct)
     apply simp
     apply (erule disjE)
      apply simp
      apply (rule items.Body [of K])
      apply (rule items.Inj)
      apply simp
     apply (rule items.Inj)
     apply simp
    apply (erule items.Fst)
   apply (erule items.Snd)
  apply (erule items.Body)
 apply (erule items.Auth_Fst)
 apply assumption
apply (erule items.Auth_Snd)
apply assumption
done

lemma items_crypt:
 "items (insert (Crypt K X) H) = insert (Crypt K X) (items (insert X H))"
by (rule equalityI, rule items_crypt_1, rule items_crypt_2)

lemma items_mpair_1:
 "items (insert \<lbrace>X, Y\<rbrace> H) \<subseteq> insert \<lbrace>X, Y\<rbrace> (items ({X, Y} \<union> H))"
apply (rule subsetI)
apply (erule items.induct)
     apply simp_all
     apply (erule disjE)
      apply simp
     apply (rule_tac [1-4] disjI2)
     apply (rule items.Inj)
     apply simp
    apply (erule disjE)
     apply simp
     apply (rule items.Inj)
     apply simp
    apply (erule items.Fst)
   apply (erule disjE)
    apply simp
    apply (rule items.Inj)
    apply simp
   apply (erule items.Snd)
  apply (erule items.Body)
 apply (erule items.Auth_Fst)
 apply assumption
apply (erule items.Auth_Snd)
apply assumption
done

lemma items_mpair_2:
 "insert \<lbrace>X, Y\<rbrace> (items ({X, Y} \<union> H)) \<subseteq> items (insert \<lbrace>X, Y\<rbrace> H)"
apply (rule subsetI)
apply simp
apply (erule disjE)
 apply (rule items.Inj)
 apply simp
apply (erule items.induct)
     apply simp
     apply (erule disjE)
      apply simp
      apply (rule items.Fst [of _ Y])
      apply (rule items.Inj)
      apply simp
     apply (erule disjE)
      apply simp
      apply (rule items.Snd [of X])
      apply (rule items.Inj)
      apply simp
     apply (rule items.Inj)
     apply simp
    apply (erule items.Fst)
   apply (erule items.Snd)
  apply (erule items.Body)
 apply (erule items.Auth_Fst)
 apply assumption
apply (erule items.Auth_Snd)
apply assumption
done

lemma items_mpair:
 "items (insert \<lbrace>X, Y\<rbrace> H) = insert \<lbrace>X, Y\<rbrace> (items ({X, Y} \<union> H))"
by (rule equalityI, rule items_mpair_1, rule items_mpair_2)

lemma analz_subset:
 "H \<subseteq> analz H"
by (rule subsetI, rule analz.Inj)

lemma analz_idem:
 "analz (analz H) = analz H"
apply (rule equalityI)
 apply (rule subsetI)
 apply (erule analz.induct)
      apply assumption
     apply (erule analz.Fst)
    apply (erule analz.Snd)
   apply (erule analz.Decrypt)
   apply assumption
  apply (erule analz.Auth_Fst)
  apply assumption
 apply (erule analz.Auth_Snd)
 apply assumption
apply (rule analz_subset)
done

lemma analz_parts_subset:
 "analz H \<subseteq> parts H"
apply (rule subsetI)
apply (erule analz.induct)
     apply (erule parts.Inj)
    apply (erule parts.Fst)
   apply (erule parts.Snd)
  apply (erule parts.Body)
 apply (erule parts.Auth_Fst)
apply (erule parts.Auth_Snd)
done

lemma analz_items_subset:
 "analz H \<subseteq> items H"
apply (rule subsetI)
apply (erule analz.induct)
     apply (erule items.Inj)
    apply (erule items.Fst)
   apply (erule items.Snd)
  apply (erule items.Body)
 apply (erule items.Auth_Fst)
 apply assumption
apply (erule items.Auth_Snd)
apply assumption
done

lemma analz_simp:
 "H \<subseteq> range Agent \<union>
    range Number \<union>
    range Nonce \<union>
    range Key \<union>
    range Hash \<union>
    range Passwd \<union>
    range Pri_AgrK \<union>
    range Pub_AgrK \<Longrightarrow>
  analz H = H"
apply (rule equalityI)
 apply (subst (3) parts_simp [symmetric])
  apply assumption
 apply (rule analz_parts_subset)
apply (rule analz_subset)
done

lemma analz_mono:
 "G \<subseteq> H \<Longrightarrow> analz G \<subseteq> analz H"
apply (rule subsetI)
apply (erule analz.induct)
     apply (drule subsetD)
      apply assumption
     apply (erule analz.Inj)
    apply (erule analz.Fst)
   apply (erule analz.Snd)
  apply (erule analz.Decrypt)
  apply assumption
 apply (erule analz.Auth_Fst)
 apply assumption
apply (erule analz.Auth_Snd)
apply assumption
done

lemma analz_insert:
 "insert X (analz H) \<subseteq> analz (insert X H)"
apply (rule subsetI)
apply simp
apply (erule disjE)
 apply simp
 apply (rule analz.Inj)
 apply simp
apply (erule rev_subsetD)
apply (rule analz_mono)
apply blast
done

lemma analz_simp_insert_1:
 "X \<in> analz H \<Longrightarrow> analz (insert X H) = analz H"
apply (rule equalityI)
 apply (rule subsetI)
 apply (erule analz.induct [of _ "insert X H"])
      apply simp
      apply (erule disjE)
       apply simp
      apply (erule analz.Inj)
     apply (erule analz.Fst)
    apply (erule analz.Snd)
   apply (erule analz.Decrypt)
   apply assumption
  apply (erule analz.Auth_Fst)
  apply assumption
 apply (erule analz.Auth_Snd)
 apply assumption
apply (rule analz_mono)
apply blast
done

lemma analz_simp_insert_2:
 "X \<in> range Agent \<union>
    range Number \<union>
    range Nonce \<union>
    range Hash \<union>
    range Passwd \<union>
    range Pub_AgrK \<Longrightarrow>
  analz (insert X H) = insert X (analz H)"
apply (rule equalityI [OF _ analz_insert])
apply (rule subsetI)
apply (erule analz.induct)
     apply simp_all
     apply (rotate_tac [!])
     apply (erule disjE)
      apply simp
     apply (rule disjI2)
     apply (erule analz.Inj)
    apply (erule disjE)
     apply blast
    apply (rule disjI2)
    apply (erule analz.Fst)
   apply (erule disjE)
    apply blast
   apply (rule disjI2)
   apply (erule analz.Snd)
  apply (erule disjE)
   apply blast
  apply (erule disjE)
   apply blast
  apply (rule disjI2)
  apply (erule analz.Decrypt)
  apply assumption
 apply (erule disjE)
  apply blast
 apply (erule disjE)
  apply blast
 apply (rule disjI2)
 apply (erule analz.Auth_Fst)
 apply assumption
apply (erule disjE)
 apply blast
apply (erule disjE)
 apply blast
apply (rule disjI2)
apply (erule analz.Auth_Snd)
apply assumption
done

lemma analz_auth_data_in_1:
 "analz (insert (Auth_Data x y) H) \<subseteq>
    insert (Auth_Data x y) (analz ({Pri_AgrK x, Pri_AgrK y} \<union> H))"
apply (rule subsetI)
apply (erule analz.induct)
     apply simp_all
     apply (erule disjE)
      apply simp
     apply (rule_tac [1-4] disjI2)
     apply (rule analz.Inj)
     apply simp
    apply (erule analz.Fst)
   apply (erule analz.Snd)
  apply (erule analz.Decrypt)
  apply assumption
 apply (erule disjE)
  apply simp
  apply (rule analz.Inj)
  apply simp
 apply (erule analz.Auth_Fst)
 apply assumption
apply (erule disjE)
 apply simp
 apply (rule analz.Inj)
 apply simp
apply (erule analz.Auth_Snd)
apply assumption
done

lemma analz_auth_data_in_2:
 "Pri_AgrK x \<in> analz H \<or> Pri_AgrK y \<in> analz H \<Longrightarrow>
    insert (Auth_Data x y) (analz ({Pri_AgrK x, Pri_AgrK y} \<union> H)) \<subseteq>
      analz (insert (Auth_Data x y) H)"
apply (rule subsetI)
apply simp
apply rotate_tac
apply (erule disjE)
 apply (rule analz.Inj)
 apply simp
apply (subst analz_idem [symmetric])
apply (erule rev_subsetD)
apply (rule analz_mono)
apply (rule subsetI)
apply simp
apply rotate_tac
apply (erule disjE)
 apply simp
 apply (erule disjE)
  apply (erule rev_subsetD)
  apply (rule analz_mono)
  apply blast
 apply (rule analz.Auth_Fst [of _ y])
  apply (rule analz.Inj)
  apply simp
 apply (erule rev_subsetD)
 apply (rule analz_mono)
 apply blast
apply rotate_tac
apply (erule disjE)
 apply simp
 apply (erule disjE)
  apply (rule analz.Auth_Snd [of x])
   apply (rule analz.Inj)
   apply simp
  apply (erule rev_subsetD)
  apply (rule analz_mono)
  apply blast
 apply (erule rev_subsetD)
 apply (rule analz_mono)
 apply blast
apply (rule analz.Inj)
apply simp
done

lemma analz_auth_data_in:
 "Pri_AgrK x \<in> analz H \<or> Pri_AgrK y \<in> analz H \<Longrightarrow>
    analz (insert (Auth_Data x y) H) =
      insert (Auth_Data x y) (analz ({Pri_AgrK x, Pri_AgrK y} \<union> H))"
by (rule equalityI, rule analz_auth_data_in_1, rule analz_auth_data_in_2)

lemma analz_auth_data_out:
 "\<lbrakk>Pri_AgrK x \<notin> analz H; Pri_AgrK y \<notin> analz H\<rbrakk> \<Longrightarrow>
    analz (insert (Auth_Data x y) H) = insert (Auth_Data x y) (analz H)"
apply (rule equalityI [OF _ analz_insert])
apply (rule subsetI)
apply (erule analz.induct)
     apply simp_all
     apply (erule disjE)
      apply simp
     apply (rule_tac [1-4] disjI2)
     apply (erule analz.Inj)
    apply (erule analz.Fst)
   apply (erule analz.Snd)
  apply (erule analz.Decrypt)
  apply assumption
 apply (erule disjE)
  apply simp
 apply (erule analz.Auth_Fst)
 apply assumption
apply (erule disjE)
 apply simp
apply (erule analz.Auth_Snd)
apply assumption
done

lemma analz_crypt_in_1:
 "analz (insert (Crypt K X) H) \<subseteq> insert (Crypt K X) (analz (insert X H))"
apply (rule subsetI)
apply (erule analz.induct)
     apply simp_all
     apply (erule disjE)
      apply simp
     apply (rule_tac [1-4] disjI2)
     apply (rule analz.Inj)
     apply simp
    apply (erule analz.Fst)
   apply (erule analz.Snd)
  apply (erule disjE)
   apply simp
   apply (rule analz.Inj)
   apply simp
  apply (erule analz.Decrypt)
  apply assumption
 apply (erule analz.Auth_Fst)
 apply assumption
apply (erule analz.Auth_Snd)
apply assumption
done

lemma analz_crypt_in_2:
 "Key (invK K) \<in> analz H \<Longrightarrow>
    insert (Crypt K X) (analz (insert X H)) \<subseteq> analz (insert (Crypt K X) H)"
apply (rule subsetI)
apply simp
apply (erule disjE)
 apply simp
 apply (rule analz.Inj)
 apply simp
apply rotate_tac
apply (erule analz.induct)
     apply simp
     apply (erule disjE)
      apply simp
      apply (rule analz.Decrypt [of K])
       apply (rule analz.Inj)
       apply simp
      apply (erule rev_subsetD)
      apply (rule analz_mono)
      apply blast
     apply (rule analz.Inj)
     apply simp
    apply (erule analz.Fst)
   apply (erule analz.Snd)
  apply (erule analz.Decrypt)
  apply assumption
 apply (erule analz.Auth_Fst)
 apply assumption
apply (erule analz.Auth_Snd)
apply assumption
done

lemma analz_crypt_in:
 "Key (invK K) \<in> analz H \<Longrightarrow>
    analz (insert (Crypt K X) H) = insert (Crypt K X) (analz (insert X H))"
by (rule equalityI, rule analz_crypt_in_1, rule analz_crypt_in_2)

lemma analz_crypt_out:
 "Key (invK K) \<notin> analz H \<Longrightarrow>
    analz (insert (Crypt K X) H) = insert (Crypt K X) (analz H)"
apply (rule equalityI [OF _ analz_insert])
apply (rule subsetI)
apply (erule analz.induct)
     apply simp_all
     apply (erule disjE)
      apply simp
     apply (rule_tac [1-4] disjI2)
     apply (erule analz.Inj)
    apply (erule analz.Fst)
   apply (erule analz.Snd)
  apply (erule disjE)
   apply simp
  apply (erule analz.Decrypt)
  apply assumption
 apply (erule analz.Auth_Fst)
 apply assumption
apply (erule analz.Auth_Snd)
apply assumption
done

lemma analz_mpair_1:
 "analz (insert \<lbrace>X, Y\<rbrace> H) \<subseteq> insert \<lbrace>X, Y\<rbrace> (analz ({X, Y} \<union> H))"
apply (rule subsetI)
apply (erule analz.induct)
     apply simp_all
     apply (erule disjE)
      apply simp
     apply (rule_tac [1-4] disjI2)
     apply (rule analz.Inj)
     apply simp
    apply (erule disjE)
     apply simp
     apply (rule analz.Inj)
     apply simp
    apply (erule analz.Fst)
   apply (erule disjE)
    apply simp
    apply (rule analz.Inj)
    apply simp
   apply (erule analz.Snd)
  apply (erule analz.Decrypt)
  apply assumption
 apply (erule analz.Auth_Fst)
 apply assumption
apply (erule analz.Auth_Snd)
apply assumption
done

lemma analz_mpair_2:
 "insert \<lbrace>X, Y\<rbrace> (analz ({X, Y} \<union> H)) \<subseteq> analz (insert \<lbrace>X, Y\<rbrace> H)"
apply (rule subsetI)
apply simp
apply (erule disjE)
 apply (rule analz.Inj)
 apply simp
apply (erule analz.induct)
     apply simp
     apply (erule disjE)
      apply simp
      apply (rule analz.Fst [of _ Y])
      apply (rule analz.Inj)
      apply simp
     apply (erule disjE)
      apply simp
      apply (rule analz.Snd [of X])
      apply (rule analz.Inj)
      apply simp
     apply (rule analz.Inj)
     apply simp
    apply (erule analz.Fst)
   apply (erule analz.Snd)
  apply (erule analz.Decrypt)
  apply assumption
 apply (erule analz.Auth_Fst)
 apply assumption
apply (erule analz.Auth_Snd)
apply assumption
done

lemma analz_mpair:
 "analz (insert \<lbrace>X, Y\<rbrace> H) = insert \<lbrace>X, Y\<rbrace> (analz ({X, Y} \<union> H))"
by (rule equalityI, rule analz_mpair_1, rule analz_mpair_2)

lemma synth_simp_intro:
 "X \<in> synth H \<Longrightarrow>
    X \<in> range Nonce \<union>
      range Key \<union>
      range Passwd \<union>
      range Pri_AgrK \<union>
      range Pub_AgrK \<Longrightarrow>
  X \<in> H"
by (erule synth.cases, blast+)

lemma synth_auth_data:
 "Auth_Data x y \<in> synth H \<Longrightarrow>
    Auth_Data x y \<in> H \<or> Pri_AgrK x \<in> H \<and> Pri_AgrK y \<in> H"
by (erule synth.cases, simp_all)

lemma synth_crypt:
 "Crypt K X \<in> synth H \<Longrightarrow> Crypt K X \<in> H \<or> X \<in> synth H \<and> Key K \<in> H"
by (erule synth.cases, simp_all)

lemma synth_mpair:
 "\<lbrace>X, Y\<rbrace> \<in> synth H \<Longrightarrow> \<lbrace>X, Y\<rbrace> \<in> H \<or> X \<in> synth H \<and> Y \<in> synth H"
by (erule synth.cases, simp_all)

lemma synth_analz_fst:
 "\<lbrace>X, Y\<rbrace> \<in> synth (analz H) \<Longrightarrow> X \<in> synth (analz H)"
proof (drule_tac synth_mpair, erule_tac disjE)
qed (drule analz.Fst, erule synth.Inj, erule conjE)

lemma synth_analz_snd:
 "\<lbrace>X, Y\<rbrace> \<in> synth (analz H) \<Longrightarrow> Y \<in> synth (analz H)"
proof (drule_tac synth_mpair, erule_tac disjE)
qed (drule analz.Snd, erule synth.Inj, erule conjE)

end
