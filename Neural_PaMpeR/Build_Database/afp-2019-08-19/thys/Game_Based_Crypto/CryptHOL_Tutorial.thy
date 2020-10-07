(* Author: Andreas Lochbihler, Digital Asset 
   Author: S. Reza Sefidgar, ETH Zurich      *)

text_raw \<open>%
\clearpage
\addcontentsline{toc}{section}{A Tutorial Introduction to \CryptHOL{}}%
\begin{center}
  \normalfont
  {\huge A Tutorial Introduction to \CryptHOL{}}
  \\[1em]
  \large
  Andreas Lochbihler
  \\
  Digital Asset (Switzerland) GmbH, Zurich, Switzerland,
  \texttt{mail@andreas-lochbihler.de}
  \\[1ex]
  S. Reza Sefidgar
  \\
  Institute of Information Security, 
  Department of Computer Science, ETH Zurich, Zurich, Switzerland, \\
  \texttt{reza.sefidgar@inf.ethz.ch}
\end{center}
%
\begin{abstract}
  \noindent
  This tutorial demonstrates how cryptographic security notions, constructions, and game-based security proofs
  can be formalized using the \CryptHOL{} framework.
  As a running example, we formalize a variant of the hash-based ElGamal encryption scheme and its IND-CPA security in the random oracle model.
  This tutorial assumes basic familiarity with Isabelle/HOL and standard cryptographic terminology.
\end{abstract}
\<close>
section \<open>Introduction\<close>

text \<open>
\CryptHOL{}~\cite{Basin2017, Lochbihler2016} is a framework for constructing rigorous game-based
proofs using the proof assistant Isabelle/HOL~\cite{Nipkow2002}.
Games are expressed as probabilistic functional programs that are shallowly embedded in higher-order logic (HOL) using \CryptHOL{}'s combinators.
The security statements, both concrete and asymptotic, are expressed as Isabelle/HOL theorem statements, and their proofs are written declaratively in Isabelle's proof language Isar~\cite{Wenzel1999}.
This way, Isabelle mechanically checks that all definitions and statements are type-correct and each proof step is a valid logical inference in HOL.
This ensures that the resulting theorems are valid in higher-order logic.

This tutorial explains the \CryptHOL{} essentials using a simple security proof.
Our running example is a variant of the hashed ElGamal encryption scheme~\cite{Elgamal1985}.
We formalize the scheme, the indistinguishability under chosen plaintext (IND-CPA) security property, the computational Diffie-Hellman (CDH) hardness assumption~\cite{Diffie1976}, and the security proof in the random oracle model.
This illustrates how the following aspects of a cryptographic security proof are formalized using \CryptHOL{}:

\begin{itemize}
\item Game-based security definitions (CDH in \S\ref{section:lcdh} and IND-CPA in \S\ref{section:ind-cpa})
\item Oracles (a random oracle in \S\ref{section:random-oracle})
\item Cryptographic schemes, both generic (the concept of an encryption scheme) and a particular instance (the hashed Elgamal scheme in \S\ref{section:hashed-elgamal-scheme})
\item Security statements (concrete and asymptotic, \S\ref{section:security:concrete} and \S\ref{section:security:asymptotic})
\item Reductions (from IND-CPA to CDH for hashed Elgamal in \S\ref{section:reduction})
\item Different kinds of proof steps (\S\ref{section:ghop-first}--\ref{section:combining:hops}):
  \begin{itemize}
  \item Using intermediate games
  \item Defining failure events and applying indistinguishability-up-to lemmas
  \item Equivalence transformations on games
  \end{itemize}
\end{itemize}

This tutorial assumes that the reader knows the basics of Isabelle/HOL and game-based cryptography and wants to get hands-on experience with \CryptHOL{}.
The semantics behind CryptHOL's embedding in higher-order logic and its soundness are not discussed;
we refer the reader to the scientific articles for that~\cite{Basin2017, Lochbihler2016}.
Shoup's tutorial~\cite{Shoup2004IACR} provides a good introduction to game-based proofs.
The following Isabelle features are frequently used in \CryptHOL{} formalizations; the tutorials are available from the Documentation panel in Isabelle/jEdit.
\begin{itemize}
\item Function definitions (tutorials @{doc "prog-prove"} and @{doc "functions"},~\cite{Krauss2009}) for games and reductions
\item Locales (tutorial @{doc locales},~\cite{Ballarin2014}) to modularize the formalization
\item The Transfer package~\cite{Huffman2013} for automating parametricity and representation independence proofs
\end{itemize}

This document is generated from a corresponding Isabelle theory file available online~\cite{Lochbihler2017b}.%
\footnote{%
  The tutorial has been added to the Archive of Formal Proofs after the release of Isabelle2018.
  Until the subsequent Isabelle release, the tutorial is only available in the development version at
  \url{https://devel.isa-afp.org/entries/Game_Based_Crypto.html}.
  The version for Isabelle2018 is available at \url{http://www.andreas-lochbihler.de/pub/crypthol_tutorial.zip}.
}
It contains this text and all examples, including the security definitions and proofs.
We encourage all readers to download the latest version of the tutorial 
and follow the proofs and examples interactively in Isabelle/HOL.
In particular, a Ctrl-click on a formal entity (function, constant, theorem name, ...) jumps to the definition of the entity.

We split the tutorial into a series of recipes for common formalization tasks. In each section, we cover
a familiar cryptography concept and show how it is formalized in \CryptHOL{}. Simultaneously, we explain
the Isabelle/HOL and functional programming topics that are essential for formalizing game-based proofs. 
\<close>

subsection \<open>Getting started\<close>

text \<open>
\CryptHOL{} is available as part of the Archive of Formal Proofs~\cite{Lochbihler2017a}.
Cryptography formalizations based on \CryptHOL{} are arranged in Isabelle theory files that import the relevant libraries.
\<close>

subsection \<open>Getting started\<close>

text \<open>
\CryptHOL{} is available as part of the Archive of Formal Proofs~\cite{Lochbihler2017a}.
Cryptography formalizations based on \CryptHOL{} are arranged in Isabelle theory files that import the relevant libraries.
\<close>

theory CryptHOL_Tutorial imports
  CryptHOL.CryptHOL
(*<*)"HOL-Library.LaTeXsugar"(*>*)

begin

unbundle %invisible lifting_syntax
no_adhoc_overloading %invisible Monad_Syntax.bind bind_pmf
declare %invisible [[names_short]]

text \<open>
The file @{theory CryptHOL.CryptHOL} is the canonical entry point into \CryptHOL{}.
For the hashed Elgamal example in this tutorial, the \CryptHOL{} library contains everything that is needed.
Additional Isabelle libraries can be imported if necessary.
\<close>


section \<open>Modelling cryptography using \CryptHOL{}\<close>

text \<open>
This section demonstrates how the following cryptographic concepts are modelled in \CryptHOL{}.
\begin{itemize}
\item A security property without oracles (\S\ref{section:lcdh})
\item An oracle (\S\ref{section:random-oracle})
\item A cryptographic concept (\S\ref{section:pk-enc})
\item A security property with an oracle (\S\ref{section:ind-cpa})
\item A concrete cryptographic scheme (\S\ref{section:hashed-elgamal-scheme})
\end{itemize}
\<close>


subsection \<open>Security notions without oracles: the CDH assumption \label{section:lcdh}\<close>

text \<open>
In game-based cryptography, a security property is specified using a game between a benign challenger and an adversary.
The probability of an adversary to win the game against the challenger is called its advantage.
A cryptographic construction satisfies a security property if the advantage for any ``feasible'' adversary is ``negligible''.
A typical security proof reduces the security of a construction to the assumed security of its building blocks.
In a concrete security proof, where the security parameter is implicit, it is therefore not necessary to formally define ``feasibility'' and ''negligibility'', 
as the security statement establishes a concrete relation between the advantages of specific adversaries.%
\footnote{%
  The cryptographic literature sometimes abstracts over the adversary and 
  defines the advantage to be the advantage of the best "feasible" adversary against a game.
  Such abstraction would require a formalization of feasibility, for which \CryptHOL{} currently does not offer any support.
  We therefore always consider the advantage of a specific adversary.
}
We return to asymptotic security statements in \S\ref{section:asymptotic}.

A formalization of a security property must therefore specify all of the following:
\begin{itemize}
\item The operations of the scheme (e.g., an algebraic group, an encryption scheme)
\item The type of adversary
\item The game with the challenger
\item The advantage of the adversary as a function of the winning probability
\end{itemize}

For hashed Elgamal, the cyclic group must satisfy the computational Diffie-Hellman assumption.
To keep the proof simple, we formalize the equivalent list version of CDH.

\begin{definition}[The list computational Diffie-Hellman game]
Let \<open>\<G>\<close> be a group of order \<open>q\<close> with generator \<open>\<^bold>g\<close>.
The List Computational Diffie-Hellman (LCDH)
assumption holds for \<open>\<G>\<close> if any ``feasible'' adversary has ``negligible'' probability in winning 
the following \textbf{LCDH game} against a challenger:
  \begin{enumerate}
  \item The challenger picks \<open>x\<close> and \<open>y\<close> randomly (and independently) from
    $\{0, \dots, \<open>q\<close> - 1\}$.
  \item It passes $\<open>\<^bold>g\<close>^x$ and $\<open>\<^bold>g\<close>^y$ to the adversary.
    The adversary generates a set \<open>L\<close> of guesses about the value of $\<open>\<^bold>g\<close>^{\<open>x\<close>\<open>y\<close>}$.
  \item The adversary wins the game if $\<open>\<^bold>g\<close>^{\<open>x\<close>\<open>y\<close>} \in \<open>L\<close>$.
  \end{enumerate}
\end{definition}

The scheme for LCDH uses only a cyclic group.
To make the LCDH formalisation reusable, we formalize the LCDH game for an arbitrary cyclic group @{term "\<G>"} using Isabelle's module system based on locales.
The locale \<open>list_cdh\<close> fixes @{term "\<G>"} to be a finite cyclic group that has elements of type @{typ "'grp"} and comes with a generator @{term "\<^bold>g\<^bsub>\<G>\<^esub>"}.
Basic facts about finite groups are formalized in the \CryptHOL{} theory @{theory CryptHOL.Cyclic_Group}.%
\footnote{%
  The syntax directive @{theory_text "structure"} tells Isabelle that all group operations in the context of the locale refer to the group @{term "\<G>"} unless stated otherwise.
  For example, @{term "\<^bold>g\<^bsub>\<G>\<^esub>"} can be written as \<open>\<^bold>g\<close> inside the locale.

  Isabelle automatically adds the locale parameters and the assumptions on them to all definitions and lemmas inside that locale.
  Of course, we could have made the group @{term "\<G>"} an explicit argument of all functions ourselves, 
  but then we would not benefit from Isabelle's module system, in particular locale instantiation.
}
\<close>

locale list_cdh = cyclic_group \<G> 
  for \<G> :: "'grp cyclic_group" (structure)
begin

text \<open>
The LCDH game does not need oracles.
The adversary is therefore just a probabilistic function from two group elements to a set of guesses, which are again group elements.
In \CryptHOL{}, the probabilistic nature is expressed by the adversary returning a discrete subprobability distribution over sets of guesses, as expressed by the type constructor \<open>spmf\<close>.
(Subprobability distributions are like probability distributions except that the whole probability mass may be less than 1, i.e., some probability may be ``lost''.
A subprobability distribution is called lossless, written @{term lossless_spmf}, if its probability mass is 1.)
We define the following abbreviation as a shorthand for the type of LCDH adversaries.%
\footnote{%
  Actually, the type of group elements has already been fixed in the locale @{locale list_cdh} to the type variable @{typ "'grp"}.
  Unfortunately, such fixed type variables cannot be used in type declarations inside a locale in Isabelle2018.
  The @{command type_synonym} \<open>adversary\<close> is therefore parametrized by a different type variable @{typ 'grp'}, but it will be used below only with @{typ 'grp}.
}
\<close>

type_synonym 'grp' adversary = "'grp' \<Rightarrow> 'grp' \<Rightarrow> 'grp' set spmf"

text \<open>
The LCDH game itself is expressed as a function from the adversary @{term "\<A>"} to the subprobability distribution of the adversary winning.
\CryptHOL{} provides operators to express these distributions as probabilistic programs and reason about them using program logics:
\begin{itemize}
\item The \<open>do\<close> notation desugars to monadic sequencing in the monad of subprobabilities~\cite{Wadler1989}.
  Intuitively, every line \<open>x \<leftarrow> p;\<close> samples an element @{term x} from the distribution @{term p}.
  The sampling is independent, unless the distribution @{term p} depends on previously sampled variables.
  At the end of the block, the @{term "return_spmf DUMMY"} returns whether the adversary has won the game.
\item @{term "sample_uniform n"} denotes the uniform distribution over the set \<open>{0, ..., n - 1}\<close>.
\item @{term "order \<G>"} denotes the order of @{term "\<G>"} and @{term [source] "([^]) :: 'grp \<Rightarrow> nat \<Rightarrow> 'grp"} is the group exponentiation operator.
\end{itemize}

The LCDH game formalizes the challenger's behavior against an adversary @{term "\<A>"}. 
In the following definition, the challenger randomly (and independently) picks two natural numbers 
@{term "x"} and @{term "y"} that are  between 0 and @{term "\<G>"}'s order and passes them to the adversary.
The adversary then returns a set @{term zs} of guesses for @{term "g ^ (x * y)"}, where @{term "g"} is the 
generator of @{term "\<G>"}. The game finally returns a @{typ bool}ean that indicates whether the 
adversary produced a right guess. Formally, @{term "game \<A>"} is a @{typ bool}ean random variable.
\<close>

definition game :: "'grp adversary \<Rightarrow> bool spmf" where 
  "game \<A> = do { 
    x \<leftarrow> sample_uniform (order \<G>);
    y \<leftarrow> sample_uniform (order \<G>);
    zs \<leftarrow> \<A> (\<^bold>g [^] x) (\<^bold>g [^] y);
    return_spmf (\<^bold>g [^] (x * y) \<in> zs)
  }"

text \<open>

The advantage of the adversary is equivalent to its probability of winning the LCDH game.
The function @{term [source] "spmf :: 'a spmf \<Rightarrow> 'a \<Rightarrow> real"} returns the probability of an elementary event under a given subprobability distribution.\<close>

definition advantage :: "'grp adversary \<Rightarrow> real"
  where "advantage \<A> = spmf (game \<A>) True"

end
text \<open>
This completes the formalisation of the LCDH game and we close the locale @{locale list_cdh} with @{command end}.
The above definitions are now accessible under the names @{term "list_cdh.game"} and @{term "list_cdh.advantage"}.
Furthermore, when we later instantiate the locale @{locale list_cdh}, they will be specialized to the given pararameters.
We will return to this topic in \S\ref{section:hashed-elgamal-scheme}.
\<close>

subsection \<open>A Random Oracle \label{section:random-oracle}\<close>

text \<open>
A cryptographic oracle grants an adversary black-box access to a certain information or functionality.
In this section, we formalize a random oracle, i.e., an oracle that models a random function with a finite codomain.
In the Elgamal security proof, the random oracle represents the hash function:
the adversary can query the oracle for a value and the oracle responds with the corresponding ``hash''.

Like for the LCDH formalization, we wrap the random oracle in the locale \<open>random_oracle\<close> for modularity.
The random oracle will return a \<open>bitstring\<close>, i.e. a list of booleans, of length \<open>len\<close>.
\<close>

type_synonym bitstring = "bool list"

locale random_oracle =
  fixes len :: "nat" 
begin

text \<open>
In \CryptHOL{}, oracles are modeled as probabilistic transition systems that given an initial state
and an input, return a subprobability distribution over the output and the successor state.
The type synonym @{typ [source] "('s, 'a, 'b) oracle'"} abbreviates @{typ "'s \<Rightarrow> 'a \<Rightarrow> ('b \<times> 's) spmf"}.


A random oracle accepts queries of type @{typ "'a"} and generates a random bitstring of length @{term len}.
The state of the random oracle remembers its previous responses in a mapping of type @{typ [source] "'a \<rightharpoonup> bitstring"}.
Upon a query @{term "x"}, the oracle first checks whether this query was received before.
If so, the oracle returns the same answer again.
Otherwise, the oracle randomly samples a bitstring of length @{term "len"}, stores it 
in its state, and returns it alongside with the new state.
\<close>

type_synonym 'a state = "'a \<rightharpoonup> bitstring"

definition "oracle" :: "'a state \<Rightarrow> 'a \<Rightarrow> (bitstring \<times> 'a state) spmf"
where
  "oracle \<sigma> x = (case \<sigma> x of 
    None \<Rightarrow> do {
      bs \<leftarrow> spmf_of_set (nlists UNIV len);
      return_spmf (bs, \<sigma>(x \<mapsto> bs)) } 
  | Some bs \<Rightarrow> return_spmf (bs, \<sigma>))"

text \<open>
Initially, the state of a random oracle is the empty map @{term Map.empty}, as no queries have been asked.
For readability, we introduce an abbreviation:\<close>

abbreviation (input) initial :: "'a state" where "initial \<equiv> Map.empty"

text \<open>
This actually completes the formalization of the random oracle.
Before we close the locale, we prove two technical lemmas:
\begin{enumerate}
\item The lemma \<open>lossless_oracle\<close> states that the distribution over answers and successor states is \emph{lossless}, i.e., a full probability distribution.
  Many reasoning steps in game-based proofs are only valid for lossless distributions, so it is generally recommended to prove losslessness of all definitions if possible.
\item The lemma \<open>fresh\<close> describes random oracle's behavior when the query is fresh.
  This lemma makes it possible to automatically unfold the random oracle only when it is known that the query is fresh.
\end{enumerate}
\<close>

lemma lossless_oracle [simp]: "lossless_spmf (oracle \<sigma> x)"
  by(simp add: oracle_def split: option.split)

lemma fresh:
  "oracle \<sigma> x =
   (do { bs \<leftarrow> spmf_of_set (nlists UNIV len);
      return_spmf (bs, \<sigma>(x \<mapsto> bs)) })"
  if "\<sigma> x = None"
  using that by(simp add: oracle_def)

end


text \<open>
\paragraph{Remark: Independence is the default.}
Note that @{typ "_ spmf"} represents a discrete probability distribution rather than a random variable.
The difference is that every spmf is independent of all other spmfs.
There is no implicit space of elementary events via which information may be passed from one random variable to the other.
If such information passing is necessary, this must be made explicit in the program.
That is why the random oracle explicitly takes a state of previous responses and returns the updated states.
Later, whenever the random oracle is used, the user must pass the state around as needed.
This also applies to adversaries that may want to store some information.
\<close>

subsection \<open>Cryptographic concepts: public-key encryption \label{section:pk-enc}\<close>

text \<open>
A cryptographic concept consists of a set of operations and their functional behaviour.
We have already seen two simple examples:
the cyclic group in \S\ref{section:lcdh} and the random oracle in \S\ref{section:random-oracle}.
We have formalized both of them as locales; we have not modelled their functional behavior as this is not needed for the proof.
In this section, we now present a more realistic example: public-key encryption with oracle access.

A public-key encryption scheme consists of three algorithms: key generation, encryption, and decryption.
They are all probabilistic and, in the most general case, they may access an oracle jointly with the adversary, e.g., a random oracle modelling a hash function.
As before, the operations are modelled as parameters of a locale, \<open>ind_cpa_pk\<close>.

\begin{itemize}
\item The key generation algorithm \<open>key_gen\<close> outputs a public-private key pair.
\item The encryption operation \<open>encrypt\<close> takes a public key and a plaintext of type @{typ "'plain"} and outputs a ciphertext of type @{typ 'cipher}.
\item The decryption operation \<open>decrypt\<close> takes a private key and a ciphertext and outputs a plaintext.
\item Additionally, the predicate \<open>valid_plains\<close> tests whether the adversary has chosen a valid pair of plaintexts.
  This operation is needed only in the IND-CPA game definition in the next section, but we include it already here for convenience.
\end{itemize}
\<close>

locale ind_cpa_pk = 
  fixes key_gen :: "('pubkey \<times> 'privkey, 'query, 'response) gpv" 
    and encrypt :: "'pubkey \<Rightarrow> 'plain \<Rightarrow> ('cipher, 'query, 'response) gpv" 
    and decrypt :: "'privkey \<Rightarrow> 'cipher \<Rightarrow> ('plain, 'query, 'response) gpv"
    and valid_plains :: "'plain \<Rightarrow> 'plain \<Rightarrow> bool"
begin

text \<open>
The three actual operations are generative probabilistic values (GPV) of type @{typ [source] "(_, 'query, 'response) gpv"}.
A GPV is a probabilistic algorithm that has not yet been connected to its oracles; see the theoretical paper @{cite Basin2017} for details.
The interface to the oracle is abstracted in the two type parameters @{typ 'query} for queries and @{typ 'response} for responses.
As before, we omit the specification of the functional behavior, namely that decrypting an encryption with a key pair returns the plaintext.
\<close>

subsection \<open>Security notions with oracles: IND-CPA security \label{section:ind-cpa}\<close>

text \<open>
In general, there are several security notions for the same cryptographic concept.
For encryption schemes, an indistinguishability notion of security~\cite{Goldwasser1982} is often used.
We now formalize the notion indistinguishability under chosen plaintext attacks (IND-CPA) for public-key encryption schemes.
Goldwasser et al.~\cite{Goldwasser1984} showed that IND-CPA is equivalent to semantic security.

\begin{definition}[IND-CPA @{cite Shoup2004IACR}]
Let @{term key_gen}, @{term encrypt} and @{term decrypt} denote a public-key encryption scheme.
The IND-CPA game is a two-stage game between the \emph{adversary} and a \emph{challenger}:
\begin{description}
\item[Stage 1 (find):]
  \strut
  \begin{enumerate}
  \item The challenger generates a public key @{term pk} using @{term key_gen} and gives the public key to the adversary.
  \item The adversary returns two messages @{term "m\<^sub>0"} and @{term "m\<^sub>1"}.
  \item The challenger checks that the two messages are a valid pair of plaintexts.
    (For example, both messages must have the same length.)
  \end{enumerate}
\item[Stage 2 (guess):]
  \strut
  \begin{enumerate}
  \item The challenger flips a coin @{term b} (either 0 or 1) and gives @{term "encrypt pk m\<^sub>b"} to the adversary.
  \item The adversary returns a bit @{term b'}.
  \end{enumerate}
\end{description}
The adversary wins the game if his guess @{term b'} is the value of @{term b}.
Let @{term "P\<^sub>w\<^sub>i\<^sub>n"} denote the winning probability.
His advantage is @{term "\<bar>P\<^sub>w\<^sub>i\<^sub>n - 1/2\<bar> :: real"}
\end{definition}

Like with the encryption scheme, we will define the game such that the challenger and the adversary have access to a shared oracle, but the oracle is still unspecified.
Consequently, the corresponding \CryptHOL{} game is a GPV, like the operations of the abstract encryption scheme.
When we specialize the definitions in the next section to the hashed Elgamal scheme, the GPV will be connected to the random oracle.

The type of adversary is now more complicated: It is a pair of probabilistic functions with oracle access, one for each stage of the game.
The first computes the pair of plaintext messages and the second guesses the challenge bit.
The additional @{typ 'state} parameter allows the adversary to maintain state between the two stages.
\<close>

type_synonym ('pubkey', 'plain', 'cipher', 'query', 'response', 'state) adversary =
  "('pubkey' \<Rightarrow> (('plain' \<times> 'plain') \<times> 'state, 'query', 'response') gpv)
   \<times> ('cipher' \<Rightarrow> 'state \<Rightarrow> (bool, 'query', 'response') gpv)"

text \<open>
The IND-CPA game formalization below follows the above informal definition.
There are three points that need some explanation.
First, this game differs from the simpler LCDH game in that it works with GPVs instead of SPMFs.
Therefore, probability distributions like coin flips @{term coin_spmf} must be lifted from SPMFs to GPVs using the coercion @{term lift_spmf}.
Second, the assertion @{term "assert_gpv (valid_plains m\<^sub>0 m\<^sub>1)"} ensures that the pair of messages is valid.
Third, the construct @{term "TRY DUMMY ELSE DUMMY :: (_, _, _) gpv"} catches a violated assertion.
In that case, the adversary's advantage drops to 0 because the result of the game is a coin flip, as we are in the \<open>ELSE\<close> branch.
\<close>

fun game :: "('pubkey, 'plain, 'cipher, 'query, 'response, 'state) adversary
  \<Rightarrow> (bool, 'query, 'response) gpv"
where
  "game (\<A>\<^sub>1, \<A>\<^sub>2) = TRY do {
    (pk, sk) \<leftarrow> key_gen;
    ((m\<^sub>0, m\<^sub>1), \<sigma>) \<leftarrow> \<A>\<^sub>1 pk;
    assert_gpv (valid_plains m\<^sub>0 m\<^sub>1);
    b \<leftarrow> lift_spmf coin_spmf;
    cipher \<leftarrow> encrypt pk (if b then m\<^sub>0 else m\<^sub>1);
    b' \<leftarrow> \<A>\<^sub>2 cipher \<sigma>; 
    Done (b' = b)
  } ELSE lift_spmf coin_spmf"

text \<open>
\input{fig-1}

Figure~\ref{fig:1} visualizes this game as a grey box.
The dashed boxes represent parameters of the game or the locale, i.e., parts that have not yet been instantiated.
The actual probabilistic program is shown on the left half, which uses the dashed boxes as sub-programs.
Arrows in the grey box from the left to the right pass the contents of the variables to the sub-program.
Those in the other direction bind the result of the sub-program to new variables.
The arrows leaving box indicate the query-response interaction with an oracle.
The thick arrows emphasize that the adversary's state is passed around explicitly.
The double arrow represents the return value of the game.
We will use this to define the adversary's advantage.

As the oracle is not specified in the game, the advantage, too, is parametrized by the oracle,
given by the transition function @{term [source] "oracle :: ('s, 'query, 'response) oracle'"}
and the initial state @{term [source] "\<sigma> :: 's"} its initial state.
The operator @{term "run_gpv"} connects the game with the oracle, whereby the GPV becomes an SPMF.
\<close>

fun advantage :: "('\<sigma>, 'query, 'response) oracle' \<times> '\<sigma>
  \<Rightarrow> ('pubkey, 'plain, 'cipher, 'query, 'response, 'state) adversary \<Rightarrow> real"
where 
  "advantage (oracle, \<sigma>) \<A> = \<bar>spmf (run_gpv oracle (game \<A>) \<sigma>) True - 1/2\<bar>"

end

subsection \<open>Concrete cryptographic constructions: the hashed ElGamal encryption scheme \label{section:hashed-elgamal-scheme}\<close>

text \<open>
With all the above modelling definitions in place,
we are now ready to explain how concrete cryptographic constructions are expressed in \CryptHOL.
In general, a cryptographic construction builds a cryptographic concept from possibly several simpler cryptographic concepts.
In the running example, the hashed ElGamal cipher~\cite{Elgamal1985} constructs a public-key encryption scheme from a finite cyclic group and a hash function.
Accordingly, the formalisation consists of three steps:

\begin{enumerate}
\item Import the cryptographic concepts on which the construction builds.
\item Define the concrete construction.
\item Instantiate the abstract concepts with the construction.
\end{enumerate}

First, we declare a new locale that imports the two building blocks: 
the cyclic group from the LCDH game with namespace \<open>lcdh\<close> and the random oracle for the hash function with namespace \<open>ro\<close>.
This ensures that the construction can be used for arbitrary cyclic groups. 
For the message space, it suffices to fix the length \<open>len_plain\<close> of the plaintexts.
\<close>

locale hashed_elgamal =
  lcdh: list_cdh \<G> + 
  ro: random_oracle len_plain
  for \<G> :: "'grp cyclic_group" (structure)
  and len_plain :: "nat"
begin

text \<open>
Second, we formalize the hashed ElGamal encryption scheme.
Here is the well-known informal definition.

\begin{definition}[Hashed Elgamal encryption scheme]
Let $G$ be a cyclic group of order $q$ that has a generator $g$. Furthermore, let $h$ be a hash
function that maps the elements of $G$ to bitstrings, and $\oplus$ be the xor operator on
bitstrings. The Hashed-ElGamal encryption scheme is given by the following algorithms:
\begin{description}
\item[Key generation]
  Pick an element $x$ randomly from the set $\{0, \dots, q-1\}$
  and output the pair $(g^x, x)$, where $g^x$ is the public key and $x$ is the private key.
\item[Encryption]
  Given the public key $pk$ and the message $m$,
  pick $y$ randomly from the set $\{0, \dots, q-1\}$
  and output the pair $(g^y, h(pk^y) \oplus m)$.
  Here $\oplus$ denotes the bitwise exclusive-or of two bitstrings.
\item[Decryption]
  Given the private key $sk$ and the ciphertext $(\alpha, \beta)$,
  output $h(\alpha^{sk}) \oplus \beta$.
\end{description}
\end{definition}

As we can see, the public key is a group element, the private key a natural number, a plaintext a bitstring, and a ciphertext a pair of a group element and a bitstring.%
\footnote{%
  More precisely, the private key ranges between 0 and $q - 1$ and the bitstrings are of length \<open>len_plain\<close>.
  However, Isabelle/HOL's type system cannot express such properties that depend on locale parameters.
}
For readability, we introduce meaningful abbreviations for these concepts.
\<close>
type_synonym 'grp' pub_key = "'grp'"
type_synonym 'grp' priv_key = nat
type_synonym plain = bitstring
type_synonym 'grp' cipher = "'grp' \<times> bitstring"

text \<open>
We next translate the three algorithms into \CryptHOL{} definitions.
The definitions are straightforward except for the hashing.
Since we analyze the security in the random oracle model, 
an application of the hash function $H$ is modelled as a query to the random oracle using the GPV @{term hash}.
Here, @{term "Pause x Done"} calls the oracle with query @{term x} and returns the oracle's response.
Furthermore, we define the plaintext validity predicate to check the length of the adversary's messages produced by the adversary.
\<close>

abbreviation hash :: "'grp \<Rightarrow> (bitstring, 'grp, bitstring) gpv"
where
  "hash x \<equiv> Pause x Done"

definition key_gen :: "('grp pub_key \<times> 'grp priv_key) spmf"
where 
  "key_gen = do {
    x \<leftarrow> sample_uniform (order \<G>);
    return_spmf (\<^bold>g [^] x, x)
  }"

definition encrypt :: "'grp pub_key \<Rightarrow> plain \<Rightarrow> ('grp cipher, 'grp, bitstring) gpv"
where
  "encrypt \<alpha> msg = do {
    y \<leftarrow> lift_spmf (sample_uniform (order \<G>));
    h \<leftarrow> hash (\<alpha> [^] y);
    Done (\<^bold>g [^] y, h [\<oplus>] msg)
  }"

definition decrypt :: "'grp priv_key \<Rightarrow> 'grp cipher \<Rightarrow> (plain, 'grp, bitstring) gpv"
where
  "decrypt x = (\<lambda>(\<beta>, \<zeta>). do {
    h \<leftarrow> hash (\<beta> [^] x);
    Done (\<zeta> [\<oplus>] h)
  })"

definition valid_plains :: "plain \<Rightarrow> plain \<Rightarrow> bool"
where 
  "valid_plains msg1 msg2 \<longleftrightarrow> length msg1 = len_plain \<and> length msg2 = len_plain"

text\<open>
The third and last step instantiates the interface of the encryption scheme with the hashed Elgamal scheme.
This specializes all definition and theorems in the locale @{locale ind_cpa_pk} to our scheme.
\<close>

sublocale ind_cpa: ind_cpa_pk "(lift_spmf key_gen)" encrypt decrypt valid_plains .

text \<open>
Figure~\ref{fig:2} illustrates the instantiation.
In comparison to Fig.~\ref{fig:1}, the boxes for the key generation and the encryption algorithm have been instantiated with the hashed Elgamal definitions from this section.
We nevertheless draw the boxes to indicate that the definitions of these algorithms has not yet been inlined in the game definition.
The thick grey border around the key generation algorithm denotes the @{term lift_spmf} operator, which embeds the probabilistic @{term key_gen} without oracle access into the type of GPVs with oracle access.
The oracle has also been instantiated with the random oracle @{term ro.oracle} imported from @{locale "hashed_elgamal"}'s parent locale @{locale random_oracle} with prefix \<open>ro\<close>.

\input{fig-2}
\<close>

section \<open>Cryptographic proofs in \CryptHOL{}\<close>

text \<open>
This section explains how cryptographic proofs are expressed in \CryptHOL{}.
We will continue our running example by stating and proving the IND-CPA security of the hashed Elgamal encryption scheme
under the computational Diffie-Hellman assumption in the random oracle model, using the definitions from the previous section.
More precisely, we will formalize a reduction argument (\S\ref{section:reduction}) and bound the IND-CPA advantage using the CDH advantage.
We will \emph{not} formally state the result that CDH hardness in the cyclic group implies IND-CPA security, 
which quantifies over all feasible adversaries--%
to that end, we would have to formally define feasibility, for which \CryptHOL{} currently does not offer any support.

The actual proof of the bound consists of several game transformations.
We will focus on those steps that illustrate common steps in cryptographic proofs (\S\ref{section:ghop-first}--\S\ref{section:combining:hops}) .
\<close>

subsection\<open>The reduction \label{section:reduction}\<close>

text \<open>
The security proof involves a reduction argument:
We will derive a bound on the advantage of an arbitrary adversary in the IND-CPA game @{term "ind_cpa.game"} for hashed Elgamal
that depends on another adversary's advantage in the LCDH game @{term "lcdh.game"} of the underlying group.
The reduction transforms every IND-CPA adversary @{term "\<A>"} into a LCDH adversary @{term "elgamal_reduction \<A>"},
using @{term "\<A>"} as a black box.
In more detail, it simulates an execution of the IND-CPA game including the random oracle.
At the end of the game, the reduction outputs the set of queries that the adversary has sent to the random oracle.
The reduction works as follows given a two part IND-CPA adversary @{term "\<A> = (\<A>\<^sub>1, \<A>\<^sub>2)"}
(Figure~\ref{fig:3} visualizes the reduction as the dotted box):
\begin{enumerate}
\item It receives two group elements @{term "\<alpha>"} and @{term "\<beta>"} from the LCDH challenger.
\item The reduction passes @{term "\<alpha>"} to the adversary as the public key and runs @{term "\<A>\<^sub>1"} to get messages @{term "m\<^sub>1"} and @{term "m\<^sub>2"}.
  The adversary is given access to the random oracle with the initial state @{term ro.initial}.
\item The assertion checks that the adversary returns two valid plaintexts, i.e., @{term m\<^sub>1} and @{term m\<^sub>2} are strings of length @{term len_plain}.
\item Instead of actually performing an encryption, the reduction generates a random bitstring @{term h} of length @{term len_plain} 
(@{term "nlists UNIV len_plain"} denotes the set of all bitstrings of length @{term len_plain} and
@{term spmf_of_set} converts the set into a uniform distribution over the set.)
\item The reduction passes @{term "(\<beta>, h)"} as the challenge ciphertext to the adversary in the second phase of the IND-CPA game.
\item The actual guess @{term b'} of the adversary is ignored; 
  instead the reduction returns the set @{term "dom s'"} of all queries that the adversary made to the random oracle as its guess for the CDH game.
\item If any of the steps after the first phase fails, the reduction's guess is the set @{term "dom s"} of oracle queries made during the first phase.
\end{enumerate}

\input{fig-3}
\<close>

fun elgamal_reduction
  :: "('grp pub_key, plain, 'grp cipher, 'grp, bitstring, 'state) ind_cpa.adversary
  \<Rightarrow> 'grp lcdh.adversary"                     
where
  "elgamal_reduction (\<A>\<^sub>1, \<A>\<^sub>2) \<alpha> \<beta> = do {
    (((m\<^sub>1, m\<^sub>2), \<sigma>), s) \<leftarrow> exec_gpv ro.oracle (\<A>\<^sub>1 \<alpha>) ro.initial;
    TRY do {
      _ :: unit \<leftarrow> assert_spmf (valid_plains m\<^sub>1 m\<^sub>2);
      h \<leftarrow> spmf_of_set (nlists UNIV len_plain);
      (b', s') \<leftarrow> exec_gpv ro.oracle (\<A>\<^sub>2 (\<beta>, h) \<sigma>) s;
      return_spmf (dom s')
    } ELSE return_spmf (dom s)
  }"


subsection \<open>Concrete security statement \label{section:security:concrete}\<close>

text \<open>
A concrete security statement in \CryptHOL{} has the form:
Subject to some side conditions for the adversary @{term \<A>}, the advantage in one game is bounded
by a function of the transformed adversary's advantage in a different game.%
\footnote{%
  A security proof often involves several reductions.
  The bound then depends on several advantages, one for each reduction.
}
\<close>

theorem concrete_security:
  assumes "side conditions for \<A>"
  shows "advantage\<^sub>1 \<A> \<le> f (advantage\<^sub>2 (reduction \<A>))"
  oops %invisible
text \<open>
For the hashed Elgamal scheme, the theorem looks as follows, i.e., the function @{term f} is the identity function.
\<close>
end %invisible \<comment> \<open>These six lines allow us to show the concrete theorem statement before we define the side condition on \<A>. They should not occur in a normal formalisation.\<close>
context %invisible begin 
local_setup %invisible \<open>Local_Theory.map_background_naming (Name_Space.mandatory_path "ind_cpa")\<close>
definition %invisible lossless where "lossless = undefined"
end %invisible
context %invisible hashed_elgamal begin
theorem concrete_security_elgamal:
  assumes lossless: "ind_cpa.lossless \<A>"
  shows "ind_cpa.advantage (ro.oracle, ro.initial) \<A> \<le> lcdh.advantage (elgamal_reduction \<A>)"
  oops%invisible \<comment> \<open>This aborts the proof as we have not yet defined @{term ind_cpa.lossless} properly. We restate the theorem below properly.\<close>
text \<open>
Such a statement captures the essence of a concrete security proof.
For if there was a feasible adversary @{term \<A>} with non-negligible advantage against the @{term ind_cpa.game},
then @{term "elgamal_reduction \<A>"} would be an adversary against the @{term lcdh.game} with at least the same advantage.
This implies the existence of an adversary with non-negligible advantage against the cryptographic primitive that was assumed to be secure.
What we cannot state formally is that the transformed adversary @{term "elgamal_reduction \<A>"} is feasible
as we have not formalized the notion of feasibility.
The readers of the formalization must convince themselves that the reduction preserves feasibility.

In the case of @{term elgamal_reduction}, this should be obvious from the definition (given the theorem's side condition)
as the reduction does nothing more than sampling and redirecting data.

Our proof for the concrete security theorem needs the side condition that the adversary is lossless.
Losslessness for adversaries is similar to losslessness for subprobability distributions.
It ensures that the adversary always terminates and returns an answer to the challenger.
For the IND-CPA game, we define losslessness as follows:
\<close>
definition (in ind_cpa_pk) lossless
  :: "('pubkey, 'plain, 'cipher, 'query, 'response, 'state) adversary \<Rightarrow> bool"
where
  "lossless = (\<lambda>(\<A>\<^sub>1, \<A>\<^sub>2). (\<forall>pk. lossless_gpv \<I>_full (\<A>\<^sub>1 pk)) 
               \<and> (\<forall>cipher \<sigma>. lossless_gpv \<I>_full (\<A>\<^sub>2 cipher \<sigma>)))"

theorem %invisible concrete_security_elgamal:
  assumes lossless: "ind_cpa.lossless \<A>"
  shows 
  "ind_cpa.advantage (ro.oracle, ro.initial) \<A> \<le> lcdh.advantage (elgamal_reduction \<A>)"
text %visible \<open>
So now let's start with the proof.
\<close>
proof %visible -
  text %invisible \<open>
    For this proof, we configure Isabelle's simplifier such that the proofs become reasonably short.
    Initially, when writing the proof, we had added those lemmas manually to to invocation
    of the simplifier and then collected the useful rules in a polishing step.
  \<close>
  note %invisible [cong del] = if_weak_cong 
   and [split del] = if_split
   and [simp] = map_lift_spmf gpv.map_id lossless_weight_spmfD map_spmf_bind_spmf bind_spmf_const lcdh.order_gt_0
   and [if_distribs] = if_distrib[where f="\<lambda>x. try_spmf x _"] if_distrib[where f="weight_spmf"] if_distrib[where f="\<lambda>r. scale_spmf r _"]
text %visible \<open>
As a preparatory step, we split the adversary @{term "\<A>"} into its two phases @{term "\<A>\<^sub>1"} and @{term "\<A>\<^sub>2"}.
We could have made the two phases explicit in the theorem statement, but our form is easier to read and use.
We also immediately decompose the losslessness assumption on @{term "\<A>"}.%
\footnote{%
  Later in the proof, we will often prove losslessness of the definitions in the proof.
  We will not show them in this document, but they are in the Isabelle sources from which this document is generated.
}
\<close>
obtain \<A>\<^sub>1 \<A>\<^sub>2 where \<A> [simp]: "\<A> = (\<A>\<^sub>1, \<A>\<^sub>2)" by (cases "\<A>")
from lossless have lossless1 [simp]: "\<And>pk. lossless_gpv \<I>_full (\<A>\<^sub>1 pk)"
  and lossless2 [simp]: "\<And>\<sigma> cipher. lossless_gpv \<I>_full (\<A>\<^sub>2 \<sigma> cipher)"
  by(auto simp add: ind_cpa.lossless_def)

subsection \<open>Recording adversary queries \label{section:ghop-first}\<close>

text \<open>
  As can be seen in Fig.~\ref{fig:2}, both the adversary and the encryption of the challenge ciphertext use the random oracle.
  The reduction, however, returns only the queries that the adversary makes to the oracle (in Fig.~\ref{fig:3}, $h$ is generated independently of the random oracle).
  To bridge this gap, we introduce an @{term interceptor} between the adversary and the oracle that records all adversary's queries.
\<close>
define interceptor :: "'grp set \<Rightarrow> 'grp \<Rightarrow> (bitstring \<times> 'grp set, _, _) gpv"
where 
  "interceptor \<sigma> x = (do {
    h \<leftarrow> hash x;
    Done (h, insert x \<sigma>)
  })" for \<sigma> x
have %invisible [simp]: "lossless_gpv \<I>_full (interceptor \<sigma> x)" for \<sigma> x by(simp add: interceptor_def)
have %invisible [simp]: "lossless_gpv \<I>_full (inline interceptor (\<A>\<^sub>1 \<alpha>) s)" for \<alpha> s
  by(rule lossless_inline[where \<I>=\<I>_full]) simp_all
have %invisible [simp]: "lossless_gpv \<I>_full (inline interceptor (\<A>\<^sub>2 \<sigma> c) s)" for \<sigma> c s
  by(rule lossless_inline[where \<I>=\<I>_full]) simp_all
text \<open>
  We integrate this interceptor into the @{term "ind_cpa.game"} using the @{term "inline"} function as illustrated in Fig.~\ref{fig:4}
  and name the result @{term "game\<^sub>0"}.

\input{fig-4}
\<close>

define game\<^sub>0 where
"game\<^sub>0 = TRY do {
  (pk, _) \<leftarrow> lift_spmf key_gen;
  (((m\<^sub>1, m\<^sub>2), \<sigma>), s) \<leftarrow> inline interceptor (\<A>\<^sub>1 pk) {};
  assert_gpv (valid_plains m\<^sub>1 m\<^sub>2);
  b \<leftarrow> lift_spmf coin_spmf;
  c \<leftarrow> encrypt pk (if b then m\<^sub>1 else m\<^sub>2);
  (b', s') \<leftarrow> inline interceptor (\<A>\<^sub>2 c \<sigma>) s;
  Done (b' = b)
} ELSE lift_spmf coin_spmf"

text \<open>
We claim that the above modifications do not affect the output of the IND-CPA game at all.
This might seem obvious since we are only logging the adversary's queries without modifying them.
However, in a formal proof, this needs to be precisely justified.

More precisely, we have been very careful that the two games @{term "ind_cpa.game \<A>"} and 
@{term game\<^sub>0} have identical structure. They differ only in that @{term game\<^sub>0} uses the adversary
@{term "(\<lambda>pk. inline interceptor (\<A>\<^sub>1 pk) {}, \<lambda>cipher \<sigma>. inline interceptor (\<A>\<^sub>2 cipher \<sigma>))"}
instead of @{term "\<A>"}. The formal justification for this replacement happens in two steps:
\begin{enumerate}
\item We replace the oracle transformer @{term interceptor} with @{term id_oracle}, which merely passes queries and results to the oracle.
\item Inlining the identity oracle transformer @{term id_oracle} does not change an adversary and can therefore be dropped.
\end{enumerate}

The first step is automated using Isabelle's Transfer package~\cite{Huffman2013},
which is based on Mitchell's representation independence~\cite{Mitchell1986}.
The replacement is controlled by so-called transfer rules of the form @{term "R x y"} which
indicates that @{term x} shall replace @{term y}; the correspondence relation @{term R} captures the 
kind of replacement.
The @{method transfer} proof method then constructs a constraint system with one constraint
for each atom in the proof goal where the correspondence relation and the replacement are unknown.
It then tries to solve the constraint system using the rules that have been declared with 
the attribute \<open>[transfer_rule]\<close>.
Atoms that do not have a suitable transfer rule are not changed and their correspondence relation is
instantiated with the identity relation @{term "(=)"}.

The second step is automated using Isabelle's simplifier.  

In the example, the crucial change happens in the state of the oracle transformer:
@{term interceptor} records all queries in a set whereas @{term id_oracle} has no state, which 
is modelled with the singleton type @{typ unit}.
To capture the change, we define the correspondence relation @{term cr} on the states of the oracle transformers.
(As we are in the process of adding this state, this state is irrelevant and @{term cr} is therefore always true.
We nevertheless have to make an explicit definition such that Isabelle does not automatically beta-reduce terms, which would confuse @{method transfer}.) 
We then prove that it relates the initial states and that @{term cr} is a bisimulation relation
for the two oracle transformers; see @{cite Basin2017} for details.
The bisimulation proof itself is automated, too: A bit of term rewriting (@{command "unfolding"}) 
makes the two oracle transformers structurally identical except for the state update function.
Having proved that the state update function @{term "\<lambda>_ \<sigma>. \<sigma>"} is a correct replacement for
@{term "insert"} w.r.t. @{term cr}, the @{method transfer_prover} then lifts this replacement
to the bisimulation rule.
Here, @{method transfer_prover} is similar to @{method transfer} except that it works only for
transfer rules and builds the constraint system only for the term to be replaced.

The theory source of this tutorial contains a step-by-step proof to illustrate how transfer works.
\<close>
{ define cr :: "unit \<Rightarrow> 'grp set \<Rightarrow> bool" where "cr \<sigma> \<sigma>' = True" for \<sigma> \<sigma>'
  have [transfer_rule]: "cr () {}" by(simp add: cr_def) \<comment> \<open>initial states\<close>
  have [transfer_rule]: "((=) ===> cr ===> cr) (\<lambda>_ \<sigma>. \<sigma>) insert" \<comment> \<open>state update\<close>
    by(simp add: rel_fun_def cr_def)
  have [transfer_rule]: \<comment> \<open>@{term cr} is a bisimulation for the oracle transformers\<close> 
    "(cr ===> (=) ===> rel_gpv (rel_prod (=) cr) (=)) id_oracle interceptor"
    unfolding interceptor_def[abs_def] id_oracle_def[abs_def] bind_gpv_Pause bind_rpv_Done
    by transfer_prover
  have "ind_cpa.game \<A> = game\<^sub>0" unfolding game\<^sub>0_def \<A> ind_cpa.game.simps
    by transfer (simp add: bind_map_gpv o_def ind_cpa.game.simps split_def) 
} note %invisible ind_cpa_game_eq_game\<^sub>0 = this

{ % invisible text \<open>And now the same proof again, but step by step.\<close>
  define cr :: "unit \<Rightarrow> 'grp set \<Rightarrow> bool" where "cr \<sigma> \<sigma>' = True" for \<sigma> \<sigma>'
  have [transfer_rule]: "cr () {}" by(simp add: cr_def) \<comment> \<open>initial states\<close>
  have [transfer_rule]: "((=) ===> cr ===> cr) (\<lambda>_ \<sigma>. \<sigma>) insert" \<comment> \<open>state update\<close>
    by(simp add: rel_fun_def cr_def)
  have [transfer_rule]: \<comment> \<open>@{term cr} is a bisimulation for the oracle transformers\<close> 
    "(cr ===> (=) ===> rel_gpv (rel_prod (=) cr) (=)) id_oracle interceptor"
    text \<open>1. Unfold the definitions of the oracle transformers and massage them to have the same structure.\<close>
    unfolding interceptor_def[abs_def] id_oracle_def[abs_def] bind_gpv_Pause bind_rpv_Done
    text \<open>2. Build the constraint system for the second argument of the correspondence relation, namely @{term interceptor} with the rewrite rules applied.\<close>
    apply transfer_prover_start
    text \<open>3. Solve the constraint system prolog-style by resolving with the rules from @{thm [source] transfer_raw}.\<close>
        apply transfer_step \<comment> \<open>This step uses the state update transfer rule proven in the previous @{command have}.\<close>
       apply transfer_step
      apply transfer_step
     apply transfer_step
    text \<open>4. Check that the found solution is the expected one, namely the first argument of the correspondence relation, here @{term id_oracle} with the rewrite rules applied.\<close>
    apply transfer_prover_end
    done
  have "ind_cpa.game \<A> = game\<^sub>0"
    text \<open>1. Unfold the definitions\<close>
    unfolding game\<^sub>0_def \<A> ind_cpa.game.simps
    text \<open>2. Build the constraint system for the whole subgoal. The \<open>fixing\<close> tells transfer
      that it must not replace the variables @{term "\<G>"}, @{term "len_plain"}, @{term "\<A>\<^sub>1"} and @{term "\<A>\<^sub>2"}.\<close>
    apply transfer_start 
    text \<open>3. Solve all constraints with the transfer rules\<close>
                        apply transfer_step+
    apply transfer_end
    text \<open>4. Get rid of the identity oracle transformer @{term id_oracle} by rewriting. Really curious readers may dare to look at the simplifer trace.\<close>
    supply [[simp_trace_new mode=full]]
    apply(simp add: bind_map_gpv o_def ind_cpa.game.simps split_def)
    done
}

subsection %visible \<open>Equational program transformations\<close>

text \<open>
Before we move on, we need to simplify @{term game\<^sub>0} and inline a few of the definitions.
All these simplifications are equational program transformations, so the Isabelle simplifier can justify them.
We combine the @{term interceptor} with the random oracle @{term ro.oracle} into a new oracle @{term oracle'} 
with which the adversary interacts.
\<close>
define oracle' :: "'grp set \<times> ('grp \<rightharpoonup> bitstring) \<Rightarrow> 'grp \<Rightarrow> _"
where "oracle' = (\<lambda>(s, \<sigma>) x. do {
  (h, \<sigma>') \<leftarrow> case \<sigma> x of
      None \<Rightarrow> do {
          bs \<leftarrow> spmf_of_set (nlists UNIV len_plain);
          return_spmf (bs, \<sigma>(x \<mapsto> bs)) }
    | Some bs \<Rightarrow> return_spmf (bs, \<sigma>);
  return_spmf (h, insert x s, \<sigma>')
})"
have %invisible [simp]: "lossless_spmf (oracle' s plain)" for s plain
  by(simp add: oracle'_def Let_def split: prod.split option.split)
have %invisible [simp]: "lossless_spmf (exec_gpv oracle' (\<A>\<^sub>1 \<alpha>) s)" for s \<alpha>
  by(rule lossless_exec_gpv[where \<I>=\<I>_full]) simp_all
have %invisible [simp]: "lossless_spmf (exec_gpv oracle' (\<A>\<^sub>2 \<sigma> cipher) s)" for \<sigma> cipher s
  by(rule lossless_exec_gpv[where \<I>=\<I>_full]) simp_all
have *: "exec_gpv ro.oracle (inline interceptor \<A> s) \<sigma> = 
  map_spmf (\<lambda>(a, b, c). ((a, b), c)) (exec_gpv oracle' \<A> (s, \<sigma>))" for \<A> \<sigma> s
  by(simp add: interceptor_def oracle'_def ro.oracle_def Let_def 
     exec_gpv_inline exec_gpv_bind o_def split_def cong del: option.case_cong_weak)
text \<open>
We also want to inline the key generation and encryption algorithms,
push the @{term "TRY DUMMY ELSE DUMMY :: (_, _, _) gpv"} towards the assertion (which is possible because the adversary is lossless by assumption),
and rearrange the samplings a bit.
The latter is automated using \<open>monad_normalisation\<close>~\cite{Schneider2017}.%
\footnote{%
  The tool \<open>monad_normalisation\<close> augments Isabelle's simplifier with a normalization procedure for commutative monads based on higher-order ordered rewriting.
  It can also commute across control structures like \<open>if\<close> and \<open>case\<close>.
  Although it is not complete as a decision procedure (as the normal forms are not unique), it usually works in practice.
}
\<close>
have game\<^sub>0: "run_gpv ro.oracle game\<^sub>0 ro.initial = do {
  x \<leftarrow> sample_uniform (order \<G>);
  y \<leftarrow> sample_uniform (order \<G>);
  b \<leftarrow> coin_spmf;
  (((msg1, msg2), \<sigma>), (s, s_h)) \<leftarrow>
    exec_gpv oracle' (\<A>\<^sub>1 (\<^bold>g [^] x)) ({}, ro.initial);
  TRY do {
    _ :: unit \<leftarrow> assert_spmf (valid_plains msg1 msg2);
    (h, s_h') \<leftarrow> ro.oracle s_h (\<^bold>g [^] (x * y));
    let cipher = (\<^bold>g [^] y, h [\<oplus>] (if b then msg1 else msg2));
    (b', (s', s_h'')) \<leftarrow> exec_gpv oracle' (\<A>\<^sub>2 cipher \<sigma>) (s, s_h');
    return_spmf (b' = b)
  } ELSE do {
    b \<leftarrow> coin_spmf;
    return_spmf b
  }
}"
  including monad_normalisation
  by(simp add: game\<^sub>0_def key_gen_def encrypt_def * exec_gpv_bind bind_map_spmf assert_spmf_def
    try_bind_assert_gpv try_gpv_bind_lossless split_def o_def if_distribs lcdh.nat_pow_pow)
text \<open>
This call to Isabelle's simplifier may look complicated at first, but it can be constructed incrementally 
by adding a few theorems and looking at the resulting goal state and searching for suitable theorems using @{command find_theorems}.
As always in Isabelle, some intuition and knowledge about the library of lemmas is crucial. 
\begin{itemize}
\item We knew that the definitions @{thm [source] game\<^sub>0_def}, @{thm [source] key_gen_def}, and @{thm [source] encrypt_def} should be unfolded,
  so they are added first to the simplifier's set of rewrite rules.
\item The equations @{thm [source] exec_gpv_bind}, @{thm [source] try_bind_assert_gpv}, and @{thm [source] try_gpv_bind_lossless}
  ensure that the operator @{term exec_gpv}, which connects the @{term game\<^sub>0} with the random oracle, is distributed over the sequencing.
  Together with @{thm [source] * }, this gives the adversary access to @{term oracle'} instead of the interceptor and the random oracle, 
  and makes the call to the random oracle in the encryption of the chosen message explicit.
\item The theorem @{thm [source] lcdh.nat_pow_pow} rewrites the iterated exponentiation @{term "(\<^bold>g [^] x) [^] y"} to @{term "\<^bold>g [^] (x * y)"}.
\item The other theorems @{thm [source] bind_map_spmf}, @{thm [source] assert_spmf_def},
  @{thm [source] split_def}, @{thm [source] o_def}, and @{thm [source] if_distribs}
  take care of all the boilerplate code that makes all these transformations type-correct.
  These theorems often have to be used together.
\end{itemize}

Note that the state of the oracle @{term oracle'} is changed between @{term "\<A>\<^sub>1"} and @{term "\<A>\<^sub>2"}.
Namely, the random oracle's part @{term s_h} may change when the chosen message is encrypted,
but the state that records the adversary's queries @{term s} is passed on unchanged.
\<close>

text\<open>\input{fig-5}\<close>

subsection \<open>Capturing a failure event\<close>

text \<open>
Suppose that two games behave the same except when a so-called failure event occurs @{cite Shoup2004IACR}.
Then the chance of an adversary distinguishing the two games is bounded by the probability of the failure event.
In other words, the simulation of the reduction is allowed to break if the failure event occurs.
In the running example, such an argument is a key step to derive the bound on the adversary's advantage.
But to reason about failure events, we must first introduce them into the games we consider.
This is because in \CryptHOL{}, the probabilistic programs describe probability distributions over what they return (@{term return_spmf}).
The variables that are used internally in the program are not accessible from the outside,
i.e., there is no memory to which these are written.
This has the advantage that we never have to worry about the names of the variables, e.g., to avoid clashes.
The drawback is that we must explicitly introduce all the events that we are interested in.

Introducing a failure event into a game is straightforward.
So far, the games @{term ind_cpa.game} and @{term game\<^sub>0} simply denoted the probability distribution of whether the adversary has guessed right.
For hashed Elgamal, the simulation breaks if the adversary queries the random oracle with the same query @{term "\<^bold>g [^] (x * y)"} that is used for encrypting the chosen message \<open>m\<^sub>b\<close>.
So we simply change the return type of the game to return whether the adversary guessed right \emph{and} whether the failure event has occurred.
The next definition @{term game\<^sub>1} does so.
(Recall that @{term oracle'} stores in its first state component @{term s} the queries by the adversary.)
In preparation of the next reasoning step, we also split off the first two samplings, namely of @{term x} and @{term y}, and make them parameters of @{term game\<^sub>1}.
\<close>
define game\<^sub>1 :: "nat \<Rightarrow> nat \<Rightarrow> (bool \<times> bool) spmf"
where "game\<^sub>1 x y = do {
  b \<leftarrow> coin_spmf;
  (((m\<^sub>1, m\<^sub>2), \<sigma>), (s, s_h)) \<leftarrow> exec_gpv oracle' (\<A>\<^sub>1 (\<^bold>g [^] x)) ({}, ro.initial);
  TRY do {
    _ :: unit \<leftarrow> assert_spmf (valid_plains m\<^sub>1 m\<^sub>2);
    (h, s_h') \<leftarrow> ro.oracle s_h (\<^bold>g [^] (x * y));
    let c = (\<^bold>g [^] y, h [\<oplus>] (if b then m\<^sub>1 else m\<^sub>2));
    (b', (s', s_h'')) \<leftarrow> exec_gpv oracle' (\<A>\<^sub>2 c \<sigma>) (s, s_h');
    return_spmf (b' = b, \<^bold>g [^] (x * y) \<in> s')
  } ELSE do {
    b \<leftarrow> coin_spmf;
    return_spmf (b, \<^bold>g [^] (x * y) \<in> s)
  }
}" for x y

text \<open>
It is easy to prove that @{term game\<^sub>0} combined with the random oracle is a projection of @{term game\<^sub>1} with the sampling added, as formalized in \<open>game\<^sub>0_game\<^sub>1\<close>.
\<close>
let ?sample = "\<lambda>f :: nat \<Rightarrow> nat \<Rightarrow> _ spmf. do {
   x \<leftarrow> sample_uniform (order \<G>);
   y \<leftarrow> sample_uniform (order \<G>);
   f x y }"
have game\<^sub>0_game\<^sub>1: 
  "run_gpv ro.oracle game\<^sub>0 ro.initial = map_spmf fst (?sample game\<^sub>1)"
  by(simp add: game\<^sub>0 game\<^sub>1_def o_def split_def map_try_spmf map_scale_spmf)

subsection \<open>Game hop based on a failure event\<close>

text \<open>
A game hop based on a failure event changes one game into another such that they behave identically unless the failure event occurs.
The @{thm [source] "fundamental_lemma"} bounds the absolute difference between the two games by the probability of the failure event.
In the running example, we would like to avoid querying the random oracle when encrypting the chosen message.
The next game @{term game\<^sub>2} is identical except that the call to the random oracle @{term ro.oracle} is replaced with sampling a random bitstring.%
\footnote{%
  In Shoup's terminology @{cite Shoup2004IACR}, such a step makes (a gnome sitting inside) the random oracle forgetting the query.
}
\<close>
define game\<^sub>2 :: "nat \<Rightarrow> nat \<Rightarrow> (bool \<times> bool) spmf"
where "game\<^sub>2 x y = do {
  b \<leftarrow> coin_spmf;
  (((m\<^sub>1, m\<^sub>2), \<sigma>), (s, s_h)) \<leftarrow> exec_gpv oracle' (\<A>\<^sub>1 (\<^bold>g [^] x)) ({}, ro.initial);
  TRY do {
    _ :: unit \<leftarrow> assert_spmf (valid_plains m\<^sub>1 m\<^sub>2);
    h \<leftarrow> spmf_of_set (nlists UNIV len_plain);
    \<comment> \<open>We do not query the random oracle for @{term \<open>\<^bold>g [^] (x * y)\<close>}, but instead sample a random bitstring @{term h} directly.
        So the rest differs from @{term game\<^sub>1} only if the adversary queries @{term \<open>\<^bold>g [^] (x * y)\<close>}.\<close>
    let cipher = (\<^bold>g [^] y, h [\<oplus>] (if b then m\<^sub>1 else m\<^sub>2));
    (b', (s', s_h')) \<leftarrow> exec_gpv oracle' (\<A>\<^sub>2 cipher \<sigma>) (s, s_h);
    return_spmf (b' = b, \<^bold>g [^] (x * y) \<in> s')
  } ELSE do {
    b \<leftarrow> coin_spmf;
    return_spmf (b, \<^bold>g [^] (x * y) \<in> s)
  }
}" for x y
text \<open>
To apply the @{thm [source] fundamental_lemma}, we first have to prove that the two games are indeed the same
except when the failure event occurs.
\<close>
have "rel_spmf (\<lambda>(win, bad) (win', bad'). bad = bad' \<and> (\<not> bad' \<longrightarrow> win = win')) (game\<^sub>2 x y) (game\<^sub>1 x y)" for x y
proof -
  text \<open>
  This proof requires two invariants on the state of @{term oracle'}.
  First, @{term "s = dom s_h"}.
  Second, @{term s} only becomes larger.
  The next two statements capture the two invariants:
\<close>
  interpret inv_oracle': callee_invariant_on "oracle'" "(\<lambda>(s, s_h). s = dom s_h)" \<I>_full
    by unfold_locales(auto simp add: oracle'_def split: option.split_asm if_split)
  interpret bad: callee_invariant_on "oracle'" "(\<lambda>(s, _). z \<in> s)" \<I>_full for z
    by unfold_locales(auto simp add: oracle'_def)
  text \<open>
  First, we identify a bisimulation relation \<open>?X\<close> between the different states of @{term oracle'} for the second phase of the game.
  Namely, the invariant @{term "s = dom s_h"} holds, the set of queries are the same, 
  and the random oracle's state (a map from queries to responses) differs only at the point @{term "\<^bold>g [^] (x * y)"}.
  \<close>
  let ?X = "\<lambda>(s, s_h) (s', s_h'). s = dom s_h \<and> s' = s \<and> s_h = s_h'(\<^bold>g [^] (x * y) := None)"
  text \<open>
  Then, we can prove that @{term [source] "?X"} really is a bisimulation for @{term oracle'} except when the failure event occurs.
  The next statement expresses this.
  \<close>
  let ?bad = "\<lambda>(s, s_h). \<^bold>g [^] (x * y) \<in> s"
  let ?R = "(\<lambda>(a, s1') (b, s2'). ?bad s1' = ?bad s2' \<and> (\<not> ?bad s2' \<longrightarrow> a = b \<and> ?X s1' s2'))"
  have bisim: "rel_spmf ?R (oracle' s1 plain) (oracle' s2 plain)"
    if "?X s1 s2" for s1 s2 plain using that
    by(auto split: prod.splits intro!: rel_spmf_bind_reflI simp add: oracle'_def rel_spmf_return_spmf2 fun_upd_twist split: option.split dest!: fun_upd_eqD)
  have inv: "callee_invariant oracle' ?bad"
    \<comment> \<open>Once the failure event has happened, it will not be forgotten any more.\<close>
    by(unfold_locales)(auto simp add: oracle'_def split: option.split_asm)
  text \<open>
  Now we are ready to prove that the two games @{term game\<^sub>1} and @{term game\<^sub>2} are sufficiently similar.
  The Isar proof now switches into an @{command apply} script that manipulates the goal state directly.
  This is sometimes convenient when it would be too cumbersome to spell out every intermediate goal state.
\<close>
  show ?thesis
    unfolding game\<^sub>1_def game\<^sub>2_def
    \<comment> \<open>Peel off the first phase of the game using the structural decomposition rules @{thm [source] rel_spmf_bind_reflI} and @{thm [source] rel_spmf_try_spmf}.\<close>
    apply(clarsimp intro!: rel_spmf_bind_reflI simp del: bind_spmf_const)
    apply(rule rel_spmf_try_spmf)
    subgoal TRY for b m\<^sub>1 m\<^sub>2 \<sigma> s s_h
      apply(rule rel_spmf_bind_reflI)
      \<comment> \<open>Exploit that in the first phase of the game, the set @{term s} of queried strings and the map of the random oracle @{term s_h} are updated in lock step, i.e., @{term "s = dom s_h"}.\<close>
      apply(drule inv_oracle'.exec_gpv_invariant; clarsimp)
      \<comment> \<open>Has the adversary queried the random oracle with @{term "\<^bold>g [^] (x * y)"} during the first phase?\<close>
      apply(cases "\<^bold>g [^] (x * y) \<in> s")
      subgoal True \<comment> \<open>Then the failure event has already happened and there is nothing more to do. 
        We just have to prove that the two games on both sides terminate with the same probability.\<close> 
        by(auto intro!: rel_spmf_bindI1 rel_spmf_bindI2 lossless_exec_gpv[where \<I>=\<I>_full] dest!: bad.exec_gpv_invariant)
      subgoal False \<comment> \<open>Then let's see whether the adversary queries @{term "\<^bold>g [^] (x * y)"} in the second phase.
        Thanks to @{thm [source] ro.fresh}, the call to the random oracle simplifies to sampling a random bitstring.\<close>
        apply(clarsimp iff del: domIff simp add: domIff ro.fresh intro!: rel_spmf_bind_reflI)
        apply(rule rel_spmf_bindI[where R="?R"])
         \<comment> \<open>The lemma @{thm [source] exec_gpv_oracle_bisim_bad_full} lifts the bisimulation for @{term oracle'}
             to the adversary @{term \<A>\<^sub>2} interacting with @{term oracle'}.\<close>
         apply(rule exec_gpv_oracle_bisim_bad_full[OF _ _ bisim inv inv])
        apply(auto simp add: fun_upd_idem)
        done
      done
    subgoal ELSE by(rule rel_spmf_reflI) clarsimp
    done
qed
text \<open>
  Now we can add the sampling of @{term x} and @{term y} in front of @{term game\<^sub>1} and @{term game\<^sub>2},
  apply the @{thm [source] fundamental_lemma}.
\<close>
hence "rel_spmf (\<lambda>(win, bad) (win', bad'). (bad \<longleftrightarrow> bad') \<and> (\<not> bad' \<longrightarrow> win \<longleftrightarrow> win')) (?sample game\<^sub>2) (?sample game\<^sub>1)"
  by(intro rel_spmf_bind_reflI)
hence "\<bar>measure (measure_spmf (?sample game\<^sub>2)) {(win, _). win} - measure (measure_spmf (?sample game\<^sub>1)) {(win, _). win}\<bar>
      \<le> measure (measure_spmf (?sample game\<^sub>2)) {(_, bad). bad}"
  unfolding split_def by(rule fundamental_lemma)
moreover
text \<open>
  The @{thm [source] fundamental_lemma} is written in full generality for arbitrary events, 
  i.e., sets of elementary events.
  But in this formalization, the events of interest (correct guess and failure) are elementary events.
  We therefore transform the above statement to measure the probability of elementary events using @{term spmf}.
\<close>
have "measure (measure_spmf (?sample game\<^sub>2)) {(win, _). win} = spmf (map_spmf fst (?sample game\<^sub>2)) True"
  and "measure (measure_spmf (?sample game\<^sub>1)) {(win, _). win} = spmf (map_spmf fst (?sample game\<^sub>1)) True"
  and "measure (measure_spmf (?sample game\<^sub>2)) {(_, bad). bad} = spmf (map_spmf snd (?sample game\<^sub>2)) True"
  unfolding spmf_conv_measure_spmf measure_map_spmf by(auto simp add: vimage_def split_def)
ultimately have hop12:
  "\<bar>spmf (map_spmf fst (?sample game\<^sub>2)) True - spmf (map_spmf fst (?sample game\<^sub>1)) True\<bar>
  \<le> spmf (map_spmf snd (?sample game\<^sub>2)) True"
  by simp

subsection \<open>Optimistic sampling: the one-time-pad  \label{section:ghop-last}\<close>

text \<open>
This step is based on the one-time-pad, which is an instance of optimistic sampling.
If two runs of the two games in an optimistic sampling step would use the same random bits,
then their results would be different.
However, if the adversary's choices are independent of the random bits, 
we may relate runs that use different random bits, as in the end, only the probabilities have to match.
The previous game hop from @{term game\<^sub>1} to @{term game\<^sub>2} made the oracle's responses in the second phase
independent from the encrypted ciphertext.
So we can now change the bits used for encrypting the chosen message
and thereby make the ciphertext independent of the message.

To that end, we parametrize @{term game\<^sub>2} by the part that does the optimistic sampling
and call this parametrized version @{term game\<^sub>3}.
\<close>
define game\<^sub>3 :: "(bool \<Rightarrow> bitstring \<Rightarrow> bitstring \<Rightarrow> bitstring spmf) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (bool \<times> bool) spmf"
where "game\<^sub>3 f x y = do {
  b \<leftarrow> coin_spmf;
  (((m\<^sub>1, m\<^sub>2), \<sigma>), (s, s_h)) \<leftarrow> exec_gpv oracle' (\<A>\<^sub>1 (\<^bold>g [^] x)) ({}, ro.initial);
  TRY do {
    _ :: unit \<leftarrow> assert_spmf (valid_plains m\<^sub>1 m\<^sub>2);
    h' \<leftarrow> f b m\<^sub>1 m\<^sub>2;
    let cipher = (\<^bold>g [^] y, h');
    (b', (s', s_h')) \<leftarrow> exec_gpv oracle' (\<A>\<^sub>2 cipher \<sigma>) (s, s_h);
    return_spmf (b' = b, \<^bold>g [^] (x * y) \<in> s')
  } ELSE do {
    b \<leftarrow> coin_spmf;
    return_spmf (b, \<^bold>g [^] (x * y) \<in> s)
  }
}" for f x y
text \<open>
Clearly, if we plug in the appropriate function \<open>?f\<close>, then we get @{term game\<^sub>2}:
\<close>
let ?f = "\<lambda>b m\<^sub>1 m\<^sub>2. map_spmf (\<lambda>h. (if b then m\<^sub>1 else m\<^sub>2) [\<oplus>] h) (spmf_of_set (nlists UNIV len_plain))"
have game\<^sub>2_game\<^sub>3: "game\<^sub>2 x y = game\<^sub>3 ?f x y" for x y
  by(simp add: game\<^sub>2_def game\<^sub>3_def Let_def bind_map_spmf xor_list_commute o_def)
text \<open>
CryptHOL's @{thm [source] one_time_pad} lemma now allows us to remove the exclusive or with the chosen message,
because the resulting distributions are the same.
The proof is slightly non-trivial because the one-time-pad lemma holds
only if the xor'ed bitstrings have the right length, which the assertion @{term valid_plains} ensures.
The congruence rules @{thm [source] try_spmf_cong bind_spmf_cong[OF refl] if_cong[OF refl]}
extract this information from the program of the game.
\<close>
let ?f' = "\<lambda>b m\<^sub>1 m\<^sub>2. spmf_of_set (nlists UNIV len_plain)"
have game\<^sub>3: "game\<^sub>3 ?f x y = game\<^sub>3 ?f' x y" for x y
  by(auto intro!: try_spmf_cong bind_spmf_cong[OF refl] if_cong[OF refl] 
    simp add: game\<^sub>3_def split_def one_time_pad valid_plains_def 
    simp del: map_spmf_of_set_inj_on bind_spmf_const split: if_split)

text \<open>
The rest of the proof consists of simplifying @{term [source] "game\<^sub>3 ?f'"}.
The steps are similar to what we have shown before, so we do not explain them in detail.
The interested reader can look at them in the theory file from which this document was generated.
At a high level, we see that there is no need to track the adversary's queries in @{term game\<^sub>2} or @{term game\<^sub>3} any more
because this information is already stored in the random oracle's state.
So we change the @{term oracle'} back into @{term ro.oracle} using the Transfer package.
With a bit of rewriting, the result is then the @{term lcdh.game} for the adversary @{term "elgamal_reduction \<A>"}.
Moreover, the guess @{term b'} of the adversary is independent of @{term b} in @{term [source] "game\<^sub>3 ?f"}, 
so the first boolean returned by @{term [source] "game\<^sub>3 ?f'"} is just a coin flip.
\<close>
have game\<^sub>3_bad: "map_spmf snd (?sample (game\<^sub>3 ?f')) = lcdh.game (elgamal_reduction \<A>)"
proof %invisible -
  define bisim where "bisim = (\<lambda>\<sigma> (s :: 'grp set, \<sigma>' :: 'grp \<rightharpoonup> bitstring). s = dom \<sigma> \<and> \<sigma> = \<sigma>')"
  have [transfer_rule]: "bisim Map_empty ({}, Map_empty)" by(simp add: bisim_def)
  have [transfer_rule]: "(bisim ===> (=) ===> rel_spmf (rel_prod (=) bisim)) ro.oracle oracle'"
    by(auto simp add: oracle'_def split_def spmf_rel_map ro.oracle_def rel_fun_def bisim_def split: option.split intro!: rel_spmf_bind_reflI)
  have * [transfer_rule]: "(bisim ===> (=)) dom fst" by(simp add: bisim_def rel_fun_def)
  have * [transfer_rule]: "(bisim ===> (=)) (\<lambda>x. x) snd" by(simp add: rel_fun_def bisim_def)
  have "game\<^sub>3 ?f' x y = do {
    b \<leftarrow> coin_spmf;
    (((msg1, msg2), \<sigma>), s) \<leftarrow> exec_gpv ro.oracle (\<A>\<^sub>1 (\<^bold>g [^] x)) ro.initial;
    TRY do {
      _ :: unit \<leftarrow> assert_spmf (valid_plains msg1 msg2);
      h' \<leftarrow> spmf_of_set (nlists UNIV len_plain);
      let cipher = (\<^bold>g [^] y, h');
      (b', s') \<leftarrow> exec_gpv ro.oracle (\<A>\<^sub>2 cipher \<sigma>) s;
      return_spmf (b' = b, \<^bold>g [^] (x * y) \<in> dom s')
    } ELSE do {
      b \<leftarrow> coin_spmf;
      return_spmf (b, \<^bold>g [^] (x * y) \<in> dom s)
    }
  }" for x y
    unfolding game\<^sub>3_def Map_empty_def[symmetric] split_def fst_conv snd_conv prod.collapse
    by(transfer fixing: \<G> len_plain x y) simp
  moreover have "map_spmf snd (\<dots> x y) = do {
      zs \<leftarrow> elgamal_reduction \<A> (\<^bold>g [^] x) (\<^bold>g [^] y);
      return_spmf (\<^bold>g [^] (x * y) \<in> zs)
    }" for x y
    by(simp add: o_def split_def map_try_spmf map_scale_spmf)
      (simp add: o_def map_try_spmf map_scale_spmf map_spmf_conv_bind_spmf[symmetric] spmf.map_comp map_const_spmf_of_set)
  ultimately show ?thesis by(simp add: o_def lcdh.game_def Let_def lcdh.nat_pow_pow) 
qed
have game\<^sub>3_guess: "map_spmf fst (game\<^sub>3 ?f' x y) = coin_spmf" for x y
proof %invisible -
  have "map_spmf fst (game\<^sub>3 ?f' x y) = do {
    (((msg1, msg2), \<sigma>), (s, s_h)) \<leftarrow> exec_gpv oracle' (\<A>\<^sub>1 (\<^bold>g [^] x)) ({}, ro.initial);
    TRY do {
      _ :: unit \<leftarrow> assert_spmf (valid_plains msg1 msg2);
      h' \<leftarrow> spmf_of_set (nlists UNIV len_plain);
      (b', (s', s_h')) \<leftarrow> exec_gpv oracle' (\<A>\<^sub>2 (\<^bold>g [^] y, h') \<sigma>) (s, s_h);
      map_spmf ((=) b') coin_spmf
    } ELSE coin_spmf
  }" for x y 
    including monad_normalisation
    by(simp add: game\<^sub>3_def o_def split_def map_spmf_conv_bind_spmf try_spmf_bind_out weight_spmf_le_1 scale_bind_spmf try_spmf_bind_out1 bind_scale_spmf)
  then show ?thesis
    by(simp add: o_def if_distribs spmf.map_comp map_eq_const_coin_spmf split_def)
qed

subsection \<open>Combining several game hops \label{section:combining:hops}\<close>

text \<open>
Finally, we combine all the (in)equalities of the previous steps to obtain the desired bound
using the lemmas for reasoning about reals from Isabelle's library.
\<close>
have "ind_cpa.advantage (ro.oracle, ro.initial) \<A> = \<bar>spmf (map_spmf fst (?sample game\<^sub>1)) True - 1 / 2\<bar>"
  using ind_cpa_game_eq_game\<^sub>0 by(simp add: game\<^sub>0_game\<^sub>1 o_def)
also have "\<dots> = \<bar>1 / 2 - spmf (map_spmf fst (?sample game\<^sub>1)) True\<bar>"
  by(simp add: abs_minus_commute)
also have "1 / 2 = spmf (map_spmf fst (?sample game\<^sub>2)) True"
  by(simp add: game\<^sub>2_game\<^sub>3 game\<^sub>3 o_def game\<^sub>3_guess spmf_of_set)
also have "\<bar>\<dots> - spmf (map_spmf fst (?sample game\<^sub>1)) True\<bar> \<le> spmf (map_spmf snd (?sample game\<^sub>2)) True" 
  by(rule hop12)
also have "\<dots> = lcdh.advantage (elgamal_reduction \<A>)"
  by(simp add: game\<^sub>2_game\<^sub>3 game\<^sub>3 game\<^sub>3_bad lcdh.advantage_def o_def del: map_bind_spmf)
finally show ?thesis .
text \<open>
This completes the concrete proof and we can end the locale @{locale hashed_elgamal}.
\<close>
qed

end

section \<open>Asymptotic security \label{section:asymptotic}\<close>

text \<open>
An asymptotic security statement can be easily derived from a concrete security theorem.
This is done in two steps:
First, we have to introduce a security parameter @{term \<eta>} into the definitions and assumptions.
Only then can we state asymptotic security.
The proof is easy given the concrete security theorem.
\<close>

subsection \<open>Introducing a security parameter\<close>

text \<open>
Since all our definitions were done in locales, it is easy to introduce a security parameter after the fact.
To that end, we define copies of all locales where their parameters now take the security parameter as an additional argument.
We illustrate it for the locale @{locale ind_cpa_pk}.

The @{command sublocale} command brings all the definitions and theorems of the original @{locale ind_cpa_pk} into the copy and adds the security parameter where necessary.
The type @{typ security} is a synonym for @{typ nat}.
\<close>
locale ind_cpa_pk' = 
  fixes key_gen :: "security \<Rightarrow> ('pubkey \<times> 'privkey, 'query, 'response) gpv" 
    and encrypt :: "security \<Rightarrow> 'pubkey \<Rightarrow> 'plain \<Rightarrow> ('cipher, 'query, 'response) gpv" 
    and decrypt :: "security \<Rightarrow> 'privkey \<Rightarrow> 'cipher \<Rightarrow> ('plain, 'query, 'response) gpv"
    and valid_plains :: "security \<Rightarrow> 'plain \<Rightarrow> 'plain \<Rightarrow> bool"
begin
sublocale ind_cpa_pk "key_gen \<eta>" "encrypt \<eta>" "decrypt \<eta>" "valid_plains \<eta>" for \<eta> .
end

locale %invisible list_cdh' = 
  fixes \<G> :: "security \<Rightarrow> 'grp cyclic_group"
  assumes cyclic_group: "cyclic_group (\<G> \<eta>)"
begin
sublocale %invisible cyclic_group "\<G> \<eta>" for \<eta> by(fact cyclic_group)
end %invisible

locale %invisible random_oracle' =
  fixes len :: "security \<Rightarrow> nat" 
begin
sublocale %invisible random_oracle "len \<eta>" for \<eta> .
end %invisible

lemma %invisible (in ind_cpa_pk) advantage_nonneg: "advantage oracle \<A> \<ge> 0"
by(cases "oracle"; simp)

lemma %invisible (in list_cdh) advantage_nonneg: "advantage \<A> \<ge> 0"
by(simp add: advantage_def)

text \<open>
We do so similarly for @{locale list_cdh}, @{locale random_oracle}, and @{locale hashed_elgamal}.
\<close>

locale hashed_elgamal' =
  lcdh: list_cdh' \<G> +
  ro: random_oracle' len_plain
  for \<G> :: "security \<Rightarrow> 'grp cyclic_group"
  and len_plain :: "security \<Rightarrow> nat"
begin
sublocale hashed_elgamal "\<G> \<eta>" "len_plain \<eta>" for \<eta> ..

subsection \<open>Asymptotic security statements \label{section:security:asymptotic}\<close>

text \<open>
For asymptotic security statements, \CryptHOL{} defines the predicate @{term negligible}.
It states that the given real-valued function approaches 0 faster than the inverse of any polynomial.
A concrete security statement translates into an asymptotic one as follows:
\begin{itemize}
\item All advantages in the bound become negligibility assumptions.
\item All side conditions of the concrete security theorems remain assumptions, but wrapped into an @{term eventually} statement.
  This expresses that the side condition holds eventually, i.e., there is a security parameter from which on it holds.
\item The conclusion is that the bounded advantage is @{term negligible}.
\end{itemize}
\<close>
theorem asymptotic_security_elgamal:
  assumes "negligible (\<lambda>\<eta>. lcdh.advantage \<eta> (elgamal_reduction \<eta> (\<A> \<eta>)))"
    and "eventually (\<lambda>\<eta>. ind_cpa.lossless (\<A> \<eta>)) at_top"
  shows "negligible (\<lambda>\<eta>. ind_cpa.advantage \<eta> (ro.oracle \<eta>, ro.initial) (\<A> \<eta>))"
text \<open>
The proof is canonical, too:
Using the lemmas about @{term negligible} and Eberl's library for asymptotic reasoning~\cite{Eberl2015},
we transform the asymptotic statement into a concrete one and then simply use the concrete security statement.
\<close>
apply(rule negligible_mono[OF assms(1)])
apply(rule landau_o.big_mono)
apply(rule eventually_rev_mp[OF assms(2)])
apply(intro eventuallyI impI)
apply(simp del: ind_cpa.advantage.simps add: ind_cpa.advantage_nonneg lcdh.advantage_nonneg)
by(rule concrete_security_elgamal)

end

end %invisible
