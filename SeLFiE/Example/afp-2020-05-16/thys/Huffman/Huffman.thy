(*  Title:       An Isabelle/HOL Formalization of the Textbook Proof of Huffman's Algorithm
    Author:      Jasmin Christian Blanchette <blanchette at in.tum.de>, 2008
    Maintainer:  Jasmin Christian Blanchette <blanchette at in.tum.de>
*)

(*<*)
theory Huffman
imports Main
begin
(*>*)

section \<open>Introduction\<close>

subsection \<open>Binary Codes \label{binary-codes}\<close>

text \<open>
Suppose we want to encode strings over a finite source alphabet to sequences
of bits. The approach used by ASCII and most other charsets is to map each
source symbol to a distinct $k$-bit code word, where $k$ is fixed and is
typically 8 or 16. To encode a string of symbols, we simply encode each symbol
in turn. Decoding involves mapping each $k$-bit block back to the symbol it
represents.

Fixed-length codes are simple and fast, but they generally waste space. If
we know the frequency $w_a$ of each source symbol $a$, we can save space
by using shorter code words for the most frequent symbols. We
say that a (variable-length) code is {\sl optimum\/} if it minimizes the sum
$\sum_a w_a \vthinspace\delta_a$, where $\delta_a$ is the length of the binary
code word for $a$. Information theory tells us that a code is optimum if
for each source symbol $c$ the code word representing $c$ has length
$$\textstyle \delta_c = \log_2 {1 \over p_c}, \qquad
  \hbox{where}\enskip p_c = {w_c \over \sum_a w_a}.$$
This number is generally not an integer, so we cannot use it directly.
Nonetheless, the above criterion is a useful yardstick and paves the way for
arithmetic coding \cite{rissanen-1976}, a generalization of the method
presented here.

\def\xabacabad{\xa\xb\xa\xc\xa\xb\xa\xd}%
As an example, consider the source string `$\xabacabad$'. We have
$$p_{\xa} = \tfrac{1}{2},\,\; p_{\xb} = \tfrac{1}{4},\,\;
  p_{\xc} = \tfrac{1}{8},\,\; p_{\xd} = \tfrac{1}{8}.$$
The optimum lengths for the binary code words are all integers, namely
$$\delta_{\xa} = 1,\,\; \delta_{\xb} = 2,\,\; \delta_{\xc} = 3,\,\;
  \delta_{\xd} = 3,$$
and they are realized by the code
$$C_1 = \{ \xa \mapsto 0,\, \xb \mapsto 10,\, \xc \mapsto 110,\,
           \xd \mapsto 111 \}.$$
Encoding `$\xabacabad$' produces the 14-bit code word 01001100100111. The code
$C_1$ is optimum: No code that unambiguously encodes source symbols one at a
time could do better than $C_1$ on the input `$\xa\xb\xa\xc\xa\xb\xa\xd$'. In
particular, with a fixed-length code such as
$$C_2 = \{ \xa \mapsto 00,\, \xb \mapsto 01,\, \xc \mapsto 10,\,
           \xd \mapsto 11 \}$$
we need at least 16~bits to encode `$\xabacabad$'.
\<close>

subsection \<open>Binary Trees\<close>

text \<open>
Inside a program, binary codes can be represented by binary trees. For example,
the trees\strut
$$\vcenter{\hbox{\includegraphics[scale=1.25]{tree-abcd-unbalanced.pdf}}}
  \qquad \hbox{and} \qquad
  \vcenter{\hbox{\includegraphics[scale=1.25]{tree-abcd-balanced.pdf}}}$$
correspond to $C_1$ and $C_2$. The code word for a given
symbol can be obtained as follows: Start at the root and descend toward the leaf
node associated with the symbol one node at a time; generate a 0 whenever the
left child of the current node is chosen and a 1 whenever the right child is
chosen. The generated sequence of 0s and 1s is the code word.

To avoid ambiguities, we require that only leaf nodes are labeled with symbols.
This ensures that no code word is a prefix of another, thereby eliminating the
source of all ambiguities.%
\footnote{Strictly speaking, there is another potential source of ambiguity.
If the alphabet consists of a single symbol $a$, that symbol could be mapped
to the empty code word, and then any string $aa\ldots a$ would map to the
empty bit sequence, giving the decoder no way to recover the original string's
length. This scenario can be ruled out by requiring that the alphabet has
cardinality 2 or more.}
Codes that have this property are called {\sl prefix codes}. As an example of a
code that does not have this property, consider the code associated with the
tree\strut
$$\vcenter{\hbox{\includegraphics[scale=1.25]{tree-abcd-non-prefix.pdf}}}$$
and observe that `$\xb\xb\xb$', `$\xb\xd$', and `$\xd\xb$' all map to the
code word 111.

Each node in a code tree is assigned a {\sl weight}. For a leaf node, the
weight is the frequency of its symbol; for an inner node, it is the sum of the
weights of its subtrees. Code trees can be annotated with their weights:\strut
$$\vcenter{\hbox{\includegraphics[scale=1.25]%
    {tree-abcd-unbalanced-weighted.pdf}}}
  \qquad\qquad
  \vcenter{\hbox{\includegraphics[scale=1.25]%
    {tree-abcd-balanced-weighted.pdf}}}$$
For our purposes, it is sufficient to consider only full binary trees (trees
whose inner nodes all have two children). This is because any inner node with
only one child can advantageously be eliminated; for example,\strut
$$\vcenter{\hbox{\includegraphics[scale=1.25]{tree-abc-non-full.pdf}}}
  \qquad \hbox{becomes} \qquad
  \vcenter{\hbox{\includegraphics[scale=1.25]{tree-abc-full.pdf}}}$$
\<close>

subsection \<open>Huffman's Algorithm\<close>

text \<open>
David Huffman \cite{huffman-1952} discovered a simple algorithm for
constructing an optimum code tree for specified symbol frequencies:
Create a forest consisting of only leaf nodes, one for each symbol in the
alphabet, taking the given symbol frequencies as initial weights for the nodes.
Then pick the two trees
$$\vcenter{\hbox{\includegraphics[scale=1.25]{tree-w1.pdf}}}
  \qquad \hbox{and} \qquad
  \vcenter{\hbox{\includegraphics[scale=1.25]{tree-w2.pdf}}}$$

\noindent\strut
with the lowest weights and replace them with the tree
$$\vcenter{\hbox{\includegraphics[scale=1.25]{tree-w1-w2.pdf}}}$$
Repeat this process until only one tree is left.

As an illustration, executing the algorithm for the frequencies
$$f_{\xd} = 3,\,\; f_{\xe} = 11,\,\; f_{\xf} = 5,\,\; f_{\xs} = 7,\,\;
  f_{\xz} = 2$$
gives rise to the following sequence of states:\strut

\def\myscale{1}%
\setbox\myboxi=\hbox{(9)\strut}%
\setbox\myboxii=\hbox{\includegraphics[scale=\myscale]{tree-prime-step1.pdf}}%
\setbox\myboxiii=\hbox{\includegraphics[scale=\myscale]{tree-prime-step2.pdf}}%
$$(1)\quad\lower\ht\myboxii\hbox{\raise\ht\myboxi\box\myboxii} \qquad\qquad
  (2)\enskip\lower\ht\myboxiii\hbox{\raise\ht\myboxi\box\myboxiii}$$

\vskip.5\smallskipamount

\noindent
\setbox\myboxii=\hbox{\includegraphics[scale=\myscale]{tree-prime-step3.pdf}}%
\setbox\myboxiii=\hbox{\includegraphics[scale=\myscale]{tree-prime-step4.pdf}}%
\setbox\myboxiv=\hbox{\includegraphics[scale=\myscale]{tree-prime-step5.pdf}}%
(3)\quad\lower\ht\myboxii\hbox{\raise\ht\myboxi\box\myboxii}\hfill\quad
  (4)\quad\lower\ht\myboxiii\hbox{\raise\ht\myboxi\box\myboxiii}\hfill
  (5)\enskip\lower\ht\myboxiv\hbox{\raise\ht\myboxi\box\myboxiv\,}

\smallskip
\noindent
Tree~(5) is an optimum tree for the given frequencies.
\<close>

subsection \<open>The Textbook Proof\<close>

text \<open>
Why does the algorithm work? In his article, Huffman gave some motivation but
no real proof. For a proof sketch, we turn to Donald Knuth
\cite[p.~403--404]{knuth-1997}:

\begin{quote}
It is not hard to prove that this method does in fact minimize the weighted
path length (i.e., $\sum_a w_a \vthinspace\delta_a$), by induction on $m$.
Suppose we have $w_1 \le w_2 \le w_3 \le \cdots \le w_m$, where $m \ge 2$, and
suppose that we are given a tree that minimizes the weighted path length.
(Such a tree certainly exists, since only finitely many binary trees with $m$
terminal nodes are possible.) Let $V$ be an internal node of maximum distance
from the root. If $w_1$ and $w_2$ are not the weights already attached to the
children of $V$, we can interchange them with the values that are already
there; such an interchange does not increase the weighted path length. Thus
there is a tree that minimizes the weighted path length and contains the
subtree\strut
$$\vcenter{\hbox{\includegraphics[scale=1.25]{tree-w1-w2-leaves.pdf}}}$$
Now it is easy to prove that the weighted path length of such a tree is
minimized if and only if the tree with
$$\vcenter{\hbox{\includegraphics[scale=1.25]{tree-w1-w2-leaves.pdf}}}
  \qquad \hbox{replaced by} \qquad
  \vcenter{\hbox{\includegraphics[scale=1.25]{tree-w1-plus-w2.pdf}}}$$
has minimum path length for the weights $w_1 + w_2$, $w_3$, $\ldots\,$, $w_m$.
\end{quote}

\noindent
There is, however, a small oddity in this proof: It is not clear why we must
assert the existence of an optimum tree that contains the subtree
$$\vcenter{\hbox{\includegraphics[scale=1.25]{tree-w1-w2-leaves.pdf}}}$$
Indeed, the formalization works without it.

Cormen et al.\ \cite[p.~385--391]{cormen-et-al-2001} provide a very similar
proof, articulated around the following propositions:

\begin{quote}
\textsl{\textbf{Lemma 16.2}} \\
Let $C$ be an alphabet in which each character $c \in C$ has frequency $f[c]$.
Let $x$ and $y$ be two characters in $C$ having the lowest frequencies. Then
there exists an optimal prefix code for $C$ in which the codewords for $x$ and
$y$ have the same length and differ only in the last bit.

\medskip

\textsl{\textbf{Lemma 16.3}} \\
Let $C$ be a given alphabet with frequency $f[c]$ defined for each character
$c \in C$. Let $x$ and $y$ be two characters in $C$ with minimum frequency. Let
$C'$ be the alphabet $C$ with characters $x$, $y$ removed and (new) character
$z$ added, so that $C' = C - \{x, y\} \cup {\{z\}}$; define $f$ for $C'$ as for
$C$, except that $f[z] = f[x] + f[y]$. Let $T'$ be any tree representing an
optimal prefix code for the alphabet $C'$. Then the tree $T$, obtained from
$T'$ by replacing the leaf node for $z$ with an internal node having $x$ and
$y$ as children, represents an optimal prefix code for the alphabet $C$.

\medskip

\textsl{\textbf{Theorem 16.4}} \\
Procedure \textsc{Huffman} produces an optimal prefix code.
\end{quote}
\<close>

subsection \<open>Overview of the Formalization\<close>

text \<open>
This document presents a formalization of the proof of Huffman's algorithm
written using Isabelle/HOL \cite{nipkow-et-al-2008}. Our proof is based on the
informal proofs given by Knuth and Cormen et al. The development was done
independently of Laurent Th\'ery's Coq proof \cite{thery-2003,thery-2004},
which through its ``cover'' concept represents a considerable departure from
the textbook proof.

The development consists of a little under 100 lemmas and theorems. Most of
them have very short proofs thanks to the extensive use of simplification
rules and custom induction rules. The remaining proofs are written using the
structured proof format Isar \cite{wenzel-2008}.
\<close>

subsection \<open>Head of the Theory File\<close>

text \<open>
The Isabelle theory starts in the standard way.

\myskip

\noindent
\isacommand{theory} \<open>Huffman\<close> \\
\isacommand{imports} \<open>Main\<close> \\
\isacommand{begin}

\myskip

\noindent
We attach the \<open>simp\<close> attribute to some predefined lemmas to add them to
the default set of simplification rules.
\<close>

declare
  Int_Un_distrib [simp]
  Int_Un_distrib2 [simp]
  max.absorb1 [simp]
  max.absorb2 [simp]

section \<open>Definition of Prefix Code Trees and Forests \label{trees-and-forests}\<close>

subsection \<open>Tree Type\<close>

text \<open>
A {\sl prefix code tree\/} is a full binary tree in which leaf nodes are of the
form @{term "Leaf w a"}, where @{term a} is a symbol and @{term w} is the
frequency associated with @{term a}, and inner nodes are of the form
@{term "Node w t\<^sub>1 t\<^sub>2"}, where @{term t\<^sub>1} and @{term t\<^sub>2} are the left and
right subtrees and @{term w} caches the sum of the weights of @{term t\<^sub>1} and
@{term t\<^sub>2}. Prefix code trees are polymorphic on the symbol datatype~@{typ 'a}.
\<close>

datatype 'a tree =
  Leaf nat 'a
| Node nat "('a tree)" "('a tree)"

subsection \<open>Forest Type\<close>

text \<open>
The intermediate steps of Huffman's algorithm involve a list of prefix code
trees, or {\sl prefix code forest}.
\<close>

type_synonym 'a forest = "'a tree list"

subsection \<open>Alphabet\<close>

text \<open>
The {\sl alphabet\/} of a code tree is the set of symbols appearing in the
tree's leaf nodes.
\<close>

primrec alphabet :: "'a tree \<Rightarrow> 'a set" where
"alphabet (Leaf w a) = {a}" |
"alphabet (Node w t\<^sub>1 t\<^sub>2) = alphabet t\<^sub>1 \<union> alphabet t\<^sub>2"

text \<open>
For sets and predicates, Isabelle gives us the choice between inductive
definitions (\isakeyword{inductive\_set} and \isakeyword{inductive}) and
recursive functions (\isakeyword{primrec}, \isakeyword{fun}, and
\isakeyword{function}). In this development, we consistently favor recursion
over induction, for two reasons:

\begin{myitemize}
\item Recursion gives rise to simplification rules that greatly help automatic
proof tactics. In contrast, reasoning about inductively defined sets and
predicates involves introduction and elimination rules, which are more clumsy
than simplification rules.

\item Isabelle's counterexample generator \isakeyword{quickcheck}
\cite{berghofer-nipkow-2004}, which we used extensively during the top-down
development of the proof (together with \isakeyword{sorry}), has better support
for recursive definitions.
\end{myitemize}

The alphabet of a forest is defined as the union of the alphabets of the trees
that compose it. Although Isabelle supports overloading for non-overlapping
types, we avoid many type inference problems by attaching an
`\raise.3ex\hbox{\<open>\<^sub>F\<close>}' subscript to the forest generalizations of
functions defined on trees.
\<close>

primrec alphabet\<^sub>F :: "'a forest \<Rightarrow> 'a set" where
"alphabet\<^sub>F [] = {}" |
"alphabet\<^sub>F (t # ts) = alphabet t \<union> alphabet\<^sub>F ts"

text \<open>
Alphabets are central to our proofs, and we need the following basic facts
about them.
\<close>

lemma finite_alphabet[simp]:
"finite (alphabet t)"
by (induct t) auto

lemma exists_in_alphabet:
"\<exists>a. a \<in> alphabet t"
by (induct t) auto

subsection \<open>Consistency\<close>

text \<open>
A tree is {\sl consistent\/} if for each inner node the alphabets of the two
subtrees are disjoint. Intuitively, this means that every symbol in the
alphabet occurs in exactly one leaf node. Consistency is a sufficient condition
for $\delta_a$ (the length of the {\sl unique\/} code word for $a$) to be
defined. Although this well\-formed\-ness property is not mentioned in algorithms
textbooks \cite{aho-et-al-1983,cormen-et-al-2001,knuth-1997}, it is essential
and appears as an assumption in many of our lemmas.
\<close>

primrec consistent :: "'a tree \<Rightarrow> bool" where
"consistent (Leaf w a) = True" |
"consistent (Node w t\<^sub>1 t\<^sub>2) =
 (consistent t\<^sub>1 \<and> consistent t\<^sub>2 \<and> alphabet t\<^sub>1 \<inter> alphabet t\<^sub>2 = {})"

primrec consistent\<^sub>F :: "'a forest \<Rightarrow> bool" where
"consistent\<^sub>F [] = True" |
"consistent\<^sub>F (t # ts) =
 (consistent t \<and> consistent\<^sub>F ts \<and> alphabet t \<inter> alphabet\<^sub>F ts = {})"

text \<open>
Several of our proofs are by structural induction on consistent trees $t$ and
involve one symbol $a$. These proofs typically distinguish the following cases.

\begin{myitemize}
\item[] {\sc Base case:}\enspace $t = @{term "Leaf w b"}$.
\item[] {\sc Induction step:}\enspace $t = @{term "Node w t\<^sub>1 t\<^sub>2"}$.
\item[] \noindent\kern\leftmargin {\sc Subcase 1:}\enspace $a$ belongs to
        @{term t\<^sub>1} but not to @{term t\<^sub>2}.
\item[] \noindent\kern\leftmargin {\sc Subcase 2:}\enspace $a$ belongs to
        @{term t\<^sub>2} but not to @{term t\<^sub>1}.
\item[] \noindent\kern\leftmargin {\sc Subcase 3:}\enspace $a$ belongs to
        neither @{term t\<^sub>1} nor @{term t\<^sub>2}.
\end{myitemize}

\noindent
Thanks to the consistency assumption, we can rule out the subcase where $a$
belongs to both subtrees.

Instead of performing the above case distinction manually, we encode it in a
custom induction rule. This saves us from writing repetitive proof scripts and
helps Isabelle's automatic proof tactics.
\<close>

lemma tree_induct_consistent[consumes 1, case_names base step\<^sub>1 step\<^sub>2 step\<^sub>3]:
"\<lbrakk>consistent t;
  \<And>w\<^sub>b b a. P (Leaf w\<^sub>b b) a;
  \<And>w t\<^sub>1 t\<^sub>2 a.
     \<lbrakk>consistent t\<^sub>1; consistent t\<^sub>2; alphabet t\<^sub>1 \<inter> alphabet t\<^sub>2 = {};
      a \<in> alphabet t\<^sub>1; a \<notin> alphabet t\<^sub>2; P t\<^sub>1 a; P t\<^sub>2 a\<rbrakk> \<Longrightarrow>
     P (Node w t\<^sub>1 t\<^sub>2) a;
  \<And>w t\<^sub>1 t\<^sub>2 a.
     \<lbrakk>consistent t\<^sub>1; consistent t\<^sub>2; alphabet t\<^sub>1 \<inter> alphabet t\<^sub>2 = {};
      a \<notin> alphabet t\<^sub>1; a \<in> alphabet t\<^sub>2; P t\<^sub>1 a; P t\<^sub>2 a\<rbrakk> \<Longrightarrow>
     P (Node w t\<^sub>1 t\<^sub>2) a;
  \<And>w t\<^sub>1 t\<^sub>2 a.
     \<lbrakk>consistent t\<^sub>1; consistent t\<^sub>2; alphabet t\<^sub>1 \<inter> alphabet t\<^sub>2 = {};
      a \<notin> alphabet t\<^sub>1; a \<notin> alphabet t\<^sub>2; P t\<^sub>1 a; P t\<^sub>2 a\<rbrakk> \<Longrightarrow>
     P (Node w t\<^sub>1 t\<^sub>2) a\<rbrakk> \<Longrightarrow>
 P t a"

txt \<open>
The proof relies on the \textit{induction\_schema} and
\textit{lexicographic\_order} tactics, which automate the most tedious
aspects of deriving induction rules. The alternative would have been to perform
a standard structural induction on @{term t} and proceed by cases, which is
straightforward but long-winded.
\<close>

apply rotate_tac
apply induction_schema
       apply atomize_elim
       apply (case_tac t)
        apply fastforce
       apply fastforce
by lexicographic_order

text \<open>
The \textit{induction\_schema} tactic reduces the putative induction rule to
simpler proof obligations.
Internally, it reuses the machinery that constructs the default induction
rules. The resulting proof obligations concern (a)~case completeness,
(b)~invariant preservation (in our case, tree consistency), and
(c)~wellfoundedness. For @{thm [source] tree_induct_consistent}, the obligations
(a)~and (b) can be discharged using
Isabelle's simplifier and classical reasoner, whereas (c) requires a single
invocation of \textit{lexicographic\_order}, a tactic that was originally
designed to prove termination of recursive functions
\cite{bulwahn-et-al-2007,krauss-2007,krauss-2009}.
\<close>

subsection \<open>Symbol Depths\<close>

text \<open>
The {\sl depth\/} of a symbol (which we denoted by $\delta_a$ in
Section~\ref{binary-codes}) is the length of the path from the root to the
leaf node labeled with that symbol, or equivalently the length of the code word
for the symbol. Symbols that do not occur in the tree or that occur at the root
of a one-node tree have depth 0. If a symbol occurs in several leaf nodes (which
may happen with inconsistent trees), the depth is arbitrarily defined in terms
of the leftmost node labeled with that symbol.
\<close>

primrec depth :: "'a tree \<Rightarrow> 'a \<Rightarrow> nat" where
"depth (Leaf w b) a = 0" |
"depth (Node w t\<^sub>1 t\<^sub>2) a =
 (if a \<in> alphabet t\<^sub>1 then depth t\<^sub>1 a + 1
  else if a \<in> alphabet t\<^sub>2 then depth t\<^sub>2 a + 1
  else 0)"

text \<open>
The definition may seem very inefficient from a functional programming
point of view, but it does not matter, because unlike Huffman's algorithm, the
@{const depth} function is merely a reasoning tool and is never actually
executed.
\<close>

subsection \<open>Height\<close>

text \<open>
The {\sl height\/} of a tree is the length of the longest path from the root to
a leaf node, or equivalently the length of the longest code word. This is
readily generalized to forests by taking the maximum of the trees' heights. Note
that a tree has height 0 if and only if it is a leaf node, and that a forest has
height 0 if and only if all its trees are leaf nodes.
\<close>

primrec height :: "'a tree \<Rightarrow> nat" where
"height (Leaf w a) = 0" |
"height (Node w t\<^sub>1 t\<^sub>2) = max (height t\<^sub>1) (height t\<^sub>2) + 1"

primrec height\<^sub>F :: "'a forest \<Rightarrow> nat" where
"height\<^sub>F [] = 0" |
"height\<^sub>F (t # ts) = max (height t) (height\<^sub>F ts)"

text \<open>
The depth of any symbol in the tree is bounded by the tree's height, and there
exists a symbol with a depth equal to the height.
\<close>

lemma depth_le_height:
"depth t a \<le> height t"
by (induct t) auto

lemma exists_at_height:
"consistent t \<Longrightarrow> \<exists>a \<in> alphabet t. depth t a = height t"
proof (induct t)
  case Leaf thus ?case by simp
next
  case (Node w t\<^sub>1 t\<^sub>2)
  note hyps = Node
  let ?t = "Node w t\<^sub>1 t\<^sub>2"
  from hyps obtain b where b: "b \<in> alphabet t\<^sub>1" "depth t\<^sub>1 b = height t\<^sub>1" by auto
  from hyps obtain c where c: "c \<in> alphabet t\<^sub>2" "depth t\<^sub>2 c = height t\<^sub>2" by auto
  let ?a = "if height t\<^sub>1 \<ge> height t\<^sub>2 then b else c"
  from b c have "?a \<in> alphabet ?t" "depth ?t ?a = height ?t"
    using \<open>consistent ?t\<close> by auto
  thus "\<exists>a \<in> alphabet ?t. depth ?t a = height ?t" ..
qed

text \<open>
The following elimination rules help Isabelle's classical prover, notably the
\textit{auto} tactic. They are easy consequences of the inequation
@{thm depth_le_height[no_vars]}.
\<close>

lemma depth_max_heightE_left[elim!]:
"\<lbrakk>depth t\<^sub>1 a = max (height t\<^sub>1) (height t\<^sub>2);
  \<lbrakk>depth t\<^sub>1 a = height t\<^sub>1; height t\<^sub>1 \<ge> height t\<^sub>2\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow>
 P"
by (cut_tac t = t\<^sub>1 and a = a in depth_le_height) simp

lemma depth_max_heightE_right[elim!]:
"\<lbrakk>depth t\<^sub>2 a = max (height t\<^sub>1) (height t\<^sub>2);
  \<lbrakk>depth t\<^sub>2 a = height t\<^sub>2; height t\<^sub>2 \<ge> height t\<^sub>1\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow>
 P"
by (cut_tac t = t\<^sub>2 and a = a in depth_le_height) simp

text \<open>
We also need the following lemma.
\<close>

lemma height_gt_0_alphabet_eq_imp_height_gt_0:
assumes "height t > 0" "consistent t" "alphabet t = alphabet u"
shows "height u > 0"
proof (cases t)
  case Leaf thus ?thesis using assms by simp
next
  case (Node w t\<^sub>1 t\<^sub>2)
  note t = Node
  from exists_in_alphabet obtain b where b: "b \<in> alphabet t\<^sub>1" ..
  from exists_in_alphabet obtain c where c: "c \<in> alphabet t\<^sub>2" ..
  from b c have bc: "b \<noteq> c" using t \<open>consistent t\<close> by fastforce
  show ?thesis
  proof (cases u)
    case Leaf thus ?thesis using b c bc t assms by auto
  next
    case Node thus ?thesis by simp
  qed
qed

subsection \<open>Symbol Frequencies\<close>

text \<open>
The {\sl frequency\/} of a symbol (which we denoted by $w_a$ in
Section~\ref{binary-codes}) is the sum of the weights attached to the
leaf nodes labeled with that symbol. If the tree is consistent, the sum
comprises at most one nonzero term. The frequency is then the weight of the leaf
node labeled with the symbol, or 0 if there is no such node. The generalization
to forests is straightforward.
\<close>

primrec freq :: "'a tree \<Rightarrow> 'a \<Rightarrow> nat" where
"freq (Leaf w a) b = (if b = a then w else 0)" |
"freq (Node w t\<^sub>1 t\<^sub>2) b = freq t\<^sub>1 b + freq t\<^sub>2 b"

primrec freq\<^sub>F :: "'a forest \<Rightarrow> 'a \<Rightarrow> nat" where
"freq\<^sub>F [] b = 0" |
"freq\<^sub>F (t # ts) b = freq t b + freq\<^sub>F ts b"

text \<open>
Alphabet and symbol frequencies are intimately related. Simplification rules
ensure that sums of the form @{term "freq t\<^sub>1 a + freq t\<^sub>2 a"} collapse to a
single term when we know which tree @{term a} belongs to.
\<close>

lemma notin_alphabet_imp_freq_0[simp]:
"a \<notin> alphabet t \<Longrightarrow> freq t a = 0"
by (induct t) simp+

lemma notin_alphabet\<^sub>F_imp_freq\<^sub>F_0[simp]:
"a \<notin> alphabet\<^sub>F ts \<Longrightarrow> freq\<^sub>F ts a = 0"
by (induct ts) simp+

lemma freq_0_right[simp]:
"\<lbrakk>alphabet t\<^sub>1 \<inter> alphabet t\<^sub>2 = {}; a \<in> alphabet t\<^sub>1\<rbrakk> \<Longrightarrow> freq t\<^sub>2 a = 0"
by (auto intro: notin_alphabet_imp_freq_0 simp: disjoint_iff_not_equal)

lemma freq_0_left[simp]:
"\<lbrakk>alphabet t\<^sub>1 \<inter> alphabet t\<^sub>2 = {}; a \<in> alphabet t\<^sub>2\<rbrakk> \<Longrightarrow> freq t\<^sub>1 a = 0"
by (auto simp: disjoint_iff_not_equal)

text \<open>
Two trees are {\em comparable} if they have the same alphabet and symbol
frequencies. This is an important concept, because it allows us to state not
only that the tree constructed by Huffman's algorithm is optimal but also that
it has the expected alphabet and frequencies.

We close this section with a more technical lemma.
\<close>

lemma height\<^sub>F_0_imp_Leaf_freq\<^sub>F_in_set:
"\<lbrakk>consistent\<^sub>F ts; height\<^sub>F ts = 0; a \<in> alphabet\<^sub>F ts\<rbrakk> \<Longrightarrow>
 Leaf (freq\<^sub>F ts a) a \<in> set ts"
proof (induct ts)
  case Nil thus ?case by simp
next
  case (Cons t ts) show ?case using Cons by (cases t) auto
qed

subsection \<open>Weight\<close>

text \<open>
The @{term weight} function returns the weight of a tree. In the
@{const Node} case, we ignore the weight cached in the node and instead
compute the tree's weight recursively. This makes reasoning simpler because we
can then avoid specifying cache correctness as an assumption in our lemmas.
\<close>

primrec weight :: "'a tree \<Rightarrow> nat" where
"weight (Leaf w a) = w" |
"weight (Node w t\<^sub>1 t\<^sub>2) = weight t\<^sub>1 + weight t\<^sub>2"

text \<open>
The weight of a tree is the sum of the frequencies of its symbols.

\myskip

\noindent
\isacommand{lemma} \<open>weight_eq_Sum_freq\<close>: \\
{\isachardoublequoteopen}$\displaystyle \<open>consistent t \<Longrightarrow> weight t\<close> =
\!\!\sum_{a\in @{term "alphabet t"}}^{\phantom{.}}\!\! @{term "freq t a"}$%
{\isachardoublequoteclose}

\vskip-\myskipamount
\<close>

(*<*)
lemma weight_eq_Sum_freq:
"consistent t \<Longrightarrow> weight t = (\<Sum>a \<in> alphabet t. freq t a)"
(*>*)
by (induct t) (auto simp: sum.union_disjoint)

text \<open>
The assumption @{term "consistent t"} is not necessary, but it simplifies the
proof by letting us invoke the lemma @{thm [source] sum.union_disjoint}:
$$\<open>\<lbrakk>finite A; finite B; A \<inter> B = {}\<rbrakk> \<Longrightarrow>\<close>~\!\sum_{x\in A} @{term "g x"}
\vthinspace \mathrel{+} \sum_{x\in B} @{term "g x"}\vthinspace = %
 \!\!\sum_{x\in A \cup B}\! @{term "g x"}.$$
\<close>

subsection \<open>Cost\<close>

text \<open>
The {\sl cost\/} of a consistent tree, sometimes called the {\sl weighted path
length}, is given by the sum $\sum_{a \in @{term "alphabet t"}\,}
@{term "freq t a"} \mathbin{\<open>*\<close>} @{term "depth t a"}$
(which we denoted by $\sum_a w_a \vthinspace\delta_a$ in
Section~\ref{binary-codes}). It obeys a simple recursive law.
\<close>

primrec cost :: "'a tree \<Rightarrow> nat" where
"cost (Leaf w a) = 0" |
"cost (Node w t\<^sub>1 t\<^sub>2) = weight t\<^sub>1 + cost t\<^sub>1 + weight t\<^sub>2 + cost t\<^sub>2"

text \<open>
One interpretation of this recursive law is that the cost of a tree is the sum
of the weights of its inner nodes \cite[p.~405]{knuth-1997}. (Recall that
$@{term "weight (Node w t\<^sub>1 t\<^sub>2)"} = @{term "weight t\<^sub>1 + weight t\<^sub>2"}$.) Since
the cost of a tree is such a fundamental concept, it seems necessary to prove
that the above function definition is correct.

\myskip

\noindent
\isacommand{theorem} \<open>cost_eq_Sum_freq_mult_depth\<close>: \\
{\isachardoublequoteopen}$\displaystyle \<open>consistent t \<Longrightarrow> cost t\<close> =
\!\!\sum_{a\in @{term "alphabet t"}}^{\phantom{.}}\!\!
@{term "freq t a * depth t a"}$%
{\isachardoublequoteclose}

\myskip

\noindent
The proof is by structural induction on $t$. If $t = @{term "Leaf w b"}$, both
sides of the equation simplify to 0. This leaves the case $@{term t} =
@{term "Node w t\<^sub>1 t\<^sub>2"}$. Let $A$, $A_1$, and $A_2$ stand for
@{term "alphabet t"}, @{term "alphabet t\<^sub>1"}, and @{term "alphabet t\<^sub>2"},
respectively. We have
%
$$\begin{tabularx}{\textwidth}{@%
{\hskip\leftmargin}cX@%
{}}
    & @{term "cost t"} \\
\eq & \justif{definition of @{const cost}} \\
    & $@{term "weight t\<^sub>1 + cost t\<^sub>1 + weight t\<^sub>2 + cost t\<^sub>2"}$ \\
\eq & \justif{induction hypothesis} \\
    & $@{term "weight t\<^sub>1"} \mathrel{+}
       \sum_{a\in A_1\,} @{term "freq t\<^sub>1 a * depth t\<^sub>1 a"} \mathrel{+} {}$ \\
    & $@{term "weight t\<^sub>2"} \mathrel{+}
       \sum_{a\in A_2\,} @{term "freq t\<^sub>2 a * depth t\<^sub>2 a"}$ \\
\eq & \justif{definition of @{const depth}, consistency} \\[\extrah]
    & $@{term "weight t\<^sub>1"} \mathrel{+}
       \sum_{a\in A_1\,} @{term "freq t\<^sub>1 a * (depth t a - 1)"} \mathrel{+}
       {}$ \\
    & $@{term "weight t\<^sub>2"} \mathrel{+}
       \sum_{a\in A_2\,} @{term "freq t\<^sub>2 a * (depth t a - 1)"}$ \\[\extrah]
\eq & \justif{distributivity of \<open>*\<close> and $\sum$ over $-$} \\[\extrah]
    & $@{term "weight t\<^sub>1"} \mathrel{+}
       \sum_{a\in A_1\,} @{term "freq t\<^sub>1 a * depth t a"} \mathrel{-}
       \sum_{a\in A_1\,} @{term "freq t\<^sub>1 a"} \mathrel{+} {}$ \\
    & $@{term "weight t\<^sub>2"} \mathrel{+}
       \sum_{a\in A_2\,} @{term "freq t\<^sub>2 a * depth t a"} \mathrel{-}
       \sum_{a\in A_2\,} @{term "freq t\<^sub>2 a"}$ \\[\extrah]
\eq & \justif{@{thm [source] weight_eq_Sum_freq}} \\[\extrah]
    & $\sum_{a\in A_1\,} @{term "freq t\<^sub>1 a * depth t a"} \mathrel{+}
       \sum_{a\in A_2\,} @{term "freq t\<^sub>2 a * depth t a"}$ \\[\extrah]
\eq & \justif{definition of @{const freq}, consistency} \\[\extrah]
    & $\sum_{a\in A_1\,} @{term "freq t a * depth t a"} \mathrel{+}
       \sum_{a\in A_2\,} @{term "freq t a * depth t a"}$ \\[\extrah]
\eq & \justif{@{thm [source] sum.union_disjoint}, consistency} \\
    & $\sum_{a\in A_1\cup A_2\,} @{term "freq t a * depth t a"}$ \\
\eq & \justif{definition of @{const alphabet}} \\
    & $\sum_{a\in A\,} @{term "freq t a * depth t a"}$.
\end{tabularx}$$

\noindent
The structured proof closely follows this argument.
\<close>

(*<*)
theorem cost_eq_Sum_freq_mult_depth:
"consistent t \<Longrightarrow> cost t = (\<Sum>a \<in> alphabet t. freq t a * depth t a)"
(*>*)
proof (induct t)
  case Leaf thus ?case by simp
next
  case (Node w t\<^sub>1 t\<^sub>2)
  let ?t = "Node w t\<^sub>1 t\<^sub>2"
  let ?A = "alphabet ?t" and ?A\<^sub>1 = "alphabet t\<^sub>1" and ?A\<^sub>2 = "alphabet t\<^sub>2"
  note c = \<open>consistent ?t\<close>
  note hyps = Node
  have d\<^sub>2: "\<And>a. \<lbrakk>?A\<^sub>1 \<inter> ?A\<^sub>2 = {}; a \<in> ?A\<^sub>2\<rbrakk> \<Longrightarrow> depth ?t a = depth t\<^sub>2 a + 1"
    by auto
  have "cost ?t = weight t\<^sub>1 + cost t\<^sub>1 + weight t\<^sub>2 + cost t\<^sub>2" by simp
  also have "\<dots> = weight t\<^sub>1 + (\<Sum>a \<in> ?A\<^sub>1. freq t\<^sub>1 a * depth t\<^sub>1 a)
    + weight t\<^sub>2 + (\<Sum>a \<in> ?A\<^sub>2. freq t\<^sub>2 a * depth t\<^sub>2 a)"
    using hyps by simp
  also have "\<dots> = weight t\<^sub>1 + (\<Sum>a \<in> ?A\<^sub>1. freq t\<^sub>1 a * (depth ?t a - 1))
    + weight t\<^sub>2 + (\<Sum>a \<in> ?A\<^sub>2. freq t\<^sub>2 a * (depth ?t a - 1))"
    using c d\<^sub>2 by simp
  also have "\<dots> = weight t\<^sub>1 + (\<Sum>a \<in> ?A\<^sub>1. freq t\<^sub>1 a * depth ?t a)
    - (\<Sum>a \<in> ?A\<^sub>1. freq t\<^sub>1 a)
    + weight t\<^sub>2 + (\<Sum>a \<in> ?A\<^sub>2. freq t\<^sub>2 a * depth ?t a)
    - (\<Sum>a \<in> ?A\<^sub>2. freq t\<^sub>2 a)"
    using c d\<^sub>2 by (simp add: sum.distrib)
  also have "\<dots> = (\<Sum>a \<in> ?A\<^sub>1. freq t\<^sub>1 a * depth ?t a)
    + (\<Sum>a \<in> ?A\<^sub>2. freq t\<^sub>2 a * depth ?t a)"
    using c by (simp add: weight_eq_Sum_freq)
  also have "\<dots> = (\<Sum>a \<in> ?A\<^sub>1. freq ?t a * depth ?t a)
    + (\<Sum>a \<in> ?A\<^sub>2. freq ?t a * depth ?t a)"
    using c by auto
  also have "\<dots> = (\<Sum>a \<in> ?A\<^sub>1 \<union> ?A\<^sub>2. freq ?t a * depth ?t a)"
    using c by (simp add: sum.union_disjoint)
  also have "\<dots> = (\<Sum>a \<in> ?A. freq ?t a * depth ?t a)" by simp
  finally show ?case .
qed

text \<open>
Finally, it should come as no surprise that trees with height 0 have cost 0.
\<close>

lemma height_0_imp_cost_0[simp]:
"height t = 0 \<Longrightarrow> cost t = 0"
by (case_tac t) simp+

subsection \<open>Optimality\<close>

text \<open>
A tree is optimum if and only if its cost is not greater than that of any
comparable tree. We can ignore inconsistent trees without loss of generality.
\<close>

definition optimum :: "'a tree \<Rightarrow> bool" where
"optimum t =
 (\<forall>u. consistent u \<longrightarrow> alphabet t = alphabet u \<longrightarrow> freq t = freq u \<longrightarrow>
  cost t \<le> cost u)"

section \<open>Functional Implementation of Huffman's Algorithm \label{implementation}\<close>

subsection \<open>Cached Weight\<close>

text \<open>
The {\sl cached weight\/} of a node is the weight stored directly in the node.
Our arguments rely on the computed weight (embodied by the @{const weight}
function) rather than the cached weight, but the implementation of Huffman's
algorithm uses the cached weight for performance reasons.
\<close>

primrec cachedWeight :: "'a tree \<Rightarrow> nat" where
"cachedWeight (Leaf w a) = w" |
"cachedWeight (Node w t\<^sub>1 t\<^sub>2) = w"

text \<open>
The cached weight of a leaf node is identical to its computed weight.
\<close>

lemma height_0_imp_cachedWeight_eq_weight[simp]:
"height t = 0 \<Longrightarrow> cachedWeight t = weight t"
by (case_tac t) simp+

subsection \<open>Tree Union\<close>

text \<open>
The implementation of Huffman's algorithm builds on two additional auxiliary
functions. The first one, \<open>uniteTrees\<close>, takes two trees
$$\vcenter{\hbox{\includegraphics[scale=1.25]{tree-w1.pdf}}}
  \qquad \hbox{and} \qquad
  \vcenter{\hbox{\includegraphics[scale=1.25]{tree-w2.pdf}}}$$

\noindent
and returns the tree\strut
$$\includegraphics[scale=1.25]{tree-w1-w2.pdf}$$

\vskip-.5\myskipamount
\<close>

definition uniteTrees :: "'a tree \<Rightarrow> 'a tree \<Rightarrow> 'a tree" where
"uniteTrees t\<^sub>1 t\<^sub>2 = Node (cachedWeight t\<^sub>1 + cachedWeight t\<^sub>2) t\<^sub>1 t\<^sub>2"

text \<open>
The alphabet, consistency, and symbol frequencies of a united tree are easy to
connect to the homologous properties of the subtrees.
\<close>

lemma alphabet_uniteTrees[simp]:
"alphabet (uniteTrees t\<^sub>1 t\<^sub>2) = alphabet t\<^sub>1 \<union> alphabet t\<^sub>2"
by (simp add: uniteTrees_def)

lemma consistent_uniteTrees[simp]:
"\<lbrakk>consistent t\<^sub>1; consistent t\<^sub>2; alphabet t\<^sub>1 \<inter> alphabet t\<^sub>2 = {}\<rbrakk> \<Longrightarrow>
 consistent (uniteTrees t\<^sub>1 t\<^sub>2)"
by (simp add: uniteTrees_def)

lemma freq_uniteTrees[simp]:
"freq (uniteTrees t\<^sub>1 t\<^sub>2) a = freq t\<^sub>1 a + freq t\<^sub>2 a"
by (simp add: uniteTrees_def)

subsection \<open>Ordered Tree Insertion\<close>

text \<open>
The auxiliary function \<open>insortTree\<close> inserts a tree into a forest sorted
by cached weight, preserving the sort order.
\<close>

primrec insortTree :: "'a tree \<Rightarrow> 'a forest \<Rightarrow> 'a forest" where
"insortTree u [] = [u]" |
"insortTree u (t # ts) =
 (if cachedWeight u \<le> cachedWeight t then u # t # ts else t # insortTree u ts)"

text \<open>
The resulting forest contains one more tree than the original forest. Clearly,
it cannot be empty.
\<close>

lemma length_insortTree[simp]:
"length (insortTree t ts) = length ts + 1"
by (induct ts) simp+

lemma insortTree_ne_Nil[simp]:
"insortTree t ts \<noteq> []"
by (case_tac ts) simp+

text \<open>
The alphabet, consistency, symbol frequencies, and height of a forest after
insertion are easy to relate to the homologous properties of the original
forest and the inserted tree.
\<close>

lemma alphabet\<^sub>F_insortTree[simp]:
"alphabet\<^sub>F (insortTree t ts) = alphabet t \<union> alphabet\<^sub>F ts"
by (induct ts) auto

lemma consistent\<^sub>F_insortTree[simp]:
"consistent\<^sub>F (insortTree t ts) = consistent\<^sub>F (t # ts)"
by (induct ts) auto

lemma freq\<^sub>F_insortTree[simp]:
"freq\<^sub>F (insortTree t ts) = (\<lambda>a. freq t a + freq\<^sub>F ts a)"
by (induct ts) (simp add: ext)+

lemma height\<^sub>F_insortTree[simp]:
"height\<^sub>F (insortTree t ts) = max (height t) (height\<^sub>F ts)"
by (induct ts) auto

subsection \<open>The Main Algorithm\<close>

text \<open>
Huffman's algorithm repeatedly unites the first two trees of the forest it
receives as argument until a single tree is left. It should initially be
invoked with a list of leaf nodes sorted by weight. Note that it is not defined
for the empty list.
\<close>

fun huffman :: "'a forest \<Rightarrow> 'a tree" where
"huffman [t] = t" |
"huffman (t\<^sub>1 # t\<^sub>2 # ts) = huffman (insortTree (uniteTrees t\<^sub>1 t\<^sub>2) ts)"

text \<open>
The time complexity of the algorithm is quadratic in the size of the forest.
If we eliminated the inner node's cached weight component, and instead
recomputed the weight each time it is needed, the complexity would remain
quadratic, but with a larger constant. Using a binary search in @{const
insortTree}, the corresponding imperative algorithm is $O(n \log n)$ if we keep
the weight cache and $O(n^2)$ if we drop it. An $O(n)$ imperative implementation
is possible by maintaining two queues, one containing the unprocessed leaf nodes
and the other containing the combined trees \cite[p.~404]{knuth-1997}.

The tree returned by the algorithm preserves the alphabet, consistency, and
symbol frequencies of the original forest.
\<close>

theorem alphabet_huffman[simp]:
"ts \<noteq> [] \<Longrightarrow> alphabet (huffman ts) = alphabet\<^sub>F ts"
by (induct ts rule: huffman.induct) auto

theorem consistent_huffman[simp]:
"\<lbrakk>consistent\<^sub>F ts; ts \<noteq> []\<rbrakk> \<Longrightarrow> consistent (huffman ts)"
by (induct ts rule: huffman.induct) simp+

theorem freq_huffman[simp]:
"ts \<noteq> [] \<Longrightarrow> freq (huffman ts) a = freq\<^sub>F ts a"
by (induct ts rule: huffman.induct) auto

section \<open>Definition of Auxiliary Functions Used in the Proof \label{auxiliary}\<close>

subsection \<open>Sibling of a Symbol\<close>

text \<open>
The {\sl sibling\/} of a symbol $a$ in a tree $t$ is the label of the node that
is the (left or right) sibling of the node labeled with $a$ in $t$. If the
symbol $a$ is not in $t$'s alphabet or it occurs in a node with no sibling
leaf, we define the sibling as being $a$ itself; this gives us the nice property
that if $t$ is consistent, then $@{term "sibling t a"} \not= a$ if and only if
$a$ has a sibling. As an illustration, we have
$@{term "sibling t a"} = b$,\vthinspace{} $@{term "sibling t b"} = a$,
and $@{term "sibling t c"} = c$ for the tree\strut
$$t \,= \vcenter{\hbox{\includegraphics[scale=1.25]{tree-sibling.pdf}}}$$
\<close>

fun sibling :: "'a tree \<Rightarrow> 'a \<Rightarrow> 'a" where
"sibling (Leaf w\<^sub>b b) a = a" |
"sibling (Node w (Leaf w\<^sub>b b) (Leaf w\<^sub>c c)) a =
     (if a = b then c else if a = c then b else a)" |
"sibling (Node w t\<^sub>1 t\<^sub>2) a =
     (if a \<in> alphabet t\<^sub>1 then sibling t\<^sub>1 a
      else if a \<in> alphabet t\<^sub>2 then sibling t\<^sub>2 a
      else a)"

text \<open>
Because @{const sibling} is defined using sequential pattern matching
\cite{krauss-2007,krauss-2009}, reasoning about it can become tedious.
Simplification rules therefore play an important role.
\<close>

lemma notin_alphabet_imp_sibling_id[simp]:
"a \<notin> alphabet t \<Longrightarrow> sibling t a = a"
by (cases rule: sibling.cases[where x = "(t, a)"]) simp+

lemma height_0_imp_sibling_id[simp]:
"height t = 0 \<Longrightarrow> sibling t a = a"
by (case_tac t) simp+

lemma height_gt_0_in_alphabet_imp_sibling_left[simp]:
"\<lbrakk>height t\<^sub>1 > 0; a \<in> alphabet t\<^sub>1\<rbrakk> \<Longrightarrow>
 sibling (Node w t\<^sub>1 t\<^sub>2) a = sibling t\<^sub>1 a"
by (case_tac t\<^sub>1) simp+

lemma height_gt_0_in_alphabet_imp_sibling_right[simp]:
"\<lbrakk>height t\<^sub>2 > 0; a \<in> alphabet t\<^sub>1\<rbrakk> \<Longrightarrow>
 sibling (Node w t\<^sub>1 t\<^sub>2) a = sibling t\<^sub>1 a"
by (case_tac t\<^sub>2) simp+

lemma height_gt_0_notin_alphabet_imp_sibling_left[simp]:
"\<lbrakk>height t\<^sub>1 > 0; a \<notin> alphabet t\<^sub>1\<rbrakk> \<Longrightarrow>
 sibling (Node w t\<^sub>1 t\<^sub>2) a = sibling t\<^sub>2 a"
by (case_tac t\<^sub>1) simp+

lemma height_gt_0_notin_alphabet_imp_sibling_right[simp]:
"\<lbrakk>height t\<^sub>2 > 0; a \<notin> alphabet t\<^sub>1\<rbrakk> \<Longrightarrow>
 sibling (Node w t\<^sub>1 t\<^sub>2) a = sibling t\<^sub>2 a"
by (case_tac t\<^sub>2) simp+

lemma either_height_gt_0_imp_sibling[simp]:
"height t\<^sub>1 > 0 \<or> height t\<^sub>2 > 0 \<Longrightarrow>
 sibling (Node w t\<^sub>1 t\<^sub>2) a =
     (if a \<in> alphabet t\<^sub>1 then sibling t\<^sub>1 a else sibling t\<^sub>2 a)"
by auto

text \<open>
The following rules are also useful for reasoning about siblings and alphabets.
\<close>

lemma in_alphabet_imp_sibling_in_alphabet:
"a \<in> alphabet t \<Longrightarrow> sibling t a \<in> alphabet t"
by (induct t a rule: sibling.induct) auto

lemma sibling_ne_imp_sibling_in_alphabet:
"sibling t a \<noteq> a \<Longrightarrow> sibling t a \<in> alphabet t"
by (metis notin_alphabet_imp_sibling_id in_alphabet_imp_sibling_in_alphabet)

text \<open>
The default induction rule for @{const sibling} distinguishes four cases.

\begin{myitemize}
\item[] {\sc Base case:}\enskip $t = @{term "Leaf w b"}$.
\item[] {\sc Induction step 1:}\enskip
        $t = @{term "Node w (Leaf w\<^sub>b b) (Leaf w\<^sub>c c)"}$.
\item[] {\sc Induction step 2:}\enskip
        $t = @{term "Node w (Node w\<^sub>1 t\<^sub>1\<^sub>1 t\<^sub>1\<^sub>2) t\<^sub>2"}$.
\item[] {\sc Induction step 3:}\enskip
        $t = @{term "Node w t\<^sub>1 (Node w\<^sub>2 t\<^sub>2\<^sub>1 t\<^sub>2\<^sub>2)"}$.
\end{myitemize}

\noindent
This rule leaves much to be desired. First, the last two cases overlap and
can normally be handled the same way, so they should be combined. Second, the
nested \<open>Node\<close> constructors in the last two cases reduce readability.
Third, under the assumption that $t$ is consistent, we would like to perform
the same case distinction on $a$ as we did for
@{thm [source] tree_induct_consistent}, with the same benefits for automation.
These observations lead us to develop a custom induction rule that
distinguishes the following cases.

\begin{myitemize}
\item[] {\sc Base case:}\enskip $t = @{term "Leaf w b"}$.
\item[] {\sc Induction step 1:}\enskip
        $t = @{term "Node w (Leaf w\<^sub>b b) (Leaf w\<^sub>c c)"}$ with
        @{prop "b \<noteq> c"}.
\item[] \begin{flushleft}
        {\sc Induction step 2:}\enskip
        $t = @{term "Node w t\<^sub>1 t\<^sub>2"}$ and either @{term t\<^sub>1} or @{term t\<^sub>2}
        has nonzero height.
        \end{flushleft}
\item[] \noindent\kern\leftmargin {\sc Subcase 1:}\enspace $a$ belongs to
        @{term t\<^sub>1} but not to @{term t\<^sub>2}.
\item[] \noindent\kern\leftmargin {\sc Subcase 2:}\enspace $a$ belongs to
        @{term t\<^sub>2} but not to @{term t\<^sub>1}.
\item[] \noindent\kern\leftmargin {\sc Subcase 3:}\enspace $a$ belongs to
        neither @{term t\<^sub>1} nor @{term t\<^sub>2}.
\end{myitemize}

The statement of the rule and its proof are similar to what we did for
consistent trees, the main difference being that we now have two induction
steps instead of one.
\<close>

lemma sibling_induct_consistent[consumes 1,
  case_names base step\<^sub>1 step\<^sub>2\<^sub>1 step\<^sub>2\<^sub>2 step\<^sub>2\<^sub>3]:
"\<lbrakk>consistent t;
  \<And>w b a. P (Leaf w b) a;
  \<And>w w\<^sub>b b w\<^sub>c c a. b \<noteq> c \<Longrightarrow> P (Node w (Leaf w\<^sub>b b) (Leaf w\<^sub>c c)) a;
  \<And>w t\<^sub>1 t\<^sub>2 a.
     \<lbrakk>consistent t\<^sub>1; consistent t\<^sub>2; alphabet t\<^sub>1 \<inter> alphabet t\<^sub>2 = {};
      height t\<^sub>1 > 0 \<or> height t\<^sub>2 > 0; a \<in> alphabet t\<^sub>1;
      sibling t\<^sub>1 a \<in> alphabet t\<^sub>1; a \<notin> alphabet t\<^sub>2;
      sibling t\<^sub>1 a \<notin> alphabet t\<^sub>2; P t\<^sub>1 a\<rbrakk> \<Longrightarrow>
     P (Node w t\<^sub>1 t\<^sub>2) a;
  \<And>w t\<^sub>1 t\<^sub>2 a.
     \<lbrakk>consistent t\<^sub>1; consistent t\<^sub>2; alphabet t\<^sub>1 \<inter> alphabet t\<^sub>2 = {};
      height t\<^sub>1 > 0 \<or> height t\<^sub>2 > 0; a \<notin> alphabet t\<^sub>1;
      sibling t\<^sub>2 a \<notin> alphabet t\<^sub>1; a \<in> alphabet t\<^sub>2;
      sibling t\<^sub>2 a \<in> alphabet t\<^sub>2; P t\<^sub>2 a\<rbrakk> \<Longrightarrow>
     P (Node w t\<^sub>1 t\<^sub>2) a;
  \<And>w t\<^sub>1 t\<^sub>2 a.
     \<lbrakk>consistent t\<^sub>1; consistent t\<^sub>2; alphabet t\<^sub>1 \<inter> alphabet t\<^sub>2 = {};
      height t\<^sub>1 > 0 \<or> height t\<^sub>2 > 0; a \<notin> alphabet t\<^sub>1; a \<notin> alphabet t\<^sub>2\<rbrakk> \<Longrightarrow>
     P (Node w t\<^sub>1 t\<^sub>2) a\<rbrakk> \<Longrightarrow>
 P t a"
apply rotate_tac
apply induction_schema
   apply atomize_elim
   apply (case_tac t, simp)
   apply clarsimp
   apply (rename_tac a t\<^sub>1 t\<^sub>2)
   apply (case_tac "height t\<^sub>1 = 0 \<and> height t\<^sub>2 = 0")
    apply simp
    apply (case_tac t\<^sub>1)
     apply (case_tac t\<^sub>2)
      apply fastforce
     apply simp+
   apply (auto intro: in_alphabet_imp_sibling_in_alphabet)[1]
by lexicographic_order

text \<open>
The custom induction rule allows us to prove new properties of @{const sibling}
with little effort.
\<close>

lemma sibling_sibling_id[simp]:
"consistent t \<Longrightarrow> sibling t (sibling t a) = a"
by (induct t a rule: sibling_induct_consistent) simp+

lemma sibling_reciprocal:
"\<lbrakk>consistent t; sibling t a = b\<rbrakk> \<Longrightarrow> sibling t b = a"
by auto

lemma depth_height_imp_sibling_ne:
"\<lbrakk>consistent t; depth t a = height t; height t > 0; a \<in> alphabet t\<rbrakk> \<Longrightarrow>
 sibling t a \<noteq> a"
by (induct t a rule: sibling_induct_consistent) auto

lemma depth_sibling[simp]:
"consistent t \<Longrightarrow> depth t (sibling t a) = depth t a"
by (induct t a rule: sibling_induct_consistent) simp+

subsection \<open>Leaf Interchange\<close>

text \<open>
The \<open>swapLeaves\<close> function takes a tree $t$ together with two symbols
$a$, $b$ and their frequencies $@{term w\<^sub>a}$, $@{term w\<^sub>b}$, and returns the tree
$t$ in which the leaf nodes labeled with $a$ and $b$ are exchanged. When
invoking \<open>swapLeaves\<close>, we normally pass @{term "freq t a"} and
@{term "freq t b"} for @{term w\<^sub>a} and @{term w\<^sub>b}.

Note that we do not bother updating the cached weight of the ancestor nodes
when performing the interchange. The cached weight is used only in the
implementation of Huffman's algorithm, which does not invoke \<open>swapLeaves\<close>.
\<close>

primrec swapLeaves :: "'a tree \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a tree" where
"swapLeaves (Leaf w\<^sub>c c) w\<^sub>a a w\<^sub>b b =
     (if c = a then Leaf w\<^sub>b b else if c = b then Leaf w\<^sub>a a else Leaf w\<^sub>c c)" |
"swapLeaves (Node w t\<^sub>1 t\<^sub>2) w\<^sub>a a w\<^sub>b b =
     Node w (swapLeaves t\<^sub>1 w\<^sub>a a w\<^sub>b b) (swapLeaves t\<^sub>2 w\<^sub>a a w\<^sub>b b)"

text \<open>
Swapping a symbol~$a$ with itself leaves the tree $t$ unchanged if $a$ does not
belong to it or if the specified frequencies @{term w\<^sub>a} and @{term w\<^sub>b} equal
@{term "freq t a"}.
\<close>

lemma swapLeaves_id_when_notin_alphabet[simp]:
"a \<notin> alphabet t \<Longrightarrow> swapLeaves t w a w' a = t"
by (induct t) simp+

lemma swapLeaves_id[simp]:
"consistent t \<Longrightarrow> swapLeaves t (freq t a) a (freq t a) a = t"
by (induct t a rule: tree_induct_consistent) simp+

text \<open>
The alphabet, consistency, symbol depths, height, and symbol frequencies of the
tree @{term "swapLeaves t w\<^sub>a a w\<^sub>b b"} can be related to the homologous
properties of $t$.
\<close>

lemma alphabet_swapLeaves:
"alphabet (swapLeaves t w\<^sub>a a w\<^sub>b b) =
     (if a \<in> alphabet t then
        if b \<in> alphabet t then alphabet t else (alphabet t - {a}) \<union> {b}
      else
        if b \<in> alphabet t then (alphabet t - {b}) \<union> {a} else alphabet t)"
by (induct t) auto

lemma consistent_swapLeaves[simp]:
"consistent t \<Longrightarrow> consistent (swapLeaves t w\<^sub>a a w\<^sub>b b)"
by (induct t) (auto simp: alphabet_swapLeaves)

lemma depth_swapLeaves_neither[simp]:
"\<lbrakk>consistent t; c \<noteq> a; c \<noteq> b\<rbrakk> \<Longrightarrow> depth (swapLeaves t w\<^sub>a a w\<^sub>b b) c = depth t c"
by (induct t a rule: tree_induct_consistent) (auto simp: alphabet_swapLeaves)

lemma height_swapLeaves[simp]:
"height (swapLeaves t w\<^sub>a a w\<^sub>b b) = height t"
by (induct t) simp+

lemma freq_swapLeaves[simp]:
"\<lbrakk>consistent t; a \<noteq> b\<rbrakk> \<Longrightarrow>
 freq (swapLeaves t w\<^sub>a a w\<^sub>b b) =
     (\<lambda>c. if c = a then if b \<in> alphabet t then w\<^sub>a else 0
          else if c = b then if a \<in> alphabet t then w\<^sub>b else 0
          else freq t c)"
apply (rule ext)
apply (induct t)
by auto

text \<open>
For the lemmas concerned with the resulting tree's weight and cost, we avoid
subtraction on natural numbers by rearranging terms. For example, we write
$$@{prop "weight (swapLeaves t w\<^sub>a a w\<^sub>b b) + freq t a = weight t + w\<^sub>b"}$$
\noindent
rather than the more conventional
$$@{prop "weight (swapLeaves t w\<^sub>a a w\<^sub>b b) = weight t + w\<^sub>b - freq t a"}.$$
In Isabelle/HOL, these two equations are not equivalent, because by definition
$m - n = 0$ if $n > m$. We could use the second equation and additionally
assert that @{prop "weight t \<ge> freq t a"} (an easy consequence of
@{thm [source] weight_eq_Sum_freq}), and then apply the \textit{arith}
tactic, but it is much simpler to use the first equation and stay with
\textit{simp} and \textit{auto}. Another option would be to use
integers instead of natural numbers.
\<close>

lemma weight_swapLeaves:
"\<lbrakk>consistent t; a \<noteq> b\<rbrakk> \<Longrightarrow>
 if a \<in> alphabet t then
   if b \<in> alphabet t then
     weight (swapLeaves t w\<^sub>a a w\<^sub>b b) + freq t a + freq t b =
         weight t + w\<^sub>a + w\<^sub>b
   else
     weight (swapLeaves t w\<^sub>a a w\<^sub>b b) + freq t a = weight t + w\<^sub>b
 else
   if b \<in> alphabet t then
     weight (swapLeaves t w\<^sub>a a w\<^sub>b b) + freq t b = weight t + w\<^sub>a
   else
     weight (swapLeaves t w\<^sub>a a w\<^sub>b b) = weight t"
proof (induct t a rule: tree_induct_consistent)
  \<comment> \<open>{\sc Base case:}\enspace $t = @{term "Leaf w b"}$\<close>
  case base thus ?case by clarsimp
next
  \<comment> \<open>{\sc Induction step:}\enspace $t = @{term "Node w t\<^sub>1 t\<^sub>2"}$\<close>
  \<comment> \<open>{\sc Subcase 1:}\enspace $a$ belongs to @{term t\<^sub>1} but not to
        @{term t\<^sub>2}\<close>
  case (step\<^sub>1 w t\<^sub>1 t\<^sub>2 a) show ?case
  proof cases
    assume b: "b \<in> alphabet t\<^sub>1"
    hence "b \<notin> alphabet t\<^sub>2" using step\<^sub>1 by auto
    thus ?case using b step\<^sub>1 by simp
  next
    assume "b \<notin> alphabet t\<^sub>1" thus ?case using step\<^sub>1 by auto
  qed
next
  \<comment> \<open>{\sc Subcase 2:}\enspace $a$ belongs to @{term t\<^sub>2} but not to
        @{term t\<^sub>1}\<close>
  case (step\<^sub>2 w t\<^sub>1 t\<^sub>2 a) show ?case
  proof cases
    assume b: "b \<in> alphabet t\<^sub>1"
    hence "b \<notin> alphabet t\<^sub>2" using step\<^sub>2 by auto
    thus ?case using b step\<^sub>2 by simp
  next
    assume "b \<notin> alphabet t\<^sub>1" thus ?case using step\<^sub>2 by auto
  qed
next
  \<comment> \<open>{\sc Subcase 3:}\enspace $a$ belongs to neither @{term t\<^sub>1} nor
        @{term t\<^sub>2}\<close>
  case (step\<^sub>3 w t\<^sub>1 t\<^sub>2 a) show ?case
  proof cases
    assume b: "b \<in> alphabet t\<^sub>1"
    hence "b \<notin> alphabet t\<^sub>2" using step\<^sub>3 by auto
    thus ?case using b step\<^sub>3 by simp
  next
    assume "b \<notin> alphabet t\<^sub>1" thus ?case using step\<^sub>3 by auto
  qed
qed

lemma cost_swapLeaves:
"\<lbrakk>consistent t; a \<noteq> b\<rbrakk> \<Longrightarrow>
 if a \<in> alphabet t then
   if b \<in> alphabet t then
     cost (swapLeaves t w\<^sub>a a w\<^sub>b b) + freq t a * depth t a
     + freq t b * depth t b =
         cost t + w\<^sub>a * depth t b + w\<^sub>b * depth t a
   else
     cost (swapLeaves t w\<^sub>a a w\<^sub>b b) + freq t a * depth t a =
         cost t + w\<^sub>b * depth t a
 else
   if b \<in> alphabet t then
     cost (swapLeaves t w\<^sub>a a w\<^sub>b b) + freq t b * depth t b =
         cost t + w\<^sub>a * depth t b
   else
     cost (swapLeaves t w\<^sub>a a w\<^sub>b b) = cost t"
proof (induct t)
  case Leaf show ?case by simp
next
  case (Node w t\<^sub>1 t\<^sub>2)
  note c = \<open>consistent (Node w t\<^sub>1 t\<^sub>2)\<close>
  note hyps = Node
  have w\<^sub>1: "if a \<in> alphabet t\<^sub>1 then
              if b \<in> alphabet t\<^sub>1 then
                weight (swapLeaves t\<^sub>1 w\<^sub>a a w\<^sub>b b) + freq t\<^sub>1 a + freq t\<^sub>1 b =
                    weight t\<^sub>1 + w\<^sub>a + w\<^sub>b
                  else
                weight (swapLeaves t\<^sub>1 w\<^sub>a a w\<^sub>b b) + freq t\<^sub>1 a = weight t\<^sub>1 + w\<^sub>b
            else
              if b \<in> alphabet t\<^sub>1 then
                weight (swapLeaves t\<^sub>1 w\<^sub>a a w\<^sub>b b) + freq t\<^sub>1 b = weight t\<^sub>1 + w\<^sub>a
              else
                weight (swapLeaves t\<^sub>1 w\<^sub>a a w\<^sub>b b) = weight t\<^sub>1" using hyps
    by (simp add: weight_swapLeaves)
  have w\<^sub>2: "if a \<in> alphabet t\<^sub>2 then
              if b \<in> alphabet t\<^sub>2 then
                weight (swapLeaves t\<^sub>2 w\<^sub>a a w\<^sub>b b) + freq t\<^sub>2 a + freq t\<^sub>2 b =
                    weight t\<^sub>2 + w\<^sub>a + w\<^sub>b
              else
                weight (swapLeaves t\<^sub>2 w\<^sub>a a w\<^sub>b b) + freq t\<^sub>2 a = weight t\<^sub>2 + w\<^sub>b
            else
              if b \<in> alphabet t\<^sub>2 then
                weight (swapLeaves t\<^sub>2 w\<^sub>a a w\<^sub>b b) + freq t\<^sub>2 b = weight t\<^sub>2 + w\<^sub>a
              else
                weight (swapLeaves t\<^sub>2 w\<^sub>a a w\<^sub>b b) = weight t\<^sub>2" using hyps
    by (simp add: weight_swapLeaves)
  show ?case
  proof cases
    assume a\<^sub>1: "a \<in> alphabet t\<^sub>1"
    hence a\<^sub>2: "a \<notin> alphabet t\<^sub>2" using c by auto
    show ?case
    proof cases
      assume b\<^sub>1: "b \<in> alphabet t\<^sub>1"
      hence "b \<notin> alphabet t\<^sub>2" using c by auto
      thus ?case using a\<^sub>1 a\<^sub>2 b\<^sub>1 w\<^sub>1 w\<^sub>2 hyps by simp
    next
      assume b\<^sub>1: "b \<notin> alphabet t\<^sub>1" show ?case
      proof cases
        assume "b \<in> alphabet t\<^sub>2" thus ?case using a\<^sub>1 a\<^sub>2 b\<^sub>1 w\<^sub>1 w\<^sub>2 hyps by simp
      next
        assume "b \<notin> alphabet t\<^sub>2" thus ?case using a\<^sub>1 a\<^sub>2 b\<^sub>1 w\<^sub>1 w\<^sub>2 hyps by simp
      qed
    qed
  next
    assume a\<^sub>1: "a \<notin> alphabet t\<^sub>1" show ?case
    proof cases
      assume a\<^sub>2: "a \<in> alphabet t\<^sub>2" show ?case
      proof cases
        assume b\<^sub>1: "b \<in> alphabet t\<^sub>1"
        hence "b \<notin> alphabet t\<^sub>2" using c by auto
        thus ?case using a\<^sub>1 a\<^sub>2 b\<^sub>1 w\<^sub>1 w\<^sub>2 hyps by simp
      next
        assume b\<^sub>1: "b \<notin> alphabet t\<^sub>1" show ?case
        proof cases
          assume "b \<in> alphabet t\<^sub>2" thus ?case using a\<^sub>1 a\<^sub>2 b\<^sub>1 w\<^sub>1 w\<^sub>2 hyps by simp
        next
          assume "b \<notin> alphabet t\<^sub>2" thus ?case using a\<^sub>1 a\<^sub>2 b\<^sub>1 w\<^sub>1 w\<^sub>2 hyps by simp
        qed
      qed
    next
      assume a\<^sub>2: "a \<notin> alphabet t\<^sub>2" show ?case
      proof cases
        assume b\<^sub>1: "b \<in> alphabet t\<^sub>1"
        hence "b \<notin> alphabet t\<^sub>2" using c by auto
        thus ?case using a\<^sub>1 a\<^sub>2 b\<^sub>1 w\<^sub>1 w\<^sub>2 hyps by simp
      next
        assume b\<^sub>1: "b \<notin> alphabet t\<^sub>1" show ?case
        proof cases
          assume "b \<in> alphabet t\<^sub>2" thus ?case using a\<^sub>1 a\<^sub>2 b\<^sub>1 w\<^sub>1 w\<^sub>2 hyps by simp
        next
          assume "b \<notin> alphabet t\<^sub>2" thus ?case using a\<^sub>1 a\<^sub>2 b\<^sub>1 w\<^sub>1 w\<^sub>2 hyps by simp
        qed
      qed
    qed
  qed
qed

text \<open>
Common sense tells us that the following statement is valid: ``If Astrid
exchanges her house with Bernard's neighbor, Bernard becomes Astrid's new
neighbor.'' A similar property holds for binary trees.
\<close>

lemma sibling_swapLeaves_sibling[simp]:
"\<lbrakk>consistent t; sibling t b \<noteq> b; a \<noteq> b\<rbrakk> \<Longrightarrow>
 sibling (swapLeaves t w\<^sub>a a w\<^sub>s (sibling t b)) a = b"
proof (induct t)
  case Leaf thus ?case by simp
next
  case (Node w t\<^sub>1 t\<^sub>2)
  note hyps = Node
  show ?case
  proof (cases "height t\<^sub>1 = 0")
    case True
    note h\<^sub>1 = True
    show ?thesis
    proof (cases t\<^sub>1)
      case (Leaf w\<^sub>c c)
      note l\<^sub>1 = Leaf
      show ?thesis
      proof (cases "height t\<^sub>2 = 0")
        case True
        note h\<^sub>2 = True
        show ?thesis
        proof (cases t\<^sub>2)
          case Leaf thus ?thesis using l\<^sub>1 hyps by auto metis+
        next
          case Node thus ?thesis using h\<^sub>2 by simp
        qed
      next
        case False
        note h\<^sub>2 = False
        show ?thesis
        proof cases
          assume "c = b" thus ?thesis using l\<^sub>1 h\<^sub>2 hyps by simp
        next
          assume "c \<noteq> b"
          have "sibling t\<^sub>2 b \<in> alphabet t\<^sub>2" using \<open>c \<noteq> b\<close> l\<^sub>1 h\<^sub>2 hyps
            by (simp add: sibling_ne_imp_sibling_in_alphabet)
          thus ?thesis using \<open>c \<noteq> b\<close> l\<^sub>1 h\<^sub>2 hyps by auto
        qed
      qed
    next
      case Node thus ?thesis using h\<^sub>1 by simp
    qed
  next
    case False
    note h\<^sub>1 = False
    show ?thesis
    proof (cases "height t\<^sub>2 = 0")
      case True
      note h\<^sub>2 = True
      show ?thesis
      proof (cases t\<^sub>2)
        case (Leaf w\<^sub>d d)
        note l\<^sub>2 = Leaf
        show ?thesis
        proof cases
          assume "d = b" thus ?thesis using h\<^sub>1 l\<^sub>2 hyps by simp
        next
          assume "d \<noteq> b" show ?thesis
          proof (cases "b \<in> alphabet t\<^sub>1")
            case True
            hence "sibling t\<^sub>1 b \<in> alphabet t\<^sub>1" using \<open>d \<noteq> b\<close> h\<^sub>1 l\<^sub>2 hyps
              by (simp add: sibling_ne_imp_sibling_in_alphabet)
            thus ?thesis using True \<open>d \<noteq> b\<close> h\<^sub>1 l\<^sub>2 hyps
              by (simp add: alphabet_swapLeaves)
          next
            case False thus ?thesis using \<open>d \<noteq> b\<close> l\<^sub>2 hyps by simp
          qed
        qed
      next
        case Node thus ?thesis using h\<^sub>2 by simp
      qed
    next
      case False
      note h\<^sub>2 = False
      show ?thesis
      proof (cases "b \<in> alphabet t\<^sub>1")
        case True thus ?thesis using h\<^sub>1 h\<^sub>2 hyps by auto
      next
        case False
        note b\<^sub>1 = False
        show ?thesis
        proof (cases "b \<in> alphabet t\<^sub>2")
          case True thus ?thesis using b\<^sub>1 h\<^sub>1 h\<^sub>2 hyps
            by (auto simp: in_alphabet_imp_sibling_in_alphabet
                           alphabet_swapLeaves)
        next
          case False thus ?thesis using b\<^sub>1 h\<^sub>1 h\<^sub>2 hyps by simp
        qed
      qed
    qed
  qed
qed

subsection \<open>Symbol Interchange\<close>

text \<open>
The \<open>swapSyms\<close> function provides a simpler interface to
@{const swapLeaves}, with @{term "freq t a"} and @{term "freq t b"} in place of
@{term "w\<^sub>a"} and @{term "w\<^sub>b"}. Most lemmas about \<open>swapSyms\<close> are directly
adapted from the homologous results about @{const swapLeaves}.
\<close>

definition swapSyms :: "'a tree \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a tree" where
"swapSyms t a b = swapLeaves t (freq t a) a (freq t b) b"

lemma swapSyms_id[simp]:
"consistent t \<Longrightarrow> swapSyms t a a = t"
by (simp add: swapSyms_def)

lemma alphabet_swapSyms[simp]:
"\<lbrakk>a \<in> alphabet t; b \<in> alphabet t\<rbrakk> \<Longrightarrow> alphabet (swapSyms t a b) = alphabet t"
by (simp add: swapSyms_def alphabet_swapLeaves)

lemma consistent_swapSyms[simp]:
"consistent t \<Longrightarrow> consistent (swapSyms t a b)"
by (simp add: swapSyms_def)

lemma depth_swapSyms_neither[simp]:
"\<lbrakk>consistent t; c \<noteq> a; c \<noteq> b\<rbrakk> \<Longrightarrow>
 depth (swapSyms t a b) c = depth t c"
by (simp add: swapSyms_def)

lemma freq_swapSyms[simp]:
"\<lbrakk>consistent t; a \<in> alphabet t; b \<in> alphabet t\<rbrakk> \<Longrightarrow>
 freq (swapSyms t a b) = freq t"
by (case_tac "a = b") (simp add: swapSyms_def ext)+

lemma cost_swapSyms:
assumes "consistent t" "a \<in> alphabet t" "b \<in> alphabet t"
shows "cost (swapSyms t a b) + freq t a * depth t a + freq t b * depth t b =
           cost t + freq t a * depth t b + freq t b * depth t a"
proof cases
  assume "a = b" thus ?thesis using assms by simp
next
  assume "a \<noteq> b"
  hence "cost (swapLeaves t (freq t a) a (freq t b) b)
    + freq t a * depth t a + freq t b * depth t b =
    cost t + freq t a * depth t b + freq t b * depth t a"
    using assms by (simp add: cost_swapLeaves)
  thus ?thesis using assms by (simp add: swapSyms_def)
qed

text \<open>
If $a$'s frequency is lower than or equal to $b$'s, and $a$ is higher up in the
tree than $b$ or at the same level, then interchanging $a$ and $b$ does not
increase the tree's cost.
\<close>

lemma le_le_imp_sum_mult_le_sum_mult:
assumes "i \<le> j" "m \<le> (n::nat)"
shows "i * n + j * m \<le> i * m + j * n"
proof -
  have "i * m + i * (n - m) + j * m \<le> i * m + j * m + j * (n - m)" using assms
    by simp
  thus ?thesis using assms
    by (simp add: diff_mult_distrib2)
qed

lemma cost_swapSyms_le:
assumes "consistent t" "a \<in> alphabet t" "b \<in> alphabet t" "freq t a \<le> freq t b"
        "depth t a \<le> depth t b"
shows "cost (swapSyms t a b) \<le> cost t"
proof -
  let ?aabb = "freq t a * depth t a + freq t b * depth t b"
  let ?abba = "freq t a * depth t b + freq t b * depth t a"
  have "?abba \<le> ?aabb" using assms(4-5)
    by (rule le_le_imp_sum_mult_le_sum_mult)
  have "cost (swapSyms t a b) + ?aabb = cost t + ?abba" using assms(1-3)
    by (simp add: cost_swapSyms add.assoc[THEN sym])
  also have "\<dots> \<le> cost t + ?aabb" using \<open>?abba \<le> ?aabb\<close> by simp
  finally show ?thesis using assms(4-5) by simp
qed

text \<open>
As stated earlier, ``If Astrid exchanges her house with Bernard's neighbor,
Bernard becomes Astrid's new neighbor.''
\<close>

lemma sibling_swapSyms_sibling[simp]:
"\<lbrakk>consistent t; sibling t b \<noteq> b; a \<noteq> b\<rbrakk> \<Longrightarrow>
 sibling (swapSyms t a (sibling t b)) a = b"
by (simp add: swapSyms_def)

text \<open>
``If Astrid exchanges her house with Bernard, Astrid becomes Bernard's old
neighbor's new neighbor.''
\<close>

lemma sibling_swapSyms_other_sibling[simp]:
"\<lbrakk>consistent t; sibling t b \<noteq> a; sibling t b \<noteq> b; a \<noteq> b\<rbrakk> \<Longrightarrow>
 sibling (swapSyms t a b) (sibling t b) = a"
by (metis consistent_swapSyms sibling_swapSyms_sibling sibling_reciprocal)

subsection \<open>Four-Way Symbol Interchange \label{four-way-symbol-interchange}\<close>

text \<open>
The @{const swapSyms} function exchanges two symbols $a$ and $b$. We use it
to define the four-way symbol interchange function \<open>swapFourSyms\<close>, which
takes four symbols $a$, $b$, $c$, $d$ with $a \ne b$ and $c \ne d$, and
exchanges them so that $a$ and $b$ occupy $c$~and~$d$'s positions.

A naive definition of this function would be
$$@{prop "swapFourSyms t a b c d = swapSyms (swapSyms t a c) b d"}.$$
This definition fails in the face of aliasing: If $a = d$, but
$b \ne c$, then \<open>swapFourSyms a b c d\<close> would leave $a$ in $b$'s
position.%
\footnote{Cormen et al.\ \cite[p.~390]{cormen-et-al-2001} forgot to consider
this case in their proof. Thomas Cormen indicated in a personal communication
that this will be corrected in the next edition of the book.}
\<close>

definition swapFourSyms :: "'a tree \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a tree" where
"swapFourSyms t a b c d =
 (if a = d then swapSyms t b c
  else if b = c then swapSyms t a d
  else swapSyms (swapSyms t a c) b d)"

text \<open>
Lemmas about @{const swapFourSyms} are easy to prove by expanding its
definition.
\<close>

lemma alphabet_swapFourSyms[simp]:
"\<lbrakk>a \<in> alphabet t; b \<in> alphabet t; c \<in> alphabet t; d \<in> alphabet t\<rbrakk> \<Longrightarrow>
 alphabet (swapFourSyms t a b c d) = alphabet t"
by (simp add: swapFourSyms_def)

lemma consistent_swapFourSyms[simp]:
"consistent t \<Longrightarrow> consistent (swapFourSyms t a b c d)"
by (simp add: swapFourSyms_def)

lemma freq_swapFourSyms[simp]:
"\<lbrakk>consistent t; a \<in> alphabet t; b \<in> alphabet t; c \<in> alphabet t;
  d \<in> alphabet t\<rbrakk> \<Longrightarrow>
 freq (swapFourSyms t a b c d) = freq t"
by (auto simp: swapFourSyms_def)

text \<open>
``If Astrid and Bernard exchange their houses with Carmen and her neighbor,
Astrid and Bernard will now be neighbors.''
\<close>

lemma sibling_swapFourSyms_when_4th_is_sibling:
assumes "consistent t" "a \<in> alphabet t" "b \<in> alphabet t" "c \<in> alphabet t"
        "a \<noteq> b" "sibling t c \<noteq> c"
shows "sibling (swapFourSyms t a b c (sibling t c)) a = b"
proof (cases "a \<noteq> sibling t c \<and> b \<noteq> c")
  case True show ?thesis
  proof -
    let ?d = "sibling t c"
    let ?t\<^sub>s = "swapFourSyms t a b c ?d"
    have abba: "(sibling ?t\<^sub>s a = b) = (sibling ?t\<^sub>s b = a)" using \<open>consistent t\<close>
      by (metis consistent_swapFourSyms sibling_reciprocal)
    have s: "sibling t c = sibling (swapSyms t a c) a" using True assms
      by (metis sibling_reciprocal sibling_swapSyms_sibling)
    have "sibling ?t\<^sub>s b = sibling (swapSyms t a c) ?d" using s True assms
      by (auto simp: swapFourSyms_def)
    also have "\<dots> = a" using True assms
      by (metis sibling_reciprocal sibling_swapSyms_other_sibling swapLeaves_id swapSyms_def)
    finally have "sibling ?t\<^sub>s b = a" .
    with abba show ?thesis ..
  qed
next
  case False thus ?thesis using assms
    by (auto intro: sibling_reciprocal simp: swapFourSyms_def)
qed

subsection \<open>Sibling Merge\<close>

text \<open>
Given a symbol $a$, the \<open>mergeSibling\<close> function transforms the tree
%
\setbox\myboxi=\hbox{\includegraphics[scale=1.25]{tree-splitLeaf-a.pdf}}%
\setbox\myboxii=\hbox{\includegraphics[scale=1.25]{tree-splitLeaf-ab.pdf}}%
\mydimeni=\ht\myboxii
$$\vcenter{\box\myboxii}
  \qquad \hbox{into} \qquad
  \smash{\lower\ht\myboxi\hbox{\raise.5\mydimeni\box\myboxi}}$$
The frequency of $a$ in the result is the sum of the original frequencies of
$a$ and $b$, so as not to alter the tree's weight.
\<close>

fun mergeSibling :: "'a tree \<Rightarrow> 'a \<Rightarrow> 'a tree" where
"mergeSibling (Leaf w\<^sub>b b) a = Leaf w\<^sub>b b" |
"mergeSibling (Node w (Leaf w\<^sub>b b) (Leaf w\<^sub>c c)) a =
     (if a = b \<or> a = c then Leaf (w\<^sub>b + w\<^sub>c) a
      else Node w (Leaf w\<^sub>b b) (Leaf w\<^sub>c c))" |
"mergeSibling (Node w t\<^sub>1 t\<^sub>2) a =
     Node w (mergeSibling t\<^sub>1 a) (mergeSibling t\<^sub>2 a)"

text \<open>
The definition of @{const mergeSibling} has essentially the same structure as
that of @{const sibling}. As a result, the custom induction rule that we
derived for @{const sibling} works equally well for reasoning about
@{const mergeSibling}.
\<close>

lemmas mergeSibling_induct_consistent = sibling_induct_consistent

text \<open>
The properties of @{const mergeSibling} echo those of @{const sibling}. Like
with @{const sibling}, simplification rules are crucial.
\<close>

lemma notin_alphabet_imp_mergeSibling_id[simp]:
"a \<notin> alphabet t \<Longrightarrow> mergeSibling t a = t"
by (induct t a rule: mergeSibling.induct) simp+

lemma height_gt_0_imp_mergeSibling_left[simp]:
"height t\<^sub>1 > 0 \<Longrightarrow>
 mergeSibling (Node w t\<^sub>1 t\<^sub>2) a =
     Node w (mergeSibling t\<^sub>1 a) (mergeSibling t\<^sub>2 a)"
by (case_tac t\<^sub>1) simp+

lemma height_gt_0_imp_mergeSibling_right[simp]:
"height t\<^sub>2 > 0 \<Longrightarrow>
 mergeSibling (Node w t\<^sub>1 t\<^sub>2) a =
     Node w (mergeSibling t\<^sub>1 a) (mergeSibling t\<^sub>2 a)"
by (case_tac t\<^sub>2) simp+

lemma either_height_gt_0_imp_mergeSibling[simp]:
"height t\<^sub>1 > 0 \<or> height t\<^sub>2 > 0 \<Longrightarrow>
 mergeSibling (Node w t\<^sub>1 t\<^sub>2) a =
     Node w (mergeSibling t\<^sub>1 a) (mergeSibling t\<^sub>2 a)"
by auto

lemma alphabet_mergeSibling[simp]:
"\<lbrakk>consistent t; a \<in> alphabet t\<rbrakk> \<Longrightarrow>
 alphabet (mergeSibling t a) = (alphabet t - {sibling t a}) \<union> {a}"
by (induct t a rule: mergeSibling_induct_consistent) auto

lemma consistent_mergeSibling[simp]:
"consistent t \<Longrightarrow> consistent (mergeSibling t a)"
by (induct t a rule: mergeSibling_induct_consistent) auto

lemma freq_mergeSibling:
"\<lbrakk>consistent t; a \<in> alphabet t; sibling t a \<noteq> a\<rbrakk> \<Longrightarrow>
 freq (mergeSibling t a) =
     (\<lambda>c. if c = a then freq t a + freq t (sibling t a)
          else if c = sibling t a then 0
          else freq t c)"
by (induct t a rule: mergeSibling_induct_consistent) (auto simp: fun_eq_iff)

lemma weight_mergeSibling[simp]:
"weight (mergeSibling t a) = weight t"
by (induct t a rule: mergeSibling.induct) simp+

text \<open>
If $a$ has a sibling, merging $a$ and its sibling reduces $t$'s cost by
@{term "freq t a + freq t (sibling t a)"}.
\<close>

lemma cost_mergeSibling:
"\<lbrakk>consistent t; sibling t a \<noteq> a\<rbrakk> \<Longrightarrow>
 cost (mergeSibling t a) + freq t a + freq t (sibling t a) = cost t"
by (induct t a rule: mergeSibling_induct_consistent) auto

subsection \<open>Leaf Split\<close>

text \<open>
The \<open>splitLeaf\<close> function undoes the merging performed by
@{const mergeSibling}: Given two symbols $a$, $b$ and two frequencies
$@{term w\<^sub>a}$, $@{term w\<^sub>b}$, it transforms
\setbox\myboxi=\hbox{\includegraphics[scale=1.25]{tree-splitLeaf-a.pdf}}%
\setbox\myboxii=\hbox{\includegraphics[scale=1.25]{tree-splitLeaf-ab.pdf}}%
$$\smash{\lower\ht\myboxi\hbox{\raise.5\ht\myboxii\box\myboxi}}
  \qquad \hbox{into} \qquad
  \vcenter{\box\myboxii}$$
In the resulting tree, $a$ has frequency @{term w\<^sub>a} and $b$ has frequency
@{term w\<^sub>b}. We normally invoke it with @{term w\<^sub>a}~and @{term w\<^sub>b} such that
@{prop "freq t a = w\<^sub>a + w\<^sub>b"}.
\<close>

primrec splitLeaf :: "'a tree \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a tree" where
"splitLeaf (Leaf w\<^sub>c c) w\<^sub>a a w\<^sub>b b =
 (if c = a then Node w\<^sub>c (Leaf w\<^sub>a a) (Leaf w\<^sub>b b) else Leaf w\<^sub>c c)" |
"splitLeaf (Node w t\<^sub>1 t\<^sub>2) w\<^sub>a a w\<^sub>b b =
 Node w (splitLeaf t\<^sub>1 w\<^sub>a a w\<^sub>b b) (splitLeaf t\<^sub>2 w\<^sub>a a w\<^sub>b b)"

primrec splitLeaf\<^sub>F :: "'a forest \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a forest" where
"splitLeaf\<^sub>F [] w\<^sub>a a w\<^sub>b b = []" |
"splitLeaf\<^sub>F (t # ts) w\<^sub>a a w\<^sub>b b =
     splitLeaf t w\<^sub>a a w\<^sub>b b # splitLeaf\<^sub>F ts w\<^sub>a a w\<^sub>b b"

text \<open>
Splitting leaf nodes affects the alphabet, consistency, symbol frequencies,
weight, and cost in unsurprising ways.
\<close>

lemma notin_alphabet_imp_splitLeaf_id[simp]:
"a \<notin> alphabet t \<Longrightarrow> splitLeaf t w\<^sub>a a w\<^sub>b b = t"
by (induct t) simp+

lemma notin_alphabet\<^sub>F_imp_splitLeaf\<^sub>F_id[simp]:
"a \<notin> alphabet\<^sub>F ts \<Longrightarrow> splitLeaf\<^sub>F ts w\<^sub>a a w\<^sub>b b = ts"
by (induct ts) simp+

lemma alphabet_splitLeaf[simp]:
"alphabet (splitLeaf t w\<^sub>a a w\<^sub>b b) =
 (if a \<in> alphabet t then alphabet t \<union> {b} else alphabet t)"
by (induct t) simp+

lemma consistent_splitLeaf[simp]:
"\<lbrakk>consistent t; b \<notin> alphabet t\<rbrakk> \<Longrightarrow> consistent (splitLeaf t w\<^sub>a a w\<^sub>b b)"
by (induct t) auto

lemma freq_splitLeaf[simp]:
"\<lbrakk>consistent t; b \<notin> alphabet t\<rbrakk> \<Longrightarrow>
 freq (splitLeaf t w\<^sub>a a w\<^sub>b b) =
 (if a \<in> alphabet t then (\<lambda>c. if c = a then w\<^sub>a else if c = b then w\<^sub>b else freq t c)
  else freq t)"
by (induct t b rule: tree_induct_consistent) (rule ext, auto)+

lemma weight_splitLeaf[simp]:
"\<lbrakk>consistent t; a \<in> alphabet t; freq t a = w\<^sub>a + w\<^sub>b\<rbrakk> \<Longrightarrow>
 weight (splitLeaf t w\<^sub>a a w\<^sub>b b) = weight t"
by (induct t a rule: tree_induct_consistent) simp+

lemma cost_splitLeaf[simp]:
"\<lbrakk>consistent t; a \<in> alphabet t; freq t a = w\<^sub>a + w\<^sub>b\<rbrakk> \<Longrightarrow>
 cost (splitLeaf t w\<^sub>a a w\<^sub>b b) = cost t + w\<^sub>a + w\<^sub>b"
by (induct t a rule: tree_induct_consistent) simp+

subsection \<open>Weight Sort Order\<close>

text \<open>
An invariant of Huffman's algorithm is that the forest is sorted by weight.
This is expressed by the \<open>sortedByWeight\<close> function.
\<close>

fun sortedByWeight :: "'a forest \<Rightarrow> bool" where
"sortedByWeight [] = True" |
"sortedByWeight [t] = True" |
"sortedByWeight (t\<^sub>1 # t\<^sub>2 # ts) =
 (weight t\<^sub>1 \<le> weight t\<^sub>2 \<and> sortedByWeight (t\<^sub>2 # ts))"

text \<open>
The function obeys the following fairly obvious laws.
\<close>

lemma sortedByWeight_Cons_imp_sortedByWeight:
"sortedByWeight (t # ts) \<Longrightarrow> sortedByWeight ts"
by (case_tac ts) simp+

lemma sortedByWeight_Cons_imp_forall_weight_ge:
"sortedByWeight (t # ts) \<Longrightarrow> \<forall>u \<in> set ts. weight u \<ge> weight t"
by (induct ts arbitrary: t) force+

lemma sortedByWeight_insortTree:
"\<lbrakk>sortedByWeight ts; height t = 0; height\<^sub>F ts = 0\<rbrakk> \<Longrightarrow>
 sortedByWeight (insortTree t ts)"
by (induct ts rule: sortedByWeight.induct) auto

subsection \<open>Pair of Minimal Symbols\<close>

text \<open>
The \<open>minima\<close> predicate expresses that two symbols
$a$, $b \in @{term "alphabet t"}$ have the lowest frequencies in the tree $t$.
Minimal symbols need not be uniquely defined.
\<close>

definition minima :: "'a tree \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
"minima t a b =
 (a \<in> alphabet t \<and> b \<in> alphabet t \<and> a \<noteq> b
  \<and> (\<forall>c \<in> alphabet t. c \<noteq> a \<longrightarrow> c \<noteq> b \<longrightarrow>
    freq t c \<ge> freq t a \<and> freq t c \<ge> freq t b))"

section \<open>Formalization of the Textbook Proof \label{formalization}\<close>

subsection \<open>Four-Way Symbol Interchange Cost Lemma\<close>

text \<open>
If $a$ and $b$ are minima, and $c$ and $d$ are at the very bottom of the tree,
then exchanging $a$ and $b$ with $c$ and $d$ does not increase the cost.
Graphically, we have\strut
%
$${\it cost\/}
  \vcenter{\hbox{\includegraphics[scale=1.25]{tree-minima-abcd.pdf}}}
  \,\mathop{\le}\;\;\;
  {\it cost\/}
  \vcenter{\hbox{\includegraphics[scale=1.25]{tree-minima.pdf}}}$$

\noindent
This cost property is part of Knuth's proof:

\begin{quote}
Let $V$ be an internal node of maximum distance from the root. If $w_1$ and
$w_2$ are not the weights already attached to the children of $V$, we can
interchange them with the values that are already there; such an interchange
does not increase the weighted path length.
\end{quote}

\noindent
Lemma~16.2 in Cormen et al.~\cite[p.~389]{cormen-et-al-2001} expresses a
similar property, which turns out to be a corollary of our cost property:

\begin{quote}
Let $C$ be an alphabet in which each character $c \in C$ has frequency $f[c]$.
Let $x$ and $y$ be two characters in $C$ having the lowest frequencies. Then
there exists an optimal prefix code for $C$ in which the codewords for $x$ and
$y$ have the same length and differ only in the last bit.
\end{quote}

\vskip-.75\myskipamount
\<close>

lemma cost_swapFourSyms_le:
assumes
  "consistent t" "minima t a b" "c \<in> alphabet t" "d \<in> alphabet t"
  "depth t c = height t" "depth t d = height t" "c \<noteq> d"
shows "cost (swapFourSyms t a b c d) \<le> cost t"
proof -
  note lems = swapFourSyms_def minima_def cost_swapSyms_le depth_le_height
  show ?thesis
  proof (cases "a \<noteq> d \<and> b \<noteq> c")
    case True show ?thesis
    proof cases
      assume "a = c" show ?thesis
      proof cases
        assume "b = d" thus ?thesis using \<open>a = c\<close> True assms
          by (simp add: lems)
      next
        assume "b \<noteq> d" thus ?thesis using \<open>a = c\<close> True assms
          by (simp add: lems)
      qed
    next
      assume "a \<noteq> c" show ?thesis
      proof cases
        assume "b = d" thus ?thesis using \<open>a \<noteq> c\<close> True assms
          by (simp add: lems)
      next
        assume "b \<noteq> d"
        have "cost (swapFourSyms t a b c d) \<le> cost (swapSyms t a c)"
          using \<open>b \<noteq> d\<close> \<open>a \<noteq> c\<close> True assms by (clarsimp simp: lems)
        also have "\<dots> \<le> cost t" using \<open>b \<noteq> d\<close> \<open>a \<noteq> c\<close> True assms
          by (clarsimp simp: lems)
        finally show ?thesis .
      qed
    qed
  next
    case False thus ?thesis using assms by (clarsimp simp: lems)
  qed
qed

subsection \<open>Leaf Split Optimality Lemma \label{leaf-split-optimality}\<close>

text \<open>
The tree @{term "splitLeaf t w\<^sub>a a w\<^sub>b b"} is optimum if $t$ is optimum, under a
few assumptions, notably that $a$ and $b$ are minima of the new tree and
that @{prop "freq t a = w\<^sub>a + w\<^sub>b"}.
Graphically:\strut
%
\setbox\myboxi=\hbox{\includegraphics[scale=1.2]{tree-splitLeaf-a.pdf}}%
\setbox\myboxii=\hbox{\includegraphics[scale=1.2]{tree-splitLeaf-ab.pdf}}%
$${\it optimum\/} \smash{\lower\ht\myboxi\hbox{\raise.5\ht\myboxii\box\myboxi}}
  \,\mathop{\Longrightarrow}\;\;\;
  {\it optimum\/} \vcenter{\box\myboxii}$$
%
This corresponds to the following fragment of Knuth's proof:

\begin{quote}
Now it is easy to prove that the weighted path length of such a tree is
minimized if and only if the tree with
$$\vcenter{\hbox{\includegraphics[scale=1.25]{tree-w1-w2-leaves.pdf}}}
  \qquad \hbox{replaced by} \qquad
  \vcenter{\hbox{\includegraphics[scale=1.25]{tree-w1-plus-w2.pdf}}}$$
has minimum path length for the weights $w_1 + w_2$, $w_3$, $\ldots\,$, $w_m$.
\end{quote}

\noindent
We only need the ``if'' direction of Knuth's equivalence. Lemma~16.3 in
Cormen et al.~\cite[p.~391]{cormen-et-al-2001} expresses essentially the same
property:

\begin{quote}
Let $C$ be a given alphabet with frequency $f[c]$ defined for each character
$c \in C$. Let $x$ and $y$ be two characters in $C$ with minimum frequency. Let
$C'$ be the alphabet $C$ with characters $x$, $y$ removed and (new) character
$z$ added, so that $C' = C - \{x, y\} \cup {\{z\}}$; define $f$ for $C'$ as for
$C$, except that $f[z] = f[x] + f[y]$. Let $T'$ be any tree representing an
optimal prefix code for the alphabet $C'$. Then the tree $T$, obtained from
$T'$ by replacing the leaf node for $z$ with an internal node having $x$ and
$y$ as children, represents an optimal prefix code for the alphabet $C$.
\end{quote}

\noindent
The proof is as follows: We assume that $t$ has a cost less than or equal to
that of any other comparable tree~$v$ and show that
@{term "splitLeaf t w\<^sub>a a w\<^sub>b b"} has a cost less than or equal to that of any
other comparable tree $u$. By @{thm [source] exists_at_height} and
@{thm [source] depth_height_imp_sibling_ne}, we know that some symbols $c$ and
$d$ appear in sibling nodes at the very bottom of~$u$:
$$\includegraphics[scale=1.25]{tree-splitLeaf-cd.pdf}$$
(The question mark is there to remind us that we know nothing specific about
$u$'s structure.) From $u$ we construct a new tree
@{term "swapFourSyms u a b c d"} in which the minima $a$ and $b$ are siblings:
$$\includegraphics[scale=1.25]{tree-splitLeaf-abcd.pdf}$$
Merging $a$ and $b$ gives a tree comparable with $t$, which we can use to
instantiate $v$ in the assumption:
$$\includegraphics[scale=1.25]{tree-splitLeaf-abcd-aba.pdf}$$
With this instantiation, the proof is easy:
$$\begin{tabularx}{\textwidth}{@%
{\hskip\leftmargin}cX@%
{}}
    & @{term "cost (splitLeaf t a w\<^sub>a b w\<^sub>b)"} \\
\eq & \justif{@{thm [source] cost_splitLeaf}} \\
    & @{term "cost t + w\<^sub>a + w\<^sub>b"} \\
\kern-1em$\leq$\kern-1em & \justif{assumption} \\[-2ex]
    & $\<open>cost (\<close>
       \overbrace{\strut\!@{term "mergeSibling (swapFourSyms u a b c d) a"}\!}
       ^{\smash{\hbox{$v$}}}\<open>) + w\<^sub>a + w\<^sub>b\<close>$ \\[\extrah]
\eq & \justif{@{thm [source] cost_mergeSibling}} \\
    & @{term "cost (swapFourSyms u a b c d)"} \\
\kern-1em$\leq$\kern-1em & \justif{@{thm [source] cost_swapFourSyms_le}} \\
    & @{term "cost u"}. \\
\end{tabularx}$$

\noindent
In contrast, the proof in Cormen et al.\ is by contradiction: Essentially, they
assume that there exists a tree $u$ with a lower cost than
@{term "splitLeaf t a w\<^sub>a b w\<^sub>b"} and show that there exists a tree~$v$
with a lower cost than~$t$, contradicting the hypothesis that $t$ is optimum. In
place of @{thm [source] cost_swapFourSyms_le}, they invoke their lemma~16.2,
which is questionable since $u$ is not necessarily optimum.%
\footnote{Thomas Cormen commented that this step will be clarified in the
next edition of the book.}

Our proof relies on the following lemma, which asserts that $a$ and $b$ are
minima of $u$.
\<close>

lemma twice_freq_le_imp_minima:
"\<lbrakk>\<forall>c \<in> alphabet t. w\<^sub>a \<le> freq t c \<and> w\<^sub>b \<le> freq t c;
  alphabet u = alphabet t \<union> {b}; a \<in> alphabet u; a \<noteq> b;
  freq u = (\<lambda>c. if c = a then w\<^sub>a else if c = b then w\<^sub>b else freq t c)\<rbrakk> \<Longrightarrow>
 minima u a b"
by (simp add: minima_def)

text \<open>
Now comes the key lemma.
\<close>

lemma optimum_splitLeaf:
assumes "consistent t" "optimum t" "a \<in> alphabet t" "b \<notin> alphabet t"
        "freq t a = w\<^sub>a + w\<^sub>b" "\<forall>c \<in> alphabet t. freq t c \<ge> w\<^sub>a \<and> freq t c \<ge> w\<^sub>b"
shows "optimum (splitLeaf t w\<^sub>a a w\<^sub>b b)"
proof (unfold optimum_def, clarify)
  fix u
  let ?t' = "splitLeaf t w\<^sub>a a w\<^sub>b b"
  assume c\<^sub>u: "consistent u" and a\<^sub>u: "alphabet ?t' = alphabet u" and
    f\<^sub>u: "freq ?t' = freq u"
  show "cost ?t' \<le> cost u"
  proof (cases "height ?t' = 0")
    case True thus ?thesis by simp
  next
    case False
    hence h\<^sub>u: "height u > 0" using a\<^sub>u assms
      by (auto intro: height_gt_0_alphabet_eq_imp_height_gt_0)
    have a\<^sub>a: "a \<in> alphabet u" using a\<^sub>u assms by fastforce
    have a\<^sub>b: "b \<in> alphabet u" using a\<^sub>u assms by fastforce
    have ab: "a \<noteq> b" using assms by blast

    from exists_at_height[OF c\<^sub>u]
    obtain c where a\<^sub>c: "c \<in> alphabet u" and d\<^sub>c: "depth u c = height u" ..
    let ?d = "sibling u c"

    have dc: "?d \<noteq> c" using d\<^sub>c c\<^sub>u h\<^sub>u a\<^sub>c by (metis depth_height_imp_sibling_ne)
    have a\<^sub>d: "?d \<in> alphabet u" using dc
      by (rule sibling_ne_imp_sibling_in_alphabet)
    have d\<^sub>d: "depth u ?d = height u" using d\<^sub>c c\<^sub>u by simp

    let ?u' = "swapFourSyms u a b c ?d"
    have c\<^sub>u\<^sub>': "consistent ?u'" using c\<^sub>u by simp
    have a\<^sub>u\<^sub>': "alphabet ?u' = alphabet u" using a\<^sub>a a\<^sub>b a\<^sub>c a\<^sub>d a\<^sub>u by simp
    have f\<^sub>u\<^sub>': "freq ?u' = freq u" using a\<^sub>a a\<^sub>b a\<^sub>c a\<^sub>d c\<^sub>u f\<^sub>u by simp
    have s\<^sub>a: "sibling ?u' a = b" using c\<^sub>u a\<^sub>a a\<^sub>b a\<^sub>c ab dc
      by (rule sibling_swapFourSyms_when_4th_is_sibling)

    let ?v = "mergeSibling ?u' a"
    have c\<^sub>v: "consistent ?v" using c\<^sub>u\<^sub>' by simp
    have a\<^sub>v: "alphabet ?v = alphabet t" using s\<^sub>a c\<^sub>u\<^sub>' a\<^sub>u\<^sub>' a\<^sub>a a\<^sub>u assms by auto
    have f\<^sub>v: "freq ?v = freq t"
      using s\<^sub>a c\<^sub>u\<^sub>' a\<^sub>u\<^sub>' f\<^sub>u\<^sub>' f\<^sub>u[THEN sym] ab a\<^sub>u[THEN sym] assms
      by (simp add: freq_mergeSibling ext)

    have "cost ?t' = cost t + w\<^sub>a + w\<^sub>b" using assms by simp
    also have "\<dots> \<le> cost ?v + w\<^sub>a + w\<^sub>b" using c\<^sub>v a\<^sub>v f\<^sub>v \<open>optimum t\<close>
      by (simp add: optimum_def)
    also have "\<dots> = cost ?u'"
      proof -
        have "cost ?v + freq ?u' a + freq ?u' (sibling ?u' a) = cost ?u'"
          using c\<^sub>u\<^sub>' s\<^sub>a assms by (subst cost_mergeSibling) auto
        moreover have "w\<^sub>a = freq ?u' a" "w\<^sub>b = freq ?u' b"
          using f\<^sub>u\<^sub>' f\<^sub>u[THEN sym] assms by clarsimp+
        ultimately show ?thesis using s\<^sub>a by simp
      qed
    also have "\<dots> \<le> cost u"
      proof -
        have "minima u a b" using a\<^sub>u f\<^sub>u assms
          by (subst twice_freq_le_imp_minima) auto
        with c\<^sub>u show ?thesis using a\<^sub>c a\<^sub>d d\<^sub>c d\<^sub>d dc[THEN not_sym]
          by (rule cost_swapFourSyms_le)
      qed
    finally show ?thesis .
  qed
qed

subsection \<open>Leaf Split Commutativity Lemma \label{leaf-split-commutativity}\<close>

text \<open>
A key property of Huffman's algorithm is that once it has combined two
lowest-weight trees using @{const uniteTrees}, it does not visit these trees
ever again. This suggests that splitting a leaf node before applying the
algorithm should give the same result as applying the algorithm first and
splitting the leaf node afterward. The diagram below illustrates the
situation:\strut

\def\myscale{1.05}%
\setbox\myboxi=\hbox{(9)\strut}%
\setbox\myboxii=\hbox{\includegraphics[scale=\myscale]{forest-a.pdf}}%
$$(1)\,\lower\ht\myboxii\hbox{\raise\ht\myboxi\box\myboxii}$$

\smallskip

\setbox\myboxii=\hbox{\includegraphics[scale=\myscale]{tree-splitLeaf-a.pdf}}%
\setbox\myboxiii=\hbox{\includegraphics[scale=\myscale]%
  {forest-splitLeaf-ab.pdf}}%
\mydimeni=\wd\myboxii

\noindent
(2a)\,\lower\ht\myboxii\hbox{\raise\ht\myboxi\box\myboxii}%
  \qquad\qquad\quad
  (2b)\,\lower\ht\myboxiii\hbox{\raise\ht\myboxi\box\myboxiii}\quad{}

\setbox\myboxiii=\hbox{\includegraphics[scale=\myscale]%
  {tree-splitLeaf-ab.pdf}}%
\setbox\myboxiv=\hbox{\includegraphics[scale=\myscale]%
  {tree-huffman-splitLeaf-ab.pdf}}%
\mydimenii=\wd\myboxiii
\vskip1.5\smallskipamount
\noindent
(3a)\,\lower\ht\myboxiii\hbox{\raise\ht\myboxi\box\myboxiii}%
  \qquad\qquad\quad
  (3b)\,\hfill\lower\ht\myboxiv\hbox{\raise\ht\myboxi\box\myboxiv}%
  \quad\hfill{}

\noindent
From the original forest (1), we can either run the algorithm (2a) and then
split $a$ (3a) or split $a$ (2b) and then run the algorithm (3b). Our goal is
to show that trees (3a) and (3b) are identical. Formally, we prove that
$$@{term "splitLeaf (huffman ts) w\<^sub>a a w\<^sub>b b"} =
  @{term "huffman (splitLeaf\<^sub>F ts w\<^sub>a a w\<^sub>b b)"}$$
when @{term ts} is consistent, @{term "a \<in> alphabet\<^sub>F ts"}, @{term
"b \<notin> alphabet\<^sub>F ts"}, and $@{term "freq\<^sub>F ts a"} = @{term w\<^sub>a}
\mathbin{\<open>+\<close>} @{term "w\<^sub>b"}$. But before we can prove this
commutativity lemma, we need to introduce a few simple lemmas.
\<close>

lemma cachedWeight_splitLeaf[simp]:
"cachedWeight (splitLeaf t w\<^sub>a a w\<^sub>b b) = cachedWeight t"
by (case_tac t) simp+

lemma splitLeaf\<^sub>F_insortTree_when_in_alphabet_left[simp]:
"\<lbrakk>a \<in> alphabet t; consistent t; a \<notin> alphabet\<^sub>F ts; freq t a = w\<^sub>a + w\<^sub>b\<rbrakk> \<Longrightarrow>
 splitLeaf\<^sub>F (insortTree t ts) w\<^sub>a a w\<^sub>b b = insortTree (splitLeaf t w\<^sub>a a w\<^sub>b b) ts"
by (induct ts) simp+

lemma splitLeaf\<^sub>F_insortTree_when_in_alphabet\<^sub>F_tail[simp]:
"\<lbrakk>a \<in> alphabet\<^sub>F ts; consistent\<^sub>F ts; a \<notin> alphabet t; freq\<^sub>F ts a = w\<^sub>a + w\<^sub>b\<rbrakk> \<Longrightarrow>
 splitLeaf\<^sub>F (insortTree t ts) w\<^sub>a a w\<^sub>b b =
 insortTree t (splitLeaf\<^sub>F ts w\<^sub>a a w\<^sub>b b)"
proof (induct ts)
  case Nil thus ?case by simp
next
  case (Cons u us) show ?case
  proof (cases "a \<in> alphabet u")
    case True
    hence "a \<notin> alphabet\<^sub>F us" using Cons by auto
    thus ?thesis using Cons by auto
  next
    case False thus ?thesis using Cons by simp
  qed
qed

text \<open>
We are now ready to prove the commutativity lemma.
\<close>

lemma splitLeaf_huffman_commute:
"\<lbrakk>consistent\<^sub>F ts; ts \<noteq> []; a \<in> alphabet\<^sub>F ts; freq\<^sub>F ts a = w\<^sub>a + w\<^sub>b\<rbrakk> \<Longrightarrow>
 splitLeaf (huffman ts) w\<^sub>a a w\<^sub>b b = huffman (splitLeaf\<^sub>F ts w\<^sub>a a w\<^sub>b b)"
proof (induct ts rule: huffman.induct)
  case (1 t) thus ?case by simp
next
  case (2 t\<^sub>1 t\<^sub>2 ts)
  note hyps = 2
  show ?case
  proof (cases "a \<in> alphabet t\<^sub>1")
    case True
    hence "a \<notin> alphabet t\<^sub>2" "a \<notin> alphabet\<^sub>F ts" using hyps by auto
    thus ?thesis using hyps by (simp add: uniteTrees_def)
  next
    case False
    note a\<^sub>1 = False
    show ?thesis
    proof (cases "a \<in> alphabet t\<^sub>2")
      case True
      hence "a \<notin> alphabet\<^sub>F ts" using hyps by auto
      thus ?thesis using a\<^sub>1 hyps by (simp add: uniteTrees_def)
    next
      case False
      thus ?thesis using a\<^sub>1 hyps by simp
    qed
  qed
next
  case 3 thus ?case by simp
qed

text \<open>
An important consequence of the commutativity lemma is that applying Huffman's
algorithm on a forest of the form
$$\vcenter{\hbox{\includegraphics[scale=1.25]{forest-uniteTrees.pdf}}}$$
gives the same result as applying the algorithm on the ``flat'' forest
$$\vcenter{\hbox{\includegraphics[scale=1.25]{forest-uniteTrees-flat.pdf}}}$$
followed by splitting the leaf node $a$ into two nodes $a$, $b$ with
frequencies $@{term w\<^sub>a}$, $@{term w\<^sub>b}$. The lemma effectively
provides a way to flatten the forest at each step of the algorithm. Its
invocation is implicit in the textbook proof.
\<close>

subsection \<open>Optimality Theorem\<close>

text \<open>
We are one lemma away from our main result.
\<close>

lemma max_0_imp_0[simp]:
"(max x y = (0::nat)) = (x = 0 \<and> y = 0)"
by auto

theorem optimum_huffman:
"\<lbrakk>consistent\<^sub>F ts; height\<^sub>F ts = 0; sortedByWeight ts; ts \<noteq> []\<rbrakk> \<Longrightarrow>
 optimum (huffman ts)"

txt \<open>
The input @{term ts} is assumed to be a nonempty consistent list of leaf nodes
sorted by weight. The proof is by induction on the length of the forest
@{term ts}. Let @{term ts} be
$$\vcenter{\hbox{\includegraphics[scale=1.25]{forest-flat.pdf}}}$$
with $w_a \le w_b \le w_c \le w_d \le \cdots \le w_z$. If @{term ts} consists
of a single leaf node, the node has cost 0 and is therefore optimum. If
@{term ts} has length 2 or more, the first step of the algorithm leaves us with
the term
$${\it huffman\/}\enskip\; \vcenter{\hbox{\includegraphics[scale=1.25]%
    {forest-uniteTrees.pdf}}}$$
In the diagram, we put the newly created tree at position 2 in the forest; in
general, it could be anywhere. By @{thm [source] splitLeaf_huffman_commute},
the above tree equals\strut
$${\it splitLeaf\/}\;\left({\it huffman\/}\enskip\;
  \vcenter{\hbox{\includegraphics[scale=1.25]{forest-uniteTrees-flat.pdf}}}
  \;\right)\,\<open>w\<^sub>a a w\<^sub>b b\<close>.$$
To prove that this tree is optimum, it suffices by
@{thm [source] optimum_splitLeaf} to show that\strut
$${\it huffman\/}\enskip\;
  \vcenter{\hbox{\includegraphics[scale=1.25]{forest-uniteTrees-flat.pdf}}}$$
is optimum, which follows from the induction hypothesis.\strut
\<close>

proof (induct ts rule: length_induct)
  \<comment> \<open>\sc Complete induction step\<close>
  case (1 ts)
  note hyps = 1
  show ?case
  proof (cases ts)
    case Nil thus ?thesis using \<open>ts \<noteq> []\<close> by fast
  next
    case (Cons t\<^sub>a ts')
    note ts = Cons
    show ?thesis
    proof (cases ts')
      case Nil thus ?thesis using ts hyps by (simp add: optimum_def)
    next
      case (Cons t\<^sub>b ts'')
      note ts' = Cons
      show ?thesis
      proof (cases t\<^sub>a)
        case (Leaf w\<^sub>a a)
        note l\<^sub>a = Leaf
        show ?thesis
        proof (cases t\<^sub>b)
          case (Leaf w\<^sub>b b)
          note l\<^sub>b = Leaf
          show ?thesis
          proof -
            let ?us = "insortTree (uniteTrees t\<^sub>a t\<^sub>b) ts''"
            let ?us' = "insortTree (Leaf (w\<^sub>a + w\<^sub>b) a) ts''"
            let ?t\<^sub>s = "splitLeaf (huffman ?us') w\<^sub>a a w\<^sub>b b"

            have e\<^sub>1: "huffman ts = huffman ?us" using ts' ts by simp
            have e\<^sub>2: "huffman ?us = ?t\<^sub>s" using l\<^sub>a l\<^sub>b ts' ts hyps
              by (auto simp: splitLeaf_huffman_commute uniteTrees_def)

            have "optimum (huffman ?us')" using l\<^sub>a ts' ts hyps
              by (drule_tac x = ?us' in spec)
                 (auto dest: sortedByWeight_Cons_imp_sortedByWeight
                  simp: sortedByWeight_insortTree)
            hence "optimum ?t\<^sub>s" using l\<^sub>a l\<^sub>b ts' ts hyps
              apply simp
              apply (rule optimum_splitLeaf)
              by (auto dest!: height\<^sub>F_0_imp_Leaf_freq\<^sub>F_in_set
                  sortedByWeight_Cons_imp_forall_weight_ge)
            thus "optimum (huffman ts)" using e\<^sub>1 e\<^sub>2 by simp
          qed
        next
          case Node thus ?thesis using ts' ts hyps by simp
        qed
      next
        case Node thus ?thesis using ts' ts hyps by simp
      qed
    qed
  qed
qed

text \<open>
\isakeyword{end}

\myskip

\noindent
So what have we achieved? Assuming that our definitions really mean what we
intend them to mean, we established that our functional implementation of
Huffman's algorithm, when invoked properly, constructs a binary tree that
represents an optimal prefix code for the specified alphabet and frequencies.
Using Isabelle's code generator \cite{haftmann-nipkow-2007}, we can convert the
Isabelle code into Standard ML, OCaml, or Haskell and use it in a real
application.

As a side note, the @{thm [source] optimum_huffman} theorem assumes that the
forest @{term ts} passed to @{const huffman} consists exclusively of leaf nodes.
It is tempting to relax this restriction, by requiring instead that the forest
@{term ts} has the lowest cost among forests of the same size. We would define
optimality of a forest as follows:
$$\begin{aligned}[t]
  @{prop "optimum\<^sub>F ts"}\,\;\<open>=\<close>\;\,
  (\<open>\<forall>us.\<close>\
    & \<open>length ts = length us \<longrightarrow> consistent\<^sub>F us \<longrightarrow>\<close> \\[-2.5pt]
    & \<open>alphabet\<^sub>F ts = alphabet\<^sub>F us \<longrightarrow> freq\<^sub>F ts = freq\<^sub>F us \<longrightarrow>\<close>
\\[-2.5pt]
    & @{prop "cost\<^sub>F ts \<le> cost\<^sub>F us"})\end{aligned}$$
with $\<open>cost\<^sub>F [] = 0\<close>$ and
$@{prop "cost\<^sub>F (t # ts) = cost t + cost\<^sub>F ts"}$. However, the modified
proposition does not hold. A counterexample is the optimum forest
$$\includegraphics{forest-optimal.pdf}$$
for which the algorithm constructs the tree
$$\vcenter{\hbox{\includegraphics{tree-suboptimal.pdf}}}
  \qquad \hbox{of greater cost than} \qquad
  \vcenter{\hbox{\includegraphics{tree-optimal.pdf}}}$$
\<close>

section \<open>Related Work \label{related-work}\<close>

text \<open>
Laurent Th\'ery's Coq formalization of Huffman's algorithm \cite{thery-2003,%
thery-2004} is an obvious yardstick for our work. It has a somewhat wider
scope, proving among others the isomorphism between prefix codes and full binary
trees. With 291 theorems, it is also much larger.

Th\'ery identified the following difficulties in formalizing the textbook
proof:

\begin{enumerate}
\item The leaf interchange process that brings the two minimal symbols together
      is tedious to formalize.

\item The sibling merging process requires introducing a new symbol for the
      merged node, which complicates the formalization.

\item The algorithm constructs the tree in a bottom-up fashion. While top-down
      procedures can usually be proved by structural induction, bottom-up
      procedures often require more sophisticated induction principles and
      larger invariants.

\item The informal proof relies on the notion of depth of a node. Defining this
      notion formally is problematic, because the depth can only be seen as a
      function if the tree is composed of distinct nodes.
\end{enumerate}

To circumvent these difficulties, Th\'ery introduced the ingenious concept of
cover. A forest @{term ts} is a {\em cover\/} of a tree~$t$ if $t$ can be built
from @{term ts} by adding inner nodes on top of the trees in @{term ts}. The
term ``cover'' is easier to understand if the binary trees are drawn with the
root at the bottom of the page, like natural trees. Huffman's algorithm is
a refinement of the cover concept. The main proof consists in showing that
the cost of @{term "huffman ts"} is less than or equal to that of any other
tree for which @{term ts} is a cover. It relies on a few auxiliary definitions,
notably an ``ordered cover'' concept that facilitates structural induction
and a four-argument depth predicate (confusingly called @{term height}).
Permutations also play a central role.

Incidentally, our experience suggests that the potential problems identified
by Th\'ery can be overcome more directly without too much work, leading to a
simpler proof:

\begin{enumerate}
\item Formalizing the leaf interchange did not prove overly tedious. Among our
      95~lemmas and theorems, 24 concern @{const swapLeaves},
      @{const swapSyms}, and @{const swapFourSyms}.

\item The generation of a new symbol for the resulting node when merging two
      sibling nodes in @{const mergeSibling} was trivially solved by reusing
      one of the two merged symbols.

\item The bottom-up nature of the tree construction process was addressed by
      using the length of the forest as the induction measure and by merging
      the two minimal symbols, as in Knuth's proof.

\item By restricting our attention to consistent trees, we were able to define
      the @{const depth} function simply and meaningfully.
\end{enumerate}
\<close>

section \<open>Conclusion \label{conclusion}\<close>

text \<open>
The goal of most formal proofs is to increase our confidence in a result. In
the case of Huffman's algorithm, however, the chances that a bug would have
gone unnoticed for the 56 years since its publication, under the scrutiny of
leading computer scientists, seem extremely low; and the existence of a Coq
proof should be sufficient to remove any remaining doubts.

The main contribution of this document has been to demonstrate that the
textbook proof of Huffman's algorithm can be elegantly formalized using
a state-of-the-art theorem prover such as Isabelle/HOL. In the process, we
uncovered a few minor snags in the proof given in Cormen et
al.~\cite{cormen-et-al-2001}.

We also found that custom induction rules, in combination with suitable
simplification rules, greatly help the automatic proof tactics, sometimes
reducing 30-line proof scripts to one-liners. We successfully applied this
approach for handling both the ubiquitous ``datatype + well\-formed\-ness
predicate'' combination (@{typ "'a tree"} + @{const consistent}) and functions
defined by sequential pattern matching (@{const sibling} and
@{const mergeSibling}). Our experience suggests that such rules, which are
uncommon in formalizations, are highly valuable and versatile. Moreover,
Isabelle's \textit{induction\_schema} and \textit{lexicographic\_order} tactics
make these easy to prove.

Formalizing the proof of Huffman's algorithm also led to a deeper
understanding of this classic algorithm. Many of the lemmas, notably the leaf
split commutativity lemma of Section~\ref{leaf-split-commutativity}, have not
been found in the literature and express fundamental properties of the
algorithm. Other discoveries did not find their way into the final proof. In
particular, each step of the algorithm appears to preserve the invariant that
the nodes in a forest are ordered by weight from left to right, bottom to top,
as in the example below:\strut
$$\vcenter{\hbox{\includegraphics[scale=1.25]{forest-zigzag.pdf}}}$$
It is not hard to prove formally that a tree exhibiting this property is
optimum. On the other hand, proving that the algorithm preserves this invariant
seems difficult---more difficult than formalizing the textbook proof---and
remains a suggestion for future work.

A few other directions for future work suggest themselves. First, we could
formalize some of our hypotheses, notably our restriction to full and
consistent binary trees. The current formalization says nothing about the
algorithm's application for data compression, so the next step could be to
extend the proof's scope to cover @{term encode}/@{term decode} functions
and show that full binary trees are isomorphic to prefix codes, as done in the
Coq development. Independently, we could generalize the development to $n$-ary
trees.
\<close>

(*<*)
end
(*>*)
