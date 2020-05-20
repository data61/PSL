(*  Title:       An Efficient Generalization of Counting Sort for Large, possibly Infinite Key Ranges
    Author:      Pasquale Noce
                 Software Engineer at HID Global, Italy
                 pasquale dot noce dot lavoro at gmail dot com
                 pasquale dot noce at hidglobal dot com
*)

section "Algorithm's description, analysis, and formalization"

theory Algorithm
  imports Main
begin

text \<open>
\null

\emph{This paper is dedicated to Gaia, my sweet niece, whose arrival has blessed me and my family
with joy and tenderness.}

\null

\emph{Moreover, I would like to thank my colleague Iacopo Rippa, who patiently listened to the ideas
underlying sections \ref{SEC1} and \ref{SEC3}, and helped me expand those ideas into complete proofs
by providing me with valuable hints and test data.}
\<close>


subsection "Introduction"

subsubsection "Counting sort"

text \<open>
\emph{Counting sort} is a well-known algorithm that sorts a collection of objects of any kind, as
long as each such object is associated with a signed integer key, according to their respective keys
(cf. \cite{R1}, \cite{R2}). If $xs$ is the input array containing $n$ objects to be sorted, $out$ is
the output, sorted array, and $key$ is the function mapping objects to keys, counting sort works as
follows (assuming arrays to be zero-based):

\begin{enumerate}

\item
Search the minimum key $mi$ and the maximum key $ma$ occurring within $xs$ (which can be done via a
single loop over $xs$).

\item
Allocate an array $ns$ of $ma - mi + 2$ unsigned integers and initialize all its elements to 0.

\item
For each $i$ from 0 to $n-1$, increase $ns[key(xs[i]) - mi + 1]$ by 1.

\item
For each $i$ from 2 to $ma - mi$, increase $ns[i]$ by $ns[i - 1]$.

\item
For each $i$ from 0 to $n-1$, set $out[ns[key(xs[i]) - mi]]$ to $xs[i]$ and increase
$ns[key(xs[i]) - mi]$ by 1.

\end{enumerate}

Steps 1 and 2 take $O(n)$ and $O(ma - mi)$ time, respectively. Step 3 counts how many times each
possible key occurs within $xs$, and takes $O(n)$ time. Step 4 computes the offset within $out$ of
the first object in $xs$, if any, having each possible key, and takes $O(ma - mi)$ time. Finally,
step 5 fills $out$, taking $O(n)$ time. Thus, the overall running time is $O(n) + O(ma - mi)$, and
the same is obviously true of memory space.

If the range of all the keys possibly occurring within $xs$, henceforth briefly referred to as the
\emph{key range}, is known in advance, the first two steps can be skipped by using the minimum and
maximum keys in the key range as $mi$, $ma$ and pre-allocating (possibly statically, rather than
dynamically, in real-world implementations) an array $ns$ of size $ma - mi + 2$. However, this does
not affect the asymptotic running time and memory space required by the algorithm, since both keep
being $O(n) + O(ma - mi)$ independently of the distribution of the keys actually occurring in $xs$
within the key range.

As a result, counting sort is suitable for direct use, viz. not just as a subroutine of another
sorting algorithm such as radix sort, only if the key range is not significantly larger than $n$.
Indeed, if 100 objects with 100,000 possible keys have to be sorted, accomplishing this task by
allocating, and iterating over, an array of 100,000 unsigned integers to count keys' occurrences
would be quite impractical! Whence the question that this paper will try to answer: how can counting
sort be generalized for direct use in case of a large key range?

Solving this problem clearly requires to renounce having one counter per key, rather using a bounded
number of counters, independent of the key range's cardinality, and partitioning the key range into
some number of intervals compatible with the upper bound on the counters' number. The resulting key
intervals will then form as many \emph{buckets}, and what will have to be counted is the number of
the objects contained in each bucket.

Counting objects per bucket, rather than per single key, has the following major consequences, the
former good, the latter bad:

\begin{itemize}

\item
\emph{Keys are no longer constrained to be integers, but may rather be elements of any linear order,
even of infinite cardinality.}
\\In fact, in counting sort keys must be integers -- or anything else in one-to-one correspondence
with some subset of the integers, such as alphabet letters -- since this ensures that the key range
contains finitely many keys, so that finitely many counters are needed. Thus, the introduction of an
upper bound for the number of counters makes this constraint vanish. As a result, keys of any kind
are now allowed and the key range can even be infinite (mathematically, since any representation of
the key range on a computer will always be finite). Notably, rational or real numbers may be used as
keys, too.
\\This observation considerably extends the scope of application of the special case where function
$key$ matches the identity function. In counting sort, this option is viable only if the objects to
be sorted are themselves integers, whereas in the generalized algorithm it is viable whenever they
are elements of any linear order, which also happens if they are rational or real numbers.

\item
\emph{Recursion needs to be introduced, since any bucket containing more than one object is in turn
required to be sorted.}
\\In fact, nothing prevents multiple objects from falling in the same bucket, and while this happens
sorting is not accomplished. Therefore, the generalized algorithm must provide for recursive rounds,
where each round splits any bucket containing multiple objects into finer-grained buckets containing
fewer objects. Recursion will then go on until every bucket contains at most one object, viz. until
there remains no counter larger than one.

\end{itemize}

Of course, the fewer recursive rounds are required to complete sorting, the more the algorithm will
be efficient, whence the following, fundamental question: how to minimize the number of the rounds?
That is to say, how to maximize the probability that, as a result of the execution of a round, there
be at most one object in each bucket, so that no more rounds be required?

The intuitive answer is: first, by making the buckets equiprobable -- or at least, by making their
probabilities as much uniform as possible --, and second, by increasing the number of the buckets as
much as possible. Providing pen-and-paper proofs of both of these statements, and showing how they
can be enforced, is the purpose of the following sections.
\<close>

subsubsection "Buckets' probability -- Proof"

text \<open>
\label{SEC1}

Suppose that $k$ objects be split randomly among $n$ equiprobable buckets, where $k \leq n$. This
operation is equivalent to selecting at random a sequence of $k$ buckets, possibly with repetitions,
so that the first object be placed into the first bucket of the sequence, the second object into the
second bucket, and so on. Thus, the probability $P$ that each bucket will contain at most one object
-- which will be called \emph{event E} in what follows -- is equal to the probability of selecting a
sequence without repetitions among all the possible sequences of $k$ buckets formed with the $n$
given ones.

Since buckets are assumed to be equiprobable, so are all such sequences. Hence, $P$ is equal to the
ratio of the number of the sequences without repetitions to the number of all sequences, namely:

\begin{equation}
\label{EQ1}
P=\frac{n!}{(n-k)!n^k}
\end{equation}

In the special case where $k = n$, this equation takes the following, simpler form:

\begin{equation}
\label{EQ2}
P=\frac{n!}{n^n}
\end{equation}

Now, suppose that the $n$ buckets be no longer equiprobable, viz. that they no longer have the same,
uniform probability $1/n$, rather having arbitrary, nonuniform probabilities $p_1$, ..., $p_n$. The
equation for probability $P$ applying to this case can be obtained through an iterative procedure,
as follows.

Let $i$ be an index in the range 1 to $n$ such that $p_i$ is larger than $1/n$. After swapping index
$i$ for 1, let $x_1$ be the increment in probability $p_1$ with respect to $1/n$, so that $p_1 =
a_0/n + x_1$ with $a_0 = 1$ and $0 < x_1 \leq a_0(n-1)/n$ (as $p_1 = 1$ for $x_1 = a_0(n-1)/n$).
Then, let $P_1$ be the probability of event $E$ in case the first bucket has probability $p_1$ and
all the other $n-1$ buckets have the same, uniform probability $q_1 = a_0/n - x_1/(n-1)$.

If $k < n$, event $E$ occurs just in case either all $k$ objects fall in as many distinct buckets
with probability $q_1$, or $k - 1$ objects do so whereas the remaining object falls in the bucket
with probability $p_1$. As these events, say $E_A$ and $E_B$, are incompatible, $P_1$ matches the
sum of their respective probabilities.

Since all the possible choices of $k$ distinct buckets are mutually incompatible, while those of the
buckets containing any two distinct objects are mutually independent, the probability of event $E_A$
is equal to the product of the following factors:

\begin{itemize}

\item
The number of the sequences without repetitions of $k$ buckets formed with the $n-1$ ones with
probability $q_1$, i.e. $(n-1)!/(n-1-k)! = (n-k)(n-1)!/(n-k)!$.

\item
The probability of any such sequence, i.e. $q_1^k$.

\end{itemize}

By virtue of similar considerations, the probability of event $E_B$ turns out to match the product
of the following factors:

\begin{itemize}

\item
The number of the sequences without repetitions of $k - 1$ buckets formed with the $n-1$ ones with
probability $q_1$, i.e. $(n-1)!/(n-\bcancel{1}-k+\bcancel{1})! = (n-1)!/(n-k)!$.

\item
The probability of any such sequence, i.e. $q_1^{k-1}$.

\item
The number of the possible choices of the object falling in the first bucket, i.e. $k$.

\item
The probability of the first bucket, i.e. $p_1$.

\end{itemize}

Therefore, $P_1$ is provided by the following equation:

\begin{equation}
\label{EQ3}
\begin{split}
P_1&=\frac{(n-k)(n-1)!}{(n-k)!}\left(\frac{a_0}{n} - \frac{x_1}{n-1}\right)^k\\
&\quad+k\frac{(n-1)!}{(n-k)!}\left(\frac{a_0}{n} - \frac{x_1}{n-1}\right)^{k-1}
\left(\frac{a_0}{n} + x_1\right)
\end{split}
\end{equation}

The correctness of this equation is confirmed by the fact that its right-hand side matches that of
equation \eqref{EQ1} for $x_1 = 0$, since $P_1$ must degenerate to $P$ in this case. In fact, being
$a_0 = 1$, it results:

\begin{align*}
&\frac{(n-k)(n-1)!}{(n-k)!}\left(\frac{a_0}{n} - 0\right)^k
+k\frac{(n-1)!}{(n-k)!}\left(\frac{a_0}{n} - 0\right)^{k-1}\left(\frac{a_0}{n} + 0\right)\\
&\quad=(n-\bcancel{k}+\bcancel{k})\frac{(n-1)!}{(n-k)!}\left(\frac{a_0}{n}\right)^k\\
&\quad=\frac{n!}{(n-k)!n^k}
\end{align*}

If $k = n$, event $E_A$ is impossible, as there is no way to accommodate $n$ objects within $n-1$
buckets without repetitions. Thus, $P_1$ is given by the following equation, derived by deleting the
first addend and replacing $k$ with $n$ in the right-hand side of equation \eqref{EQ3}:

\begin{equation}
\label{EQ4}
P_1=n!\left(\frac{a_0}{n} - \frac{x_1}{n-1}\right)^{n-1}\left(\frac{a_0}{n} + x_1\right)
\end{equation}

Likewise, the right-hand side of this equation matches that of equation \eqref{EQ2} for $x_1 = 0$,
which confirms its correctness.

The conclusions reached so far can be given a concise form, suitable for generalization, through the
following definitions, where $i$ and $j$ are any two natural numbers such that $0 < k-j \leq n-i$
and $a_i$ is some assigned real number:

\begin{align*}
A_{i,j}&\equiv\frac{(n-i)!}{(n-i-k+j)!}\left(\frac{a_i}{n-i}\right)^{k-j}\\
F_{i,j}&\equiv(k-j+1)A_{i,j}p_i\\
G_{i,j}&\equiv A_{i,j-1}+F_{i,j}
\end{align*}

Then, denoting the value of $P$ in the uniform probability case with $P_0$, and $a_0(n-1)/n - x_1$
with $a_1$, so that $q_1 = a_1/(n-1)$, equations \eqref{EQ1}, \eqref{EQ3}, and \eqref{EQ4} can be
rewritten as follows:

\begin{align}
\label{EQ5}
P_0&=A_{0,0}\\
\label{EQ6}
P_1&=
\begin{cases}
G_{1,1}=A_{1,0}+kA_{1,1}p_1&\quad\text{if $k < n$,}\\
F_{1,1}=kA_{1,1}p_1&\quad\text{if $k = n$.}
\end{cases}
\end{align}

Even more than for their conciseness, these equations are significant insofar as they show that the
right-hand side of equation \eqref{EQ6} can be obtained from the one of equation \eqref{EQ5} by
replacing $A_{0,0}$ with either $G_{1,1}$ or $F_{1,1}$, depending on whether $k < n$ or $k = n$.

If $p_i$ matches $q_1$ for any $i$ in the range 2 to $n$, $P = P_1$, thus $P$ is given by equation
\eqref{EQ6}. Otherwise, the procedure that has led to equation \eqref{EQ6} can be applied again. For
some index $i$ in the range 2 to $n$ such that $p_i$ is larger than $q_1$, swap $i$ for 2, and let
$x_2 = p_2 - a_1/(n-1)$, $a_2 = a_1(n-2)/(n-1) - x_2$, with $0 < x_2 \leq a_1(n-2)/(n-1)$. Moreover,
let $P_2$ be the probability of event $E$ if the first two buckets have probabilities $p_1$, $p_2$
and the other $n-2$ buckets have the same probability $q_2 = a_2/(n-2)$.

Then, reasoning as before, it turns out that the equation for $P_2$ can be obtained from equation
\eqref{EQ6} by replacing:

\begin{itemize}

\item
$A_{1,0}$ with $G_{2,1}$ or $F_{2,1}$, depending on whether $k < n-1$ or $k = n-1$, and

\item
$A_{1,1}$ with $G_{2,2}$ or $F_{2,2}$, depending on whether $k-1 < n-1$, i.e. $k < n$, or $k-1 =
n-1$, i.e. $k = n$.

\end{itemize}

As a result, $P_2$ is provided by the following equation:

\begin{equation}
\label{EQ7}
P_2=
\begin{cases}
G_{2,1}+kG_{2,2}p_1=A_{2,0}+kA_{2,1}p_2+k[A_{2,1}+(k-1)A_{2,2}p_2]p_1\\
\quad\text{if $k < n-1$,}\\
F_{2,1}+kG_{2,2}p_1=kA_{2,1}p_2+k[A_{2,1}+(k-1)A_{2,2}p_2]p_1\\
\quad\text{if $k = n-1$,}\\
kF_{2,2}p_1=k(k-1)A_{2,2}p_2p_1\\
\quad\text{if $k = n$.}
\end{cases}
\end{equation}

Since the iterative procedure used to derive equations \eqref{EQ6} and \eqref{EQ7} can be further
applied as many times as required, it follows that for any nonuniform probability distribution
$p_1$, ..., $p_n$, the equation for $P$ can be obtained from equation \eqref{EQ5} with $n-1$ steps
at most, where each step consists of replacing terms of the form $A_{i,j}$ with terms of either form
$G_{i+1,j+1}$ or $F_{i+1,j+1}$, depending on whether $k-j < n-i$ or $k-j = n-i$.

Let us re-use letters $n$, $k$ in lieu of $n-i$ and $k-j$, and use letters $a$, $x$ as aliases for
$a_i$ and $x_{i+1}$. Then, any aforesaid replacement is equivalent to the insertion of either of the
following expressions, regarded as images of as many functions $G$, $F$ of real variable $x$:

\begin{align}
\nonumber
G(x)&=\frac{(n-k)(n-1)!}{(n-k)!}\left(\frac{a}{n} - \frac{x}{n-1}\right)^k\\
\label{EQ8}
&\quad+k\frac{(n-1)!}{(n-k)!}\left(\frac{a}{n} - \frac{x}{n-1}\right)^{k-1}
\left(\frac{a}{n} + x\right)
&& \text{for $k < n$,}\\
\label{EQ9}
F(x)&=n!\left(\frac{a}{n} - \frac{x}{n-1}\right)^{n-1}\left(\frac{a}{n} + x\right)
&& \text{for $k = n$}
\end{align}

in place of the following expression:

\begin{equation}
\label{EQ10}
\frac{n!}{(n-k)!}\left(\frac{a}{n}\right)^k=
\begin{cases}
G(0)&\quad\text{if $k < n$,}\\
F(0)&\quad\text{if $k = n$.}
\end{cases}
\end{equation}

Equation \eqref{EQ10} can be obtained from equations \eqref{EQ8} and \eqref{EQ9} in the same way as
equations \eqref{EQ3} and \eqref{EQ4} have previously been shown to match equations \eqref{EQ1} and
\eqref{EQ2} for $x_1 = 0$.

Since every such replacement takes place within a sum of nonnegative terms, $P$ can be proven to be
increasingly less than $P_0$ for increasingly nonuniform probability distributions -- which implies
that the probability of event $E$ is maximum in case of equiprobable buckets -- by proving that
functions $G$ and $F$ are strictly decreasing in $[0, b]$, where $b = a(n-1)/n$.

The slopes of the segments joining points $(0, G(0))$, $(b, G(b))$ and $(0, F(0))$, $(b, F(b))$ are:

\begin{align*}
\frac{G(b)-G(0)}{b-0}&=\frac{0-\dfrac{n!}{(n-k)!}\left(\dfrac{a}{n}\right)^k}{b}<0\text{,}\\
\frac{F(b)-F(0)}{b-0}&=\frac{0-n!\left(\dfrac{a}{n}\right)^n}{b}<0\text{.}
\end{align*}

Therefore, by Lagrange's mean value theorem, there exist $c, d \in (0, b)$ such that $G'(c) < 0$ and
$F'(d) < 0$. On the other hand, it is:

\begin{align*}
G'(x)&=-k\frac{(n-1)!}{(n-k)!}\frac{n-k}{n-1}\left(\frac{a}{n}-\frac{x}{n-1}\right)^{k-1}\\
&\quad-k\frac{(n-1)!}{(n-k)!}\frac{k-1}{n-1}\left(\frac{a}{n}-\frac{x}{n-1}\right)^{k-2}
\left(\frac{a}{n}+x\right)\\
&\quad+k\frac{(n-1)!}{(n-k)!}\left(\frac{a}{n}-\frac{x}{n-1}\right)^{k-1}\text{,}\\
F'(x)&=-n!\left(\frac{a}{n}-\frac{x}{n-1}\right)^{n-2}
\left(\frac{a}{n}+x\right)
+n!\left(\frac{a}{n}-\frac{x}{n-1}\right)^{n-1}\text{.}
\end{align*}

Thus, solving equations $G'(x) = 0$ and $F'(x) = 0$ for $x \neq b$, viz. for $a/n - x/(n-1) \neq 0$,
it results:

\begin{align*}
&G'(x)=0\\
&\quad\Rightarrow\bcancel{k\frac{(n-1)!}{(n-k)!}\left(\frac{a}{n}-\frac{x}{n-1}\right)^{k-2}}
\biggl[\frac{k-n}{n-1}\left(\frac{a}{n}-\frac{x}{n-1}\right)\\
&\quad\quad\quad+\frac{1-k}{n-1}\left(\frac{a}{n}+x\right)+\frac{a}{n}-\frac{x}{n-1}\biggr]=0\\
&\quad\Rightarrow\frac{1}{\bcancel{n(n-1)^2}}\bigl\{(k-n)[(n-1)a-nx]+(1-k)[(n-1)a+n(n-1)x]\\
&\quad\quad\quad+(n-1)^2a-n(n-1)x\bigr\}=0\\
&\quad\Rightarrow\bcancel{k(n-1)a}-knx-n(n-1)a+n^2x+(n-1)a+\bcancel{n(n-1)x}\\
&\quad\quad\quad-\bcancel{k(n-1)a}-kn(n-1)x+(n-1)^2a-\bcancel{n(n-1)x}=0\\
&\quad\Rightarrow-\bcancel{knx}-\bcancel{n^2a}+\bcancel{na}+n^2x+\bcancel{na}-\bcancel{a}
-kn^2x+\bcancel{knx}+\bcancel{n^2a}-\bcancel{2na}+\bcancel{a}=0\\
&\quad\Rightarrow\bcancel{n^2(1-k)}x=0\\
&\quad\Rightarrow x=0\text{,}
\end{align*}

\begin{align*}
&F'(x)=0\\
&\quad\Rightarrow\bcancel{n!\left(\frac{a}{n}-\frac{x}{n-1}\right)^{n-2}}
\left(-\bcancel{\frac{a}{n}}-x+\bcancel{\frac{a}{n}}-\frac{x}{n-1}\right)=0\\
&\quad\Rightarrow\bcancel{\frac{n}{1-n}}x=0\\
&\quad\Rightarrow x=0\text{.}
\end{align*}

Hence, there is no $x \in (0, b)$ such that $G'(x) = 0$ or $F'(x) = 0$. Moreover, if there existed
$y, z \in (0, b)$ such that $G'(y) > 0$ or $F'(z) > 0$, by Bolzano's theorem there would also exist
$u, v$ in the open intervals with endpoints $c, y$ and $d, z$, both included in $(0, b)$, such that
$G'(u) = 0$ or $F'(v) = 0$, which is not the case. Therefore, $G'(x)$ and $F'(x)$ are negative for
any $x \in (0, b)$, so that functions $G$ and $F$ are strictly decreasing in $[0, b]$, Q.E.D..
\<close>

subsubsection "Buckets' probability -- Implementation"

text \<open>
\label{SEC2}

Given $n > 1$ buckets, numbered with indices 0 to $n - 1$, and a finite set $A$ of objects having
minimum key $mi$ and maximum key $ma$, let $E(k)$, $I(mi,ma)$ be the following events, defined as
subsets of the whole range $R$ of function $key$, with $k$ varying over $R$:

\begin{align*}
E(k)&\equiv\{k'\in R.\;k'\leq k\}\\
I(mi,ma)&\equiv\{k'\in R.\;mi\leq k'\leq ma\}
\end{align*}

Furthermore, define functions $r$, $f$ as follows:

\begin{align*}
r(k,n,mi,ma)&\equiv (n-1)\cdot P(E(k)\;|\;I(mi,ma))\\
f(k,n,mi,ma)&\equiv floor(r(k,n,mi,ma))
\end{align*}

where $P(E(k)\;|\;I(mi,ma))$ denotes the conditional probability of event $E(k)$, viz. for a key not
to be larger than $k$, given event $I(mi,ma)$, viz. if the key is comprised between $mi$ and $ma$.

Then, the buckets' probabilities can be made as much uniform as possible by placing each object $x
\in A$ into the bucket whose index matches the following value:

\begin{equation*}
index(key,x,n,mi,ma)\equiv f(key(x),n,mi,ma)
\end{equation*}

For example, given $n = 5$ buckets, suppose that the image of set $A$ under function $key$ consists
of keys $k_1 = mi$, $k_2$, ..., $k_9 = ma$, where the conditional probabilities for a key comprised
between $k_1$ and $k_9$ to match each of these keys have the following values:

\begin{align*}
P_1&=0.05,\\
P_2&=0.05,\\
P_3&=0.15,\\
P_4&=0.075,\\
P_5&=0.2,\\
P_6&=0.025,\\
P_7&=0.1,\\
P_8&=0.25,\\
P_9&=0.1
\end{align*}

Evidently, there is no way of partitioning set $\{k_1, ..., k_9\}$ into five equiprobable subsets
comprised of contiguous keys. However, it results:

\begin{equation*}
floor\left(4\cdot\sum_{i=1}^{n}P_i\right)=
\begin{cases}
0&\quad\text{for $n = 1, 2$,}\\
1&\quad\text{for $n = 3, 4$,}\\
2&\quad\text{for $n = 5, 6, 7$,}\\
3&\quad\text{for $n = 8$,}\\
4&\quad\text{for $n = 9$.}
\end{cases}
\end{equation*}

Hence, in spite of the highly nonuniform distribution of the keys' probabilities -- key $k_8$'s
probability is 10 times that of key $k_6$ --, function $index$ manages all the same to split the
objects in $A$ so as to make the buckets' probabilities more uniform -- with the maximum one being
about 3 times the minimum one --, as follows:

\begin{itemize}

\item
Bucket 0 has probability 0.1, as it collects the objects with keys $k_1$, $k_2$.

\item
Bucket 1 has probability 0.225, as it collects the objects with keys $k_3$, $k_4$.

\item
Bucket 2 has probability 0.325, as it collects the objects with keys $k_5$, $k_6$, $k_7$.

\item
Bucket 3 has probability 0.25, as it collects the objects with key $k_8$.

\item
Bucket 4 has probability 0.1, as it collects the objects with key $k_9$.

\end{itemize}

Remarkably, function $index$ makes the buckets' probabilities exactly or almost uniform -- meaning
that the maximum one is at most twice the minimum nonzero one, possibly except for the last bucket
alone -- in the following most common, even though special, cases:

\begin{enumerate}

\item
$I(mi,ma)$ is a finite set of equiprobable keys.

\item
$I(mi,ma)$ is a closed interval of real numbers, i.e. $I(mi,ma) = [mi,ma] \subset \mathbb{R}$, with
$P(\{mi\}) = 0$, and function $r$ is continuous for $k \in [mi,ma]$.

\end{enumerate}

In case 1, let $m$ be the cardinality of $I(mi,ma)$. It is $m > 0$ since $mi \in I(mi,ma)$, so that
each key in $I(mi,ma)$ has probability $1/m$.

If $m \leq n - 1$, then $(n - 1)/m \geq 1$, thus $f$ is nonzero and strictly increasing for $k \in
I(mi,ma)$. Thus, in this subcase function $index$ fills exactly $m$ buckets, one for each single key
in $I(mi,ma)$, whereas the remaining $n - m$ buckets, particularly the first one, are left unused.
Therefore, every used bucket has probability $1/m$.

If $m > n - 1$ and $m$ is divisible by $n - 1$, let $q > 1$ be the quotient of the division, so that
$m = q(n - 1)$. Dividing both sides of this equation by $m(n - 1)$, it turns out that $1/(n - 1) =
q/m$, and then $1/(n - 1) - 1/m = (q - 1)/m$. Hence, $f$ matches zero for the first $q - 1$ keys in
$I(mi,ma)$, increases by one for each of the $n - 2$ subsequent groups of $q$ contiguous keys, and
reaches value $n - 1$ in correspondence with the last key. Indeed, $q - 1 + q(n - 2) + 1 = q +
q(n - 2) = q(n - 1) = m$.

Consequently, in this subcase function $index$ places the objects mapped to the first $q - 1$ keys
into the first bucket -- which then has probability $(q - 1)/m$ --, the objects mapped to the $i$-th
subsequent group of $q$ keys, where $1 \leq i \leq n - 2$, into the bucket with index $i$ -- which
then has probability $q/m$ -- and the objects mapped to the last key into the last bucket -- which
then has probability $1/m$ --. Since $2(q - 1)/m = 2q/m - 2/m \geq 2q/m - q/m = q/m$, the maximum
probability is at most twice the minimum one, excluding the last bucket if $q > 2$.

If $m > n - 1$ and $m$ is not divisible by $n - 1$, let $q$, $r$ be the quotient and the remainder
of the division, where $q > 0$ and $n - 1 > r > 0$. For any $i > 0$, it is:

\begin{align}
\nonumber
&m=q(n-1)+r\\
\nonumber
&\quad\Rightarrow\frac{\bcancel{m}}{\bcancel{m}(n-1)}=
\frac{q\bcancel{(n-1)}}{m\bcancel{(n-1)}}+\frac{r}{m(n-1)}\\
\nonumber
&\quad\Rightarrow\frac{i}{n-1}=\frac{iq}{m}+i\frac{r}{m(n-1)}\\
\label{EQ11}
&\quad\Rightarrow\frac{iq}{m}=\frac{i}{n-1}-\left(i\frac{r}{n-1}\right)\frac{1}{m}\\
\label{EQ12}
&\quad\Rightarrow\frac{iq+1}{m}=\frac{i}{n-1}+\left(1-i\frac{r}{n-1}\right)\frac{1}{m}
\end{align}

Both equations \eqref{EQ11} and \eqref{EQ12} have something significant to say for $i = 1$.

Equation \eqref{EQ11} takes the following form:

\begin{equation*}
\frac{q}{m}=\frac{1}{n-1}-\left(\frac{r}{n-1}\right)\frac{1}{m}
\end{equation*}

where $r/(n - 1) > 0$, so that $q/m < 1/(n - 1)$. This implies that, if $k$ is the first key in
$I(mi,ma)$ for which $f$ matches any given value, the subsequent $q - 1$ keys are never sufficient
to increase $f$ by one. Thus, function $index$ fills every bucket but the last one -- which collects
the objects mapped to the last key only -- with the objects mapped to $1 + q - 1 = q$ keys at least.

For its part, equation \eqref{EQ12} takes the following form:

\begin{equation*}
\frac{q+1}{m}=\frac{1}{n-1}+\left(1-\frac{r}{n-1}\right)\frac{1}{m}
\end{equation*}

where $1 - r/(n - 1) > 0$, so that $(q + 1)/m > 1/(n - 1)$. Therefore, the $q$ keys following any
aforesaid key $k$ are always sufficient to increase $f$ by one. Hence, function $index$ fills every
bucket with the objects mapped to $1 + q = q + 1$ keys at most. A further consequence is that $f$
changes from zero to one for $k$ matching the $(q + 1)$-th key in $I(mi,ma)$, which entails that the
first bucket collects the objects mapped to exactly the first $q$ keys.

Which is the first $i_1$, if any, such that the bucket with index $i_1$ collects the objects mapped
to $q + 1$, rather than $q$, keys? Such bucket, if any, is preceded by $i_1$ buckets (as indices are
zero-based), whose total probability is $i_1q/m$ (as each of those buckets accommodates a group of
$q$ keys). So, $i_1$ is the least index, if any, such that $0 < i_1 < n - 1$ and $[(i_1 + 1)q + 1]/m
< (i_1 + 1)/(n - 1)$. Rewriting the latter inequality using equation \eqref{EQ12}, it results:

\begin{align*}
&\bcancel{\frac{i_1+1}{n-1}}+\left[1-(i_1+1)\frac{r}{n-1}\right]\frac{1}{m}<
\bcancel{\frac{i_1+1}{n-1}}\\
&\quad\Rightarrow\left[1-(i_1+1)\frac{r}{n-1}\right]\bcancel{\frac{1}{m}}<0\\
&\quad\Rightarrow(i_1+1)\frac{r}{n-1}>1\\
&\quad\Rightarrow i_1>\frac{n-1}{r}-1
\end{align*}

where $(n - 1)/r - 1 > 0$ since $r < n - 1$. Hence, index $i_1$ there exists just in case:

\begin{align*}
&\frac{n-1}{r}-1<n-2\\
&\quad\Rightarrow\frac{\bcancel{n-1}}{r}<\bcancel{n-1}\\
&\quad\Rightarrow r>1
\end{align*}

Likewise, let $i_2$ be the next index, if any, such that the bucket with index $i_2$ accommodates a
group of $q + 1$ keys. Such bucket, if any, is preceded by $i_2 - 1$ buckets accommodating $q$ keys
and one bucket accommodating $q + 1$ keys, whose total probability is $(i_2q + 1)/m$. Thus, $i_2$ is
the least index, if any, such that $i_1 < i_2 < n - 1$ and $[(i_2 + 1)q + 2]/m < (i_2 + 1)/(n - 1)$.
Adding term $1/m$ to both sides of equation \eqref{EQ12}, the latter inequality can be rewritten as
follows:

\begin{align*}
&\bcancel{\frac{i_2+1}{n-1}}+\left[2-(i_2+1)\frac{r}{n-1}\right]\frac{1}{m}<
\bcancel{\frac{i_2+1}{n-1}}\\
&\quad\Rightarrow\left[2-(i_2+1)\frac{r}{n-1}\right]\bcancel{\frac{1}{m}}<0\\
&\quad\Rightarrow(i_2+1)\frac{r}{n-1}>2\\
&\quad\Rightarrow i_2>\frac{2(n-1)}{r}-1
\end{align*}

where $2(n - 1)/r - 1 > [(n - 1)/r - 1] + 1 \geq i_1$. Hence, index $i_2$ there exists just in case:

\begin{align*}
&\frac{2(n-1)}{r}-1<n-2\\
&\quad\Rightarrow\frac{2\bcancel{(n-1)}}{r}<\bcancel{n-1}\\
&\quad\Rightarrow r>2
\end{align*}

To sum up, in this subcase function $index$ turns out to work as follows:

\begin{itemize}

\item
The $r - 1$ buckets whose indices $i_j$ match the least solutions of inequalities $i_j > j(n - 1)/r
- 1$, for $1 \leq j \leq r - 1$, accommodate a group of $q + 1$ contiguous keys each, so that each
one has probability $(q + 1)/m$.

\item
The other $n - 1 - (r - 1) = n - r$ buckets excluding the last one, particularly the first bucket,
accommodate a group of $q$ contiguous keys each, so that each one has probability $q/m$.

\item
The last bucket accommodates the last key alone, so that its probability is $1/m$.

\end{itemize}

Indeed, $(q + 1)(r - 1) + q(n - r) + 1 = \bcancel{qr} - q + r - \bcancel{1} + qn - \bcancel{qr} +
\bcancel{1} = q(n - 1) + r = m$. Furthermore, being $2q/m \geq (q + 1)/m$, the maximum value among
buckets' probabilities is at most twice the minimum one, excluding the last bucket if $q > 2$.

Two further observations can be made concerning case 1. First, if $m > n - 1$, then the larger $q$
gets, the more efficient it becomes to use the buckets' number $n$ itself instead of $n - 1$ within
function $r$, placing the objects with index $n$, viz. mapped to the last key, into the bucket with
index $n - 1$. In fact, this ensures that all the buckets have almost uniform probabilities rather
than leaving a bucket, the last one, with a small, or even negligible, probability.

Second, if keys are integers and $I(mi,ma)$ includes all the integers comprised between $mi$ and
$ma$, it is $m = ma - mi + 1$, whereas the cardinality of set $E(k) \cap I(mi,ma)$ is $k - mi + 1$
for any $k \in I(mi,ma)$. Therefore, it results:

\begin{equation*}
r(k,n,mi,ma)=(n-1)\frac{k - mi + 1}{ma - mi + 1},
\end{equation*}

so that function $r$ resembles the approximate rank function $R$ described in \cite{R3}.

In case 2, let $Z$ be the set of the integers $i$ such that $0 \leq i \leq n-1$. As $r(k,n,mi,ma)$
matches 0 for $k = mi$ and $n-1$ for $k = ma$, by the intermediate value theorem, for each $i \in Z$
there exists a least $k_i \in [mi,ma]$ such that $r(k_i,n,mi,ma) = i$, where $k_0 = mi$. Then, let
$B_i = [k_i, k_{i+1})$ for each $i \in Z - \{n-1\}$ and $B_{n-1} = [k_{n-1}, ma]$.

For any $i \in Z - \{n-1\}$, $k \in B_i$, it is $r(k,n,mi,ma) \neq i+1$, since otherwise there would
exist some $k < k_{i+1}$ in $[mi,ma]$ such that $r(k,n,mi,ma) = i+1$. On the other hand, being $k <
k_{i+1}$, it is $r(k,n,mi,ma) \leq i+1$, since function $r$ is increasing with respect to variable
$k$. Hence, it turns out that $r(k,n,mi,ma) < i+1$. Moreover, the monotonicity of $r$ also implies
that $r(k,n,mi,ma) \geq i$. Therefore, it is $f(k,n,mi,ma) = i$, so that for any $i \in Z$, function
$index$ fills the bucket with index $i$ with the objects mapped to the keys in $B_i$.

Consequently, for each $i \in Z - \{n-1\}$, the probability of the bucket with index $i$ is:

\begin{align*}
&P(B_i\;|\;I(mi,ma))\\
&\quad=\frac{P(B_i\cap I(mi,ma))}{P(I(mi,ma))}\\
&\quad=\frac{P((k_i,k_{i+1}]\cap I(mi,ma))}{P(I(mi,ma))}\\
&\quad=\frac{P(E(k_{i+1})\cap I(mi,ma))-P(E(k_i)\cap I(mi,ma))}{P(I(mi,ma))}\\
&\quad=\frac{P(E(k_{i+1})\cap I(mi,ma))}{P(I(mi,ma))}-\frac{P(E(k_i)\cap I(mi,ma))}{P(I(mi,ma))}\\
&\quad=P(E(k_{i+1})\;|\;I(mi,ma))-P(E(k_i)\;|\;I(mi,ma))\\
&\quad=\frac{(n-1)\cdot P(E(k_{i+1})\;|\;I(mi,ma))-(n-1)\cdot P(E(k_i)\;|\;I(mi,ma))}{n-1}\\
&\quad=\frac{r(k_{i+1},n,mi,ma)-r(k_i,n,mi,ma)}{n-1}\\
&\quad=\frac{\bcancel{i}+1-\bcancel{i}}{n-1}\\
&\quad=\frac{1}{n-1}
\end{align*}

Observe that the computation uses:

\begin{itemize}

\item
The definition of conditional probability.

\item
The fact that events $B_i$ and $(k_i, k_{i+1}]$ differ by singletons $\{k_i\}$ and $\{k_{i+1}\}$,
whose probability is zero.
\\Indeed, it is $P(\{k_0\}) = P(\{mi\}) = 0$ by hypothesis, whereas for any $k \in (mi,ma]$, it is
$P(\{k\}) = 0$ due to the continuity of function $r$, and then of function $P(E(k) \cap I(mi,ma))$,
in point $k$. In fact, for any $k' \in (mi,k)$ it is $E(k') \cap I(mi,ma) = [mi,k'] \subset [mi,k)$,
so that $P(E(k') \cap I(mi,ma)) \leq P([mi,k))$. However, it is also $E(k) \cap I(mi,ma) = [mi,k] =
[mi,k) \cup \{k\}$, so that $P(E(k) \cap I(mi,ma)) = P([mi,k)) + P(\{k\})$. Thus, if $P(\{k\}) > 0$,
then $P(E(k) \cap I(mi,ma)) > P([mi,k))$, in contradiction with the assumption that:

\begin{equation*}
\lim_{k'\to k^-}P(E(k') \cap I(mi,ma))=P(E(k) \cap I(mi,ma))
\end{equation*}

\item
The fact that event $E(k_{i+1}) \cap I(mi,ma)$ is equal to the union of the disjoint events $E(k_i)
\cap I(mi,ma)$ and $(k_i, k_{i+1}] \cap I(mi,ma)$, so that the probability of the former event is
equal to the sum of the probabilities of the latter ones.

\end{itemize}

As a result, all the buckets but the last one are equiprobable, whereas the last one has probability
zero. Thus, in this case it is again more efficient to replace $n - 1$ with $n$ within function $r$,
assigning the objects with index $n$, viz. mapped to the keys falling in $B_n$, to the bucket with
index $n - 1$, which ensures that all the buckets have uniform probabilities.

If function $r$ is linear for $k \in [mi,ma]$, viz. if interval $[mi,ma]$ is endowed with a constant
probability density, then the function's graph (with factor $n - 1$ replaced by $n$) is the straight
line passing through points $(mi,0)$ and $(ma,n)$. Therefore, it results:

\begin{equation*}
r(k,n,mi,ma)=n\frac{k - mi}{ma - mi},
\end{equation*}

so that function $r$ matches the approximate rank function $R$ described in \cite{R3}.
\<close>

subsubsection "Buckets' number -- Proof"

text \<open>
\label{SEC3}

Given $n$ equiprobable buckets and $k$ objects to be partitioned randomly among such buckets, where
$1 < k \leq n$, the probability $P_{n,k}$ that each bucket will contain at most one object is given
by equation \eqref{EQ1}, namely:

\begin{equation*}
P_{n,k}=\frac{n!}{(n-k)!n^k}
\end{equation*}

Thus, it is:

\begin{align*}
&P_{n+1,k}-P_{n,k}\\
&\quad=\frac{(n+1)!}{(n-k+1)(n-k)!(n+1)^k}-\frac{n!}{(n-k)!n^k}\\
&\quad=\frac{(n+1)!n^k-n!(n-k+1)(n+1)^k}{(n-k+1)(n-k)!n^k(n+1)^k}
\end{align*}

Using the binomial theorem and Pascal's rule, the numerator of the fraction in the right-hand side
of this equation can be expressed as follows:

\begin{align*}
&(n+1)!n^k-(n-k+1)n!(n+1)^k\\
&\quad=n!(n+1)n^k+n!k(n+1)^k-n!n(n+1)^k-n!(n+1)^k\\
&\quad=n!n^{k+1}+n!n^k\\
&\quad\quad+n!k\left[n^k+\binom{k}{1}n^{k-1}+\binom{k}{2}n^{k-2}+...
+\binom{k}{k-1}n+\binom{k}{k}\right]\\
&\quad\quad-n!n\left[n^k+\binom{k}{1}n^{k-1}+\binom{k}{2}n^{k-2}+...
+\binom{k}{k-1}n+\binom{k}{k}\right]\\
&\quad\quad-n!\left[n^k+\binom{k}{1}n^{k-1}+\binom{k}{2}n^{k-2}+...
+\binom{k}{k-1}n+\binom{k}{k}\right]\\
&\quad=\bcancel{n!n^{k+1}}+\bcancel{n!n^k}+\bcancel{n!kn^k}\\
&\quad\quad+n!k\binom{k}{1}n^{k-1}+n!k\binom{k}{2}n^{k-2}+...
+n!k\binom{k}{k-1}n+n!k\\
&\quad\quad-\bcancel{n!n^{k+1}}-\bcancel{n!kn^k}-n!\binom{k}{2}n^{k-1}-...
-n!\binom{k}{k-1}n^2-n!\binom{k}{k}n\\
&\quad\quad-\bcancel{n!n^k}-n!\binom{k}{1}n^{k-1}-n!\binom{k}{2}n^{k-2}-...
-n!\binom{k}{k-1}n-n!\\
&\quad=n!(k-1)+n!n^{k-1}\left[k\binom{k}{1}-\binom{k}{1}-\binom{k}{2}\right]+...\\
&\quad\quad+n!n\left[k\binom{k}{k-1}-\binom{k}{k-1}-\binom{k}{k}\right]\\
&\quad=n!(k-1)+n!\cdot\sum_{i=1}^{k-1}
n^{k-i}\left\{k\binom{k}{i}-\left[\binom{k}{i}+\binom{k}{i+1}\right]\right\}\\
&\quad=n!(k-1)+n!\cdot\sum_{i=1}^{k-1}
n^{k-i}\left[k\binom{k}{i}-\binom{k+1}{i+1}\right]\\
&\quad=n!(k-1)+n!\cdot\sum_{i=1}^{k-1}
n^{k-i}\left[\frac{kk!}{i!(k-i)!}-\frac{(k+1)!}{(i+1)i!(k-i)!}\right]\\
&\quad=n!(k-1)+n!\cdot\sum_{i=1}^{k-1}
n^{k-i}k!\frac{(i+1)k-(k+1)}{(i+1)i!(k-i)!}\\
&\quad=n!(k-1)+n!\cdot\sum_{i=1}^{k-1}
n^{k-i}k!\frac{ik-1}{(i+1)i!(k-i)!}>0
\end{align*}

Therefore, for any fixed $k > 1$, sequence $(P_{n,k})_{n \geq k}$ is strictly increasing, viz. the
larger $n$ is, such is also the probability that each of the $n$ equiprobable buckets will contain
at most one of the $k$ given objects.

Moreover, it is $P_{n,k} = [n(n-1)(n-2)(n-3)...(n-k+1)]/n^k < n^k/n^k = 1$, as the product enclosed
within the square brackets comprises $k$ factors, one equal to $n$ and the other ones less than $n$.

On the other hand, it turns out that:

\begin{align*}
&n(n-1)(n-2)(n-3)...(n-k+1)\\
&\quad=n^2[(n-2)(n-3)...(n-k+1)]-n[(n-2)(n-3)...(n-k+1)]\\
&\quad\geq n^2[(n-2)(n-3)...(n-k+1)]-n\cdot n^{k-2}\\
&\quad=n[n(n-2)(n-3)...(n-k+1)]-n^{k-1}\\
&\quad=n\cdot n^2[(n-3)...(n-k+1)]-n\cdot 2n[(n-3)...(n-k+1)]-n^{k-1}\\
&\quad\geq n^3[(n-3)...(n-k+1)]-2n^2\cdot n^{k-3}-n^{k-1}\\
&\quad=n^2[n(n-3)...(n-k+1)]-(1+2)n^{k-1}\;...
\end{align*}

Hence, applying the same line of reasoning until the product within the square brackets disappears,
it results:

\begin{align*}
&n(n-1)(n-2)(n-3)...(n-k+1)\\
&\quad\geq n^k-[1+2+...+(k-1)]n^{k-1}\\
&\quad=n^k-\frac{k(k-1)}{2}n^{k-1},
\end{align*}

so that:

\begin{equation*}
P_{n,k}=\frac{n(n-1)(n-2)(n-3)...(n-k+1)}{n^k}\geq 1-\frac{k(k-1)}{2n}
\end{equation*}

Therefore, for any fixed $k > 1$, the terms of sequence $(P_{n,k})_{n \geq k}$ are comprised between
the corresponding terms of sequence $(1 - k(k-1)/2n)_{n \geq k}$ and constant sequence $(1)_{n \geq
k}$. Since both of these sequences converge to 1, by the squeeze theorem it is:

\begin{equation*}
\lim_{n\to\infty}P_{n,k}=1,
\end{equation*}

viz. the larger $n$ is, the closer to 1 is the probability that each of the $n$ equiprobable buckets
will contain at most one of the $k$ given objects.

As a result, the probability of placing at most one object into each bucket in any algorithm's round
is maximized by increasing the number of the buckets as much as possible, Q.E.D..
\<close>

subsubsection "Buckets' number -- Implementation"

text \<open>
\label{SEC4}

Let $n$ be the number of the objects to be sorted, and $p$ the upper bound on the counters' number
-- and then on the buckets' number as well, since there must be exactly one counter per bucket --.
This means that before the round begins, the objects to be split are located in $m$ buckets $B_1$,
..., $B_m$, where $0 < m \leq p$, respectively containing $n_1$, ..., $n_m$ objects, where $n_i > 0$
for each $i$ from 1 to $m$ and $n_1 + ... + n_m = n$.

Moreover, let $c$ be the number of the objects known to be the sole elements of their buckets, viz.
to require no partition into finer-grained buckets, at the beginning of a given algorithm's round.
Then, the number of the objects requiring to be split into finer-grained buckets in that round is
$n - c$, whereas the number of the available buckets is $p - c$, since $c$ counters must be left to
store as many 1s, one for each singleton bucket.

How to compute $c$? At first glance, the answer seems trivial: by counting, among the counters input
(either by the algorithm's caller or by the previous round) to the round under consideration, those
that match 1. However, this value would not take into account the fact that, for each non-singleton
bucket, the algorithm must find the leftmost occurrence of the minimum key, as well as the rightmost
occurrence of the maximum key, and place the corresponding objects into two new singleton buckets,
which shall be the first and the last finer-grained bucket, respectively.

The most fundamental reason for this is that, as a result of the partition of such a bucket, nothing
prevents all its objects from falling in the same finer-grained bucket -- particularly, this happens
whenever all its objects have the same key --, in which case the algorithm does not terminate unless
some object is removed from the bucket prior to the partition, so as to reduce its size. Just as
clearly, the algorithm must know where to place the finer-grained buckets containing the removed
objects with respect to the finer-grained buckets resulting from the partition. This is exactly what
is ensured by removing objects with minimum or maximum keys, whereas selecting the leftmost or the
rightmost ones, respectively, preserves the algorithm's stability.

Actually, the algorithm's termination requires the removal of at least one object per non-singleton
bucket, so the removal of one object only, either with minimum or maximum key, would be sufficient.
Nonetheless, the leftmost minimum and the rightmost maximum can be searched via a single loop, and
finding both of them enables to pass them as inputs to the function $index$ described in section
\ref{SEC2}, or to whatever other function used to split buckets into finer-grained ones. Moreover,
non-singleton buckets whose objects all have the same key can be detected as those whose minimum and
maximum keys are equal. This allows to optimize the algorithm by preventing it from unnecessarily
applying multiple recursive rounds to any such bucket; it shall rather be left as is, just replacing
its counter with as many 1s as its size to indicate that it is already sorted.

Therefore, as the round begins, the objects already known to be placed in singleton buckets are one
for each bucket whose counter matches 1, and two for each bucket whose counter is larger than 1. As
a result, $c$ shall be computed as follows. First, initialize $c$ to zero. Then, for each $i$ from 1
to $m$, increase $c$ by one if $n_i = 1$, by two otherwise.

Conversely, for any such $i$, the number $N_i$ of the objects contained in bucket $B_i$ having to be
partitioned into finer-grained buckets is 0 if $n_i = 1$, $n_i - 2$ otherwise, so that $N_1 + ... +
N_m = n - c$. According to the findings of section \ref{SEC3}, the number $N'_i$ of the resulting
finer-grained buckets should be maximized, and the most efficient way to do this is to render $N'_i$
proportional to $N_i$, since otherwise, viz. if some buckets were preferred to some other ones, the
unprivileged buckets would form as many bottlenecks.

This can be accomplished by means of the following procedure. First, initialize integers $R$ and $U$
to 0. Then, for each $i$ from 1 to $m$, check whether $N_i \leq 1$:

\begin{itemize}

\item
If so, set $N'_i$ to $N_i$.
\\In fact, no finer-grained bucket is necessary if there are no objects to be split, while a single
finer-grained bucket is sufficient for a lonely object.

\item
Otherwise, perform the integer division of $N_i \cdot (p - c) + R$ by $n - c$, and set integer $Q$
to the resulting quotient and $R$ to the resulting remainder. Then, if the minimum and maximum keys
occurring in bucket $B_i$ are equal, increase $U$ by $Q - N_i$, otherwise set $N'_i$ to $U + Q$ and
reset $U$ to 0.
\\In fact, as observed above, if its minimum and maximum keys are equal, bucket $B_i$ can be split
into $n_i = N_i + 2$ singleton buckets. Hence, the difference $Q - N_i$ between the number of the
available finer-grained buckets, i.e. $Q + 2$ (where 2 is the number of the buckets containing the
leftmost minimum and the rightmost maximum), and the number of those being used, i.e. $N_i + 2$, can
be added to the total number $U$ of the available finer-grained buckets still unused in the current
round. Such buckets can then be utilized as soon as a bucket $B_j$ with $N_j > 1$ whose minimum and
maximum keys do not match is encountered next, in addition to those already reserved for $B_j$.

\end{itemize}

Of course, for any $i$ from 1 to $m$ such that $N_i > 1$, it is $N_i \leq Q$ -- viz. the number of
the objects in $B_i$ to be split is not larger than that of the finer-grained buckets where they are
to be placed even if $U = 0$, so that the probability of placing at most one object into each bucket
is nonzero -- just in case $n - c \leq p - c$, i.e. $n \leq p$. Indeed, it will be formally proven
that for $n \leq p$, this procedure is successful in maximizing the buckets' number in each round
never exceeding the upper bound $p$.
\<close>

subsubsection "Generalized counting sort (GCsort)"

text \<open>
The conclusions of the efficiency analysis performed so far, put together, result in the following
\emph{generalized counting sort (GCsort)} algorithm.

Let $xs$ be the input array containing $n$ objects to be sorted, and $ns$ an array of $p$ integers,
where $0 < p$ and $n \leq p$. Moreover, let $xs'$ and $ns'$ be two further arrays of the same type
and size of $xs$ and $ns$, respectively, and let $i$, $i'$, and $j$ be as many integers.

Then, GCsort works as follows (assuming arrays to be zero-based):

\begin{enumerate}

\item
Initialize the first element of $ns$ to $n$ and any other element to 0.

\item
Check whether $ns$ contains any element larger than 1.
\\If not, terminate the algorithm and output $xs$ as the resulting sorted array.

\item
Initialize $i$, $i'$, and $j$ to 0.

\item
Check whether $ns[i] = 1$ or $ns[i] > 1$:

  \begin{enumerate}

  \item
  In the former case, set $xs'[j]$ to $xs[j]$ and $ns'[i']$ to 1.
  \\Then, increase $i'$ and $j$ by 1.

  \item
  In the latter case, partition the bucket comprised of objects $xs[j]$ to $xs[j+ns[i]-1]$ into
  finer-grained buckets according to section \ref{SEC4}, storing the resulting $n'$ buckets in
  $xs'[j]$ to $xs'[j+ns[i]-1]$ and their sizes in $ns'[i']$ to $ns'[i'+n'-1]$.
  \\Then, increase $i'$ by $n'$ and $j$ by $ns[i]$.

  \end{enumerate}

\item
Increase $i$ by 1, and then check whether $i < p$.
\\If so, go back to step 4.
\\Otherwise, perform the following operations:

  \begin{enumerate}

  \item
  If $i' < p$, set integers $ns'[i']$ to $ns'[p-1]$ to 0.

  \item
  Swap addresses $xs$ and $xs'$, as well as addresses $ns$ and $ns'$.

  \item
  Go back to step 2.

  \end{enumerate}

\end{enumerate}

Since the algorithm is tail-recursive, the memory space required for its execution matches the one
required for a single recursive round, which is $O(n) + O(p)$.

The best-case running time can be computed easily. The running time taken by step 1 is equal to $p$.
Moreover, the partition of a bucket into finer-grained ones is performed by determining their sizes,
computing the cumulative sum of such sizes, and rearranging the bucket's objects according to the
resulting offsets. All these operations only involve sequential, non-nested loops, which iterate
through either the objects or the finer-grained counters pertaining to the processed bucket alone.
Hence, the running time taken by a single recursive round is $O(n) + O(p)$, so that in the best case
where at most one round is executed after step 1, the running time taken by the algorithm is $O(n) +
O(p)$, too.

The asymptotic worst-case running time can be computed as follows. Let $t_{n,p}$ be the worst-case
running time taken by a single round. As $t_{n,p}$ is $O(n) + O(p)$, there exist three real numbers
$a > 0$, $b > 0$, and $c$ such that $t_{n,p} \leq an + bp + c$. Moreover, let $U_{n,p}$ be the set
of the $p$-tuples of natural numbers such that the sum of their elements matches $n$, and $max(u)$
the maximum element of a given $u \in U_{n,p}$. Finally, let $T_{n,p,u}$ be the worst-case running
time taken by the algorithm if it starts from step 2, viz. skipping step 1, using as initial content
of array $ns$ the $p$-tuple $u \in U_{n,p}$.

Then, it can be proven by induction on $max(u)$ that:

\begin{equation}
\label{EQ13}
T_{n,p,u}\leq
\begin{cases}
a\dfrac{max(u)}{2}n+\left[b\dfrac{max(u)}{2}+1\right]p+c\dfrac{max(u)}{2}\\
\quad\text{if $max(u)$ is even,}\\
\\
a\dfrac{max(u)-1}{2}n+\left[b\dfrac{max(u)-1}{2}+1\right]p+c\dfrac{max(u)-1}{2}\\
\quad\text{if $max(u)$ is odd}
\end{cases}
\end{equation}

In fact, if $max(u) = 0$, the initial $p$-tuple $u$ matches the all-zero one. Hence, the algorithm
executes step 2 just once and then immediately terminates. Therefore, the running time is $p$, which
matches the right-hand side of inequality \eqref{EQ13} for $max(u) = 0$.

If $max(u) = 1$, $u$ contains no element larger than 1. Thus, again, the algorithm terminates just
after the first execution of step 2. As a result, the running time is still $p$, which matches the
right-hand side of inequality \eqref{EQ13} for $max(u) = 1$.

If $max(u) = 2$, $u$ contains some element larger than 1, so that one round is executed, taking time
$t_{n,p}$ in the worst case. Once this round is over, array $ns$ will contain a $p$-tuple $u' \in
U_{n,p}$ such that $max(u') = 1$. Hence, step 2 is executed again, taking time $p$, and then the
algorithm terminates. As a result, it is:

\begin{equation*}
T_{n,p,u}\leq an+bp+c+p=an+(b+1)p+c,
\end{equation*}

which matches the right-hand side of inequality \eqref{EQ13} for $max(u) = 2$.

Finally, if $max(u) > 2$, $u$ has some element larger than 1, so one round is executed, taking time
$t_{n,p}$ in the worst case. Once this round is over, array $ns$ will contain a $p$-tuple $u' \in
U_{n,p}$ such that $max(u') \leq max(u) - 2$, because of the removal of the leftmost minimum and the
rightmost maximum from any non-singleton bucket. By the induction hypothesis, the worst-case time
$T_{n,p,u'}$ taken by the algorithm from this point onward complies with inequality \eqref{EQ13},
whose right-hand side is maximum if such is $max(u')$, viz. if $max(u') = max(u) - 2$.

As a result, if $max(u)$ is even, it is:

\begin{align*}
&T_{n,p,u}\leq an+bp+c\\
&\quad\quad+a\frac{max(u)-2}{2}n+\left[b\frac{max(u)-2}{2}+1\right]p+c\frac{max(u)-2}{2}\\
&\quad=a\frac{max(u)}{2}n+\left[b\frac{max(u)}{2}+1\right]p+c\frac{max(u)}{2},
\end{align*}

which matches the right-hand side of inequality \eqref{EQ13} for an even $max(u)$.

Similarly, if $max(u)$ is odd, it is:

\begin{align*}
&T_{n,p,u}\leq an+bp+c\\
&\quad\quad+a\frac{max(u)-3}{2}n+\left[b\frac{max(u)-3}{2}+1\right]p+c\frac{max(u)-3}{2}\\
&\quad=a\frac{max(u)-1}{2}n+\left[b\frac{max(u)-1}{2}+1\right]p+c\frac{max(u)-1}{2},
\end{align*}

which matches the right-hand side of inequality \eqref{EQ13} for an odd $max(u)$.

With this, the proof of inequality \eqref{EQ13} is complete. Now, let $T_{n,p}$ be the worst-case
time taken by the algorithm executed in full. Step 1 is executed first, taking time $p$. Then, array
$ns$ contains a $p$-tuple $u$ such that $max(u) = n$, and by definition, the worst-case time taken
by the algorithm from this point onward is $T_{n,p,u}$. Therefore, applying inequality \eqref{EQ13},
it turns out that:

\begin{align*}
&T_{n,p}=p+T_{n,p,u}\\
&\quad\leq
\begin{cases}
a\dfrac{n^2}{2}+\left(b\dfrac{n}{2}+2\right)p+c\dfrac{n}{2}
&\quad\text{if $n$ is even,}\\
\\
a\dfrac{n^2-n}{2}+\left(b\dfrac{n-1}{2}+2\right)p+c\dfrac{n-1}{2}
&\quad\text{if $n$ is odd}
\end{cases}
\end{align*}

As a result, the asymptotic worst-case running time taken by the algorithm is $O(n^2) + O(np)$.
\<close>


subsection "Formal definitions"

text \<open>
Here below, a formal definition of GCsort is provided, which will later enable to formally prove the
correctness of the algorithm. Henceforth, the main points of the formal definitions and proofs are
commented. For further information, see Isabelle documentation, particularly \cite{R5}, \cite{R6},
\cite{R7}, and \cite{R8}.

The following formalization of GCsort does not define any specific function @{text index} to be used
to split buckets into finer-grained ones. It rather defines only the type @{text index_sign} of such
functions, matching the signature of the function $index$ described in section \ref{SEC2}, along
with three predicates that whatever chosen @{text index} function is required to satisfy for GCsort
to work correctly:

\begin{itemize}

\item
Predicate @{text index_less} requires function @{text index} to map any object within a given bucket
to an index less than the number of the associated finer-grained buckets (\emph{less than} instead
of \emph{not larger than} since type @{typ "'a list"} is zero-based).

\item
Predicate @{text index_mono} requires function @{text index} to be monotonic with respect to the
keys of the objects within a given bucket.

\item
Predicate @{text index_same} requires function @{text index} to map any two distinct objects within
a given bucket that have the same key to the same index (premise \emph{distinct} is added to enable
this predicate to be used by the simplifier).

\end{itemize}

\null
\<close>

type_synonym ('a, 'b) index_sign = "('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> nat"

definition index_less :: "('a, 'b::linorder) index_sign \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool"
where
"index_less index key \<equiv>
  \<forall>x n mi ma. key x \<in> {mi..ma} \<longrightarrow> 0 < n \<longrightarrow>
    index key x n mi ma < n"

definition index_mono :: "('a, 'b::linorder) index_sign \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool"
where
"index_mono index key \<equiv>
  \<forall>x y n mi ma. {key x, key y} \<subseteq> {mi..ma} \<longrightarrow> key x \<le> key y \<longrightarrow>
    index key x n mi ma \<le> index key y n mi ma"

definition index_same :: "('a, 'b::linorder) index_sign \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool"
where
"index_same index key \<equiv>
  \<forall>x y n mi ma. key x \<in> {mi..ma} \<longrightarrow> x \<noteq> y \<longrightarrow> key x = key y \<longrightarrow>
    index key x n mi ma = index key y n mi ma"

text \<open>
\null

Functions @{text bn_count} and @{text bn_comp} count, respectively, the objects known to be placed
in singleton buckets in a given round, and the finer-grained buckets available to partition a given
non-singleton bucket, according to section \ref{SEC4}.

\null
\<close>

fun bn_count :: "nat list \<Rightarrow> nat" where
"bn_count [] = 0" |
"bn_count (Suc (Suc (Suc (Suc n))) # ns) = Suc (Suc (bn_count ns))" |
"bn_count (n # ns) = n + bn_count ns"

fun bn_comp :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<times> nat" where
"bn_comp (Suc (Suc n)) p q r =
  ((Suc (Suc n) * p + r) div q, (Suc (Suc n) * p + r) mod q)" |
"bn_comp n p q r = (n, r)"

fun bn_valid :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
"bn_valid (Suc (Suc n)) p q = (q \<in> {0<..p})" |
"bn_valid n p q = True"

text \<open>
\null

Functions @{text mini} and @{text maxi} return the indices of the leftmost minimum and the rightmost
maximum within a given non-singleton bucket.

\null
\<close>

primrec (nonexhaustive) mini :: "'a list \<Rightarrow> ('a \<Rightarrow> 'b::linorder) \<Rightarrow> nat" where
"mini (x # xs) key =
  (let m = mini xs key in if xs = [] \<or> key x \<le> key (xs ! m) then 0 else Suc m)"

primrec (nonexhaustive) maxi :: "'a list \<Rightarrow> ('a \<Rightarrow> 'b::linorder) \<Rightarrow> nat" where
"maxi (x # xs) key =
  (let m = maxi xs key in if xs = [] \<or> key (xs ! m) < key x then 0 else Suc m)"

text \<open>
\null

Function @{text enum} counts the objects contained in each finer-grained bucket reserved for the
partition of a given non-singleton bucket.

\null
\<close>

primrec enum :: "'a list \<Rightarrow> ('a, 'b) index_sign \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow>
  nat \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> nat list" where
"enum [] index key n mi ma = replicate n 0" |
"enum (x # xs) index key n mi ma =
  (let i = index key x n mi ma;
     ns = enum xs index key n mi ma
   in ns[i := Suc (ns ! i)])"

text \<open>
\null

Function @{text offs} computes the cumulative sum of the resulting finer-grained buckets' sizes so
as to generate the associated offsets' list.

\null
\<close>

primrec offs :: "nat list \<Rightarrow> nat \<Rightarrow> nat list" where
"offs [] i = []" |
"offs (n # ns) i = i # offs ns (i + n)"

text \<open>
\null

Function @{text fill} fills the finer-grained buckets with their respective objects.

\null
\<close>

primrec fill :: "'a list \<Rightarrow> nat list \<Rightarrow> ('a, 'b) index_sign \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow>
  nat \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> 'a option list" where
"fill [] ns index key n mi ma = replicate n None" |
"fill (x # xs) ns index key n mi ma =
  (let i = index key x (length ns) mi ma;
     ys = fill xs (ns[i := Suc (ns ! i)]) index key n mi ma
   in ys[ns ! i := Some x])"

text \<open>
\null

Then, function @{text round} formalizes a single GCsort's recursive round.

\null
\<close>

definition round_suc_suc :: "('a, 'b::linorder) index_sign \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow>
  'a list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<times> nat list \<times> 'a list" where
"round_suc_suc index key ws n n' u \<equiv>
  let nmi = mini ws key; nma = maxi ws key;
    xmi = ws ! nmi; xma = ws ! nma; mi = key xmi; ma = key xma
  in if mi = ma
    then (u + n' - n, replicate (Suc (Suc n)) (Suc 0), ws)
    else
      let k = case n of Suc (Suc i) \<Rightarrow> u + n' | _ \<Rightarrow> n;
        zs = nths ws (- {nmi, nma}); ms = enum zs index key k mi ma
      in (u + n' - k, Suc 0 # ms @ [Suc 0],
        xmi # map the (fill zs (offs ms 0) index key n mi ma) @ [xma])"

fun round :: "('a, 'b::linorder) index_sign \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
  nat \<times> nat list \<times> 'a list \<Rightarrow> nat \<times> nat list \<times> 'a list" where
"round index key p q r (u, [], xs) = (u, [], xs)" |
"round index key p q r (u, 0 # ns, xs) = round index key p q r (u, ns, xs)" |
"round index key p q r (u, Suc 0 # ns, xs) =
  (let (u', ns', xs') = round index key p q r (u, ns, tl xs)
   in (u', Suc 0 # ns', hd xs # xs'))" |
"round index key p q r (u, Suc (Suc n) # ns, xs) =
  (let ws = take (Suc (Suc n)) xs; (n', r') = bn_comp n p q r;
     (v, ms', ws') = round_suc_suc index key ws n n' u;
     (u', ns', xs') = round index key p q r' (v, ns, drop (Suc (Suc n)) xs)
   in (u', ms' @ ns', ws' @ xs'))"

text \<open>
\null

Finally, function @{text gcsort_aux} formalizes GCsort. Since the algorithm is tail-recursive, this
function complies with the requirements for an auxiliary tail-recursive function applying to step 1
of the proof method described in \cite{R4} -- henceforth briefly referred to as the \emph{proof
method} --. This feature will later enable to formally prove the algorithm's correctness properties
by means of such method.

\null
\<close>

abbreviation gcsort_round :: "('a, 'b::linorder) index_sign \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow>
  nat \<Rightarrow> nat list \<Rightarrow> 'a list \<Rightarrow> nat \<times> nat list \<times> 'a list" where
"gcsort_round index key p ns xs \<equiv>
  round index key (p - bn_count ns) (length xs - bn_count ns) 0 (0, ns, xs)"

function gcsort_aux :: "('a, 'b::linorder) index_sign \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> nat \<Rightarrow>
  nat \<times> nat list \<times> 'a list \<Rightarrow> nat \<times> nat list \<times> 'a list" where
"gcsort_aux index key p (u, ns, xs) = (if find (\<lambda>n. Suc 0 < n) ns = None
  then (u, ns, xs)
  else gcsort_aux index key p (gcsort_round index key p ns xs))"
by auto

text \<open>
\null

First of all, even before accomplishing step 2 of the proof method, it is necessary to prove that
function @{const gcsort_aux} always terminates by showing that the maximum bucket's size decreases
in each recursive round.

\null
\<close>

lemma add_zeros:
 "foldl (+) (m :: nat) (replicate n 0) = m"
by (induction n, simp_all)

lemma add_suc:
 "foldl (+) (Suc m) ns = Suc (foldl (+) m ns)"
by (induction ns arbitrary: m, simp_all)

lemma add_update:
 "i < length ns \<Longrightarrow> foldl (+) m (ns[i := Suc (ns ! i)]) = Suc (foldl (+) m ns)"
by (induction ns arbitrary: i m, simp_all add: add_suc split: nat.split)

lemma add_le:
 "(m :: nat) \<le> foldl (+) m ns"
by (induction ns arbitrary: m, simp_all, rule order_trans, rule le_add1)

lemma add_mono:
 "(m :: nat) \<le> n \<Longrightarrow> foldl (+) m ns \<le> foldl (+) n ns"
by (induction ns arbitrary: m n, simp_all)

lemma add_max [rule_format]:
 "ns \<noteq> [] \<longrightarrow> Max (set ns) \<le> foldl (+) (0 :: nat) ns"
by (induction ns, simp_all add: add_le, erule impCE, simp, rule ballI, drule bspec,
 assumption, rule order_trans, assumption, rule add_mono, simp)

lemma enum_length:
 "length (enum xs index key n mi ma) = n"
by (induction xs, simp_all add: Let_def)

lemma enum_add_le:
 "foldl (+) 0 (enum xs index key n mi ma) \<le> length xs"
proof (induction xs, simp_all add: Let_def add_zeros)
  fix x xs
  let ?i = "index key x n mi ma"
  assume "foldl (+) 0 (enum xs index key n mi ma) \<le> length xs"
    (is "foldl _ _ ?ns \<le> _")
  thus "foldl (+) 0 (?ns[?i := Suc (?ns ! ?i)]) \<le> Suc (length xs)"
    by (cases "?i < length ?ns", simp_all add: add_update)
qed

lemma enum_max_le:
 "0 < n \<Longrightarrow> Max (set (enum xs index key n mi ma)) \<le> length xs"
  (is "_ \<Longrightarrow> Max (set ?ns) \<le> _")
by (insert add_max [of ?ns], insert enum_add_le [of xs index key n mi ma],
 simp only: length_greater_0_conv [symmetric] enum_length, simp)

lemma mini_less:
 "0 < length xs \<Longrightarrow> mini xs key < length xs"
by (induction xs, simp_all add: Let_def)

lemma maxi_less:
 "0 < length xs \<Longrightarrow> maxi xs key < length xs"
by (induction xs, simp_all add: Let_def)

lemma mini_lb:
 "x \<in> set xs \<Longrightarrow> key (xs ! mini xs key) \<le> key x"
by (induction xs, simp_all add: Let_def, auto)

lemma maxi_ub:
 "x \<in> set xs \<Longrightarrow> key x \<le> key (xs ! maxi xs key)"
by (induction xs, simp_all add: Let_def, auto)

lemma mini_maxi_neq [rule_format]:
 "Suc 0 < length xs \<longrightarrow> mini xs key \<noteq> maxi xs key"
proof (induction xs, simp_all add: Let_def, rule conjI, (rule impI)+,
 (rule_tac [2] impI)+, rule_tac [2] notI, simp_all, rule ccontr)
  fix x xs
  assume "key (xs ! maxi xs key) < key x" and "key x \<le> key (xs ! mini xs key)"
  hence "key (xs ! maxi xs key) < key (xs ! mini xs key)" by simp
  moreover assume "xs \<noteq> []"
  hence "0 < length xs" by simp
  hence "mini xs key < length xs"
    by (rule mini_less)
  hence "xs ! mini xs key \<in> set xs" by simp
  hence "key (xs ! mini xs key) \<le> key (xs ! maxi xs key)"
    by (rule maxi_ub)
  ultimately show False by simp
qed

lemma mini_maxi_nths:
 "length (nths xs (- {mini xs key, maxi xs key})) =
    (case length xs of 0 \<Rightarrow> 0 | Suc 0 \<Rightarrow> 0 | Suc (Suc n) \<Rightarrow> n)"
proof (simp add: length_nths split: nat.split, rule allI, rule conjI, rule_tac [2] allI,
 (rule_tac [!] impI)+, simp add: length_Suc_conv, erule exE, simp, blast)
  fix n
  assume A: "length xs = Suc (Suc n)"
  hence B: "Suc 0 < length xs" by simp
  hence C: "0 < length xs" by arith
  have "{i. i < Suc (Suc n) \<and> i \<noteq> mini xs key \<and> i \<noteq> maxi xs key} =
    {..<Suc (Suc n)} - {mini xs key} - {maxi xs key}"
    by blast
  thus "card {i. i < Suc (Suc n) \<and> i \<noteq> mini xs key \<and> i \<noteq> maxi xs key} = n"
    by (simp add: card_Diff_singleton_if, insert mini_maxi_neq [OF B, of key],
     simp add: mini_less [OF C] maxi_less [OF C] A [symmetric])
qed

lemma mini_maxi_nths_le:
 "length xs \<le> Suc (Suc n) \<Longrightarrow> length (nths xs (- {mini xs key, maxi xs key})) \<le> n"
by (simp add: mini_maxi_nths split: nat.split)

lemma round_nil:
 "(fst (snd (round index key p q r t)) \<noteq> []) = (\<exists>n \<in> set (fst (snd t)). 0 < n)"
by (induction index key p q r t rule: round.induct,
 simp_all add: round_suc_suc_def Let_def split: prod.split)

lemma round_max_eq [rule_format]:
 "fst (snd t) \<noteq> [] \<longrightarrow> Max (set (fst (snd t))) = Suc 0 \<longrightarrow>
    Max (set (fst (snd (round index key p q r t)))) = Suc 0"
proof (induction index key p q r t rule: round.induct, simp_all add: Let_def split:
 prod.split del: all_simps, rule impI, (rule_tac [2] allI)+, (rule_tac [2] impI)+,
 (rule_tac [3] allI)+, (rule_tac [3] impI)+, rule_tac [3] FalseE)
  fix index p q r u ns xs and key :: "'a \<Rightarrow> 'b"
  let ?t = "round index key p q r (u, ns, xs)"
  assume "ns \<noteq> [] \<longrightarrow> Max (set ns) = Suc 0 \<longrightarrow>
    Max (set (fst (snd ?t))) = Suc 0"
  moreover assume A: "Max (insert 0 (set ns)) = Suc 0"
  hence "ns \<noteq> []"
    by (cases ns, simp_all)
  moreover from this have "Max (set ns) = Suc 0"
    using A by simp
  ultimately show "Max (set (fst (snd ?t))) = Suc 0"
    by simp
next
  fix index p q r u ns xs u' ns' xs' and key :: "'a \<Rightarrow> 'b"
  let ?t = "round index key p q r (u, ns, tl xs)"
  assume A: "?t = (u', ns', xs')" and
   "ns \<noteq> [] \<longrightarrow> Max (set ns) = Suc 0 \<longrightarrow> Max (set (fst (snd ?t))) = Suc 0"
  hence B: "ns \<noteq> [] \<longrightarrow> Max (set ns) = Suc 0 \<longrightarrow> Max (set ns') = Suc 0"
    by simp
  assume C: "Max (insert (Suc 0) (set ns)) = Suc 0"
  show "Max (insert (Suc 0) (set ns')) = Suc 0"
  proof (cases "ns' = []", simp)
    assume D: "ns' \<noteq> []"
    hence "fst (snd ?t) \<noteq> []"
      using A by simp
    hence "\<exists>n \<in> set ns. 0 < n"
      by (simp add: round_nil)
    then obtain n where E: "n \<in> set ns" and F: "0 < n" ..
    hence G: "ns \<noteq> []"
      by (cases ns, simp_all)
    moreover have "n \<le> Max (set ns)"
      using E by (rule_tac Max_ge, simp_all)
    hence "0 < Max (set ns)"
      using F by simp
    hence "Max (set ns) = Suc 0"
      using C and G by simp
    ultimately have "Max (set ns') = Suc 0"
      using B by simp
    thus ?thesis
      using D by simp
  qed
next
  fix n ns
  assume "Max (insert (Suc (Suc n)) (set ns)) = Suc 0"
  thus False
    by (cases ns, simp_all)
qed

lemma round_max_less [rule_format]:
 "fst (snd t) \<noteq> [] \<longrightarrow> Suc 0 < Max (set (fst (snd t))) \<longrightarrow>
    Max (set (fst (snd (round index key p q r t)))) < Max (set (fst (snd t)))"
proof (induction index key p q r t rule: round.induct, simp_all add: Let_def split:
 prod.split del: all_simps, rule impI, (rule_tac [2] allI)+, (rule_tac [2] impI)+,
 (rule_tac [3] allI)+, (rule_tac [3] impI)+, rule_tac [2] ballI)
  fix index p q r u ns xs and key :: "'a \<Rightarrow> 'b"
  let ?t = "round index key p q r (u, ns, xs)"
  assume "ns \<noteq> [] \<longrightarrow> Suc 0 < Max (set ns) \<longrightarrow>
    Max (set (fst (snd ?t))) < Max (set ns)"
  moreover assume A: "Suc 0 < Max (insert 0 (set ns))"
  hence "ns \<noteq> []"
    by (cases ns, simp_all)
  moreover from this have "Suc 0 < Max (set ns)"
    using A by simp
  ultimately show "Max (set (fst (snd ?t))) < Max (insert 0 (set ns))"
    by simp
next
  fix index p q r u ns xs u' ns' xs' i and key :: "'a \<Rightarrow> 'b"
  let ?t = "round index key p q r (u, ns, tl xs)"
  assume
   "?t = (u', ns', xs')" and
   "ns \<noteq> [] \<longrightarrow> Suc 0 < Max (set ns) \<longrightarrow>
      Max (set (fst (snd ?t))) < Max (set ns)"
  hence "ns \<noteq> [] \<longrightarrow> Suc 0 < Max (set ns) \<longrightarrow>
    Max (set ns') < Max (set ns)"
    by simp
  moreover assume A: "Suc 0 < Max (insert (Suc 0) (set ns))"
  hence B: "ns \<noteq> []"
    by (cases ns, simp_all)
  moreover from this have "Suc 0 < Max (set ns)"
    using A by simp
  ultimately have "Max (set ns') < Max (set ns)" by simp
  moreover assume "i \<in> set ns'"
  hence "i \<le> Max (set ns')"
    by (rule_tac Max_ge, simp)
  ultimately show "i < Max (insert (Suc 0) (set ns))"
    using B by simp
next
  fix index p q r u n ns n' r' v ms' ws' u' ns' xs'
    and key :: "'a \<Rightarrow> 'b" and xs :: "'a list"
  let ?ws = "take (Suc (Suc n)) xs"
  let ?ys = "drop (Suc (Suc n)) xs"
  let ?r = "\<lambda>n'. round_suc_suc index key ?ws n n' u"
  let ?t = "\<lambda>r' v. round index key p q r' (v, ns, ?ys)"
  assume
    A: "?r n' = (v, ms', ws')" and
    B: "?t r' v = (u', ns', xs')"
  moreover assume "\<And>ws a b c d e f g h.
    ws = ?ws \<Longrightarrow> a = bn_comp n p q r \<Longrightarrow> (b, c) = bn_comp n p q r \<Longrightarrow>
    d = ?r b \<Longrightarrow> (e, f) = ?r b \<Longrightarrow> (g, h) = f \<Longrightarrow>
      ns \<noteq> [] \<longrightarrow> Suc 0 < Max (set ns) \<longrightarrow>
        Max (set (fst (snd (?t c e)))) < Max (set ns)" and
   "bn_comp n p q r = (n', r')"
  ultimately have C: "ns \<noteq> [] \<longrightarrow> Suc 0 < Max (set ns) \<longrightarrow>
    Max (set ns') < Max (set ns)"
    by simp
  from A [symmetric] show "Max (set ms' \<union> set ns') <
    Max (insert (Suc (Suc n)) (set ns))"
  proof (simp add: round_suc_suc_def Let_def, subst Max_less_iff, simp_all,
   rule_tac impI, simp add: Let_def split: if_split_asm, rule_tac ballI,
   erule_tac UnE, simp add: Let_def split: if_split_asm, (erule_tac [1-2] conjE)+)
    fix i
    assume "i = Suc 0 \<or> i = Suc 0 \<and> 0 < n"
    hence "i = Suc 0" by blast
    hence "i < Suc (Suc n)" by simp
    also have "\<dots> \<le> Max (insert (Suc (Suc n)) (set ns))"
      by (rule Max_ge, simp_all)
    finally show "i < Max (insert (Suc (Suc n)) (set ns))" .
  next
    fix i
    let ?nmi = "mini ?ws key"
    let ?nma = "maxi ?ws key"
    let ?xmi = "?ws ! ?nmi"
    let ?xma = "?ws ! ?nma"
    let ?mi = "key ?xmi"
    let ?ma = "key ?xma"
    let ?k = "case n of 0 \<Rightarrow> n | Suc 0 \<Rightarrow> n | Suc (Suc i) \<Rightarrow> u + n'"
    let ?zs = "nths ?ws (- {?nmi, ?nma})"
    let ?ms = "enum ?zs index key ?k ?mi ?ma"
    assume "i = Suc 0 \<or> i \<in> set ?ms"
    moreover {
      assume "i = Suc 0"
      hence "i < Suc (Suc n)" by simp
    }
    moreover {
      assume D: "i \<in> set ?ms"
      hence "i \<le> Max (set ?ms)"
      by (rule_tac Max_ge, simp)
      moreover have "0 < length ?ms"
        using D by (rule length_pos_if_in_set)
      hence "0 < ?k"
        by (simp add: enum_length)
      hence "Max (set ?ms) \<le> length ?zs"
        by (rule enum_max_le)
      ultimately have "i \<le> length ?zs" by simp
      moreover have "length ?zs \<le> n"
        by (rule mini_maxi_nths_le, simp)
      ultimately have "i < Suc (Suc n)" by simp
    }
    ultimately have "i < Suc (Suc n)" ..
    also have "\<dots> \<le> Max (insert (Suc (Suc n)) (set ns))"
      by (rule Max_ge, simp_all)
    finally show "i < Max (insert (Suc (Suc n)) (set ns))" .
  next
    fix i
    assume D: "i \<in> set ns'"
    hence "0 < length ns'"
      by (rule length_pos_if_in_set)
    hence "fst (snd (?t r' v)) \<noteq> []"
      using B by simp
    hence E: "\<exists>n \<in> set ns. 0 < n"
      by (simp add: round_nil)
    hence F: "ns \<noteq> []"
      by (cases ns, simp_all)
    show "i < Max (insert (Suc (Suc n)) (set ns))"
    proof (cases "Suc 0 < Max (set ns)")
      case True
      hence "Max (set ns') < Max (set ns)"
        using C and F by simp
      moreover have "i \<le> Max (set ns')"
        using D by (rule_tac Max_ge, simp)
      ultimately show ?thesis
        using F by simp
    next
      case False
      moreover from E obtain j where G: "j \<in> set ns" and H: "0 < j" ..
      have "j \<le> Max (set ns)"
        using G by (rule_tac Max_ge, simp)
      hence "0 < Max (set ns)"
        using H by simp
      ultimately have "Max (set ns) = Suc 0" by simp
      hence "Max (set (fst (snd (?t r' v)))) = Suc 0"
        using F by (rule_tac round_max_eq, simp_all)
      hence "Max (set ns') = Suc 0"
        using B by simp
      moreover have "i \<le> Max (set ns')"
        using D by (rule_tac Max_ge, simp)
      ultimately have "i < Suc (Suc n)" by simp
      also have "\<dots> \<le> Max (insert (Suc (Suc n)) (set ns))"
        by (rule Max_ge, simp_all)
      finally show ?thesis .
    qed
  qed
qed

termination gcsort_aux
proof (relation "measure (\<lambda>(index, key, p, t). Max (set (fst (snd t))))",
 simp_all add: find_None_iff, erule exE, erule conjE)
  fix index p ns xs i and key :: "'a \<Rightarrow> 'b"
  let ?t = "gcsort_round index key p ns xs"
  assume A: "Suc 0 < i" and B: "i \<in> set ns"
  have C: "0 < length ns"
    using B by (rule length_pos_if_in_set)
  moreover have "\<exists>i \<in> set ns. Suc 0 < i"
    using A and B ..
  hence "Suc 0 < Max (set ns)"
    using C by (subst Max_gr_iff, simp_all)
  ultimately have "Max (set (fst (snd ?t))) < Max (set (fst (snd (0, ns, xs))))"
    by (insert round_max_less [of "(0, ns, xs)"], simp)
  thus "Max (set (fst (snd ?t))) < Max (set ns)" by simp
qed

text \<open>
\null

Now steps 2, 3, and 4 of the proof method, which are independent of the properties to be proven, can
be accomplished. Particularly, function @{text gcsort} constitutes the complete formal definition of
GCsort, as it puts the algorithm's inputs and outputs into their expected form.

Observe that the conditional expression contained in the definition of function @{const gcsort_aux}
need not be reflected in the definition of inductive set @{text gcsort_set} as just one alternative
gives rise to a recursive call, viz. as its only purpose is to ensure the function's termination.

\null
\<close>

definition gcsort_in :: "'a list \<Rightarrow> nat \<times> nat list \<times> 'a list" where
"gcsort_in xs \<equiv> (0, [length xs], xs)"

definition gcsort_out :: "nat \<times> nat list \<times> 'a list \<Rightarrow> 'a list" where
"gcsort_out \<equiv> snd \<circ> snd"

definition gcsort :: "('a, 'b::linorder) index_sign \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> nat \<Rightarrow>
  'a list \<Rightarrow> 'a list" where
"gcsort index key p xs \<equiv> gcsort_out (gcsort_aux index key p (gcsort_in xs))"

inductive_set gcsort_set :: "('a, 'b::linorder) index_sign \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> nat \<Rightarrow>
  nat \<times> nat list \<times> 'a list \<Rightarrow> (nat \<times> nat list \<times> 'a list) set"
for index key p t where
R0: "t \<in> gcsort_set index key p t" |
R1: "(u, ns, xs) \<in> gcsort_set index key p t \<Longrightarrow>
  gcsort_round index key p ns xs \<in> gcsort_set index key p t"

lemma gcsort_subset:
  assumes A: "t' \<in> gcsort_set index key p t"
  shows "gcsort_set index key p t' \<subseteq> gcsort_set index key p t"
by (rule subsetI, erule gcsort_set.induct, rule A, rule R1)

lemma gcsort_aux_set:
 "gcsort_aux index key p t \<in> gcsort_set index key p t"
proof (induction index key p t rule: gcsort_aux.induct, simp, rule conjI,
 rule_tac [!] impI, rule R0, simp)
  fix index p u ns xs and key :: "'a \<Rightarrow> 'b"
  let ?t = "gcsort_round index key p ns xs"
  assume "gcsort_aux index key p ?t \<in> gcsort_set index key p ?t"
  moreover have "(u, ns, xs) \<in> gcsort_set index key p (u, ns, xs)"
    by (rule R0)
  hence "?t \<in> gcsort_set index key p (u, ns, xs)"
    by (rule R1)
  hence "gcsort_set index key p ?t \<subseteq> gcsort_set index key p (u, ns, xs)"
    by (rule gcsort_subset)
  ultimately show "gcsort_aux index key p ?t
    \<in> gcsort_set index key p (u, ns, xs)" ..
qed


subsection "Proof of a preliminary invariant"

text \<open>
This section is dedicated to the proof of the invariance of predicate @{text add_inv}, defined here
below, over inductive set @{const gcsort_set}. This invariant will later be used to prove GCsort's
correctness properties.

Another predicate, @{text bn_inv}, is also defined, using predicate @{const bn_valid} defined above.

\null
\<close>

fun bn_inv :: "nat \<Rightarrow> nat \<Rightarrow> nat \<times> nat list \<times> 'a list \<Rightarrow> bool" where
"bn_inv p q (u, ns, xs) =
  (\<forall>n \<in> set ns. case n of Suc (Suc m) \<Rightarrow> bn_valid m p q | _ \<Rightarrow> True)"

fun add_inv :: "nat \<Rightarrow> nat \<times> nat list \<times> 'a list \<Rightarrow> bool" where
"add_inv n (u, ns, xs) =
  (foldl (+) 0 ns = n \<and> length xs = n)"

lemma gcsort_add_input:
 "add_inv (length xs) (0, [length xs], xs)"
by simp

lemma add_base:
 "foldl (+) (k + m) ns = foldl (+) m ns + (k :: nat)"
by (induction ns arbitrary: m, simp_all, subst add.assoc, simp)

lemma add_base_zero:
 "foldl (+) k ns = foldl (+) 0 ns + (k :: nat)"
by (insert add_base [of k 0 ns], simp)

lemma bn_count_le:
 "bn_count ns \<le> foldl (+) 0 ns"
by (induction ns rule: bn_count.induct, simp_all add: add_suc, subst add_base_zero,
 simp)

text \<open>
\null

Here below is the proof of the main property of predicate @{const bn_inv}, which states that if the
objects' number is not larger than the counters' upper bound, then, as long as there are buckets to
be split, the arguments $p$ and $q$ passed by function @{const round} to function @{const bn_comp}
are such that $0 < q \leq p$.

\null
\<close>

lemma bn_inv_intro [rule_format]:
 "foldl (+) 0 ns \<le> p \<longrightarrow>
    bn_inv (p - bn_count ns) (foldl (+) 0 ns - bn_count ns) (u, ns, xs)"
proof (induction ns, simp_all, (rule impI)+, subst (asm) (3) add_base_zero,
 subst (1 2) add_base_zero, simp)
  fix n ns
  assume
    A: "\<forall>x \<in> set ns. case x of 0 \<Rightarrow> True | Suc 0 \<Rightarrow> True | Suc (Suc m) \<Rightarrow>
      bn_valid m (p - bn_count ns) (foldl (+) 0 ns - bn_count ns)" and
    B: "foldl (+) 0 ns + n \<le> p"
  show
   "(case n of 0 \<Rightarrow> True | Suc 0 \<Rightarrow> True | Suc (Suc m) \<Rightarrow>
      bn_valid m (p - bn_count (n # ns))
        (foldl (+) 0 ns + n - bn_count (n # ns))) \<and>
    (\<forall>x \<in> set ns. case x of 0 \<Rightarrow> True | Suc 0 \<Rightarrow> True | Suc (Suc m) \<Rightarrow>
      bn_valid m (p - bn_count (n # ns))
        (foldl (+) 0 ns + n - bn_count (n # ns)))"
  proof (rule conjI, rule_tac [2] ballI, simp_all split: nat.split, rule_tac [!] allI,
   rule_tac [!] impI)
    fix m
    assume C: "n = Suc (Suc m)"
    show "bn_valid m (p - bn_count (Suc (Suc m) # ns))
      (Suc (Suc (foldl (+) 0 ns + m)) - bn_count (Suc (Suc m) # ns))"
      (is "bn_valid _ ?p ?q")
    proof (rule bn_valid.cases [of "(m, ?p, ?q)"], simp_all, erule conjE, rule conjI)
      fix k
      have "bn_count ns \<le> foldl (+) 0 ns"
        by (rule bn_count_le)
      thus "bn_count ns < Suc (Suc (foldl (+) 0 ns + k))" by simp
    next
      fix k
      assume "m = Suc (Suc k)"
      hence "Suc (Suc (foldl (+) 0 ns + k)) - bn_count ns =
        foldl (+) 0 ns + n - Suc (Suc (bn_count ns))"
        using C by simp
      also have "\<dots> \<le> p - Suc (Suc (bn_count ns))"
        using B by simp
      finally show "Suc (Suc (foldl (+) 0 ns + k)) - bn_count ns \<le>
        p - Suc (Suc (bn_count ns))" .
    qed
  next
    fix n' m
    assume "n' \<in> set ns"
    with A have "case n' of 0 \<Rightarrow> True | Suc 0 \<Rightarrow> True | Suc (Suc m) \<Rightarrow>
      bn_valid m (p - bn_count ns) (foldl (+) 0 ns - bn_count ns)" ..
    moreover assume "n' = Suc (Suc m)"
    ultimately have "bn_valid m (p - bn_count ns) (foldl (+) 0 ns - bn_count ns)"
      by simp
    thus "bn_valid m (p - bn_count (n # ns))
      (foldl (+) 0 ns + n - bn_count (n # ns))"
      (is "bn_valid _ ?p ?q")
    proof (rule_tac bn_valid.cases [of "(m, ?p, ?q)"], simp_all, (erule_tac conjE)+,
     simp)
      fix p' q'
      assume "bn_count ns < foldl (+) 0 ns"
      moreover assume "p - bn_count (n # ns) = p'"
      hence "p' = p - bn_count (n # ns)" ..
      moreover assume "foldl (+) 0 ns + n - bn_count (n # ns) = q'"
      hence "q' = foldl (+) 0 ns + n - bn_count (n # ns)" ..
      ultimately show "0 < q' \<and> q' \<le> p'"
        using B by (rule_tac bn_count.cases [of "n # ns"], simp_all)
    qed
  qed
qed

text \<open>
\null

In what follows, the invariance of predicate @{const add_inv} over inductive set @{const gcsort_set}
is then proven as lemma @{text gcsort_add_inv}. It holds under the conditions that the objects'
number is not larger than the counters' upper bound and function @{text index} satisfies predicate
@{const index_less}, and states that, if the counters' sum initially matches the objects' number,
this is still true after any recursive round.

\null
\<close>

lemma bn_comp_fst_ge [rule_format]:
 "bn_valid n p q \<longrightarrow> n \<le> fst (bn_comp n p q r)"
proof (induction n p q r rule: bn_comp.induct, simp_all del: mult_Suc,
 rule impI, erule conjE)
  fix n p r and q :: nat
  assume "0 < q"
  hence "Suc (Suc n) = Suc (Suc n) * q div q" by simp
  also assume "q \<le> p"
  hence "Suc (Suc n) * q \<le> Suc (Suc n) * p"
    by (rule mult_le_mono2)
  hence "Suc (Suc n) * q div q \<le> (Suc (Suc n) * p + r) div q"
    by (rule_tac div_le_mono, simp)
  finally show "Suc (Suc n) \<le> (Suc (Suc n) * p + r) div q" .
qed

lemma bn_comp_fst_nonzero:
 "bn_valid n p q \<Longrightarrow> 0 < n \<Longrightarrow> 0 < fst (bn_comp n p q r)"
by (drule bn_comp_fst_ge [where r = r], simp)

lemma bn_comp_snd_less:
 "r < q \<Longrightarrow> snd (bn_comp n p q r) < q"
by (induction n p q r rule: bn_comp.induct, simp_all)

lemma add_replicate:
 "foldl (+) k (replicate m n) = k + m * n"
by (induction m arbitrary: k, simp_all)

lemma fill_length:
 "length (fill xs ns index key n mi ma) = n"
by (induction xs arbitrary: ns, simp_all add: Let_def)

lemma enum_add [rule_format]:
  assumes
    A: "index_less index key" and
    B: "0 < n"
  shows "(\<forall>x \<in> set xs. key x \<in> {mi..ma}) \<longrightarrow>
    foldl (+) 0 (enum xs index key n mi ma) = length xs"
proof (induction xs, simp_all add: Let_def add_zeros, rule impI, (erule conjE)+,
 simp)
  fix x xs
  assume "mi \<le> key x" and "key x \<le> ma"
  hence "index key x n mi ma < n"
    (is "?i < _")
    using A and B by (simp add: index_less_def)
  hence "?i < length (enum xs index key n mi ma)"
    (is "_ < length ?ns")
    by (simp add: enum_length)
  hence "foldl (+) 0 (?ns[?i := Suc (?ns ! ?i)]) = Suc (foldl (+) 0 ?ns)"
    by (rule add_update)
  moreover assume "foldl (+) 0 ?ns = length xs"
  ultimately show "foldl (+) 0 (?ns[?i := Suc (?ns ! ?i)]) = Suc (length xs)"
    by simp
qed

lemma round_add_inv [rule_format]:
 "index_less index key \<longrightarrow> bn_inv p q t \<longrightarrow> add_inv n t \<longrightarrow>
    add_inv n (round index key p q r t)"
proof (induction index key p q r t arbitrary: n rule: round.induct, simp_all
 add: Let_def split: prod.split, (rule allI)+, (rule impI)+, erule conjE,
 (rule_tac [2] allI)+, (rule_tac [2] impI)+, (erule_tac [2] conjE)+,
 rule_tac [2] ssubst [OF add_base_zero], simp_all add: add_suc)
  fix n ns ns' and xs' :: "'a list"
  assume "\<And>n'. foldl (+) 0 ns = n' \<and> n - Suc 0 = n' \<longrightarrow>
    foldl (+) 0 ns' = n' \<and> length xs' = n'"
  hence "foldl (+) 0 ns = n - Suc 0 \<longrightarrow>
    foldl (+) 0 ns' = n - Suc 0 \<and> length xs' = n - Suc 0"
    by simp
  moreover assume "Suc (foldl (+) 0 ns) = n"
  ultimately show "Suc (foldl (+) 0 ns') = n \<and> Suc (length xs') = n" by simp
next
  fix index p q r u m m' ns v ms' ws' ns' n
    and key :: "'a \<Rightarrow> 'b" and xs :: "'a list" and xs' :: "'a list" and r' :: nat
  let ?ws = "take (Suc (Suc m)) xs"
  assume
    A: "round_suc_suc index key ?ws m m' u = (v, ms', ws')" and
    B: "bn_comp m p q r = (m', r')" and
    C: "index_less index key" and
    D: "bn_valid m p q" and
    E: "length xs = n"
  assume "\<And>ws a b c d e f g h n'.
    ws = ?ws \<Longrightarrow> a = (m', r') \<Longrightarrow> b = m' \<and> c = r' \<Longrightarrow>
    d = (v, ms', ws') \<Longrightarrow> e = v \<and> f = (ms', ws') \<Longrightarrow> g = ms' \<and> h = ws' \<Longrightarrow>
      foldl (+) 0 ns = n' \<and> n - Suc (Suc m) = n' \<longrightarrow>
        foldl (+) 0 ns' = n' \<and> length xs' = n'"
  moreover assume "Suc (Suc (foldl (+) m ns)) = n"
  hence F: "foldl (+) 0 ns + Suc (Suc m) = n"
    by (subst (asm) add_base_zero, simp)
  ultimately have
    G: "foldl (+) 0 ns' = n - Suc (Suc m) \<and> length xs' = n - Suc (Suc m)"
    by simp
  from A show "foldl (+) 0 ns' + foldl (+) 0 ms' = n \<and>
    length ws' + length xs' = n"
  proof (subst (2) add_base_zero, simp add: round_suc_suc_def Let_def split:
   if_split_asm, (erule_tac [!] conjE)+, simp_all)
    assume "Suc 0 # Suc 0 # replicate m (Suc 0) = ms'"
    hence "ms' = Suc 0 # Suc 0 # replicate m (Suc 0)" ..
    hence "foldl (+) 0 ms' = Suc (Suc m)"
      by (simp add: add_replicate)
    hence "foldl (+) 0 ns' + foldl (+) 0 ms' = n"
      using F and G by simp
    moreover assume "?ws = ws'"
    hence "ws' = ?ws" ..
    hence "length ws' = Suc (Suc m)"
      using F and E by simp
    hence "length ws' + length xs' = n"
      using F and G by simp
    ultimately show ?thesis ..
  next
    let ?nmi = "mini ?ws key"
    let ?nma = "maxi ?ws key"
    let ?xmi = "?ws ! ?nmi"
    let ?xma = "?ws ! ?nma"
    let ?mi = "key ?xmi"
    let ?ma = "key ?xma"
    let ?k = "case m of 0 \<Rightarrow> m | Suc 0 \<Rightarrow> m | Suc (Suc i) \<Rightarrow> u + m'"
    let ?zs = "nths ?ws (- {?nmi, ?nma})"
    let ?ms = "enum ?zs index key ?k ?mi ?ma"
    assume "Suc 0 # ?ms @ [Suc 0] = ms'"
    hence "ms' = Suc 0 # ?ms @ [Suc 0]" ..
    moreover assume
     "?xmi # map the (fill ?zs (offs ?ms 0) index key m ?mi ?ma) @ [?xma] = ws'"
    hence "ws' = ?xmi # map the (fill ?zs (offs ?ms 0) index key m ?mi ?ma)
      @ [?xma]" ..
    ultimately show ?thesis
    proof (simp add: fill_length, subst (2) add_base_zero, simp, cases m)
      case 0
      moreover from this have "length ?ms = 0"
        by (simp add: enum_length)
      ultimately show "Suc (Suc (foldl (+) 0 ns' + foldl (+) 0 ?ms)) = n \<and>
        Suc (Suc (m + length xs')) = n"
        using F and G by simp
    next
      case Suc
      moreover from this have "0 < fst (bn_comp m p q r)"
        by (rule_tac bn_comp_fst_nonzero [OF D], simp)
      hence "0 < m'"
        using B by simp
      ultimately have H: "0 < ?k"
        by (simp split: nat.split)
      have "foldl (+) 0 ?ms = length ?zs"
        by (rule enum_add [OF C H], simp, rule conjI,
         ((rule mini_lb | rule maxi_ub), erule in_set_nthsD)+)
      moreover have "length ?ws = Suc (Suc m)"
        using F and E by simp
      hence "length ?zs = m"
        by (simp add: mini_maxi_nths)
      ultimately show "Suc (Suc (foldl (+) 0 ns' + foldl (+) 0 ?ms)) = n \<and>
        Suc (Suc (m + length xs')) = n"
        using F and G by simp
    qed
  qed
qed

lemma gcsort_add_inv:
  assumes A: "index_less index key"
  shows "\<lbrakk>t' \<in> gcsort_set index key p t; add_inv n t; n \<le> p\<rbrakk> \<Longrightarrow>
    add_inv n t'"
by (erule gcsort_set.induct, simp, rule round_add_inv [OF A], simp_all del:
 bn_inv.simps, erule conjE, frule sym, erule subst, rule bn_inv_intro, simp)


subsection "Proof of counters' optimization"

text \<open>
In this section, it is formally proven that the number of the counters (and then of the buckets as
well) used in each recursive round is maximized never exceeding the fixed upper bound.

This property is formalized by theorem @{text round_len}, which holds under the condition that the
objects' number is not larger than the counters' upper bound and states what follows:

\begin{itemize}

\item
While there is some bucket with size larger than two, the sum of the number of the used counters and
the number of the unused ones -- viz. those, if any, left unused due to the presence of some bucket
with size larger than two and equal minimum and maximum keys (cf. section \ref{SEC4}) -- matches the
counters' upper bound.
\\In addition to ensuring the upper bound's enforcement, this implies that the number of the used
counters matches the upper bound unless there is some aforesaid bucket not followed by any other
bucket with size larger than two and distinct minimum and maximum keys.

\item
Once there is no bucket with size larger than two -- in which case a round is executed just in case
there is some bucket with size two --, the number of the used counters matches the objects' number.
\\In fact, the algorithm immediately terminates after such a round since every resulting bucket has
size one, so that increasing the number of the used counters does not matter in this case.

\end{itemize}

\null
\<close>

lemma round_len_less [rule_format]:
 "bn_inv p q t \<longrightarrow> r < q \<longrightarrow>
  (r + (foldl (+) 0 (fst (snd t)) - bn_count (fst (snd t))) * p) mod q = 0 \<longrightarrow>
    (fst (round index key p q r t) +
      length (fst (snd (round index key p q r t)))) * q =
    (fst t + bn_count (fst (snd t))) * q +
      (foldl (+) 0 (fst (snd t)) - bn_count (fst (snd t))) * p + r"
proof (induction index key p q r t rule: round.induct, simp_all add: Let_def
 split: prod.split del: all_simps, ((rule allI)+, (rule impI)+, simp add:
 add_suc)+, subst (asm) (3) add_base_zero, subst add_base_zero, erule conjE)
  fix index p q r u n ns n' r' v ms' ws' u'
    and key :: "'a \<Rightarrow> 'b" and xs :: "'a list" and ns' :: "nat list"
  let ?ws = "take (Suc (Suc n)) xs"
  assume
    A: "round_suc_suc index key ?ws n n' u = (v, ms', ws')" and
    B: "bn_comp n p q r = (n', r')" and
    C: "bn_valid n p q"
  have D: "bn_count ns \<le> foldl (+) 0 ns"
    by (rule bn_count_le)
  assume "\<And>ws a b c d e f g h.
    ws = ?ws \<Longrightarrow> a = (n', r') \<Longrightarrow> b = n' \<and> c = r' \<Longrightarrow>
    d = (v, ms', ws') \<Longrightarrow> e = v \<and> f = (ms', ws') \<Longrightarrow> g = ms' \<and> h = ws' \<Longrightarrow>
      r' < q \<longrightarrow> (r' + (foldl (+) 0 ns - bn_count ns) * p) mod q = 0 \<longrightarrow>
        (u' + length ns') * q =
        (v + bn_count ns) * q + (foldl (+) 0 ns - bn_count ns) * p + r'"
  moreover assume "r < q"
  hence "snd (bn_comp n p q r) < q"
    by (rule bn_comp_snd_less)
  hence "r' < q"
    using B by simp
  moreover assume E: "(r + (Suc (Suc (foldl (+) 0 ns + n)) -
    bn_count (Suc (Suc n) # ns)) * p) mod q = 0"
  from B [symmetric] have "(r' + (foldl (+) 0 ns - bn_count ns) * p) mod q = 0"
  proof (rule_tac trans [OF _ E], rule_tac bn_comp.cases [of "(n, p, q, r)"],
   simp_all add: add_mult_distrib diff_mult_distrib mod_add_left_eq,
   rule_tac arg_cong2 [where f = "(mod)"], simp_all)
    fix n p q r
    have "bn_count ns * p \<le> foldl (+) 0 ns * p"
      using D by (rule mult_le_mono1)
    thus "p + (p + (n * p + (foldl (+) 0 ns * p - bn_count ns * p))) =
      p + (p + (foldl (+) 0 ns * p + n * p)) - bn_count ns * p"
      by arith
  qed
  ultimately have "(u' + length ns') * q =
    (v + bn_count ns) * q + (foldl (+) 0 ns - bn_count ns) * p + r'"
    by simp
  with A [symmetric] and B [symmetric] show
   "(u' + (length ms' + length ns')) * q =
    (u + bn_count (Suc (Suc n) # ns)) * q +
      (Suc (Suc (foldl (+) 0 ns + n)) - bn_count (Suc (Suc n) # ns)) * p + r"
  proof (rule_tac bn_comp.cases [of "(n, p, q, r)"],
   simp_all add: round_suc_suc_def Let_def enum_length split: if_split_asm)
    fix m p' q' r'
    assume
     "n = Suc (Suc m)" and
     "p = p'" and
     "q = q'" and
     "r = r'"
    moreover have "n \<le> fst (bn_comp n p q r)"
      using C by (rule bn_comp_fst_ge)
    ultimately have "Suc (Suc m) \<le> (p' + (p' + m * p') + r') div q'"
      (is "_ \<le> ?a div _")
      by simp
    hence F: "Suc (Suc m) * q' \<le> ?a div q' * q'"
      by (rule mult_le_mono1)
    moreover assume "(u' + length ns') * q' =
      (u + ?a div q' - Suc (Suc m) + bn_count ns) * q' +
        (foldl (+) 0 ns - bn_count ns) * p' + ?a mod q'"
    ultimately have "(u' + length ns') * q' + Suc (Suc m) * q' =
      (u + bn_count ns) * q' + (foldl (+) 0 ns - bn_count ns) * p' +
        ?a div q' * q' + ?a mod q'"
      (is "?c = ?d")
    proof (simp add: add_mult_distrib diff_mult_distrib)
      have "Suc (Suc m) * q' \<le> ?a div q' * q' + ?a mod q'"
        using F by arith
      hence "q' + (q' + m * q') \<le> ?a"
        (is "?b \<le> _")
        by simp
      thus
       "?a + (u * q' + (bn_count ns * q' +
          (foldl (+) 0 ns * p' - bn_count ns * p'))) - ?b + ?b =
        ?a + (u * q' + (bn_count ns * q' +
          (foldl (+) 0 ns * p' - bn_count ns * p')))"
        by simp
    qed
    moreover have "?c = q' + (q' + (u' + (m + length ns')) * q')"
      (is "_ = ?e")
      by (simp add: add_mult_distrib)
    moreover have "bn_count ns * p' \<le> foldl (+) 0 ns * p'"
      using D by (rule mult_le_mono1)
    hence "?d = (u + bn_count ns) * q' +
      ((Suc (Suc (foldl (+) 0 ns + m)) - bn_count ns) * p' + r')"
      (is "_ = ?f")
      by (simp (no_asm_simp) add: add_mult_distrib diff_mult_distrib)
    ultimately show "?e = ?f" by simp
  next
    fix m p' q' r'
    assume "(u' + length ns') * q' = bn_count ns * q' +
      (foldl (+) 0 ns - bn_count ns) * p' + (p' + (p' + m * p') + r') mod q'"
      (is "_ = _ + _ + ?a mod _")
    hence "(u' + length ns') * q' + (u + ?a div q') * q' =
      (u + bn_count ns) * q' + (foldl (+) 0 ns - bn_count ns) * p' + ?a"
      (is "?c = ?d")
      by (simp add: add_mult_distrib)
    moreover have "?c = (u' + (u + ?a div q' + length ns')) * q'"
      (is "_ = ?e")
      by (simp add: add_mult_distrib)
    moreover have "bn_count ns * p' \<le> foldl (+) 0 ns * p'"
      using D by (rule mult_le_mono1)
    hence "?d = (u + bn_count ns) * q' +
      ((Suc (Suc (foldl (+) 0 ns + m)) - bn_count ns) * p' + r')"
      (is "_ = ?f")
      by (simp (no_asm_simp) add: add_mult_distrib diff_mult_distrib)
    ultimately show "?e = ?f" by simp
  qed
qed

lemma round_len_eq [rule_format]:
 "bn_count (fst (snd t)) = foldl (+) 0 (fst (snd t)) \<longrightarrow>
    length (fst (snd (round index key p q r t))) = foldl (+) 0 (fst (snd t))"
proof (induction index key p q r t rule: round.induct, simp_all add: Let_def
 split: prod.split del: all_simps, ((rule allI)+, (rule impI)+, simp add:
 add_suc)+, subst (asm) (3) add_base_zero, subst add_base_zero)
  fix index p q r u n ns n' v ms' ws'
    and key :: "'a \<Rightarrow> 'b" and xs :: "'a list" and ns' :: "nat list" and r' :: nat
  let ?ws = "take (Suc (Suc n)) xs"
  assume
    A: "round_suc_suc index key ?ws n n' u = (v, ms', ws')" and
    B: "bn_count (Suc (Suc n) # ns) = Suc (Suc (foldl (+) 0 ns + n))"
  assume "\<And>ws a b c d e f g h.
    ws = ?ws \<Longrightarrow> a = (n', r') \<Longrightarrow> b = n' \<and> c = r' \<Longrightarrow>
    d = (v, ms', ws') \<Longrightarrow> e = v \<and> f = (ms', ws') \<Longrightarrow> g = ms' \<and> h = ws' \<Longrightarrow>
      bn_count ns = foldl (+) 0 ns \<longrightarrow> length ns' = foldl (+) 0 ns"
  moreover have C: "n = 0 \<or> n = Suc 0"
    using B by (rule_tac bn_comp.cases [of "(n, p, q, r)"],
     insert bn_count_le [of ns], simp_all)
  hence "bn_count ns = foldl (+) 0 ns"
    using B by (erule_tac disjE, simp_all)
  ultimately have "length ns' = foldl (+) 0 ns" by simp
  with A [symmetric] show "length ms' + length ns' =
    Suc (Suc (foldl (+) 0 ns + n))"
    by (rule_tac disjE [OF C], simp_all
     add: round_suc_suc_def Let_def enum_length split: if_split_asm)
qed

theorem round_len:
  assumes
    A: "length xs = foldl (+) 0 ns" and
    B: "length xs \<le> p"
  shows "if bn_count ns < length xs
    then fst (gcsort_round index key p ns xs) +
      length (fst (snd (gcsort_round index key p ns xs))) = p
    else length (fst (snd (gcsort_round index key p ns xs))) = length xs"
  (is "if _ then fst ?t + _ = _ else _")
proof (split if_split, rule conjI, rule_tac [!] impI)
  assume C: "bn_count ns < length xs"
  moreover have
   "bn_inv (p - bn_count ns) (foldl (+) 0 ns - bn_count ns) (0, ns, xs)"
    using A and B by (rule_tac bn_inv_intro, simp)
  ultimately have
   "(fst ?t + length (fst (snd ?t))) * (length xs - bn_count ns) =
    bn_count ns * (length xs - bn_count ns) +
      (p - bn_count ns) * (length xs - bn_count ns)"
    (is "?a * ?b = ?c")
    using A by (subst round_len_less, simp_all)
  also have "bn_count ns \<le> p"
    using B and C by simp
  hence "bn_count ns * ?b \<le> p * ?b"
    by (rule mult_le_mono1)
  hence "?c = p * ?b"
    by (simp (no_asm_simp) add: diff_mult_distrib)
  finally have "?a * ?b = p * ?b" .
  thus "?a = p"
    using C by simp
next
  assume "\<not> bn_count ns < length xs"
  moreover have "bn_count ns \<le> foldl (+) 0 ns"
    by (rule bn_count_le)
  ultimately show "length (fst (snd ?t)) = length xs"
    using A by (subst round_len_eq, simp_all)
qed

end
