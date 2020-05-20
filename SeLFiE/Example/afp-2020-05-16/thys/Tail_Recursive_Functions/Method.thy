(*  Title:       A General Method for the Proof of Theorems on Tail-recursive Functions
    Author:      Pasquale Noce
                 Security Certification Specialist at Arjo Systems - Gep S.p.A.
                 pasquale dot noce dot lavoro at gmail dot com
                 pasquale dot noce at arjowiggins-it dot com
*)

section "Method rationale"

(*<*)
theory Method
imports Main 
begin
(*>*)

text \<open>
Tail-recursive function definitions are sometimes more intuitive and
straightforward than alternatives, and this alone would be enough to make them
preferable in such cases for the mere purposes of functional programming. However,
proving theorems about them with a formal proof assistant like Isabelle may be
roundabout because of the peculiar form of the resulting recursion induction
rules.

Let:

\begin{itemize}

\item
\<open>f_naive\<close> be a tail-recursive function of type
\<open>'a\<^sub>1 \<Rightarrow> ... \<Rightarrow> 'a\<^sub>n \<Rightarrow> 'b\<close>.

\item
\<open>a\<close> be an \<open>n\<close>-tuple of values of types \<open>'a\<^sub>1\<close>, ...,
\<open>'a\<^sub>n\<close> such that the computation of \<open>f_naive a\<close>, say outputting
value \<open>b\<close>, involves at least one recursive call -- which is what happens in
general for significant inputs (e.g. those complying with initial conditions for
accumulator arguments), as otherwise a non-recursive function definition would be
sufficient.

\item
\<open>a\<^sub>1\<close>, ..., \<open>a\<^sub>m\<close> be the sequence of the intermediate
\<open>n\<close>-tuples of values of types \<open>'a\<^sub>1\<close>, ..., \<open>'a\<^sub>n\<close> arising from
the computation of \<open>f_naive a\<close>.

\item
\<open>f_naive X\<^sub>1 = f_naive X'\<^sub>1\<close>, ..., \<open>f_naive X\<^sub>m = f_naive X'\<^sub>m\<close>,
\<open>f_naive X = Y\<close> be the sequence (possibly with repetitions) of the
equations involved in the computation of \<open>f_naive a\<close> -- which implies
that, putting \<open>a\<^sub>0 = a\<close>, they are satisfied for
\<open>(X\<^sub>1, X'\<^sub>1) = (a\<^sub>0, a\<^sub>1)\<close>, ..., \<open>(X\<^sub>m, X'\<^sub>m) = (a\<^sub>m\<^sub>-\<^sub>1, a\<^sub>m)\<close>,
\<open>(X, Y) = (a\<^sub>m, b)\<close>, respectively.

\end{itemize}

That being stated, suppose that theorem \<open>P (f_naive a)\<close> has to be proven.
If recursion induction is applied to such goal, for each \<open>i \<in> {1..m}\<close>,
the recursive equation \<open>f_naive X\<^sub>i = f_naive X'\<^sub>i\<close> gives rise to subgoal
\<open>P (f_naive X'\<^sub>i) \<Longrightarrow> P (f_naive X\<^sub>i)\<close>, trivially discharged by
simplification. On the contrary, the non-recursive equation
\<open>f_naive X = Y\<close> brings about the generation of subgoal
\<open>P (f_naive X)\<close>, which is intractable unless it trivially follows from
either the equation or the form of pattern \<open>X\<close>.

Indeed, in non-trivial cases such as the case studies examined in this paper, this
formula even fails to be a theorem, thus being hopeless as a goal, since it is
false for some values of its variables. The reason for this is that non-trivial
properties of the output of tail-recursive functions depend on the input as well
as on the whole recursive call pipeline leading from the input to the output, and
all of this information corresponds to missing necessary assumptions in subgoal
\<open>P (f_naive X)\<close>.

Therefore, for a non-trivial theorem \<open>P (f_naive a)\<close>, recursion induction
is rather applicable to some true conditional statement
\<open>f_inv x \<longrightarrow> P (f_naive x)\<close> complying with both of the following
requirements:

\begin{itemize}

\item
subgoal \<open>f_inv X \<longrightarrow> P (f_naive X)\<close> arising from equation
\<open>f_naive X = Y\<close> be tractable, and

\item
formula \<open>f_inv a\<close> can be shown to be true, so that theorem
\<open>P (f_naive a)\<close> can be inferred from conditional
\<open>f_inv a \<longrightarrow> P (f_naive a)\<close> by \emph{modus ponens}.

\end{itemize}

Observe that the antecedent of the conditional may not have the form
\<open>f_inv (f_naive x)\<close>. Otherwise, the latter requirement would ask for
proving formula \<open>f_inv (f_naive a)\<close>, which would be at least as hard to
prove as formula \<open>P (f_naive a)\<close> being the former a sufficient condition
for the latter. Hence, the same problem as that originating from the proof of
formula \<open>P (f_naive a)\<close> would have to be solved again, which would give
rise to a \emph{regressio ad infinitum}.

The latter requirement entails that formula \<open>f_inv a\<^sub>0\<close> holds. Moreover,
for each \<open>i \<in> {1..m}\<close>, in the proof of conditional
\<open>f_inv x \<longrightarrow> P (f_naive x)\<close> by recursion induction, the recursive equation
\<open>f_naive X\<^sub>i = f_naive X'\<^sub>i\<close> brings about the generation of subgoal
\<open>f_inv X'\<^sub>i \<longrightarrow> P (f_naive X'\<^sub>i) \<Longrightarrow> f_inv X\<^sub>i \<longrightarrow> P (f_naive X\<^sub>i)\<close>. Assuming
that formula \<open>f_inv a\<^sub>i\<^sub>-\<^sub>1\<close> holds, it turns out that the conclusion
antecedent \<open>f_inv X\<^sub>i\<close> may not be shown to be false, as \<open>n\<close>-tuple
\<open>a\<^sub>i\<^sub>-\<^sub>1\<close> matches pattern \<open>X\<^sub>i\<close>; thus, the conclusion consequent
\<open>P (f_naive X\<^sub>i)\<close> has to be proven.

In non-trivial cases, this requires that the assumption antecedent
\<open>f_inv X'\<^sub>i\<close> be derived from the conclusion antecedent \<open>f_inv X\<^sub>i\<close>
used as a further assumption, so that the assumption consequent
\<open>P (f_naive X'\<^sub>i)\<close> -- matching \<open>P (f_naive X\<^sub>i)\<close> by virtue of
equation \<open>f_naive X\<^sub>i = f_naive X'\<^sub>i\<close> -- can be proven by
\emph{modus ponens}. This in turn requires that \<open>f_inv X\<^sub>i\<close> imply
\<open>f_inv X'\<^sub>i\<close>, i.e. that \<open>f_inv x\<^sub>i\<close> imply \<open>f_inv x'\<^sub>i\<close> for any
pair of \<open>n\<close>-tuples \<open>x\<^sub>i\<close>, \<open>x'\<^sub>i\<close> matching patterns \<open>X\<^sub>i\<close>,
\<open>X'\<^sub>i\<close> with respect to the same value assignment. But such are
\<open>n\<close>-tuples \<open>a\<^sub>i\<^sub>-\<^sub>1\<close>, \<open>a\<^sub>i\<close> as they solve equation
\<open>f_naive X\<^sub>i = f_naive X'\<^sub>i\<close>, so that the supposed truth of
\<open>f_inv a\<^sub>i\<^sub>-\<^sub>1\<close> entails that of \<open>f_inv a\<^sub>i\<close>.

Hence, by induction, all of formulae \<open>f_inv a\<close>, \<open>f_inv a\<^sub>1\<close>, ...,
\<open>f_inv a\<^sub>m\<close> turn out to be true. On the other hand, the former requirement
is verified if either the antecedent \<open>f_inv X\<close> can be shown to be false,
which would entail its falsity for any \<open>n\<close>-tuple matching pattern \<open>X\<close>,
or else the consequent \<open>P (f_naive X)\<close> can be shown to be true using the
antecedent as an assumption. Since formula \<open>f_inv a\<^sub>m\<close> is true and
\<open>n\<close>-tuple \<open>a\<^sub>m\<close> matches pattern \<open>X\<close>, the case that actually
occurs is the second one.

Thus, the former requirement is equivalent to asking for an introduction rule to
be proven -- in fact, a conditional with a contradiction as antecedent may not be
used as an introduction rule -- having the form
\<open>f_inv X \<Longrightarrow> P (f_naive X)\<close>, or rather
\<open>\<lbrakk>f_inv x; f_form x\<rbrakk> \<Longrightarrow> P (f_naive x)\<close> for a suitable predicate
\<open>f_form\<close> satisfied by any \<open>n\<close>-tuple matching pattern \<open>X\<close>. In
the degenerate case in which the rule can be shown to be true for
\<open>f_form = (\<lambda>x. True)\<close>, it admits to be put into the simpler equivalent
form \<open>f_inv x \<Longrightarrow> P (f_naive x)\<close>.

An even more important consequence of the previous argument is that in non-trivial
cases, the task of proving conditional \<open>f_inv x \<longrightarrow> P (f_naive x)\<close> by
recursion induction requires that \<open>f_inv X'\<^sub>i\<close> be derived from
\<open>f_inv X\<^sub>i\<close> for each recursive equation \<open>f_naive X\<^sub>i = f_naive X'\<^sub>i\<close>,
where \<open>i \<in> {1..m}\<close>.

Let:

\begin{itemize}

\item
\<open>'a\<close> be the Cartesian product of types \<open>'a\<^sub>1\<close>, ..., \<open>'a\<^sub>n\<close>.

\item
\<open>f_set\<close> be the inductive set of type \<open>'a \<Rightarrow> 'a set\<close> defined by
introduction rules \<open>x \<in> f_set x\<close>,
\<open>X\<^sub>1 \<in> f_set x \<Longrightarrow> X'\<^sub>1 \<in> f_set x\<close>, ...,
\<open>X\<^sub>m \<in> f_set x \<Longrightarrow> X'\<^sub>m \<in> f_set x\<close> -- where patterns \<open>X\<^sub>1\<close>,
\<open>X'\<^sub>1\<close>, ..., \<open>X\<^sub>m\<close>, \<open>X'\<^sub>m\<close> are now viewed as values of type
\<open>'a\<close>.

\end{itemize}

Then, the problem of discharging the above proof obligation on predicate
\<open>f_inv\<close> is at least as hard as that of proving by rule induction
introduction rule \<open>\<lbrakk>y \<in> f_set x; f_inv x\<rbrakk> \<Longrightarrow> f_inv y\<close> -- which states that
for any \<open>x\<close> such that \<open>f_inv x\<close> is true, \<open>f_inv\<close> is an
invariant over inductive set \<open>f_set x\<close>, i.e. \<open>f_inv y\<close> is true for
each \<open>y \<in> f_set x\<close>.

In fact, the application of rule induction to this goal generates subgoals
\<open>f_inv x \<Longrightarrow> f_inv x\<close>,
\<open>\<lbrakk>X\<^sub>1 \<in> f_set x; f_inv X\<^sub>1; f_inv x\<rbrakk> \<Longrightarrow> f_inv X'\<^sub>1\<close>, ...,
\<open>\<lbrakk>X\<^sub>m \<in> f_set x; f_inv X\<^sub>m; f_inv x\<rbrakk> \<Longrightarrow> f_inv X'\<^sub>m\<close>; the first is trivial,
and such would also be the other ones if rules \<open>f_inv X\<^sub>1 \<Longrightarrow> f_inv X'\<^sub>1\<close>,
..., \<open>f_inv X\<^sub>m \<Longrightarrow> f_inv X'\<^sub>m\<close> were available.

Furthermore, suppose that the above invariance property of predicate \<open>f_inv\<close>
have been proven; then, the proof of conditional
\<open>f_inv x \<longrightarrow> P (f_naive x)\<close> by recursion induction can be made unnecessary
by slightly refining the definition of function \<open>f_naive\<close>, as shown in the
continuation.

Let \<open>f_aux\<close> be the tail-recursive function of type \<open>'a \<Rightarrow> 'a\<close> whose
definition is obtained from that of \<open>f_naive\<close> by treating as fixed points
the patterns to which non-recursive equations apply as well as those to which no
equation applies, if any -- i.e. by replacing recursive equation
\<open>f_naive X\<^sub>i = f_naive X'\<^sub>i\<close> with \<open>f_aux X\<^sub>i = f_aux X'\<^sub>i\<close> for each
\<open>i \<in> {1..m}\<close> and non-recursive equation \<open>f_naive X = Y\<close> with
\<open>f_aux X = X\<close>.

Then, define function \<open>f\<close> by means of a non-recursive equation
\<open>f x = f_out (f_aux (f_in x))\<close>, where:

\begin{itemize}

\item
\<open>f_in\<close> is a function of type \<open>'a' \<Rightarrow> 'a\<close>, for a suitable type
\<open>'a'\<close>, whose range contains all the significant inputs of function
\<open>f_naive\<close>.

\item
\<open>f_out\<close> is a function of type \<open>'a \<Rightarrow> 'b\<close> mapping the outputs of
\<open>f_aux\<close> to those of \<open>f_naive\<close>, i.e. the values of type \<open>'a\<close>
matching pattern \<open>X\<close> to those of type \<open>'b\<close> matching pattern
\<open>Y\<close> with respect to the same value assignment.

\end{itemize}

The definitions of functions \<open>f_aux\<close> and \<open>f_out\<close> entail that equation
\<open>f_naive x = f_out (f_aux x)\<close> holds for any \<open>x\<close>. Particularly,
\<open>f_naive a = f_out (f_aux a)\<close>; thus, being \<open>a'\<close> an inverse image of
\<open>a\<close> under \<open>f_in\<close>, viz. \<open>a = f_in a'\<close>, it follows that
\<open>f_naive a = f a'\<close>. As a result, theorem \<open>P (f_naive a)\<close> may be
rewritten as \<open>P (f a')\<close>.

For any \<open>x\<close>, \<open>f_set x\<close> is precisely the set of the values
recursively input to function \<open>f_aux\<close> in the computation of
\<open>f_aux x\<close>, including \<open>x\<close> itself, and it can easily be ascertained
that \<open>f_aux x\<close> is such a value. In fact, the equation invoked last in the
computation of \<open>f_aux x\<close> must be a non-recursive one, so that it has the
form \<open>f_aux X = X\<close>, since all non-recursive equations in the definition
of \<open>f_aux\<close> apply to fixed points. Thus, being \<open>f_aux x\<close> the output
of the computation, the right-hand side of the equation, i.e. the pattern
\<open>X\<close> also input to function \<open>f_aux\<close> in the left-hand side, is
instantiated to value \<open>f_aux x\<close>.

Therefore, \<open>f_aux x \<in> f_set x\<close> for any \<open>x\<close>. Observe that the
argument rests on the assumption that whatever \<open>x\<close> is given, a sequence of
equations leading from \<open>x\<close> to \<open>f_aux x\<close> be actually available -- and
what is more, nothing significant could be proven on \<open>f_aux x\<close> for any
\<open>x\<close> for which its value were undefined, and then arbitrary. The trick of
making the definition of \<open>f_aux\<close> total by adding equations for the patterns
not covered in the definition of \<open>f_naive\<close>, if any, guarantees that this
assumption be satisfied.

An additional consequence of the previous argument is that
\<open>f_aux (f_aux x) = f_aux x\<close> for any \<open>x\<close>, i.e. function \<open>f_aux\<close>
is idempotent. If introduction rule \<open>\<lbrakk>f_inv x; f_form x\<rbrakk> \<Longrightarrow> P (f_naive x)\<close>
is rewritten by applying equation \<open>f_naive x = f_out (f_aux x)\<close>,
instantiating free variable \<open>x\<close> to \<open>f_aux x\<close>, and then applying the
idempotence of function \<open>f_aux\<close>, the result is formula
\<open>\<lbrakk>f_inv (f_aux x); f_form (f_aux x)\<rbrakk> \<Longrightarrow> P (f_out (f_aux x))\<close>, which is
nothing but an instantiation of introduction rule
\<open>\<lbrakk>f_inv x; f_form x\<rbrakk> \<Longrightarrow> P (f_out x)\<close>.

Observe that this rule is just a refinement of a rule whose proof is required for
proving conditional \<open>f_inv x \<longrightarrow> P (f_naive x)\<close> by recursion induction, so
that it does not give rise to any additional proof obligation. Moreover, it
contains neither function \<open>f_naive\<close> nor \<open>f_aux\<close>, thus its proof does
not require recursion induction with respect to the corresponding induction rules.

The instantiation of such refined introduction rule with value \<open>f_aux a\<close>
is \<open>\<lbrakk>f_inv (f_aux a); f_form (f_aux a)\<rbrakk> \<Longrightarrow> P (f_out (f_aux a))\<close>, which by
virtue of equality \<open>a = f_in a'\<close> and the definition of function \<open>f\<close>
is equivalent to formula
\<open>\<lbrakk>f_inv (f_aux a); f_form (f_aux a)\<rbrakk> \<Longrightarrow> P (f a')\<close>. Therefore, the rule is
sufficient to prove theorem \<open>P (f a')\<close> -- hence making unnecessary the
proof of conditional \<open>f_inv x \<longrightarrow> P (f_naive x)\<close> by recursion induction,
as mentioned previously -- provided the instantiated assumptions
\<open>f_inv (f_aux a)\<close>, \<open>f_form (f_aux a)\<close> can be shown to be true.

This actually is the case: the former assumption can be derived from formulae
\<open>f_aux a \<in> f_set a\<close>, \<open>f_inv a\<close> and the invariance of predicate
\<open>f_inv\<close> over \<open>f_set a\<close>, while the latter can be proven by recursion
induction, as by construction goal \<open>f_form X\<close> is trivial for any pattern
\<open>X\<close> to which some non-recursive equation in the definition of function
\<open>f_naive\<close> applies. If further non-recursive equations whose patterns do not
satisfy predicate \<open>f_form\<close> have been added to the definition of
\<open>f_aux\<close> to render it total, rule inversion can be applied to exclude that
\<open>f_aux a\<close> may match any of such patterns, again using formula
\<open>f_aux a \<in> f_set a\<close>.
\<close>

section "Method summary"

text \<open>
The general method developed so far can be schematized as follows.

Let \<open>f_naive\<close> be a tail-recursive function of type
\<open>'a\<^sub>1 \<Rightarrow> ... \<Rightarrow> 'a\<^sub>n \<Rightarrow> 'b\<close>, and \<open>P (f_naive a\<^sub>1 ... a\<^sub>n)\<close> be a
non-trivial theorem having to be proven on this function.

In order to accomplish such task, the following procedure shall be observed.

\begin{itemize}

\item
\emph{Step 1} --- Refine the definition of \<open>f_naive\<close> into that of an
auxiliary tail-recursive function \<open>f_aux\<close> of type \<open>'a \<Rightarrow> 'a\<close>, where
\<open>'a\<close> is a product or record type with types \<open>'a\<^sub>1\<close>, ..., \<open>'a\<^sub>n\<close>
as components, by treating as fixed points the patterns to which non-recursive
equations apply as well as those to which no equation applies, if any.

\item
\emph{Step 2} --- Define a function \<open>f\<close> of type \<open>'a' \<Rightarrow> 'b\<close> by means
of a non-recursive equation \<open>f x = f_out (f_aux (f_in x))\<close>, where
\<open>f_in\<close> is a function of type \<open>'a' \<Rightarrow> 'a\<close> (possibly matching the
identity function) whose range contains all the significant inputs of function
\<open>f_naive\<close>, and \<open>f_out\<close> is a function of type \<open>'a \<Rightarrow> 'b\<close>
mapping the outputs of \<open>f_aux\<close> to those of \<open>f_naive\<close>.
\\Then, denoting with \<open>a\<close> the value of type \<open>'a\<close> with components
\<open>a\<^sub>1\<close>, ..., \<open>a\<^sub>n\<close>, and with \<open>a'\<close> an inverse image of \<open>a\<close>
under function \<open>f_in\<close>, the theorem to be proven takes the equivalent form
\<open>P (f a')\<close>.

\item
\emph{Step 3} --- Let \<open>f_aux X\<^sub>1 = f_aux X'\<^sub>1\<close>, ...,
\<open>f_aux X\<^sub>m = f_aux X'\<^sub>m\<close> be the recursive equations in the definition of
function \<open>f_aux\<close>.
\\Then, define an inductive set \<open>f_set\<close> of type \<open>'a \<Rightarrow> 'a set\<close> with
introduction rules \<open>x \<in> f_set x\<close>,
\<open>X\<^sub>1 \<in> f_set x \<Longrightarrow> X'\<^sub>1 \<in> f_set x\<close>, ...,
\<open>X\<^sub>m \<in> f_set x \<Longrightarrow> X'\<^sub>m \<in> f_set x\<close>.
\\If the right-hand side of some recursive equation contains conditionals in the
form of \<open>if\<close> or \<open>case\<close> constructs, the corresponding introduction
rule can be split into as many rules as the possible mutually exclusive cases;
each of such rules shall then provide for the related case as an additional
assumption.

\item
\emph{Step 4} --- Prove lemma \<open>f_aux x \<in> f_set x\<close>; a general inference
scheme, independent of the specific function \<open>f_aux\<close>, applies to this proof.
\\First, prove lemma \<open>y \<in> f_set x \<Longrightarrow> f_set y \<subseteq> f_set x\<close>, which can easily
be done by rule induction.
\\Next, applying recursion induction to goal \<open>f_aux x \<in> f_set x\<close> and then
simplifying, a subgoal \<open>X\<^sub>i \<in> f_set X\<^sub>i\<close> arises for each non-recursive
equation \<open>f_aux X\<^sub>i = X\<^sub>i\<close>, while a subgoal
\<open>f_aux X'\<^sub>j \<in> f_set X'\<^sub>j \<Longrightarrow> f_aux X'\<^sub>j \<in> f_set X\<^sub>j\<close> arises for each recursive
equation \<open>f_aux X\<^sub>j = f_aux X'\<^sub>j\<close>.
\\The former subgoals can be proven by introduction rule \<open>x \<in> f_set x\<close>, the
latter ones as follows: rule instantiations \<open>X\<^sub>j \<in> f_set X\<^sub>j\<close> and
\<open>X\<^sub>j \<in> f_set X\<^sub>j \<Longrightarrow> X'\<^sub>j \<in> f_set X\<^sub>j\<close> imply formula \<open>X'\<^sub>j \<in> f_set X\<^sub>j\<close>;
thus \<open>f_set X'\<^sub>j \<subseteq> f_set X\<^sub>j\<close> by the aforesaid lemma; from this and subgoal
assumption \<open>f_aux X'\<^sub>j \<in> f_set X'\<^sub>j\<close>, subgoal conclusion
\<open>f_aux X'\<^sub>j \<in> f_set X\<^sub>j\<close> ensues.
\\As regards recursive equations containing conditionals, the above steps have to
be preceded by a case distinction, so as to obtain further assumptions sufficient
for splitting such conditionals.

\item
\emph{Step 5} --- Define a predicate \<open>f_inv\<close> of type \<open>'a \<Rightarrow> bool\<close> in
such a way as to meet the proof obligations prescribed by the following steps.

\item
\emph{Step 6} --- Prove lemma \<open>f_inv a\<close>.
\\In case of failure, return to step 5 so as to suitably change the definition of
predicate \<open>f_inv\<close>.

\item
\emph{Step 7} --- Prove introduction rule \<open>f_inv x \<Longrightarrow> P (f_out x)\<close>, or
rather \<open>\<lbrakk>f_inv x; f_form x\<rbrakk> \<Longrightarrow> P (f_out x)\<close>, where \<open>f_form\<close> is a
suitable predicate of type \<open>'a \<Rightarrow> bool\<close> satisfied by any pattern to which
some non-recursive equation in the definition of function \<open>f_naive\<close> applies.
\\In case of failure, return to step 5 so as to suitably change the definition of
predicate \<open>f_inv\<close>.

\item
\emph{Step 8} --- In case an introduction rule of the second form has been proven
in step 7, prove lemma \<open>f_form (f_aux a)\<close> by recursion induction.
\\If the definition of function \<open>f_aux\<close> resulting from step 1 contains
additional non-recursive equations whose patterns do not satisfy predicate
\<open>f_form\<close>, rule inversion can be applied to exclude that \<open>f_aux a\<close>
may match any of such patterns, using instantiation \<open>f_aux a \<in> f_set a\<close> of
the lemma proven in step 4.

\item
\emph{Step 9} --- Prove by rule induction introduction rule
\<open>\<lbrakk>y \<in> f_set x; f_inv x\<rbrakk> \<Longrightarrow> f_inv y\<close>, which states the invariance of
predicate \<open>f_inv\<close> over inductive set \<open>f_set x\<close> for any \<open>x\<close>
satisfying \<open>f_inv\<close>.
\\In case of failure, return to step 5 so as to suitably change the definition of
predicate \<open>f_inv\<close>.
\\Observe that the order in which the proof obligations related to predicate
\<open>f_inv\<close> are distributed among steps 6 to 9 is ascending in the effort
typically required to discharge them. The reason why this strategy is advisable is
that in case one step fails, which forces to revise the definition of predicate
\<open>f_inv\<close> and then also the proofs already worked out, such proofs will be the
least demanding ones so as to minimize the effort required for their revision.

\item
\emph{Step 10} --- Prove theorem \<open>P (f a')\<close> by means of the following
inference scheme.
\\First, derive formula \<open>f_inv (f_aux a)\<close> from introduction rule
\<open>\<lbrakk>y \<in> f_set x; f_inv x\<rbrakk> \<Longrightarrow> f_inv y\<close> and formulae
\<open>f_aux a \<in> f_set a\<close>, \<open>f_inv a\<close>.
\\Then, derive formula \<open>P (f_out (f_aux a))\<close> from either introduction rule
\<open>f_inv x \<Longrightarrow> P (f_out x)\<close> or \<open>\<lbrakk>f_inv x; f_form x\<rbrakk> \<Longrightarrow> P (f_out x)\<close>
and formulae \<open>f_inv (f_aux a)\<close>, \<open>f_form (f_aux a)\<close> (in the latter
case).
\\Finally, derive theorem \<open>P (f a')\<close> from formulae
\<open>P (f_out (f_aux a))\<close>, \<open>a = f_in a'\<close> and the definition of
function \<open>f\<close>.

\end{itemize}

In the continuation, the application of this method is illustrated by analyzing
two case studies drawn from an exercise comprised in Isabelle online course
material; see \cite{R5}. The salient points of definitions and proofs are
commented; for additional information see Isabelle documentation, particularly
\cite{R1}, \cite{R2}, \cite{R3}, and \cite{R4}.
\<close>

(*<*)
end
(*>*)
