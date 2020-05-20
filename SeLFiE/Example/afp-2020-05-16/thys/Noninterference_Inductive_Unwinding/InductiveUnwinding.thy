(*  Title:       The Inductive Unwinding Theorem for CSP Noninterference Security
    Author:      Pasquale Noce
                 Security Certification Specialist at Arjo Systems - Gep S.p.A.
                 pasquale dot noce dot lavoro at gmail dot com
                 pasquale dot noce at arjowiggins-it dot com
*)

section "The Inductive Unwinding Theorem"

theory InductiveUnwinding
imports Noninterference_Ipurge_Unwinding.DeterministicProcesses
begin

text \<open>
\null

The necessary and sufficient condition for CSP noninterference security \cite{R2} stated by the
Ipurge Unwinding Theorem \cite{R3} is expressed in terms of a pair of event lists varying over the
set of process traces. This does not render it suitable for the subsequent application of rule
induction in the case of a process defined inductively, since rule induction may rather be applied
to a single variable ranging over an inductively defined set (cf. \cite{R6}).

However, the formulation of an inductive definition is the standard way of defining a process that
admits traces of unbounded length, indeed because it provides rule induction as a powerful method to
prove process properties, particularly noninterference security, by considering any indefinitely
long trace of the process. Therefore, it is essential to infer some condition equivalent to CSP
noninterference security and suitable for being handled by means of rule induction.

Starting from the Ipurge Unwinding Theorem, this paper derives a necessary and sufficient condition
for CSP noninterference security that involves a single event list varying over the set of process
traces, and is thus suitable for rule induction; hence its name, \emph{Inductive Unwinding Theorem}.
Similarly to the Ipurge Unwinding Theorem, the new theorem only requires to consider individual
accepted and refused events for each process trace, and applies to the general case of a possibly
intransitive noninterference policy. Specific variants of this theorem are additionally proven for
deterministic processes and trace set processes \cite{R3}.

For details about the theory of Communicating Sequential Processes, to which the notion of process
security defined in \cite{R2} and applied in this paper refers, cf. \cite{R4}.

As regards the formal contents of this paper, the salient points of definitions and proofs are
commented; for additional information, cf. Isabelle documentation, particularly \cite{R6},
\cite{R7}, \cite{R8}, and \cite{R9}.
\<close>


subsection "Propaedeutic lemmas"

text \<open>
Here below are the proofs of some lemmas on the constants defined in \cite{R2} and \cite{R3} which
are propaedeutic to the demonstration of the Inductive Unwinding Theorem.

Among other things, the lemmas being proven formalize the following statements:

\begin{itemize}

\item
A set of domains @{term U} may affect a set of domains @{term V} via an event list @{term xs}, as
expressed through function @{term sinks_aux}, just in case @{term V} may be affected by @{term U}
via @{term xs}, as expressed through function @{term sources_aux}.

\item
The event lists output by function @{term ipurge_tr} are not longer than the corresponding input
ones.

\item
Function @{term ipurge_tr_rev} is idempotent.

\end{itemize}

\null
\<close>

lemma sources_aux_single_dom:
 "sources_aux I D {u} xs = insert u (sources I D u xs)"
by (simp add: sources_sinks sources_sinks_aux sinks_aux_single_dom)

lemma sources_interference_eq:
 "((D x, u) \<in> I \<or> (\<exists>v \<in> sources I D u xs. (D x, v) \<in> I)) =
  (D x \<in> sources I D u (x # xs))"
proof (simp only: sources_sinks rev.simps, subst (1 2) converse_iff [symmetric])
qed (rule sinks_interference_eq)

lemma ex_sinks_sources_aux_1 [rule_format]:
 "(\<exists>u \<in> sinks_aux I D U xs. \<exists>v \<in> V. (u, v) \<in> I) \<longrightarrow>
  (\<exists>u \<in> U. \<exists>v \<in> sources_aux I D V xs. (u, v) \<in> I)"
proof (induction xs arbitrary: V rule: rev_induct, simp, subst sources_aux_append,
 rule impI)
  fix x xs V
  let
    ?V = "sources_aux I D V [x]" and
    ?V' = "insert (D x) V"
  assume
    A: "\<And>V. (\<exists>u \<in> sinks_aux I D U xs. \<exists>v \<in> V. (u, v) \<in> I) \<longrightarrow>
      (\<exists>u \<in> U. \<exists>v \<in> sources_aux I D V xs. (u, v) \<in> I)" and
    B: "\<exists>u \<in> sinks_aux I D U (xs @ [x]). \<exists>v \<in> V. (u, v) \<in> I"
  show "\<exists>u \<in> U. \<exists>v \<in> sources_aux I D ?V xs. (u, v) \<in> I"
  proof (cases "\<exists>u \<in> sinks_aux I D U xs. (u, D x) \<in> I")
    case True
    hence "(\<exists>v \<in> V. (D x, v) \<in> I) \<or>
      (\<exists>u \<in> sinks_aux I D U xs. \<exists>v \<in> V. (u, v) \<in> I)"
     (is "?A \<or> ?B") using B by simp
    moreover {
      assume ?A
      have "(\<exists>u \<in> sinks_aux I D U xs. \<exists>v \<in> ?V'. (u, v) \<in> I) \<longrightarrow>
        (\<exists>u \<in> U. \<exists>v \<in> sources_aux I D ?V' xs. (u, v) \<in> I)"
       using A .
      moreover obtain u where
        C: "u \<in> sinks_aux I D U xs" and D: "(u, D x) \<in> I"
       using True ..
      have "D x \<in> ?V'" by simp
      with D have "\<exists>v \<in> ?V'. (u, v) \<in> I" ..
      hence "\<exists>u \<in> sinks_aux I D U xs. \<exists>v \<in> ?V'. (u, v) \<in> I" using C ..
      ultimately have "\<exists>u \<in> U. \<exists>v \<in> sources_aux I D ?V' xs. (u, v) \<in> I" ..
      hence ?thesis using \<open>?A\<close> by simp
    }
    moreover {
      assume ?B
      have "(\<exists>u \<in> sinks_aux I D U xs. \<exists>v \<in> ?V. (u, v) \<in> I) \<longrightarrow>
        (\<exists>u \<in> U. \<exists>v \<in> sources_aux I D ?V xs. (u, v) \<in> I)"
       using A .
      moreover obtain u where
        C: "u \<in> sinks_aux I D U xs" and D: "\<exists>v \<in> V. (u, v) \<in> I"
       using \<open>?B\<close> ..
      have "V \<subseteq> ?V" by (rule sources_aux_subset)
      hence "\<exists>v \<in> ?V. (u, v) \<in> I" using D by simp
      hence "\<exists>u \<in> sinks_aux I D U xs. \<exists>v \<in> ?V. (u, v) \<in> I" using C ..
      ultimately have ?thesis ..
    }
    ultimately show ?thesis ..
  next
    case False
    have "(\<exists>u \<in> sinks_aux I D U xs. \<exists>v \<in> ?V. (u, v) \<in> I) \<longrightarrow>
      (\<exists>u \<in> U. \<exists>v \<in> sources_aux I D ?V xs. (u, v) \<in> I)"
     using A .
    moreover have "\<exists>u \<in> sinks_aux I D U xs. \<exists>v \<in> V. (u, v) \<in> I"
     using B and False by simp
    then obtain u where
      C: "u \<in> sinks_aux I D U xs" and D: "\<exists>v \<in> V. (u, v) \<in> I" ..
    have "V \<subseteq> ?V" by (rule sources_aux_subset)
    hence "\<exists>v \<in> ?V. (u, v) \<in> I" using D by simp
    hence "\<exists>u \<in> sinks_aux I D U xs. \<exists>v \<in> ?V. (u, v) \<in> I" using C ..
    ultimately show ?thesis ..
  qed
qed

lemma ex_sinks_sources_aux_2 [rule_format]:
 "(\<exists>u \<in> U. \<exists>v \<in> sources_aux I D V xs. (u, v) \<in> I) \<longrightarrow>
  (\<exists>u \<in> sinks_aux I D U xs. \<exists>v \<in> V. (u, v) \<in> I)"
proof (induction xs arbitrary: V rule: rev_induct, simp, subst sources_aux_append,
 rule impI)
  fix x xs V
  let
    ?V = "sources_aux I D V [x]" and
    ?V' = "insert (D x) V"
  assume
    A: "\<And>V. (\<exists>u \<in> U. \<exists>v \<in> sources_aux I D V xs. (u, v) \<in> I) \<longrightarrow>
      (\<exists>u \<in> sinks_aux I D U xs. \<exists>v \<in> V. (u, v) \<in> I)" and
    B: "\<exists>u \<in> U. \<exists>v \<in> sources_aux I D ?V xs. (u, v) \<in> I"
  show "\<exists>u \<in> sinks_aux I D U (xs @ [x]). \<exists>v \<in> V. (u, v) \<in> I"
  proof (cases "\<exists>u \<in> sinks_aux I D U xs. (u, D x) \<in> I",
   cases "\<exists>v \<in> V. (D x, v) \<in> I", simp_all (no_asm_simp))
    have "(\<exists>u \<in> U. \<exists>v \<in> sources_aux I D V xs. (u, v) \<in> I) \<longrightarrow>
      (\<exists>u \<in> sinks_aux I D U xs. \<exists>v \<in> V. (u, v) \<in> I)"
     using A .
    moreover assume "\<not> (\<exists>v \<in> V. (D x, v) \<in> I)"
    hence "\<exists>u \<in> U. \<exists>v \<in> sources_aux I D V xs. (u, v) \<in> I" using B by simp
    ultimately show "\<exists>u \<in> sinks_aux I D U xs. \<exists>v \<in> V. (u, v) \<in> I" ..
  next
    assume C: "\<not> (\<exists>u \<in> sinks_aux I D U xs. (u, D x) \<in> I)"
    have "(\<exists>u \<in> U. \<exists>v \<in> sources_aux I D ?V xs. (u, v) \<in> I) \<longrightarrow>
      (\<exists>u \<in> sinks_aux I D U xs. \<exists>v \<in> ?V. (u, v) \<in> I)"
     using A .
    hence "\<exists>u \<in> sinks_aux I D U xs. \<exists>v \<in> ?V. (u, v) \<in> I" using B ..
    then obtain u where
      D: "u \<in> sinks_aux I D U xs" and E: "\<exists>v \<in> ?V. (u, v) \<in> I" ..
    obtain v where F: "v \<in> ?V" and G: "(u, v) \<in> I" using E ..
    have "v = D x \<or> v \<in> V" using F by (cases "\<exists>v \<in> V. (D x, v) \<in> I", simp_all)
    moreover {
      assume "v = D x"
      hence "(u, D x) \<in> I" using G by simp
      hence "\<exists>u \<in> sinks_aux I D U xs. (u, D x) \<in> I" using D ..
      hence "\<exists>u \<in> sinks_aux I D U xs. \<exists>v \<in> V. (u, v) \<in> I"
       using C by contradiction
    }
    moreover {
      assume "v \<in> V"
      with G have "\<exists>v \<in> V. (u, v) \<in> I" ..
      hence "\<exists>u \<in> sinks_aux I D U xs. \<exists>v \<in> V. (u, v) \<in> I" using D ..
    }
    ultimately show "\<exists>u \<in> sinks_aux I D U xs. \<exists>v \<in> V. (u, v) \<in> I" ..
  qed
qed

lemma ex_sinks_sources_aux:
 "(\<exists>u \<in> sinks_aux I D U xs. \<exists>v \<in> V. (u, v) \<in> I) =
  (\<exists>u \<in> U. \<exists>v \<in> sources_aux I D V xs. (u, v) \<in> I)"
by (rule iffI, erule ex_sinks_sources_aux_1, rule ex_sinks_sources_aux_2)

lemma ipurge_tr_rev_ipurge_tr_sources_aux_1 [rule_format]:
 "\<not> (\<exists>v \<in> D ` set ys. \<exists>u \<in> sources_aux I D U zs. (v, u) \<in> I) \<longrightarrow>
  ipurge_tr_rev_aux I D U (xs @ ys @ zs) =
  ipurge_tr_rev_aux I D U (xs @ ipurge_tr_aux I D (D ` set ys) zs)"
proof (induction zs arbitrary: U rule: rev_induct, rule_tac [!] impI,
 simp del: bex_simps)
  fix U
  assume "\<not> (\<exists>v \<in> D ` set ys. \<exists>u \<in> U. (v, u) \<in> I)"
  hence "ipurge_tr_rev_aux I D U ys = []" by (simp add: ipurge_tr_rev_aux_nil)
  thus "ipurge_tr_rev_aux I D U (xs @ ys) = ipurge_tr_rev_aux I D U xs"
   by (simp add: ipurge_tr_rev_aux_append_nil)
next
  fix z zs U
  let
    ?U = "sources_aux I D U [z]" and
    ?U' = "insert (D z) U"
  assume "\<And>U. \<not> (\<exists>v \<in> D ` set ys. \<exists>u \<in> sources_aux I D U zs. (v, u) \<in> I) \<longrightarrow>
    ipurge_tr_rev_aux I D U (xs @ ys @ zs) =
    ipurge_tr_rev_aux I D U (xs @ ipurge_tr_aux I D (D ` set ys) zs)"
  hence "\<not> (\<exists>v \<in> D ` set ys. \<exists>u \<in> sources_aux I D ?U zs. (v, u) \<in> I) \<longrightarrow>
    ipurge_tr_rev_aux I D ?U (xs @ ys @ zs) =
    ipurge_tr_rev_aux I D ?U (xs @ ipurge_tr_aux I D (D ` set ys) zs)" .
  moreover assume
   "\<not> (\<exists>v \<in> D ` set ys. \<exists>u \<in> sources_aux I D U (zs @ [z]). (v, u) \<in> I)"
  hence A:
   "\<not> (\<exists>v \<in> D ` set ys. \<exists>u \<in> sources_aux I D ?U zs. (v, u) \<in> I)"
   by (subst (asm) sources_aux_append)
  ultimately have B:
   "ipurge_tr_rev_aux I D ?U (xs @ ys @ zs) =
    ipurge_tr_rev_aux I D ?U (xs @ ipurge_tr_aux I D (D ` set ys) zs)" ..
  have 
   "ipurge_tr_rev_aux I D U (xs @ ys @ zs @ [z]) =
    ipurge_tr_rev_aux I D U ((xs @ ys @ zs) @ [z])"
   by simp
  hence C:
   "ipurge_tr_rev_aux I D U (xs @ ys @ zs @ [z]) =
    ipurge_tr_rev_aux I D ?U (xs @ ys @ zs) @ ipurge_tr_rev_aux I D U [z]"
   (is "_ = _ @ ?ws") by (simp only: ipurge_tr_rev_aux_append)
  show
   "ipurge_tr_rev_aux I D U (xs @ ys @ zs @ [z]) =
    ipurge_tr_rev_aux I D U (xs @ ipurge_tr_aux I D (D ` set ys) (zs @ [z]))"
  proof (subst C, cases "\<exists>u \<in> U. (D z, u) \<in> I",
   simp_all (no_asm_simp) del: ipurge_tr_aux.simps)
    case True
    have "\<not> (\<exists>v \<in> sinks_aux I D (D ` set ys) zs. \<exists>u \<in> ?U. (v, u) \<in> I)"
     using A by (simp add: ex_sinks_sources_aux)
    hence "\<not> (\<exists>v \<in> sinks_aux I D (D ` set ys) zs. (v, D z) \<in> I)"
     using True by simp
    hence
     "ipurge_tr_rev_aux I D U (xs @ ipurge_tr_aux I D (D ` set ys) (zs @ [z])) =
      ipurge_tr_rev_aux I D U ((xs @ ipurge_tr_aux I D (D ` set ys) zs) @ [z])"
     by simp
    also have "\<dots> =
      ipurge_tr_rev_aux I D ?U (xs @ ipurge_tr_aux I D (D ` set ys) zs) @ ?ws"
     by (simp only: ipurge_tr_rev_aux_append)
    also have "\<dots> =
      ipurge_tr_rev_aux I D ?U' (xs @ ipurge_tr_aux I D (D ` set ys) zs) @ [z]"
     using True by simp
    finally have
     "ipurge_tr_rev_aux I D U (xs @ ipurge_tr_aux I D (D ` set ys) (zs @ [z])) =
      ipurge_tr_rev_aux I D ?U' (xs @ ipurge_tr_aux I D (D ` set ys) zs) @ [z]" .
    thus
     "ipurge_tr_rev_aux I D ?U' (xs @ ys @ zs) @ [z] =
      ipurge_tr_rev_aux I D U (xs @ ipurge_tr_aux I D (D ` set ys) (zs @ [z]))"
     using B and True by simp
  next
    case False
    have
     "ipurge_tr_rev_aux I D U (xs @ ipurge_tr_aux I D (D ` set ys) (zs @ [z])) =
      ipurge_tr_rev_aux I D U (xs @ ipurge_tr_aux I D (D ` set ys) zs)"
    proof (cases "\<exists>v \<in> sinks_aux I D (D ` set ys) zs. (v, D z) \<in> I", simp_all)
      have
       "ipurge_tr_rev_aux I D U (xs @ ipurge_tr_aux I D (D ` set ys) zs @ [z]) =
        ipurge_tr_rev_aux I D U ((xs @ ipurge_tr_aux I D (D ` set ys) zs) @ [z])"
       by simp
      also have "\<dots> =
        ipurge_tr_rev_aux I D ?U (xs @ ipurge_tr_aux I D (D ` set ys) zs) @ ?ws"
       by (simp only: ipurge_tr_rev_aux_append)
      also have "\<dots> =
        ipurge_tr_rev_aux I D U (xs @ ipurge_tr_aux I D (D ` set ys) zs)"
       using False by simp
      finally show
       "ipurge_tr_rev_aux I D U (xs @ ipurge_tr_aux I D (D ` set ys) zs @ [z]) =
        ipurge_tr_rev_aux I D U (xs @ ipurge_tr_aux I D (D ` set ys) zs)" .
    qed
    thus
     "ipurge_tr_rev_aux I D U (xs @ ys @ zs) =
      ipurge_tr_rev_aux I D U (xs @ ipurge_tr_aux I D (D ` set ys) (zs @ [z]))"
     using B and False by simp
  qed
qed

lemma ipurge_tr_rev_ipurge_tr_sources_1:
  assumes A: "D y \<notin> sources I D u (y # zs)"
  shows
   "ipurge_tr_rev I D u (xs @ y # zs) =
    ipurge_tr_rev I D u (xs @ ipurge_tr I D (D y) zs)"
proof -
  have "\<not> ((D y, u) \<in> I \<or> (\<exists>v \<in> sources I D u zs. (D y, v) \<in> I))"
   using A by (simp only: sources_interference_eq, simp)
  hence "\<not> (\<exists>v \<in> D ` set [y]. \<exists>u \<in> sources_aux I D {u} zs. (v, u) \<in> I)"
   by (simp add: sources_aux_single_dom)
  hence
   "ipurge_tr_rev_aux I D {u} (xs @ [y] @ zs) =
    ipurge_tr_rev_aux I D {u} (xs @ ipurge_tr_aux I D (D ` set [y]) zs)"
   by (rule ipurge_tr_rev_ipurge_tr_sources_aux_1)
  thus ?thesis by (simp add: ipurge_tr_aux_single_dom ipurge_tr_rev_aux_single_dom)
qed

lemma ipurge_tr_length:
 "length (ipurge_tr I D u xs) \<le> length xs"
by (induction xs rule: rev_induct, simp_all)

lemma sources_idem:
 "sources I D u (ipurge_tr_rev I D u xs) = sources I D u xs"
by (induction xs, simp_all)

lemma ipurge_tr_rev_idem:
 "ipurge_tr_rev I D u (ipurge_tr_rev I D u xs) = ipurge_tr_rev I D u xs"
by (induction xs, simp_all add: sources_idem)


subsection "Closure of the traces of a secure process under reverse intransitive purge"

text \<open>
The derivation of the Inductive Unwinding Theorem from the Ipurge Unwinding Theorem requires to
prove that the set of the traces of a secure process is closed under reverse intransitive purge,
i.e. function @{term ipurge_tr_rev} \cite{R3}. This can be expressed formally by means of the
following statement:

\null

@{term "secure P I D \<Longrightarrow> xs \<in> traces P \<Longrightarrow> ipurge_tr_rev I D u xs \<in> traces P"}

\null

The reason why such closure property holds is that the reverse intransitive purge of a list
@{term xs} with regard to a policy @{term I}, an event-domain map @{term D}, and a domain @{term u}
can equivalently be computed as follows: for each item @{term x} of @{term xs}, if @{term x} may
affect @{term u}, retain @{term x} and go on recursively using as input the sublist of @{term xs}
following @{term x}, say @{term xs'}; otherwise, discard @{term x} and go on recursively using
@{term "ipurge_tr I D (D x) xs'"} \cite{R2} as input.

The result actually matches @{term "ipurge_tr_rev I D u xs"}. In fact, for each @{term x} not
affecting @{term u}, @{term "ipurge_tr I D (D x) xs'"} retains any item of @{term xs'} not affected
by @{term x}, which is the case for any item of @{term xs'} affecting @{term u}, since otherwise
@{term x} would affect @{term u}.

Furthermore, if @{term xs} is a trace of a secure process, the result is still a trace. In fact, for
each @{term x} not affecting @{term u}, if @{term ys} is the partial output for the sublist of
@{term xs} preceding @{term x}, then @{term "ys @ ipurge_tr I D (D x) xs'"} is a trace provided such
is @{term "ys @ x # xs'"}, by virtue of the definition of CSP noninterference security \cite{R2}.
Hence, the property of being a trace is conserved upon each recursive call by the concatenation of
the partial output and the residual input, until the latter is nil and the former matches the total
output.

This argument shows that in order to prove by induction, under the aforesaid assumptions, that the
output of such a reverse intransitive purge function is a trace, the partial output has to be passed
to the function as an argument, in addition to the residual input, in the recursive calls contained
within the definition of the function. Therefore, the output of the function has to be accumulated
into one of its parameters, viz. the function needs to be tail-recursive. This suggests to prove the
properties of interest of the function by applying the ten-step proof method for theorems on
tail-recursive functions described in \cite{R1}.

The starting point is to formulate a naive definition of the function, which will then be refined as
specified by the proof method. The name of the refined function, from which the name of the naive
function here below is derived, will be \<open>ipurge_tr_rev_t\<close>, where suffix \emph{t} stands for
\emph{tail-recursive}.

\null
\<close>

function (sequential) ipurge_tr_rev_t_naive ::
  "('d \<times> 'd) set \<Rightarrow> ('a \<Rightarrow> 'd) \<Rightarrow> 'd \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"ipurge_tr_rev_t_naive I D u (x # xs) ys =
 (if D x \<in> sources I D u (x # xs)
  then ipurge_tr_rev_t_naive I D u xs (ys @ [x])
  else ipurge_tr_rev_t_naive I D u (ipurge_tr I D (D x) xs) ys)" |
"ipurge_tr_rev_t_naive _ _ _ _ ys = ys"
oops

text \<open>
\null

The parameter into which the output is accumulated is the last one.

As shown by the previous argument, the properties of function @{term ipurge_tr_rev_t_naive} that
would have to be proven are the following ones:

\null

@{term "ipurge_tr_rev_t_naive I D u xs [] = ipurge_tr_rev I D u xs"}

\null

@{term "secure P I D \<Longrightarrow> xs \<in> traces P \<Longrightarrow> ipurge_tr_rev_t_naive I D u xs [] \<in> traces P"}

\null

as they clearly entail the above formal statement of the target closure lemma.
\<close>

subsubsection "Step 1"

text \<open>
In the definition of the auxiliary tail-recursive function @{term ipurge_tr_rev_t_aux}, the
Cartesian product of the input types of function @{term ipurge_tr_rev_t_naive} will be implemented
as a record type.

\null
\<close>

record ('a, 'd) ipurge_rec =
  Pol :: "('d \<times> 'd) set"
  Map :: "'a \<Rightarrow> 'd"
  Dom :: 'd
  In :: "'a list"
  Out :: "'a list"

function (sequential) ipurge_tr_rev_t_aux ::
  "('a, 'd) ipurge_rec \<Rightarrow> ('a, 'd) ipurge_rec" where
"ipurge_tr_rev_t_aux \<lparr>Pol = I, Map = D, Dom = u, In = x # xs, Out = ys\<rparr> =
 (if D x \<in> sources I D u (x # xs)
  then ipurge_tr_rev_t_aux
    \<lparr>Pol = I, Map = D, Dom = u, In = xs, Out = ys @ [x]\<rparr>
  else ipurge_tr_rev_t_aux
    \<lparr>Pol = I, Map = D, Dom = u, In = ipurge_tr I D (D x) xs, Out = ys\<rparr>)" |
"ipurge_tr_rev_t_aux X = X"
proof (simp_all, atomize_elim)
  fix X :: "('a, 'd) ipurge_rec"
  show
   "(\<exists>I D u x xs ys.
      X = \<lparr>Pol = I, Map = D, Dom = u, In = x # xs, Out = ys\<rparr>) \<or>
    (\<exists>I D u ys.
      X = \<lparr>Pol = I, Map = D, Dom = u, In = [], Out = ys\<rparr>)"
  proof (cases X, simp_all)
  qed (subst disj_commute, rule spec [OF list.nchotomy])
qed

termination ipurge_tr_rev_t_aux
proof (relation "measure (\<lambda>X. length (In X))", simp_all)
  fix D :: "'a \<Rightarrow> 'd" and I x xs
  have "length (ipurge_tr I D (D x) xs) \<le> length xs" by (rule ipurge_tr_length)
  thus "length (ipurge_tr I D (D x) xs) < Suc (length xs)" by simp
qed

text \<open>
\null

As shown by this proof, the termination of function @{term ipurge_tr_rev_t_aux} is guaranteed by the
fact, proven previously, that the event lists output by function @{term ipurge_tr} are not longer
than the corresponding input ones.
\<close>

subsubsection "Step 2"

definition ipurge_tr_rev_t_in ::
  "('d \<times> 'd) set \<Rightarrow> ('a \<Rightarrow> 'd) \<Rightarrow> 'd \<Rightarrow> 'a list \<Rightarrow> ('a, 'd) ipurge_rec" where
"ipurge_tr_rev_t_in I D u xs \<equiv>
  \<lparr>Pol = I, Map = D, Dom = u, In = xs, Out = []\<rparr>"

definition ipurge_tr_rev_t_out ::
  "('a, 'd) ipurge_rec \<Rightarrow> 'a list" where
"ipurge_tr_rev_t_out \<equiv> Out"

definition ipurge_tr_rev_t ::
  "('d \<times> 'd) set \<Rightarrow> ('a \<Rightarrow> 'd) \<Rightarrow> 'd \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"ipurge_tr_rev_t I D u xs \<equiv>
  ipurge_tr_rev_t_out (ipurge_tr_rev_t_aux (ipurge_tr_rev_t_in I D u xs))"

text \<open>
\null

Since the significant inputs of function @{term ipurge_tr_rev_t_naive} match pattern \<open>_\<close>,
\<open>_\<close>, \<open>_\<close>, \<open>_\<close>, @{term "[]"}, those of function @{term ipurge_tr_rev_t_aux}, as
returned by function @{term ipurge_tr_rev_t_in}, match pattern
\<open>\<lparr>Pol = _, Map = _, Dom = _, In = _, Out = []\<rparr>\<close>.

In terms of function @{term ipurge_tr_rev_t}, the statements to be proven, henceforth respectively
named \<open>ipurge_tr_rev_t_equiv\<close> and \<open>ipurge_tr_rev_t_trace\<close>, take the following form:

\null

@{term "ipurge_tr_rev_t I D u xs = ipurge_tr_rev I D u xs"}

\null

@{term "secure P I D \<Longrightarrow> xs \<in> traces P \<Longrightarrow> ipurge_tr_rev_t I D u xs \<in> traces P"}
\<close>

subsubsection "Step 3"

inductive_set ipurge_tr_rev_t_set :: "('a, 'd) ipurge_rec \<Rightarrow> ('a, 'd) ipurge_rec set"
  for X :: "('a, 'd) ipurge_rec" where
R0: "X \<in> ipurge_tr_rev_t_set X" |
R1: "\<lbrakk>\<lparr>Pol = I, Map = D, Dom = u, In = x # xs, Out = ys\<rparr>
        \<in> ipurge_tr_rev_t_set X;
      D x \<in> sources I D u (x # xs)\<rbrakk> \<Longrightarrow>
     \<lparr>Pol = I, Map = D, Dom = u, In = xs, Out = ys @ [x]\<rparr>
       \<in> ipurge_tr_rev_t_set X" |
R2: "\<lbrakk>\<lparr>Pol = I, Map = D, Dom = u, In = x # xs, Out = ys\<rparr>
        \<in> ipurge_tr_rev_t_set X;
      D x \<notin> sources I D u (x # xs)\<rbrakk> \<Longrightarrow>
     \<lparr>Pol = I, Map = D, Dom = u, In = ipurge_tr I D (D x) xs, Out = ys\<rparr>
       \<in> ipurge_tr_rev_t_set X"

subsubsection "Step 4"

lemma ipurge_tr_rev_t_subset:
  assumes A: "Y \<in> ipurge_tr_rev_t_set X"
  shows "ipurge_tr_rev_t_set Y \<subseteq> ipurge_tr_rev_t_set X"
proof (rule subsetI, erule ipurge_tr_rev_t_set.induct)
  show "Y \<in> ipurge_tr_rev_t_set X" using A .
next
  fix I D u x xs ys
  assume
    "\<lparr>Pol = I, Map = D, Dom = u, In = x # xs, Out = ys\<rparr>
       \<in> ipurge_tr_rev_t_set X" and
    "D x \<in> sources I D u (x # xs)"
  thus "\<lparr>Pol = I, Map = D, Dom = u, In = xs, Out = ys @ [x]\<rparr>
    \<in> ipurge_tr_rev_t_set X"
   by (rule R1)
next
  fix I D u x xs ys
  assume
    "\<lparr>Pol = I, Map = D, Dom = u, In = x # xs, Out = ys\<rparr>
       \<in> ipurge_tr_rev_t_set X" and
    "D x \<notin> sources I D u (x # xs)"
  thus "\<lparr>Pol = I, Map = D, Dom = u, In = ipurge_tr I D (D x) xs, Out = ys\<rparr>
    \<in> ipurge_tr_rev_t_set X"
   by (rule R2)
qed

lemma ipurge_tr_rev_t_aux_set:
 "ipurge_tr_rev_t_aux X \<in> ipurge_tr_rev_t_set X"
proof (induction rule: ipurge_tr_rev_t_aux.induct,
 simp_all only: ipurge_tr_rev_t_aux.simps(2) R0)
  fix I u x xs ys and D :: "'a \<Rightarrow> 'd"
  assume
    A: "D x \<in> sources I D u (x # xs) \<Longrightarrow>
        ipurge_tr_rev_t_aux
          \<lparr>Pol = I, Map = D, Dom = u, In = xs, Out = ys @ [x]\<rparr>
        \<in> ipurge_tr_rev_t_set
          \<lparr>Pol = I, Map = D, Dom = u, In = xs, Out = ys @ [x]\<rparr>"
      (is "_ \<Longrightarrow> ipurge_tr_rev_t_aux ?Y \<in> _") and
    B: "D x \<notin> sources I D u (x # xs) \<Longrightarrow>
        ipurge_tr_rev_t_aux
          \<lparr>Pol = I, Map = D, Dom = u, In = ipurge_tr I D (D x) xs, Out = ys\<rparr>
        \<in> ipurge_tr_rev_t_set
          \<lparr>Pol = I, Map = D, Dom = u, In = ipurge_tr I D (D x) xs, Out = ys\<rparr>"
      (is "_ \<Longrightarrow> ipurge_tr_rev_t_aux ?Z \<in> _")
  show
   "ipurge_tr_rev_t_aux
      \<lparr>Pol = I, Map = D, Dom = u, In = x # xs, Out = ys\<rparr>
    \<in> ipurge_tr_rev_t_set
      \<lparr>Pol = I, Map = D, Dom = u, In = x # xs, Out = ys\<rparr>"
    (is "ipurge_tr_rev_t_aux ?X \<in> _")
  proof (cases "D x \<in> sources I D u (x # xs)", simp_all del: sources.simps)
    case True
    have "?X \<in> ipurge_tr_rev_t_set ?X" by (rule R0)
    moreover have "?X \<in> ipurge_tr_rev_t_set ?X \<Longrightarrow> ?Y \<in> ipurge_tr_rev_t_set ?X"
     by (rule R1 [OF _ True])
    ultimately have "?Y \<in> ipurge_tr_rev_t_set ?X" by simp
    hence "ipurge_tr_rev_t_set ?Y \<subseteq> ipurge_tr_rev_t_set ?X"
     by (rule ipurge_tr_rev_t_subset)
    moreover have "ipurge_tr_rev_t_aux ?Y \<in> ipurge_tr_rev_t_set ?Y"
     using True by (rule A)
    ultimately show "ipurge_tr_rev_t_aux ?Y \<in> ipurge_tr_rev_t_set ?X" ..
  next
    case False
    have "?X \<in> ipurge_tr_rev_t_set ?X" by (rule R0)
    moreover have "?X \<in> ipurge_tr_rev_t_set ?X \<Longrightarrow> ?Z \<in> ipurge_tr_rev_t_set ?X"
     by (rule R2 [OF _ False])
    ultimately have "?Z \<in> ipurge_tr_rev_t_set ?X" by simp
    hence "ipurge_tr_rev_t_set ?Z \<subseteq> ipurge_tr_rev_t_set ?X"
     by (rule ipurge_tr_rev_t_subset)
    moreover have "ipurge_tr_rev_t_aux ?Z \<in> ipurge_tr_rev_t_set ?Z"
     using False by (rule B)
    ultimately show "ipurge_tr_rev_t_aux ?Z \<in> ipurge_tr_rev_t_set ?X" ..
  qed
qed

subsubsection "Step 5"

definition ipurge_tr_rev_t_inv_1 ::
  "('d \<times> 'd) set \<Rightarrow> ('a \<Rightarrow> 'd) \<Rightarrow> 'd \<Rightarrow> 'a list \<Rightarrow> ('a, 'd) ipurge_rec \<Rightarrow> bool"
where
"ipurge_tr_rev_t_inv_1 I D u xs X \<equiv>
  Out X @ ipurge_tr_rev I D u (In X) = ipurge_tr_rev I D u xs"

definition ipurge_tr_rev_t_inv_2 ::
  "'a process \<Rightarrow> ('d \<times> 'd) set \<Rightarrow> ('a \<Rightarrow> 'd) \<Rightarrow> 'a list \<Rightarrow> ('a, 'd) ipurge_rec \<Rightarrow> bool"
where
"ipurge_tr_rev_t_inv_2 P I D xs X \<equiv>
  secure P I D \<longrightarrow> xs \<in> traces P \<longrightarrow> Out X @ In X \<in> traces P"

text \<open>
\null

Two invariants have been defined, one for each of lemmas \<open>ipurge_tr_rev_t_equiv\<close>,
\<open>ipurge_tr_rev_t_trace\<close>.

More precisely, the invariants are @{term "ipurge_tr_rev_t_inv_1 I D u xs"} and
@{term "ipurge_tr_rev_t_inv_2 P I D xs"}, where the free variables are intended to match those
appearing in the aforesaid lemmas.
\<close>

subsubsection "Step 6"

lemma ipurge_tr_rev_t_input_1:
 "ipurge_tr_rev_t_inv_1 I D u xs \<lparr>Pol = I, Map = D, Dom = u, In = xs, Out = []\<rparr>"
by (simp add: ipurge_tr_rev_t_inv_1_def)

lemma ipurge_tr_rev_t_input_2:
 "ipurge_tr_rev_t_inv_2 P I D xs \<lparr>Pol = I, Map = D, Dom = u, In = xs, Out = []\<rparr>"
by (simp add: ipurge_tr_rev_t_inv_2_def)

subsubsection "Step 7"

definition ipurge_tr_rev_t_form :: "('a, 'd) ipurge_rec \<Rightarrow> bool" where
"ipurge_tr_rev_t_form X \<equiv> In X = []"

lemma ipurge_tr_rev_t_intro_1:
 "\<lbrakk>ipurge_tr_rev_t_inv_1 I D u xs X; ipurge_tr_rev_t_form X\<rbrakk> \<Longrightarrow>
  ipurge_tr_rev_t_out X = ipurge_tr_rev I D u xs"
by (simp add: ipurge_tr_rev_t_inv_1_def ipurge_tr_rev_t_form_def
 ipurge_tr_rev_t_out_def)

lemma ipurge_tr_rev_t_intro_2:
 "\<lbrakk>ipurge_tr_rev_t_inv_2 P I D xs X; ipurge_tr_rev_t_form X\<rbrakk> \<Longrightarrow>
  secure P I D \<longrightarrow> xs \<in> traces P \<longrightarrow> ipurge_tr_rev_t_out X \<in> traces P"
by (simp add: ipurge_tr_rev_t_inv_2_def ipurge_tr_rev_t_form_def
 ipurge_tr_rev_t_out_def)

subsubsection "Step 8"

lemma ipurge_tr_rev_t_form_aux:
 "ipurge_tr_rev_t_form (ipurge_tr_rev_t_aux X)"
by (induction X rule: ipurge_tr_rev_t_aux.induct,
 simp_all add: ipurge_tr_rev_t_form_def)

subsubsection "Step 9"

lemma ipurge_tr_rev_t_invariance_aux:
 "Y \<in> ipurge_tr_rev_t_set X \<Longrightarrow>
  Pol Y = Pol X \<and> Map Y = Map X \<and> Dom Y = Dom X"
by (erule ipurge_tr_rev_t_set.induct, simp_all)

text \<open>
\null

The lemma just proven, stating the invariance of the first three record fields over inductive set
@{term "ipurge_tr_rev_t_set X"}, is used in the following proofs of the invariance of predicates
@{term "ipurge_tr_rev_t_inv_1 I D u xs"} and @{term "ipurge_tr_rev_t_inv_2 P I D xs"}.

The equality between the free variables appearing in the predicates and the corresponding fields of
the record generating the set, which is required for such invariance properties to hold, is asserted
in the enunciation of the properties by means of record updates. In the subsequent proofs of lemmas
\<open>ipurge_tr_rev_t_equiv\<close>, \<open>ipurge_tr_rev_t_trace\<close>, the enforcement of this equality will
be ensured by the identification of both predicate variables and record fields with the related free
variables appearing in the lemmas.

\null
\<close>

lemma ipurge_tr_rev_t_invariance_1:
 "\<lbrakk>Y \<in> ipurge_tr_rev_t_set (X\<lparr>Pol := I, Map := D, Dom := u\<rparr>);
    ipurge_tr_rev_t_inv_1 I D u ws (X\<lparr>Pol := I, Map := D, Dom := u\<rparr>)\<rbrakk> \<Longrightarrow>
  ipurge_tr_rev_t_inv_1 I D u ws Y"
proof (erule ipurge_tr_rev_t_set.induct, assumption,
 drule_tac [!] ipurge_tr_rev_t_invariance_aux,
 simp_all add: ipurge_tr_rev_t_inv_1_def del: sources.simps)
  fix x xs ys
  assume A: "D x \<notin> sources I D u (x # xs)"
  hence "ipurge_tr_rev I D u xs = ipurge_tr_rev I D u ([] @ x # xs)" by simp
  also have "\<dots> = ipurge_tr_rev I D u ([] @ ipurge_tr I D (D x) xs)"
   using A by (rule ipurge_tr_rev_ipurge_tr_sources_1)
  finally have
   "ipurge_tr_rev I D u xs = ipurge_tr_rev I D u (ipurge_tr I D (D x) xs)"
   by simp
  moreover assume "ys @ ipurge_tr_rev I D u xs = ipurge_tr_rev I D u ws"
  ultimately show
   "ys @ ipurge_tr_rev I D u (ipurge_tr I D (D x) xs) = ipurge_tr_rev I D u ws"
   by simp
qed

lemma ipurge_tr_rev_t_invariance_2:
 "\<lbrakk>Y \<in> ipurge_tr_rev_t_set (X\<lparr>Pol := I, Map := D\<rparr>);
    ipurge_tr_rev_t_inv_2 P I D ws (X\<lparr>Pol := I, Map := D\<rparr>)\<rbrakk> \<Longrightarrow>
  ipurge_tr_rev_t_inv_2 P I D ws Y"
proof (erule ipurge_tr_rev_t_set.induct, assumption,
 drule_tac [!] ipurge_tr_rev_t_invariance_aux,
 simp_all add: ipurge_tr_rev_t_inv_2_def, (rule impI)+)
  fix x xs ys
  assume
    S: "secure P I D" and
    "ws \<in> traces P" and
    "secure P I D \<longrightarrow> ws \<in> traces P \<longrightarrow> ys @ x # xs \<in> traces P"
  hence "ys @ x # xs \<in> traces P" by simp
  hence "(ys @ x # xs, {}) \<in> failures P" by (rule traces_failures)
  hence "(x # xs, {}) \<in> futures P ys" by (simp add: futures_def)
  hence "(ipurge_tr I D (D x) xs, ipurge_ref I D (D x) xs {}) \<in> futures P ys"
   using S by (simp add: secure_def)
  hence "(ys @ ipurge_tr I D (D x) xs, ipurge_ref I D (D x) xs {}) \<in> failures P"
   by (simp add: futures_def)
  thus "ys @ ipurge_tr I D (D x) xs \<in> traces P" by (rule failures_traces)
qed

subsubsection "Step 10"

text \<open>
Here below are the proofs of lemmas \<open>ipurge_tr_rev_t_equiv\<close>, \<open>ipurge_tr_rev_t_trace\<close>,
which are then applied to demonstrate the target closure lemma.

\null
\<close>

lemma ipurge_tr_rev_t_equiv:
 "ipurge_tr_rev_t I D u xs = ipurge_tr_rev I D u xs"
proof -
  let ?X = "\<lparr>Pol = I, Map = D, Dom = u, In = xs, Out = []\<rparr>"
  have "ipurge_tr_rev_t_aux ?X
    \<in> ipurge_tr_rev_t_set (?X\<lparr>Pol := I, Map := D, Dom := u\<rparr>)"
   by (simp add: ipurge_tr_rev_t_aux_set)
  moreover have
   "ipurge_tr_rev_t_inv_1 I D u xs (?X\<lparr>Pol := I, Map := D, Dom := u\<rparr>)"
   by (simp add: ipurge_tr_rev_t_input_1)
  ultimately have "ipurge_tr_rev_t_inv_1 I D u xs (ipurge_tr_rev_t_aux ?X)"
   by (rule ipurge_tr_rev_t_invariance_1)
  moreover have "ipurge_tr_rev_t_form (ipurge_tr_rev_t_aux ?X)"
   by (rule ipurge_tr_rev_t_form_aux)
  ultimately have
   "ipurge_tr_rev_t_out (ipurge_tr_rev_t_aux ?X) = ipurge_tr_rev I D u xs"
   by (rule ipurge_tr_rev_t_intro_1)
  moreover have "?X = ipurge_tr_rev_t_in I D u xs"
   by (simp add: ipurge_tr_rev_t_in_def)
  ultimately show ?thesis by (simp add: ipurge_tr_rev_t_def)
qed

lemma ipurge_tr_rev_t_trace [rule_format]:
 "secure P I D \<longrightarrow> xs \<in> traces P \<longrightarrow> ipurge_tr_rev_t I D u xs \<in> traces P"
proof -
  let ?X = "\<lparr>Pol = I, Map = D, Dom = u, In = xs, Out = []\<rparr>"
  have "ipurge_tr_rev_t_aux ?X
    \<in> ipurge_tr_rev_t_set (?X\<lparr>Pol := I, Map := D\<rparr>)"
   by (simp add: ipurge_tr_rev_t_aux_set)
  moreover have "ipurge_tr_rev_t_inv_2 P I D xs (?X\<lparr>Pol := I, Map := D\<rparr>)"
   by (simp add: ipurge_tr_rev_t_input_2)
  ultimately have "ipurge_tr_rev_t_inv_2 P I D xs (ipurge_tr_rev_t_aux ?X)"
   by (rule ipurge_tr_rev_t_invariance_2)
  moreover have "ipurge_tr_rev_t_form (ipurge_tr_rev_t_aux ?X)"
   by (rule ipurge_tr_rev_t_form_aux)
  ultimately have "secure P I D \<longrightarrow> xs \<in> traces P \<longrightarrow>
    ipurge_tr_rev_t_out (ipurge_tr_rev_t_aux ?X) \<in> traces P"
   by (rule ipurge_tr_rev_t_intro_2)
  moreover have "?X = ipurge_tr_rev_t_in I D u xs"
   by (simp add: ipurge_tr_rev_t_in_def)
  ultimately show ?thesis by (simp add: ipurge_tr_rev_t_def)
qed

lemma ipurge_tr_rev_trace:
 "secure P I D \<Longrightarrow> xs \<in> traces P \<Longrightarrow> ipurge_tr_rev I D u xs \<in> traces P"
by (subst ipurge_tr_rev_t_equiv [symmetric], rule ipurge_tr_rev_t_trace)


subsection "The Inductive Unwinding Theorem in its general form"

text \<open>
In what follows, the Inductive Unwinding Theorem is proven, in the form applying to a generic
process. The equivalence of the condition expressed by the theorem to CSP noninterference security,
as defined in \cite{R2}, is demonstrated by showing that it is necessary and sufficient for the
verification of the condition expressed by the Ipurge Unwinding Theorem, under the same assumption
that the sets of refusals of the process be closed under union (cf. \cite{R3}).

Particularly, the closure of the traces of a secure process under function @{term ipurge_tr_rev} and
the idempotence of this function are used in the proof of condition necessity.

\null
\<close>

lemma inductive_unwinding_1:
  assumes
    R: "ref_union_closed P" and
    S: "secure P I D"
  shows "\<forall>xs \<in> traces P. \<forall>u \<in> range D \<inter> (-I) `` range D.
    next_dom_events P D u (ipurge_tr_rev I D u xs) = next_dom_events P D u xs \<and>
    ref_dom_events P D u (ipurge_tr_rev I D u xs) = ref_dom_events P D u xs"
proof (rule ballI)+
  fix xs u
  from R and S have "\<forall>u \<in> range D \<inter> (- I) `` range D. \<forall>xs ys.
    xs \<in> traces P \<and> ys \<in> traces P \<and>
      ipurge_tr_rev I D u xs = ipurge_tr_rev I D u ys \<longrightarrow>
    next_dom_events P D u xs = next_dom_events P D u ys \<and>
    ref_dom_events P D u xs = ref_dom_events P D u ys"
   by (simp add: ipurge_unwinding weakly_future_consistent_def rel_ipurge_def)
  moreover assume "u \<in> range D \<inter> (- I) `` range D"
  ultimately have "\<forall>xs ys.
    xs \<in> traces P \<and> ys \<in> traces P \<and>
      ipurge_tr_rev I D u xs = ipurge_tr_rev I D u ys \<longrightarrow>
    next_dom_events P D u xs = next_dom_events P D u ys \<and>
    ref_dom_events P D u xs = ref_dom_events P D u ys" ..
  hence
   "ipurge_tr_rev I D u xs \<in> traces P \<and> xs \<in> traces P \<and>
      ipurge_tr_rev I D u (ipurge_tr_rev I D u xs) = ipurge_tr_rev I D u xs \<longrightarrow>
    next_dom_events P D u (ipurge_tr_rev I D u xs) = next_dom_events P D u xs \<and>
    ref_dom_events P D u (ipurge_tr_rev I D u xs) = ref_dom_events P D u xs"
   by blast
  moreover assume xs: "xs \<in> traces P"
  moreover from S and xs have "ipurge_tr_rev I D u xs \<in> traces P"
   by (rule ipurge_tr_rev_trace)
  moreover have
   "ipurge_tr_rev I D u (ipurge_tr_rev I D u xs) = ipurge_tr_rev I D u xs"
   by (rule ipurge_tr_rev_idem)
  ultimately show
   "next_dom_events P D u (ipurge_tr_rev I D u xs) = next_dom_events P D u xs \<and>
    ref_dom_events P D u (ipurge_tr_rev I D u xs) = ref_dom_events P D u xs"
   by simp
qed

lemma inductive_unwinding_2:
  assumes
    R: "ref_union_closed P" and
    S: "\<forall>xs \<in> traces P. \<forall>u \<in> range D \<inter> (-I) `` range D.
      next_dom_events P D u (ipurge_tr_rev I D u xs) =
        next_dom_events P D u xs \<and>
      ref_dom_events P D u (ipurge_tr_rev I D u xs) =
        ref_dom_events P D u xs"
  shows "secure P I D"
proof (simp add: ipurge_unwinding [OF R] weakly_future_consistent_def rel_ipurge_def,
 rule ballI, (rule allI)+, rule impI, (erule conjE)+)
  fix u xs ys
  assume "xs \<in> traces P"
  with S have "\<forall>u \<in> range D \<inter> (-I) `` range D.
    next_dom_events P D u (ipurge_tr_rev I D u xs) = next_dom_events P D u xs \<and>
    ref_dom_events P D u (ipurge_tr_rev I D u xs) = ref_dom_events P D u xs" ..
  moreover assume A: "u \<in> range D \<inter> (- I) `` range D"
  ultimately have B:
   "next_dom_events P D u (ipurge_tr_rev I D u xs) = next_dom_events P D u xs \<and>
    ref_dom_events P D u (ipurge_tr_rev I D u xs) = ref_dom_events P D u xs" ..
  assume "ys \<in> traces P"
  with S have "\<forall>u \<in> range D \<inter> (-I) `` range D.
    next_dom_events P D u (ipurge_tr_rev I D u ys) = next_dom_events P D u ys \<and>
    ref_dom_events P D u (ipurge_tr_rev I D u ys) = ref_dom_events P D u ys" ..
  hence
   "next_dom_events P D u (ipurge_tr_rev I D u ys) = next_dom_events P D u ys \<and>
    ref_dom_events P D u (ipurge_tr_rev I D u ys) = ref_dom_events P D u ys"
   using A ..
  moreover assume "ipurge_tr_rev I D u xs = ipurge_tr_rev I D u ys"
  ultimately show
   "next_dom_events P D u xs = next_dom_events P D u ys \<and>
    ref_dom_events P D u xs = ref_dom_events P D u ys"
   using B by simp
qed

theorem inductive_unwinding:
 "ref_union_closed P \<Longrightarrow>
  secure P I D =
  (\<forall>xs \<in> traces P. \<forall>u \<in> range D \<inter> (-I) `` range D.
    next_dom_events P D u (ipurge_tr_rev I D u xs) = next_dom_events P D u xs \<and>
    ref_dom_events P D u (ipurge_tr_rev I D u xs) = ref_dom_events P D u xs)"
by (rule iffI, rule inductive_unwinding_1, assumption+, rule inductive_unwinding_2)

text \<open>
\null

Interestingly, this necessary and sufficient condition for the noninterference security of a process
resembles the classical definition of noninterference security for a deterministic state machine
with outputs formulated in \cite{R5}, which is formalized in \cite{R2} as predicate
\<open>c_secure\<close>.

Denoting with (1) the former and with (2) the latter, the differences between them can be summarized
as follows:

\begin{itemize}

\item
The event list appearing in (1) is constrained to vary over process traces, whereas the action list
appearing in (2) is unconstrained.
\\This comes as no surprise, since the state machines used as model of computation in \cite{R5}
accept any action list as a trace.

\item
The definition of function @{term ipurge_tr_rev}, used in (1), does not implicitly assume that the
noninterference policy be reflexive, even though any policy of practical significance will be such.
On the contrary, the definition of the intransitive purge function used in (2), which is formalized
in \cite{R2} as function \<open>c_ipurge\<close>, makes this implicit assumption, as shown by the
consideration that \<open>c_ipurge I D (D x) [x] = [x]\<close> regardless of whether
@{term "(D x, D x) \<in> I"} or not.
\\This is the mathematical reason why the equivalence between CSP noninterference security and
classical noninterference security for deterministic state machines with outputs, proven in
\cite{R2}, is subordinated to the assumption that the noninterference policy be reflexive.

\item
The equality of action outputs appearing in (2) is replaced in (1) by the equality of accepted and
refused events.

\end{itemize}

The binding of the universal quantification over domains contained in (1) does not constitute an
actual difference, since in (2) the purge function is only applied to domains in the range of the
event-domain map, and its output matches the entire input action list, thus rendering the equation
trivial, for domains allowed to be affected by any event domain.
\<close>


subsection "The Inductive Unwinding Theorem for deterministic and trace set processes"

text \<open>
Here below are the proofs of specific variants of the Inductive Unwinding Theorem applying to
deterministic processes and trace set processes \cite{R3}. The variant for deterministic processes
is derived, following the above proof of the general form of the theorem, from the Ipurge Unwinding
Theorem for deterministic processes \cite{R3}. Then, the variant for trace set processes is inferred
from the variant for deterministic processes.

Similarly to what happens for the Ipurge Unwinding Theorem, the refusals union closure assumption
that characterizes the general form of the Inductive Unwinding Theorem is replaced by the assumption
that the process actually be deterministic in the variant for deterministic processes, and by the
assumption that the set of traces actually be such in the variant for trace set processes. Moreover,
these variants involve accepted events only, in accordance with the fact that in deterministic
processes, refused events are completely specified by accepted events (cf. \cite{R4}, \cite{R2}).

\null
\<close>

lemma d_inductive_unwinding_1:
  assumes
    D: "deterministic P" and
    S: "secure P I D"
  shows "\<forall>xs \<in> traces P. \<forall>u \<in> range D \<inter> (-I) `` range D.
    next_dom_events P D u (ipurge_tr_rev I D u xs) = next_dom_events P D u xs"
proof (rule ballI)+
  fix xs u
  from D and S have "\<forall>u \<in> range D \<inter> (- I) `` range D. \<forall>xs ys.
    xs \<in> traces P \<and> ys \<in> traces P \<and>
      ipurge_tr_rev I D u xs = ipurge_tr_rev I D u ys \<longrightarrow>
    next_dom_events P D u xs = next_dom_events P D u ys"
   by (simp add: d_ipurge_unwinding d_weakly_future_consistent_def rel_ipurge_def)
  moreover assume "u \<in> range D \<inter> (- I) `` range D"
  ultimately have "\<forall>xs ys.
    xs \<in> traces P \<and> ys \<in> traces P \<and>
      ipurge_tr_rev I D u xs = ipurge_tr_rev I D u ys \<longrightarrow>
    next_dom_events P D u xs = next_dom_events P D u ys" ..
  hence
   "ipurge_tr_rev I D u xs \<in> traces P \<and> xs \<in> traces P \<and>
      ipurge_tr_rev I D u (ipurge_tr_rev I D u xs) = ipurge_tr_rev I D u xs \<longrightarrow>
    next_dom_events P D u (ipurge_tr_rev I D u xs) = next_dom_events P D u xs"
    by blast
  moreover assume xs: "xs \<in> traces P"
  moreover from S and xs have "ipurge_tr_rev I D u xs \<in> traces P"
    by (rule ipurge_tr_rev_trace)
  moreover have
   "ipurge_tr_rev I D u (ipurge_tr_rev I D u xs) = ipurge_tr_rev I D u xs"
    by (rule ipurge_tr_rev_idem)
  ultimately show
   "next_dom_events P D u (ipurge_tr_rev I D u xs) = next_dom_events P D u xs"
    by simp
qed

lemma d_inductive_unwinding_2:
  assumes
    D: "deterministic P" and
    S: "\<forall>xs \<in> traces P. \<forall>u \<in> range D \<inter> (-I) `` range D.
      next_dom_events P D u (ipurge_tr_rev I D u xs) = next_dom_events P D u xs"
  shows "secure P I D"
proof (simp add: d_ipurge_unwinding [OF D] d_weakly_future_consistent_def rel_ipurge_def,
 rule ballI, (rule allI)+, rule impI, (erule conjE)+)
  fix u xs ys
  assume "xs \<in> traces P"
  with S have "\<forall>u \<in> range D \<inter> (-I) `` range D.
    next_dom_events P D u (ipurge_tr_rev I D u xs) = next_dom_events P D u xs" ..
  moreover assume A: "u \<in> range D \<inter> (- I) `` range D"
  ultimately have B:
   "next_dom_events P D u (ipurge_tr_rev I D u xs) = next_dom_events P D u xs" ..
  assume "ys \<in> traces P"
  with S have "\<forall>u \<in> range D \<inter> (-I) `` range D.
    next_dom_events P D u (ipurge_tr_rev I D u ys) = next_dom_events P D u ys" ..
  hence
   "next_dom_events P D u (ipurge_tr_rev I D u ys) = next_dom_events P D u ys"
   using A ..
  moreover assume "ipurge_tr_rev I D u xs = ipurge_tr_rev I D u ys"
  ultimately show "next_dom_events P D u xs = next_dom_events P D u ys"
   using B by simp
qed

theorem d_inductive_unwinding:
 "deterministic P \<Longrightarrow>
  secure P I D =
  (\<forall>xs \<in> traces P. \<forall>u \<in> range D \<inter> (-I) `` range D.
    next_dom_events P D u (ipurge_tr_rev I D u xs) = next_dom_events P D u xs)"
by (rule iffI, rule d_inductive_unwinding_1, assumption+, rule d_inductive_unwinding_2)

theorem ts_inductive_unwinding:
  assumes T: "trace_set T"
  shows "secure (ts_process T) I D =
    (\<forall>xs \<in> T. \<forall>u \<in> range D \<inter> (-I) `` range D. \<forall>x \<in> D -` {u}.
      (ipurge_tr_rev I D u xs @ [x] \<in> T) = (xs @ [x] \<in> T))"
    (is "secure ?P I D = _")
proof (subst d_inductive_unwinding, rule ts_process_d [OF T],
 simp add: next_dom_events_def ts_process_next_events [OF T] set_eq_iff,
 rule iffI, (rule ballI)+, (rule_tac [2] ballI)+, rule_tac [2] allI)
  fix xs u x
  assume A: "\<forall>xs \<in> traces ?P. \<forall>u \<in> range D \<inter> (- I) `` range D.
    \<forall>x. (u = D x \<and> ipurge_tr_rev I D u xs @ [x] \<in> T) = (u = D x \<and> xs @ [x] \<in> T)"
  assume "xs \<in> T"
  moreover have "traces ?P = T" using T by (rule ts_process_traces)
  ultimately have "xs \<in> traces ?P" by simp
  with A have "\<forall>u \<in> range D \<inter> (- I) `` range D.
    \<forall>x. (u = D x \<and> ipurge_tr_rev I D u xs @ [x] \<in> T) =
      (u = D x \<and> xs @ [x] \<in> T)" ..
  moreover assume "u \<in> range D \<inter> (- I) `` range D"
  ultimately have
   "\<forall>x. (u = D x \<and> ipurge_tr_rev I D u xs @ [x] \<in> T) =
      (u = D x \<and> xs @ [x] \<in> T)" ..
  hence "(u = D x \<and> ipurge_tr_rev I D u xs @ [x] \<in> T) =
    (u = D x \<and> xs @ [x] \<in> T)" ..
  moreover assume "x \<in> D -` {u}"
  hence "u = D x" by simp
  ultimately show "(ipurge_tr_rev I D u xs @ [x] \<in> T) = (xs @ [x] \<in> T)" by simp
next
  fix xs u x
  assume A: "\<forall>xs \<in> T. \<forall>u \<in> range D \<inter> (- I) `` range D.
    \<forall>x \<in> D -` {u}. (ipurge_tr_rev I D u xs @ [x] \<in> T) = (xs @ [x] \<in> T)"
  assume "xs \<in> traces ?P"
  moreover have "traces ?P = T" using T by (rule ts_process_traces)
  ultimately have "xs \<in> T" by simp
  with A have "\<forall>u \<in> range D \<inter> (- I) `` range D.
    \<forall>x \<in> D -` {u}. (ipurge_tr_rev I D u xs @ [x] \<in> T) = (xs @ [x] \<in> T)" ..
  moreover assume "u \<in> range D \<inter> (- I) `` range D"
  ultimately have B:
   "\<forall>x \<in> D -` {u}. (ipurge_tr_rev I D u xs @ [x] \<in> T) = (xs @ [x] \<in> T)" ..
  show "(u = D x \<and> ipurge_tr_rev I D u xs @ [x] \<in> T) =
    (u = D x \<and> xs @ [x] \<in> T)"
  proof (cases "D x = u", simp_all)
    case True
    hence "x \<in> D -` {u}" by simp
    with B show "(ipurge_tr_rev I D u xs @ [x] \<in> T) = (xs @ [x] \<in> T)" ..
  qed
qed

end
