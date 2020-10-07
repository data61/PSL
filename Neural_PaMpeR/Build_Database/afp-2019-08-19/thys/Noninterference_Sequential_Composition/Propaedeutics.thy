(*  Title:       Conservation of CSP Noninterference Security under Sequential Composition
    Author:      Pasquale Noce
                 Security Certification Specialist at Arjo Systems, Italy
                 pasquale dot noce dot lavoro at gmail dot com
                 pasquale dot noce at arjosystems dot com
*)

section "Propaedeutic definitions and lemmas"

theory Propaedeutics
imports Noninterference_Ipurge_Unwinding.DeterministicProcesses
begin

text \<open>
\null

\emph{To our Lord Jesus Christ, my dear parents, and my "little" sister,}

\emph{for the immense love with which they surround me.}

\null

In his outstanding work on Communicating Sequential Processes \cite{R4}, Hoare has defined two
fundamental binary operations allowing to compose the input processes into another, typically more
complex, process: sequential composition and concurrent composition. Particularly, the output of the
former operation is a process that initially behaves like the first operand, and then like the
second operand once the execution of the first one has terminated successfully, as long as it does.
In order to distinguish it from deadlock, successful termination is regarded as a special event in
the process alphabet (required to be the same for both the input processes and the output one).

This paper formalizes Hoare's definition of sequential composition and proves, in the general case
of a possibly intransitive policy, that CSP noninterference security \cite{R2} is conserved under
this operation, viz. the security of both of the input processes implies that of the output process.

This property is conditional on two nontrivial assumptions. The first assumption is that the policy
do not allow successful termination to be affected by confidential events, viz. by other events not
allowed to affect some event in the process alphabet. The second assumption is that successful
termination do not occur as an alternative to other events in the traces of the first operand, viz.
that whenever the process can terminate successfully, it cannot engage in any other event. Both of
these assumptions are shown, by means of counterexamples, to be necessary for the theorem to hold.

From the above sketch of the sequential composition of two processes @{term P} and @{term Q},
notwithstanding its informal character, it clearly follows that any failure of the output process
is either a failure of @{term P} (case A), or a pair @{term "(xs @ ys, Y)"}, where @{term xs} is a
trace of @{term P} and @{term "(ys, Y)"} is a failure of @{term Q} (case B). On the other hand,
according to the definition of security given in \cite{R2}, the output process is secure just in
case, for each of its failures, any event @{term x} contained in the failure trace can be removed
from the trace, or inserted into the trace of another failure after the same previous events as in
the original trace, and the resulting pair is still a failure of the process, provided that the
future of @{term x} is deprived of the events that may be affected by @{term x}.

In case A, this transformation is performed on a failure of process @{term P}; being it secure, the
result is still a failure of @{term P}, and then of the output process. In case B, the
transformation may involve either @{term ys} alone, or both @{term xs} and @{term ys}, depending on
the position at which @{term x} is removed or inserted. In the former subcase, being @{term Q}
secure, the result has the form @{term "(xs @ ys', Y')"} where @{term "(ys', Y')"} is a failure of
@{term Q}, thus it is still a failure of the output process. In the latter subcase, @{term ys} has
to be deprived of the events that may be affected by @{term x}, as well as by any event affected by
@{term x} in the involved portion of @{term xs}, and a similar transformation applies to @{term Y}.
In order that the output process be secure, the resulting pair @{term "(ys'', Y'')"} must still be a
failure of @{term Q}, so that the pair @{term "(xs' @ ys'', Y'')"}, where @{term xs'} results from
the transformation of @{term xs}, be a failure of the output process.

The transformations bringing from @{term ys} and @{term Y} to @{term ys''} and @{term Y''} are
implemented by the functions @{term ipurge_tr_aux} and @{term ipurge_ref_aux} defined in \cite{R3}.
Therefore, the proof of the target security conservation theorem requires that of the following
lemma: given a process @{term P}, a noninterference policy @{term I}, and an event-domain map
@{term D}, if @{term P} is secure with respect to @{term I} and @{term D} and @{term "(xs, X)"} is a
failure of @{term P}, then @{term "(ipurge_tr_aux I D U xs, ipurge_ref_aux I D U xs X)"} is still a
failure of @{term P}. In other words, the lemma states that the failures of a secure process are
closed under intransitive purge. This section contains a proof of such closure lemma, as well as
further definitions and lemmas required for the proof of the target theorem.

Throughout this paper, the salient points of definitions and proofs are commented; for additional
information, cf. Isabelle documentation, particularly \cite{R6}, \cite{R7}, \cite{R8}, and
\cite{R9}.
\<close>


subsection "Preliminary propaedeutic lemmas"

text \<open>
In what follows, some lemmas required for the demonstration of the target closure lemma are proven.

Here below is the proof of some properties of functions @{term ipurge_tr} and @{term ipurge_ref}.

\null
\<close>

lemma ipurge_tr_length:
 "length (ipurge_tr I D u xs) \<le> length xs"
by (induction xs rule: rev_induct, simp_all)

lemma ipurge_ref_swap:
 "ipurge_ref I D u xs {x \<in> X. P x} =
  {x \<in> ipurge_ref I D u xs X. P x}"
proof (simp add: ipurge_ref_def)
qed blast

lemma ipurge_ref_last:
 "ipurge_ref I D u (xs @ [x]) X =
   (if (u, D x) \<in> I \<or> (\<exists>v \<in> sinks I D u xs. (v, D x) \<in> I)
    then ipurge_ref I D u xs {x' \<in> X. (D x, D x') \<notin> I}
    else ipurge_ref I D u xs X)"
proof (cases "(u, D x) \<in> I \<or> (\<exists>v \<in> sinks I D u xs. (v, D x) \<in> I)",
 simp_all add: ipurge_ref_def)
qed blast

text \<open>
\null

Here below is the proof of some properties of function @{term sinks_aux}.

\null
\<close>

lemma sinks_aux_append:
 "sinks_aux I D U (xs @ ys) = sinks_aux I D (sinks_aux I D U xs) ys"
proof (induction ys rule: rev_induct, simp, subst append_assoc [symmetric])
qed (simp del: append_assoc)

lemma sinks_aux_union:
 "sinks_aux I D (U \<union> V) xs =
  sinks_aux I D U xs \<union> sinks_aux I D V (ipurge_tr_aux I D U xs)"
proof (induction xs rule: rev_induct, simp)
  fix x xs
  assume A: "sinks_aux I D (U \<union> V) xs =
    sinks_aux I D U xs \<union> sinks_aux I D V (ipurge_tr_aux I D U xs)"
  show "sinks_aux I D (U \<union> V) (xs @ [x]) =
    sinks_aux I D U (xs @ [x]) \<union> sinks_aux I D V (ipurge_tr_aux I D U (xs @ [x]))"
  proof (cases "\<exists>w \<in> sinks_aux I D (U \<union> V) xs. (w, D x) \<in> I")
    case True
    hence "\<exists>w \<in> sinks_aux I D U xs \<union> sinks_aux I D V (ipurge_tr_aux I D U xs).
      (w, D x) \<in> I"
     using A by simp
    hence "(\<exists>w \<in> sinks_aux I D U xs. (w, D x) \<in> I) \<or>
      (\<exists>w \<in> sinks_aux I D V (ipurge_tr_aux I D U xs). (w, D x) \<in> I)"
     by blast
    thus ?thesis
     using A and True by (cases "\<exists>w \<in> sinks_aux I D U xs. (w, D x) \<in> I", simp_all)
  next
    case False
    hence "\<not> (\<exists>w \<in> sinks_aux I D U xs \<union>
      sinks_aux I D V (ipurge_tr_aux I D U xs). (w, D x) \<in> I)"
     using A by simp
    hence "\<not> (\<exists>w \<in> sinks_aux I D U xs. (w, D x) \<in> I) \<and>
      \<not> (\<exists>w \<in> sinks_aux I D V (ipurge_tr_aux I D U xs). (w, D x) \<in> I)"
     by blast
    thus ?thesis
     using A and False by simp
  qed
qed

lemma sinks_aux_subset_dom:
  assumes A: "U \<subseteq> V"
  shows "sinks_aux I D U xs \<subseteq> sinks_aux I D V xs"
proof (induction xs rule: rev_induct, simp add: A, rule subsetI)
  fix x xs w
  assume
    B: "sinks_aux I D U xs \<subseteq> sinks_aux I D V xs" and
    C: "w \<in> sinks_aux I D U (xs @ [x])"
  show "w \<in> sinks_aux I D V (xs @ [x])"
  proof (cases "\<exists>u \<in> sinks_aux I D U xs. (u, D x) \<in> I")
    case True
    hence "w = D x \<or> w \<in> sinks_aux I D U xs"
     using C by simp
    moreover {
      assume D: "w = D x"
      obtain u where E: "u \<in> sinks_aux I D U xs" and F: "(u, D x) \<in> I"
        using True ..
      have "u \<in> sinks_aux I D V xs" using B and E ..
      with F have "\<exists>u \<in> sinks_aux I D V xs. (u, D x) \<in> I" ..
      hence ?thesis using D by simp
    }
    moreover {
      assume "w \<in> sinks_aux I D U xs"
      with B have "w \<in> sinks_aux I D V xs" ..
      hence ?thesis by simp
    }
    ultimately show ?thesis ..
  next
    case False
    hence "w \<in> sinks_aux I D U xs"
     using C by simp
    with B have "w \<in> sinks_aux I D V xs" ..
    thus ?thesis by simp
  qed
qed

lemma sinks_aux_subset_ipurge_tr_aux:
 "sinks_aux I D U (ipurge_tr_aux I' D' U' xs) \<subseteq> sinks_aux I D U xs"
proof (induction xs rule: rev_induct, simp, rule subsetI)
  fix x xs w
  assume
    A: "sinks_aux I D U (ipurge_tr_aux I' D' U' xs) \<subseteq> sinks_aux I D U xs" and
    B: "w \<in> sinks_aux I D U (ipurge_tr_aux I' D' U' (xs @ [x]))"
  show "w \<in> sinks_aux I D U (xs @ [x])"
  proof (cases "\<exists>u \<in> sinks_aux I D U xs. (u, D x) \<in> I", simp_all (no_asm_simp))
    from B have "w = D x \<or> w \<in> sinks_aux I D U (ipurge_tr_aux I' D' U' xs)"
    proof (cases "\<exists>u' \<in> sinks_aux I' D' U' xs. (u', D' x) \<in> I'", simp_all)
    qed (cases "\<exists>u \<in> sinks_aux I D U (ipurge_tr_aux I' D' U' xs). (u, D x) \<in> I",
     simp_all)
    moreover {
      assume "w = D x"
      hence "w = D x \<or> w \<in> sinks_aux I D U xs" ..
    }
    moreover {
      assume "w \<in> sinks_aux I D U (ipurge_tr_aux I' D' U' xs)"
      with A have "w \<in> sinks_aux I D U xs" ..
      hence "w = D x \<or> w \<in> sinks_aux I D U xs" ..
    }
    ultimately show "w = D x \<or> w \<in> sinks_aux I D U xs" ..
  next
    assume C: "\<not> (\<exists>u \<in> sinks_aux I D U xs. (u, D x) \<in> I)"
    have "w \<in> sinks_aux I D U (ipurge_tr_aux I' D' U' xs)"
    proof (cases "\<exists>u' \<in> sinks_aux I' D' U' xs. (u', D' x) \<in> I'")
      case True
      thus "w \<in> sinks_aux I D U (ipurge_tr_aux I' D' U' xs)"
       using B by simp
    next
      case False
      hence "w \<in> sinks_aux I D U (ipurge_tr_aux I' D' U' xs @ [x])"
       using B by simp
      moreover have
       "\<not> (\<exists>u \<in> sinks_aux I D U (ipurge_tr_aux I' D' U' xs). (u, D x) \<in> I)"
       (is "\<not> ?P")
      proof
        assume ?P
        then obtain u where
          D: "u \<in> sinks_aux I D U (ipurge_tr_aux I' D' U' xs)" and
          E: "(u, D x) \<in> I" ..
        have "u \<in> sinks_aux I D U xs" using A and D ..
        with E have "\<exists>u \<in> sinks_aux I D U xs. (u, D x) \<in> I" ..
        thus False using C by contradiction
      qed
      ultimately show "w \<in> sinks_aux I D U (ipurge_tr_aux I' D' U' xs)"
       by simp
    qed
    with A show "w \<in> sinks_aux I D U xs" ..
  qed
qed

lemma sinks_aux_subset_ipurge_tr:
 "sinks_aux I D U (ipurge_tr I' D' u' xs) \<subseteq> sinks_aux I D U xs"
by (simp add: ipurge_tr_aux_single_dom [symmetric] sinks_aux_subset_ipurge_tr_aux)

lemma sinks_aux_member_ipurge_tr_aux [rule_format]:
 "u \<in> sinks_aux I D (U \<union> V) xs \<longrightarrow>
    (u, w) \<in> I \<longrightarrow>
    \<not> (\<exists>v \<in> sinks_aux I D V xs. (v, w) \<in> I) \<longrightarrow>
  u \<in> sinks_aux I D U (ipurge_tr_aux I D V xs)"
proof (induction xs arbitrary: u w rule: rev_induct, (rule_tac [!] impI)+, simp)
  fix u w
  assume
    A: "(u, w) \<in> I" and
    B: "\<forall>v \<in> V. (v, w) \<notin> I"
  assume "u \<in> U \<or> u \<in> V"
  moreover {
    assume "u \<in> U"
  }
  moreover {
    assume "u \<in> V"
    with B have "(u, w) \<notin> I" ..
    hence "u \<in> U" using A by contradiction
  }
  ultimately show "u \<in> U" ..
next
  fix x xs u w
  assume
    A: "\<And>u w. u \<in> sinks_aux I D (U \<union> V) xs \<longrightarrow>
      (u, w) \<in> I \<longrightarrow>
      \<not> (\<exists>v \<in> sinks_aux I D V xs. (v, w) \<in> I) \<longrightarrow>
      u \<in> sinks_aux I D U (ipurge_tr_aux I D V xs)" and
    B: "u \<in> sinks_aux I D (U \<union> V) (xs @ [x])" and
    C: "(u, w) \<in> I" and
    D: "\<not> (\<exists>v \<in> sinks_aux I D V (xs @ [x]). (v, w) \<in> I)"
  show "u \<in> sinks_aux I D U (ipurge_tr_aux I D V (xs @ [x]))"
  proof (cases "\<exists>u' \<in> sinks_aux I D (U \<union> V) xs. (u', D x) \<in> I")
    case True
    hence "u = D x \<or> u \<in> sinks_aux I D (U \<union> V) xs"
     using B by simp
    moreover {
      assume E: "u = D x"
      obtain u' where "u' \<in> sinks_aux I D (U \<union> V) xs" and F: "(u', D x) \<in> I"
       using True ..
      moreover have "u' \<in> sinks_aux I D (U \<union> V) xs \<longrightarrow>
        (u', D x) \<in> I \<longrightarrow>
        \<not> (\<exists>v \<in> sinks_aux I D V xs. (v, D x) \<in> I) \<longrightarrow>
        u' \<in> sinks_aux I D U (ipurge_tr_aux I D V xs)"
       (is "_ \<longrightarrow> _ \<longrightarrow> \<not> ?P \<longrightarrow> ?Q") using A .
      ultimately have "\<not> ?P \<longrightarrow> ?Q"
       by simp
      moreover have "\<not> ?P"
      proof
        have "(D x, w) \<in> I" using C and E by simp
        moreover assume ?P
        hence "D x \<in> sinks_aux I D V (xs @ [x])" by simp
        ultimately have "\<exists>v \<in> sinks_aux I D V (xs @ [x]). (v, w) \<in> I" ..
        moreover have "\<not> (\<exists>v \<in> sinks_aux I D V (xs @ [x]). (v, w) \<in> I)"
         using D by simp
        ultimately show False by contradiction
      qed
      ultimately have ?Q ..
      with F have "\<exists>u' \<in> sinks_aux I D U (ipurge_tr_aux I D V xs).
        (u', D x) \<in> I" ..
      hence "D x \<in> sinks_aux I D U (ipurge_tr_aux I D V xs @ [x])"
       by simp
      moreover have "ipurge_tr_aux I D V xs @ [x] =
        ipurge_tr_aux I D V (xs @ [x])"
       using \<open>\<not> ?P\<close> by simp
      ultimately have ?thesis using E by simp
    }
    moreover {
      assume "u \<in> sinks_aux I D (U \<union> V) xs"
      moreover have "u \<in> sinks_aux I D (U \<union> V) xs \<longrightarrow>
        (u, w) \<in> I \<longrightarrow>
        \<not> (\<exists>v \<in> sinks_aux I D V xs. (v, w) \<in> I) \<longrightarrow>
        u \<in> sinks_aux I D U (ipurge_tr_aux I D V xs)"
       (is "_ \<longrightarrow> _ \<longrightarrow> \<not> ?P \<longrightarrow> ?Q") using A .
      ultimately have "\<not> ?P \<longrightarrow> ?Q"
       using C by simp
      moreover have "\<not> ?P"
      proof
        assume ?P
        hence "\<exists>v \<in> sinks_aux I D V (xs @ [x]). (v, w) \<in> I"
         by simp
        thus False using D by contradiction
      qed
      ultimately have "u \<in> sinks_aux I D U (ipurge_tr_aux I D V xs)" ..
      hence ?thesis by simp
    }
    ultimately show ?thesis ..
  next
    case False
    hence "u \<in> sinks_aux I D (U \<union> V) xs"
     using B by simp
    moreover have "u \<in> sinks_aux I D (U \<union> V) xs \<longrightarrow>
      (u, w) \<in> I \<longrightarrow>
      \<not> (\<exists>v \<in> sinks_aux I D V xs. (v, w) \<in> I) \<longrightarrow>
      u \<in> sinks_aux I D U (ipurge_tr_aux I D V xs)"
     (is "_ \<longrightarrow> _ \<longrightarrow> \<not> ?P \<longrightarrow> ?Q") using A .
    ultimately have "\<not> ?P \<longrightarrow> ?Q"
     using C by simp
    moreover have "\<not> ?P"
    proof
      assume ?P
      hence "\<exists>v \<in> sinks_aux I D V (xs @ [x]). (v, w) \<in> I"
       by simp
      thus False using D by contradiction
    qed
    ultimately have "u \<in> sinks_aux I D U (ipurge_tr_aux I D V xs)" ..
    thus ?thesis by simp
  qed
qed

lemma sinks_aux_member_ipurge_tr:
  assumes
    A: "u \<in> sinks_aux I D (insert v U) xs" and
    B: "(u, w) \<in> I" and
    C: "\<not> ((v, w) \<in> I \<or> (\<exists>v' \<in> sinks I D v xs. (v', w) \<in> I))"
  shows "u \<in> sinks_aux I D U (ipurge_tr I D v xs)"
proof (subst ipurge_tr_aux_single_dom [symmetric],
 rule_tac w = w in sinks_aux_member_ipurge_tr_aux)
  show "u \<in> sinks_aux I D (U \<union> {v}) xs"
   using A by simp
next
  show "(u, w) \<in> I"
   using B .
next
  show "\<not> (\<exists>v' \<in> sinks_aux I D {v} xs. (v', w) \<in> I)"
   using C by (simp add: sinks_aux_single_dom)
qed

text \<open>
\null

Here below is the proof of some properties of functions @{term ipurge_tr_aux} and
@{term ipurge_ref_aux}.

\null
\<close>

lemma ipurge_tr_aux_append:
 "ipurge_tr_aux I D U (xs @ ys) =
  ipurge_tr_aux I D U xs @ ipurge_tr_aux I D (sinks_aux I D U xs) ys"
proof (induction ys rule: rev_induct, simp, subst append_assoc [symmetric])
qed (simp add: sinks_aux_append del: append_assoc)

lemma ipurge_tr_aux_single_event:
 "ipurge_tr_aux I D U [x] = (if \<exists>v \<in> U. (v, D x) \<in> I
    then []
    else [x])"
by (subst (2) append_Nil [symmetric], simp del: append_Nil)

lemma ipurge_tr_aux_cons:
 "ipurge_tr_aux I D U (x # xs) = (if \<exists>u \<in> U. (u, D x) \<in> I
    then ipurge_tr_aux I D (insert (D x) U) xs
    else x # ipurge_tr_aux I D U xs)"
proof -
  have "ipurge_tr_aux I D U (x # xs) = ipurge_tr_aux I D U ([x] @ xs)"
   by simp
  also have "\<dots> =
    ipurge_tr_aux I D U [x] @ ipurge_tr_aux I D (sinks_aux I D U [x]) xs"
   by (simp only: ipurge_tr_aux_append)
  finally show ?thesis
   by (simp add: sinks_aux_single_event ipurge_tr_aux_single_event)
qed

lemma ipurge_tr_aux_union:
 "ipurge_tr_aux I D (U \<union> V) xs =
  ipurge_tr_aux I D V (ipurge_tr_aux I D U xs)"
proof (induction xs rule: rev_induct, simp)
  fix x xs
  assume A: "ipurge_tr_aux I D (U \<union> V) xs =
    ipurge_tr_aux I D V (ipurge_tr_aux I D U xs)"
  show "ipurge_tr_aux I D (U \<union> V) (xs @ [x]) =
    ipurge_tr_aux I D V (ipurge_tr_aux I D U (xs @ [x]))"
  proof (cases "\<exists>v \<in> sinks_aux I D (U \<union> V) xs. (v, D x) \<in> I")
    case True
    hence "\<exists>w \<in> sinks_aux I D U xs \<union> sinks_aux I D V (ipurge_tr_aux I D U xs).
      (w, D x) \<in> I"
     by (simp add: sinks_aux_union)
    hence "(\<exists>w \<in> sinks_aux I D U xs. (w, D x) \<in> I) \<or>
      (\<exists>w \<in> sinks_aux I D V (ipurge_tr_aux I D U xs). (w, D x) \<in> I)"
     by blast
    thus ?thesis
     using A and True by (cases "\<exists>w \<in> sinks_aux I D U xs. (w, D x) \<in> I", simp_all)
  next
    case False
    hence "\<not> (\<exists>w \<in> sinks_aux I D U xs \<union>
      sinks_aux I D V (ipurge_tr_aux I D U xs). (w, D x) \<in> I)"
     by (simp add: sinks_aux_union)
    hence "\<not> (\<exists>w \<in> sinks_aux I D U xs. (w, D x) \<in> I) \<and>
      \<not> (\<exists>w \<in> sinks_aux I D V (ipurge_tr_aux I D U xs). (w, D x) \<in> I)"
     by blast
    thus ?thesis
     using A and False by simp
  qed
qed

lemma ipurge_tr_aux_insert:
 "ipurge_tr_aux I D (insert v U) xs =
  ipurge_tr_aux I D U (ipurge_tr I D v xs)"
by (subst insert_is_Un, simp only: ipurge_tr_aux_union ipurge_tr_aux_single_dom)

lemma ipurge_ref_aux_subset:
 "ipurge_ref_aux I D U xs X \<subseteq> X"
by (subst ipurge_ref_aux_def, rule subsetI, simp)


subsection "Intransitive purge of event sets with trivial base case"

text \<open>
Here below are the definitions of variants of functions @{term sinks_aux} and
@{term ipurge_ref_aux}, respectively named \<open>sinks_aux_less\<close> and \<open>ipurge_ref_aux_less\<close>,
such that their base cases in correspondence with an empty input list are trivial, viz. such that
@{term "sinks_aux_less I D U [] = {}"} and @{term "ipurge_ref_aux_less I D U [] X = X"}. These
functions will prove to be useful in what follows.

\null
\<close>

function sinks_aux_less ::
 "('d \<times> 'd) set \<Rightarrow> ('a \<Rightarrow> 'd) \<Rightarrow> 'd set \<Rightarrow> 'a list \<Rightarrow> 'd set" where
"sinks_aux_less _ _ _ [] = {}" |
"sinks_aux_less I D U (xs @ [x]) =
 (if \<exists>v \<in> U \<union> sinks_aux_less I D U xs. (v, D x) \<in> I
  then insert (D x) (sinks_aux_less I D U xs)
  else sinks_aux_less I D U xs)"
proof (atomize_elim, simp_all add: split_paired_all)
qed (rule rev_cases, rule disjI1, assumption, simp)
termination by lexicographic_order

definition ipurge_ref_aux_less ::
 "('d \<times> 'd) set \<Rightarrow> ('a \<Rightarrow> 'd) \<Rightarrow> 'd set \<Rightarrow> 'a list \<Rightarrow> 'a set \<Rightarrow> 'a set" where
"ipurge_ref_aux_less I D U xs X \<equiv>
  {x \<in> X. \<forall>v \<in> sinks_aux_less I D U xs. (v, D x) \<notin> I}"

text \<open>
\null

Here below is the proof of some properties of function @{term sinks_aux_less} used in what follows.

\null
\<close>

lemma sinks_aux_sinks_aux_less:
 "sinks_aux I D U xs = U \<union> sinks_aux_less I D U xs"
by (induction xs rule: rev_induct, simp_all)

lemma sinks_aux_less_single_dom:
 "sinks_aux_less I D {u} xs = sinks I D u xs"
by (induction xs rule: rev_induct, simp_all)

lemma sinks_aux_less_single_event:
 "sinks_aux_less I D U [x] = (if \<exists>u \<in> U. (u, D x) \<in> I then {D x} else {})"
by (subst append_Nil [symmetric], simp del: append_Nil)

lemma sinks_aux_less_append:
 "sinks_aux_less I D U (xs @ ys) =
  sinks_aux_less I D U xs \<union> sinks_aux_less I D (U \<union> sinks_aux_less I D U xs) ys"
proof (induction ys rule: rev_induct, simp, subst append_assoc [symmetric])
qed (simp del: append_assoc)

lemma sinks_aux_less_cons:
 "sinks_aux_less I D U (x # xs) = (if \<exists>u \<in> U. (u, D x) \<in> I
   then insert (D x) (sinks_aux_less I D (insert (D x) U) xs)
   else sinks_aux_less I D U xs)"
proof -
  have "sinks_aux_less I D U (x # xs) = sinks_aux_less I D U ([x] @ xs)"
   by simp
  also have "\<dots> =
    sinks_aux_less I D U [x] \<union> sinks_aux_less I D (U \<union> sinks_aux_less I D U [x]) xs"
   by (simp only: sinks_aux_less_append)
  finally show ?thesis
   by (cases "\<exists>u \<in> U. (u, D x) \<in> I", simp_all add: sinks_aux_less_single_event)
qed

text \<open>
\null

Here below is the proof of some properties of function @{term ipurge_ref_aux_less} used in what
follows.

\null
\<close>

lemma ipurge_ref_aux_less_last:
 "ipurge_ref_aux_less I D U (xs @ [x]) X =
   (if \<exists>v \<in> U \<union> sinks_aux_less I D U xs. (v, D x) \<in> I
    then ipurge_ref_aux_less I D U xs {x' \<in> X. (D x, D x') \<notin> I}
    else ipurge_ref_aux_less I D U xs X)"
by (cases "\<exists>v \<in> U \<union> sinks_aux_less I D U xs. (v, D x) \<in> I",
 simp_all add: ipurge_ref_aux_less_def)

lemma ipurge_ref_aux_less_nil:
 "ipurge_ref_aux_less I D U xs (ipurge_ref_aux I D U [] X) =
  ipurge_ref_aux I D U xs X"
proof (simp add: ipurge_ref_aux_def ipurge_ref_aux_less_def sinks_aux_sinks_aux_less)
qed blast

lemma ipurge_ref_aux_less_cons_1:
  assumes A: "\<exists>u \<in> U. (u, D x) \<in> I"
  shows "ipurge_ref_aux_less I D U (x # xs) X =
    ipurge_ref_aux_less I D U (ipurge_tr I D (D x) xs) (ipurge_ref I D (D x) xs X)"
proof (induction xs arbitrary: X rule: rev_induct,
 simp add: ipurge_ref_def ipurge_ref_aux_less_def sinks_aux_less_single_event A)
  fix x' xs X
  assume B: "\<And>X.
    ipurge_ref_aux_less I D U (x # xs) X =
    ipurge_ref_aux_less I D U (ipurge_tr I D (D x) xs)
      (ipurge_ref I D (D x) xs X)"
  show
   "ipurge_ref_aux_less I D U (x # xs @ [x']) X =
    ipurge_ref_aux_less I D U (ipurge_tr I D (D x) (xs @ [x']))
      (ipurge_ref I D (D x) (xs @ [x']) X)"
  proof (cases "\<exists>v \<in> U \<union> sinks_aux_less I D U (x # xs). (v, D x') \<in> I")
    assume C: "\<exists>v \<in> U \<union> sinks_aux_less I D U (x # xs). (v, D x') \<in> I"
    hence "ipurge_ref_aux_less I D U (x # xs @ [x']) X =
      ipurge_ref_aux_less I D U (x # xs) {y \<in> X. (D x', D y) \<notin> I}"
     by (subst append_Cons [symmetric],
      simp add: ipurge_ref_aux_less_last del: append_Cons)
    also have "\<dots> =
      ipurge_ref_aux_less I D U (ipurge_tr I D (D x) xs)
        (ipurge_ref I D (D x) xs {y \<in> X. (D x', D y) \<notin> I})"
     using B .
    finally have D: "ipurge_ref_aux_less I D U (x # xs @ [x']) X =
      ipurge_ref_aux_less I D U (ipurge_tr I D (D x) xs)
        (ipurge_ref I D (D x) xs {y \<in> X. (D x', D y) \<notin> I})" .
    show ?thesis
    proof (cases "(D x, D x') \<in> I \<or> (\<exists>v \<in> sinks I D (D x) xs. (v, D x') \<in> I)")
      case True
      hence "ipurge_ref I D (D x) xs {y \<in> X. (D x', D y) \<notin> I} =
        ipurge_ref I D (D x) (xs @ [x']) X"
       by (simp add: ipurge_ref_last)
      moreover have "D x' \<in> sinks I D (D x) (xs @ [x'])"
       using True by (simp only: sinks_interference_eq)
      hence "ipurge_tr I D (D x) xs = ipurge_tr I D (D x) (xs @ [x'])"
       by simp
      ultimately show ?thesis using D by simp
    next
      case False
      hence "ipurge_ref I D (D x) xs {y \<in> X. (D x', D y) \<notin> I} =
        ipurge_ref I D (D x) (xs @ [x']) {y \<in> X. (D x', D y) \<notin> I}"
       by (simp add: ipurge_ref_last)
      also have "\<dots> = {y \<in> ipurge_ref I D (D x) (xs @ [x']) X. (D x', D y) \<notin> I}"
       by (simp add: ipurge_ref_swap)
      finally have "ipurge_ref_aux_less I D U (x # xs @ [x']) X =
        ipurge_ref_aux_less I D U (ipurge_tr I D (D x) xs)
          {y \<in> ipurge_ref I D (D x) (xs @ [x']) X. (D x', D y) \<notin> I}"
       using D by simp
      also have "\<dots> = ipurge_ref_aux_less I D U (ipurge_tr I D (D x) xs @ [x'])
        (ipurge_ref I D (D x) (xs @ [x']) X)"
      proof -
        have "\<exists>v \<in> U \<union> sinks_aux_less I D U (ipurge_tr I D (D x) xs).
          (v, D x') \<in> I"
        proof -
          obtain v where
            E: "v \<in> U \<union> sinks_aux_less I D U (x # xs)" and
            F: "(v, D x') \<in> I"
           using C ..
          have "v \<in> sinks_aux I D U (x # xs)"
           using E by (simp add: sinks_aux_sinks_aux_less)
          hence "v \<in> sinks_aux I D (insert (D x) U) xs"
           using A by (simp add: sinks_aux_cons)
          hence "v \<in> sinks_aux I D U (ipurge_tr I D (D x) xs)"
           using F and False by (rule sinks_aux_member_ipurge_tr)
          hence "v \<in> U \<union> sinks_aux_less I D U (ipurge_tr I D (D x) xs)"
           by (simp add: sinks_aux_sinks_aux_less)
          with F show ?thesis ..
        qed
        thus ?thesis by (simp add: ipurge_ref_aux_less_last)
      qed
      finally have "ipurge_ref_aux_less I D U (x # xs @ [x']) X =
        ipurge_ref_aux_less I D U (ipurge_tr I D (D x) xs @ [x'])
          (ipurge_ref I D (D x) (xs @ [x']) X)" .
      moreover have "D x' \<notin> sinks I D (D x) (xs @ [x'])"
       using False by (simp only: sinks_interference_eq, simp)
      hence "ipurge_tr I D (D x) xs @ [x'] = ipurge_tr I D (D x) (xs @ [x'])"
       by simp
      ultimately show ?thesis by simp
    qed
  next
    assume C: "\<not> (\<exists>v \<in> U \<union> sinks_aux_less I D U (x # xs). (v, D x') \<in> I)"
    hence "ipurge_ref_aux_less I D U (x # xs @ [x']) X =
      ipurge_ref_aux_less I D U (x # xs) X"
     by (subst append_Cons [symmetric],
      simp add: ipurge_ref_aux_less_last del: append_Cons)
    also have "\<dots> =
      ipurge_ref_aux_less I D U (ipurge_tr I D (D x) xs)
        (ipurge_ref I D (D x) xs X)"
     using B .
    also have "\<dots> =
      ipurge_ref_aux_less I D U (ipurge_tr I D (D x) xs @ [x'])
        (ipurge_ref I D (D x) xs X)"
    proof -
      have "\<not> (\<exists>v \<in> U \<union> sinks_aux_less I D U (ipurge_tr I D (D x) xs).
        (v, D x') \<in> I)" (is "\<not> ?P")
      proof
        assume ?P
        then obtain v where
          D: "v \<in> U \<union> sinks_aux_less I D U (ipurge_tr I D (D x) xs)" and
          E: "(v, D x') \<in> I" ..
        have "sinks_aux I D U (ipurge_tr I D (D x) xs) \<subseteq> sinks_aux I D U xs"
         by (rule sinks_aux_subset_ipurge_tr)
        moreover have "v \<in> sinks_aux I D U (ipurge_tr I D (D x) xs)"
         using D by (simp add: sinks_aux_sinks_aux_less)
        ultimately have "v \<in> sinks_aux I D U xs" ..
        moreover have "U \<subseteq> insert (D x) U"
         by (rule subset_insertI)
        hence "sinks_aux I D U xs \<subseteq> sinks_aux I D (insert (D x) U) xs"
         by (rule sinks_aux_subset_dom)
        ultimately have "v \<in> sinks_aux I D (insert (D x) U) xs" ..
        hence "v \<in> sinks_aux I D U (x # xs)"
         using A by (simp add: sinks_aux_cons)
        hence "v \<in> U \<union> sinks_aux_less I D U (x # xs)"
         by (simp add: sinks_aux_sinks_aux_less)
        with E have "\<exists>v \<in> U \<union> sinks_aux_less I D U (x # xs). (v, D x') \<in> I" ..
        thus False using C by contradiction
      qed
      thus ?thesis by (simp add: ipurge_ref_aux_less_last)
    qed
    also have "\<dots> =
      ipurge_ref_aux_less I D U (ipurge_tr I D (D x) (xs @ [x']))
        (ipurge_ref I D (D x) (xs @ [x']) X)"
    proof -
      have "\<not> ((D x, D x') \<in> I \<or> (\<exists>v \<in> sinks I D (D x) xs. (v, D x') \<in> I))"
       (is "\<not> ?P")
      proof (rule notI, erule disjE)
        assume D: "(D x, D x') \<in> I"
        have "insert (D x) U \<subseteq> sinks_aux I D (insert (D x) U) xs"
         by (rule sinks_aux_subset)
        moreover have "D x \<in> insert (D x) U"
         by simp
        ultimately have "D x \<in> sinks_aux I D (insert (D x) U) xs" ..
        hence "D x \<in> sinks_aux I D U (x # xs)"
         using A by (simp add: sinks_aux_cons)
        hence "D x \<in> U \<union> sinks_aux_less I D U (x # xs)"
         by (simp add: sinks_aux_sinks_aux_less)
        with D have "\<exists>v \<in> U \<union> sinks_aux_less I D U (x # xs). (v, D x') \<in> I" ..
        thus False using C by contradiction
      next
        assume "\<exists>v \<in> sinks I D (D x) xs. (v, D x') \<in> I"
        then obtain v where
          D: "v \<in> sinks I D (D x) xs" and
          E: "(v, D x') \<in> I" ..
        have "{D x} \<subseteq> insert (D x) U"
         by simp
        hence "sinks_aux I D {D x} xs \<subseteq> sinks_aux I D (insert (D x) U) xs"
         by (rule sinks_aux_subset_dom)
        moreover have "v \<in> sinks_aux I D {D x} xs"
         using D by (simp add: sinks_aux_single_dom)
        ultimately have "v \<in> sinks_aux I D (insert (D x) U) xs" ..
        hence "v \<in> sinks_aux I D U (x # xs)"
         using A by (simp add: sinks_aux_cons)
        hence "v \<in> U \<union> sinks_aux_less I D U (x # xs)"
         by (simp add: sinks_aux_sinks_aux_less)
        with E have "\<exists>v \<in> U \<union> sinks_aux_less I D U (x # xs). (v, D x') \<in> I" ..
        thus False using C by contradiction
      qed
      hence "ipurge_tr I D (D x) xs @ [x'] = ipurge_tr I D (D x) (xs @ [x'])"
       by (simp only: sinks_interference_eq, simp)
      moreover have "ipurge_ref I D (D x) xs X =
        ipurge_ref I D (D x) (xs @ [x']) X"
       using \<open>\<not> ?P\<close> by (simp add: ipurge_ref_last)
      ultimately show ?thesis by simp
    qed
    finally show ?thesis .
  qed
qed

lemma ipurge_ref_aux_less_cons_2:
 "\<not> (\<exists>u \<in> U. (u, D x) \<in> I) \<Longrightarrow>
  ipurge_ref_aux_less I D U (x # xs) X =
    ipurge_ref_aux_less I D U xs X"
by (simp add: ipurge_ref_aux_less_def sinks_aux_less_cons)


subsection "Closure of the failures of a secure process under intransitive purge"

text \<open>
The intransitive purge of an event list @{term xs} with regard to a policy @{term I}, an
event-domain map @{term D}, and a set of domains @{term U} can equivalently be computed as follows:
for each item @{term x} of @{term xs}, if @{term x} may be affected by some domain in @{term U},
discard @{term x} and go on recursively using @{term "ipurge_tr I D (D x) xs'"} as input, where
@{term xs'} is the sublist of @{term xs} following @{term x}; otherwise, retain @{term x} and go on
recursively using @{term xs'} as input.

In fact, in each recursive step, any item allowed to be indirectly affected by @{term U} through the
effect of some item preceding @{term x} within @{term xs} has already been removed from the list.
Hence, it is sufficient to check whether @{term x} may be directly affected by @{term U}, and remove
@{term x}, as well as any residual item allowed to be affected by @{term x}, if this is the case.

Similarly, the intransitive purge of an event set @{term X} with regard to a policy @{term I}, an
event-domain map @{term D}, a set of domains @{term U}, and an event list @{term xs} can be computed
as follows. First of all, compute @{term "ipurge_ref_aux I D U [] X"} and use this set, along with
@{term xs}, as the input for the subsequent step. Then, for each item @{term x} of @{term xs}, if
@{term x} may be affected by some domain in @{term U}, go on recursively using
@{term "ipurge_tr I D (D x) xs'"} and @{term "ipurge_ref I D (D x) xs' X'"} as input, where
@{term X'} is the set input to the current recursive step; otherwise, go on recursively using
@{term xs'} and @{term X'} as input.

In fact, in each recursive step, any item allowed to be affected by @{term U} either directly, or
through the effect of some item preceding @{term x} within @{term xs}, has already been removed from
the set (in the initial step and in subsequent steps, respectively). Thus, it is sufficient to check
whether @{term x} may be directly affected by @{term U}, and remove any residual item allowed to be
affected by @{term x} if this is the case.

Assume that the two computations be performed simultaneously by a single function, which will then
take as input an event list-event set pair and return as output another such pair. Then, if the
input pair is a failure of a secure process, the output pair is still a failure. In fact, for each
item @{term x} of @{term xs} allowed to be affected by @{term U}, if @{term ys} is the partial
output list for the sublist of @{term xs} preceding @{term x}, then
@{term "(ys @ ipurge_tr I D (D x) xs', ipurge_ref I D (D x) xs' X')"} is a failure provided that
such is @{term "(ys @ x # xs', X')"}, by virtue of the definition of CSP noninterference security
\cite{R2}. Hence, the property of being a failure is conserved upon each recursive call by the event
list-event set pair such that the list matches the concatenation of the partial output list with the
residual input list, and the set matches the residual input set. This holds until the residual input
list is nil, which is the base case determining the end of the computation.

As shown by this argument, a proof by induction that the output event list-event set pair, under the
aforesaid assumptions, is still a failure, requires that the partial output list be passed to the
function as a further argument, in addition to the residual input list, in the recursive calls
contained within the definition of the function. Therefore, the output list has to be accumulated
into a parameter of the function, viz. the function needs to be tail-recursive. This suggests to
prove the properties of interest of the function by applying the ten-step proof method for theorems
on tail-recursive functions described in \cite{R1}.

The starting point is to formulate a naive definition of the function, which will then be refined as
specified by the proof method. A slight complication is due to the preliminary replacement of the
input event set @{term X} with @{term "ipurge_ref_aux I D U [] X"}, to be performed before the items
of the input event list start to be consumed recursively. A simple solution to this problem is to
nest the accumulator of the output list within data type \<open>option\<close>. In this way, the initial
state can be distinguished from the subsequent one, in which the input event list starts to be
consumed, by assigning the distinct values @{term None} and @{term "Some []"}, respectively, to the
accumulator.

Everything is now ready for giving a naive definition of the function under consideration:

\null
\<close>

function (sequential) ipurge_fail_aux_t_naive ::
 "('d \<times> 'd) set \<Rightarrow> ('a \<Rightarrow> 'd) \<Rightarrow> 'd set \<Rightarrow> 'a list \<Rightarrow> 'a list option \<Rightarrow> 'a set \<Rightarrow>
    'a failure"
where
"ipurge_fail_aux_t_naive I D U xs None X =
  ipurge_fail_aux_t_naive I D U xs (Some []) (ipurge_ref_aux I D U [] X)" |
"ipurge_fail_aux_t_naive I D U (x # xs) (Some ys) X =
 (if \<exists>u \<in> U. (u, D x) \<in> I
  then ipurge_fail_aux_t_naive I D U
    (ipurge_tr I D (D x) xs) (Some ys) (ipurge_ref I D (D x) xs X)
  else ipurge_fail_aux_t_naive I D U
    xs (Some (ys @ [x])) X)" |
"ipurge_fail_aux_t_naive _ _ _ _ (Some ys) X = (ys, X)"
oops

text \<open>
\null

The parameter into which the output list is accumulated is the last but one.

As shown by the above informal argument, function \<open>ipurge_fail_aux_t_naive\<close> enjoys the
following properties:

\null

@{term "fst (ipurge_fail_aux_t_naive I D U xs None X) = ipurge_tr_aux I D U xs"}

\null

@{term "snd (ipurge_fail_aux_t_naive I D U xs None X) = ipurge_ref_aux I D U xs X"}

\null

@{term "\<lbrakk>secure P I D; (xs, X) \<in> failures P\<rbrakk> \<Longrightarrow>
  ipurge_fail_aux_t_naive I D U xs None X \<in> failures P"}

\null

which altogether imply the target lemma, viz. the closure of the failures of a secure process under
intransitive purge.

In what follows, the steps provided for by the aforesaid proof method will be dealt with one after
the other, with the purpose of proving the target closure lemma in the final step. For more
information on this proof method, cf. \cite{R1}.
\<close>

subsubsection "Step 1"

text \<open>
In the definition of the auxiliary tail-recursive function \<open>ipurge_fail_aux_t_aux\<close>, the
Cartesian product of the input parameter types of function \<open>ipurge_fail_aux_t_naive\<close> will be
implemented as the following record type:

\null
\<close>

record ('a, 'd) ipurge_rec =
  Pol :: "('d \<times> 'd) set"
  Map :: "'a \<Rightarrow> 'd"
  Doms :: "'d set"
  List :: "'a list"
  ListOp :: "'a list option"
  Set :: "'a set"

text \<open>
\null

Here below is the resulting definition of function \<open>ipurge_fail_aux_t_aux\<close>:

\null
\<close>

function ipurge_fail_aux_t_aux :: "('a, 'd) ipurge_rec \<Rightarrow> ('a, 'd) ipurge_rec"
where

"ipurge_fail_aux_t_aux \<lparr>Pol = I, Map = D, Doms = U, List = xs,
  ListOp = None, Set = X\<rparr> =
 ipurge_fail_aux_t_aux \<lparr>Pol = I, Map = D, Doms = U, List = xs,
  ListOp = Some [], Set = ipurge_ref_aux I D U [] X\<rparr>" |

"ipurge_fail_aux_t_aux \<lparr>Pol = I, Map = D, Doms = U, List = x # xs,
  ListOp = Some ys, Set = X\<rparr> =
 (if \<exists>u \<in> U. (u, D x) \<in> I
  then ipurge_fail_aux_t_aux \<lparr>Pol = I, Map = D, Doms = U,
   List = ipurge_tr I D (D x) xs, ListOp = Some ys,
    Set = ipurge_ref I D (D x) xs X\<rparr>
  else ipurge_fail_aux_t_aux \<lparr>Pol = I, Map = D, Doms = U,
   List = xs, ListOp = Some (ys @ [x]), Set = X\<rparr>)" |

"ipurge_fail_aux_t_aux
  \<lparr>Pol = I, Map = D, Doms = U, List = [], ListOp = Some ys, Set = X\<rparr> =
 \<lparr>Pol = I, Map = D, Doms = U, List = [], ListOp = Some ys, Set = X\<rparr>"

proof (simp_all, atomize_elim)
  fix Y :: "('a, 'd) ipurge_rec"
  show
   "(\<exists>I D U xs X. Y = \<lparr>Pol = I, Map = D, Doms = U, List = xs,
      ListOp = None, Set = X\<rparr>) \<or>
    (\<exists>I D U x xs ys X. Y = \<lparr>Pol = I, Map = D, Doms = U, List = x # xs,
      ListOp = Some ys, Set = X\<rparr>) \<or>
    (\<exists>I D U ys X. Y = \<lparr>Pol = I, Map = D, Doms = U, List = [],
      ListOp = Some ys, Set = X\<rparr>)"
  proof (cases Y, simp)
    fix xs :: "'a list" and yso :: "'a list option"
    show
     "yso = None \<or>
      (\<exists>x' xs'. xs = x' # xs') \<and> (\<exists>ys. yso = Some ys) \<or>
      xs = [] \<and> (\<exists>ys. yso = Some ys)"
    proof (cases yso, simp_all)
    qed (subst disj_commute, rule spec [OF list.nchotomy])
  qed
qed

text \<open>
\null

The length of the input event list of function @{term ipurge_fail_aux_t_aux} decreases in every
recursive call except for the first one, where the input list is left unchanged while the nested
output list passes from @{term None} to @{term "Some []"}. A measure function decreasing in the
first recursive call as well can then be obtained by increasing the length of the input list by one
in case the nested output list matches @{term None}. Using such a measure function, the termination
of function @{term ipurge_fail_aux_t_aux} is guaranteed by the fact that the event lists output by
function @{term ipurge_tr} are not longer than the corresponding input ones.

\null
\<close>

termination ipurge_fail_aux_t_aux
proof (relation "measure (\<lambda>Y. (if ListOp Y = None then Suc else id)
 (length (List Y)))", simp_all)
  fix D :: "'a \<Rightarrow> 'd" and I x xs
  have "length (ipurge_tr I D (D x) xs) \<le> length xs" by (rule ipurge_tr_length)
  thus "length (ipurge_tr I D (D x) xs) < Suc (length xs)" by simp
qed

subsubsection "Step 2"

definition ipurge_fail_aux_t_in ::
 "('d \<times> 'd) set \<Rightarrow> ('a \<Rightarrow> 'd) \<Rightarrow> 'd set \<Rightarrow> 'a list \<Rightarrow> 'a set \<Rightarrow> ('a, 'd) ipurge_rec"
where
"ipurge_fail_aux_t_in I D U xs X \<equiv>
  \<lparr>Pol = I, Map = D, Doms = U, List = xs, ListOp = None, Set = X\<rparr>"

definition ipurge_fail_aux_t_out :: "('a, 'd) ipurge_rec \<Rightarrow> 'a failure" where
"ipurge_fail_aux_t_out Y \<equiv> (case ListOp Y of Some ys \<Rightarrow> ys, Set Y)"

definition ipurge_fail_aux_t ::
 "('d \<times> 'd) set \<Rightarrow> ('a \<Rightarrow> 'd) \<Rightarrow> 'd set \<Rightarrow> 'a list \<Rightarrow> 'a set \<Rightarrow> 'a failure"
where
"ipurge_fail_aux_t I D U xs X \<equiv>
  ipurge_fail_aux_t_out (ipurge_fail_aux_t_aux (ipurge_fail_aux_t_in I D U xs X))"

text \<open>
\null

Since the significant inputs of function \<open>ipurge_fail_aux_t_naive\<close> match pattern
\<open>_, _, _, _, None, _\<close>, those of function @{term ipurge_fail_aux_t_aux}, as returned by
function @{term ipurge_fail_aux_t_in}, match pattern
\<open>\<lparr>Pol = _, Map = _, Doms = _, List = _, ListOp = None, Set = _\<rparr>\<close>.

Likewise, since the nested output lists returned by function @{term ipurge_fail_aux_t_aux} match
pattern \<open>Some _\<close>, function @{term ipurge_fail_aux_t_out} does not need to worry about
dealing with nested output lists equal to @{term None}.

In terms of function @{term ipurge_fail_aux_t}, the statements to be proven in order to demonstrate
the target closure lemma, previously expressed using function \<open>ipurge_fail_aux_t_naive\<close> and
henceforth respectively named \<open>ipurge_fail_aux_t_eq_tr\<close>, \<open>ipurge_fail_aux_t_eq_ref\<close>, and
\<open>ipurge_fail_aux_t_failures\<close>, take the following form:

\null

@{term "fst (ipurge_fail_aux_t I D U xs X) = ipurge_tr_aux I D U xs"}

\null

@{term "snd (ipurge_fail_aux_t I D U xs X) = ipurge_ref_aux I D U xs X"}

\null

@{term "\<lbrakk>secure P I D; (xs, X) \<in> failures P\<rbrakk> \<Longrightarrow>
  ipurge_fail_aux_t I D U xs X \<in> failures P"}
\<close>

subsubsection "Step 3"

inductive_set ipurge_fail_aux_t_set ::
 "('a, 'd) ipurge_rec \<Rightarrow> ('a, 'd) ipurge_rec set"
for Y :: "('a, 'd) ipurge_rec" where

R0: "Y \<in> ipurge_fail_aux_t_set Y" |

R1: "\<lparr>Pol = I, Map = D, Doms = U, List = xs,
  ListOp = None, Set = X\<rparr> \<in> ipurge_fail_aux_t_set Y \<Longrightarrow>
 \<lparr>Pol = I, Map = D, Doms = U, List = xs,
  ListOp = Some [], Set = ipurge_ref_aux I D U [] X\<rparr> \<in> ipurge_fail_aux_t_set Y" |

R2: "\<lbrakk>\<lparr>Pol = I, Map = D, Doms = U, List = x # xs,
  ListOp = Some ys, Set = X\<rparr> \<in> ipurge_fail_aux_t_set Y;
 \<exists>u \<in> U. (u, D x) \<in> I\<rbrakk> \<Longrightarrow>
 \<lparr>Pol = I, Map = D, Doms = U, List = ipurge_tr I D (D x) xs,
  ListOp = Some ys, Set = ipurge_ref I D (D x) xs X\<rparr> \<in> ipurge_fail_aux_t_set Y" |

R3: "\<lbrakk>\<lparr>Pol = I, Map = D, Doms = U, List = x # xs,
  ListOp = Some ys, Set = X\<rparr> \<in> ipurge_fail_aux_t_set Y;
 \<not> (\<exists>u \<in> U. (u, D x) \<in> I)\<rbrakk> \<Longrightarrow>
 \<lparr>Pol = I, Map = D, Doms = U, List = xs,
  ListOp = Some (ys @ [x]), Set = X\<rparr> \<in> ipurge_fail_aux_t_set Y"

subsubsection "Step 4"

lemma ipurge_fail_aux_t_subset:
  assumes A: "Z \<in> ipurge_fail_aux_t_set Y"
  shows "ipurge_fail_aux_t_set Z \<subseteq> ipurge_fail_aux_t_set Y"
proof (rule subsetI, erule ipurge_fail_aux_t_set.induct)
  show "Z \<in> ipurge_fail_aux_t_set Y" using A .
next
  fix I D U xs X
  assume "\<lparr>Pol = I, Map = D, Doms = U, List = xs,
    ListOp = None, Set = X\<rparr> \<in> ipurge_fail_aux_t_set Y"
  thus "\<lparr>Pol = I, Map = D, Doms = U, List = xs,
    ListOp = Some [], Set = ipurge_ref_aux I D U [] X\<rparr> \<in> ipurge_fail_aux_t_set Y"
   by (rule R1)
next
  fix I D U x xs ys X
  assume
   "\<lparr>Pol = I, Map = D, Doms = U, List = x # xs,
      ListOp = Some ys, Set = X\<rparr> \<in> ipurge_fail_aux_t_set Y" and
   "\<exists>u \<in> U. (u, D x) \<in> I"
  thus "\<lparr>Pol = I, Map = D, Doms = U, List = ipurge_tr I D (D x) xs,
    ListOp = Some ys, Set = ipurge_ref I D (D x) xs X\<rparr> \<in> ipurge_fail_aux_t_set Y"
   by (rule R2)
next
  fix I D U x xs ys X
  assume
   "\<lparr>Pol = I, Map = D, Doms = U, List = x # xs,
      ListOp = Some ys, Set = X\<rparr> \<in> ipurge_fail_aux_t_set Y" and
   "\<not> (\<exists>u \<in> U. (u, D x) \<in> I)"
  thus "\<lparr>Pol = I, Map = D, Doms = U, List = xs,
    ListOp = Some (ys @ [x]), Set = X\<rparr> \<in> ipurge_fail_aux_t_set Y"
   by (rule R3)
qed

lemma ipurge_fail_aux_t_aux_set:
 "ipurge_fail_aux_t_aux Y \<in> ipurge_fail_aux_t_set Y"
proof (induction rule: ipurge_fail_aux_t_aux.induct,
 simp_all add: R0 del: ipurge_fail_aux_t_aux.simps(2))
  fix I U xs X and D :: "'a \<Rightarrow> 'd"
  let
    ?Y = "\<lparr>Pol = I, Map = D, Doms = U, List = xs,
      ListOp = None, Set = X\<rparr>" and
    ?Y' = "\<lparr>Pol = I, Map = D, Doms = U, List = xs,
      ListOp = Some [], Set = ipurge_ref_aux I D U [] X\<rparr>"
  have "?Y \<in> ipurge_fail_aux_t_set ?Y"
   by (rule R0)
  moreover have "?Y \<in> ipurge_fail_aux_t_set ?Y \<Longrightarrow>
    ?Y' \<in> ipurge_fail_aux_t_set ?Y"
   by (rule R1)
  ultimately have "?Y' \<in> ipurge_fail_aux_t_set ?Y"
   by simp
  hence "ipurge_fail_aux_t_set ?Y' \<subseteq> ipurge_fail_aux_t_set ?Y"
   by (rule ipurge_fail_aux_t_subset)
  moreover assume "ipurge_fail_aux_t_aux ?Y' \<in> ipurge_fail_aux_t_set ?Y'"
  ultimately show "ipurge_fail_aux_t_aux ?Y' \<in> ipurge_fail_aux_t_set ?Y" ..
next
  fix I U x xs ys X and D :: "'a \<Rightarrow> 'd"
  let
    ?Y = "\<lparr>Pol = I, Map = D, Doms = U, List = x # xs,
      ListOp = Some ys, Set = X\<rparr>" and
    ?Y' = "\<lparr>Pol = I, Map = D, Doms = U, List = ipurge_tr I D (D x) xs,
      ListOp = Some ys, Set = ipurge_ref I D (D x) xs X\<rparr>" and
    ?Y'' = "\<lparr>Pol = I, Map = D, Doms = U, List = xs,
      ListOp = Some (ys @ [x]), Set = X\<rparr>"
  assume
    A: "\<exists>u \<in> U. (u, D x) \<in> I \<Longrightarrow>
      ipurge_fail_aux_t_aux ?Y' \<in> ipurge_fail_aux_t_set ?Y'" and
    B: "\<forall>u \<in> U. (u, D x) \<notin> I \<Longrightarrow>
      ipurge_fail_aux_t_aux ?Y'' \<in> ipurge_fail_aux_t_set ?Y''"
  show "ipurge_fail_aux_t_aux ?Y \<in> ipurge_fail_aux_t_set ?Y"
  proof (cases "\<exists>u \<in> U. (u, D x) \<in> I", simp_all (no_asm_simp))
    case True
    have "?Y \<in> ipurge_fail_aux_t_set ?Y"
     by (rule R0)
    moreover have "?Y \<in> ipurge_fail_aux_t_set ?Y \<Longrightarrow> \<exists>u \<in> U. (u, D x) \<in> I \<Longrightarrow>
      ?Y' \<in> ipurge_fail_aux_t_set ?Y"
     by (rule R2)
    ultimately have "?Y' \<in> ipurge_fail_aux_t_set ?Y"
     using True by simp
    hence "ipurge_fail_aux_t_set ?Y' \<subseteq> ipurge_fail_aux_t_set ?Y"
     by (rule ipurge_fail_aux_t_subset)
    moreover have "ipurge_fail_aux_t_aux ?Y' \<in> ipurge_fail_aux_t_set ?Y'"
     using A and True by simp
    ultimately show "ipurge_fail_aux_t_aux ?Y' \<in> ipurge_fail_aux_t_set ?Y" ..
  next
    case False
    have "?Y \<in> ipurge_fail_aux_t_set ?Y"
     by (rule R0)
    moreover have "?Y \<in> ipurge_fail_aux_t_set ?Y \<Longrightarrow>
      \<not> (\<exists>u \<in> U. (u, D x) \<in> I) \<Longrightarrow> ?Y'' \<in> ipurge_fail_aux_t_set ?Y"
     by (rule R3)
    ultimately have "?Y'' \<in> ipurge_fail_aux_t_set ?Y"
     using False by simp
    hence "ipurge_fail_aux_t_set ?Y'' \<subseteq> ipurge_fail_aux_t_set ?Y"
     by (rule ipurge_fail_aux_t_subset)
    moreover have "ipurge_fail_aux_t_aux ?Y'' \<in> ipurge_fail_aux_t_set ?Y''"
     using B and False by simp
    ultimately show "ipurge_fail_aux_t_aux ?Y'' \<in> ipurge_fail_aux_t_set ?Y" ..
  qed
qed

subsubsection "Step 5"

definition ipurge_fail_aux_t_inv_1 ::
 "('d \<times> 'd) set \<Rightarrow> ('a \<Rightarrow> 'd) \<Rightarrow> 'd set \<Rightarrow> 'a list \<Rightarrow> ('a, 'd) ipurge_rec \<Rightarrow> bool"
where
"ipurge_fail_aux_t_inv_1 I D U xs Y \<equiv>
  (case ListOp Y of None \<Rightarrow> [] | Some ys \<Rightarrow> ys) @ ipurge_tr_aux I D U (List Y) =
  ipurge_tr_aux I D U xs"

definition ipurge_fail_aux_t_inv_2 ::
 "('d \<times> 'd) set \<Rightarrow> ('a \<Rightarrow> 'd) \<Rightarrow> 'd set \<Rightarrow> 'a list \<Rightarrow> 'a set \<Rightarrow>
    ('a, 'd) ipurge_rec \<Rightarrow> bool"
where
"ipurge_fail_aux_t_inv_2 I D U xs X Y \<equiv>
  if ListOp Y = None
  then List Y = xs \<and> Set Y = X
  else ipurge_ref_aux_less I D U (List Y) (Set Y) = ipurge_ref_aux I D U xs X"

definition ipurge_fail_aux_t_inv_3 ::
 "'a process \<Rightarrow> ('d \<times> 'd) set \<Rightarrow> ('a \<Rightarrow> 'd) \<Rightarrow> 'a list \<Rightarrow> 'a set \<Rightarrow>
    ('a, 'd) ipurge_rec \<Rightarrow> bool"
where
"ipurge_fail_aux_t_inv_3 P I D xs X Y \<equiv>
  secure P I D \<longrightarrow> (xs, X) \<in> failures P \<longrightarrow>
  ((case ListOp Y of None \<Rightarrow> [] | Some ys \<Rightarrow> ys) @ List Y, Set Y) \<in> failures P"

text \<open>
\null

Three invariants have been defined, one for each of lemmas \<open>ipurge_fail_aux_t_eq_tr\<close>,
\<open>ipurge_fail_aux_t_eq_ref\<close>, and \<open>ipurge_fail_aux_t_failures\<close>. More precisely, the
invariants are @{term "ipurge_fail_aux_t_inv_1 I D U xs"},
@{term "ipurge_fail_aux_t_inv_2 I D U xs X"}, and @{term "ipurge_fail_aux_t_inv_3 P I D xs X"},
where the free variables are intended to match those appearing in the aforesaid lemmas.

Particularly:

\begin{itemize}

\item
The first invariant expresses the fact that in each recursive step, any item of the residual input
list @{term "List Y"} indirectly affected by @{term U} through the effect of previous, already
consumed items has already been removed from the list, so that applying function
@{term "ipurge_tr_aux I D U"} to the list is sufficient to obtain the intransitive purge of the
whole original list.

\item
The second invariant expresses the fact that in each recursive step, any item of the residual input
set @{term "Set Y"} affected by @{term U} either directly, or through the effect of previous,
already consumed items, has already been removed from the set, so that applying function
@{term "ipurge_ref_aux_less I D U (List Y)"} to the set is sufficient to obtain the intransitive
purge of the whole original set.
\\The use of function @{term ipurge_ref_aux_less} ensures that the invariant implies the equality
@{term "Set Y = ipurge_ref_aux I D U xs X"} for @{term "List Y = []"}, viz. for the output values of
function @{term ipurge_fail_aux_t_aux}, which is the reason requiring the introduction of function
@{term ipurge_ref_aux_less}.

\item
The third invariant expresses the fact that in each recursive step, the event list-event set pair
such that the list matches the concatenation of the partial output list with @{term "List Y"}, and
the set matches @{term "Set Y"}, is a failure provided that the original input pair is such as well.

\end{itemize}
\<close>

subsubsection "Step 6"

lemma ipurge_fail_aux_t_input_1:
 "ipurge_fail_aux_t_inv_1 I D U xs
    \<lparr>Pol = I, Map = D, Doms = U, List = xs, ListOp = None, Set = X\<rparr>"
by (simp add: ipurge_fail_aux_t_inv_1_def)

lemma ipurge_fail_aux_t_input_2:
 "ipurge_fail_aux_t_inv_2 I D U xs X
    \<lparr>Pol = I, Map = D, Doms = U, List = xs, ListOp = None, Set = X\<rparr>"
by (simp add: ipurge_fail_aux_t_inv_2_def)

lemma ipurge_fail_aux_t_input_3:
 "ipurge_fail_aux_t_inv_3 P I D xs X
    \<lparr>Pol = I, Map = D, Doms = U, List = xs, ListOp = None, Set = X\<rparr>"
by (simp add: ipurge_fail_aux_t_inv_3_def)

subsubsection "Step 7"

definition ipurge_fail_aux_t_form :: "('a, 'd) ipurge_rec \<Rightarrow> bool" where
"ipurge_fail_aux_t_form Y \<equiv>
  case ListOp Y of None \<Rightarrow> False | Some ys \<Rightarrow> List Y = []"

lemma ipurge_fail_aux_t_intro_1:
 "\<lbrakk>ipurge_fail_aux_t_inv_1 I D U xs Y; ipurge_fail_aux_t_form Y\<rbrakk> \<Longrightarrow>
    fst (ipurge_fail_aux_t_out Y) = ipurge_tr_aux I D U xs"
proof (simp add: ipurge_fail_aux_t_inv_1_def ipurge_fail_aux_t_form_def
 ipurge_fail_aux_t_out_def)
qed (simp split: option.split_asm)

lemma ipurge_fail_aux_t_intro_2:
 "\<lbrakk>ipurge_fail_aux_t_inv_2 I D U xs X Y; ipurge_fail_aux_t_form Y\<rbrakk> \<Longrightarrow>
    snd (ipurge_fail_aux_t_out Y) = ipurge_ref_aux I D U xs X"
proof (simp add: ipurge_fail_aux_t_inv_2_def ipurge_fail_aux_t_form_def
 ipurge_fail_aux_t_out_def)
qed (simp add: ipurge_ref_aux_less_def split: option.split_asm)

lemma ipurge_fail_aux_t_intro_3:
 "\<lbrakk>ipurge_fail_aux_t_inv_3 P I D xs X Y; ipurge_fail_aux_t_form Y\<rbrakk> \<Longrightarrow>
    secure P I D \<longrightarrow> (xs, X) \<in> failures P \<longrightarrow>
      ipurge_fail_aux_t_out Y \<in> failures P"
proof (simp add: ipurge_fail_aux_t_inv_3_def ipurge_fail_aux_t_form_def
 ipurge_fail_aux_t_out_def)
qed (simp split: option.split_asm)

subsubsection "Step 8"

lemma ipurge_fail_aux_t_form_aux:
 "ipurge_fail_aux_t_form (ipurge_fail_aux_t_aux Y)"
by (induction Y rule: ipurge_fail_aux_t_aux.induct,
 simp_all add: ipurge_fail_aux_t_form_def)

subsubsection "Step 9"

lemma ipurge_fail_aux_t_invariance_aux:
 "Z \<in> ipurge_fail_aux_t_set Y \<Longrightarrow>
  Pol Z = Pol Y \<and> Map Z = Map Y \<and> Doms Z = Doms Y"
by (erule ipurge_fail_aux_t_set.induct, simp_all)

text \<open>
\null

The lemma just proven, stating the invariance of the first three record fields over inductive set
@{term "ipurge_fail_aux_t_set Y"}, is used in the following proofs of the invariance of predicates
@{term "ipurge_fail_aux_t_inv_1 I D U xs"}, @{term "ipurge_fail_aux_t_inv_2 I D U xs X"}, and
@{term "ipurge_fail_aux_t_inv_3 P I D xs X"}.

The equality between the free variables appearing in the predicates and the corresponding fields of
the record generating the set, which is required for such invariance properties to hold, is asserted
in the enunciation of the properties by means of record updates. In the subsequent proofs of lemmas
\<open>ipurge_fail_aux_t_eq_tr\<close>, \<open>ipurge_fail_aux_t_eq_ref\<close>, and
\<open>ipurge_fail_aux_t_failures\<close>, the enforcement of this equality will be ensured by the
identification of both predicate variables and record fields with the related free variables
appearing in the lemmas.

\null
\<close>

lemma ipurge_fail_aux_t_invariance_1:
 "\<lbrakk>Z \<in> ipurge_fail_aux_t_set (Y\<lparr>Pol := I, Map := D, Doms := U\<rparr>);
    ipurge_fail_aux_t_inv_1 I D U xs (Y\<lparr>Pol := I, Map := D, Doms := U\<rparr>)\<rbrakk> \<Longrightarrow>
  ipurge_fail_aux_t_inv_1 I D U xs Z"
proof (erule ipurge_fail_aux_t_set.induct, assumption,
 drule_tac [!] ipurge_fail_aux_t_invariance_aux,
 simp_all add: ipurge_fail_aux_t_inv_1_def)
  fix x xs' ys
  assume "ys @ ipurge_tr_aux I D U (x # xs') = ipurge_tr_aux I D U xs"
   (is "?A = ?C")
  moreover assume "\<exists>u \<in> U. (u, D x) \<in> I"
  hence "?A = ys @ ipurge_tr_aux I D (insert (D x) U) xs'"
   by (simp add: ipurge_tr_aux_cons)
  hence "?A = ys @ ipurge_tr_aux I D U (ipurge_tr I D (D x) xs')"
   (is "_ = ?B") by (simp add: ipurge_tr_aux_insert)
  ultimately show "?B = ?C" by simp
next
  fix x xs' ys
  assume "ys @ ipurge_tr_aux I D U (x # xs') = ipurge_tr_aux I D U xs"
   (is "?A = ?C")
  moreover assume "\<forall>u \<in> U. (u, D x) \<notin> I"
  hence "?A = ys @ x # ipurge_tr_aux I D U xs'"
   (is "_ = ?B") by (simp add: ipurge_tr_aux_cons)
  ultimately show "?B = ?C" by simp
qed

lemma ipurge_fail_aux_t_invariance_2:
 "\<lbrakk>Z \<in> ipurge_fail_aux_t_set (Y\<lparr>Pol := I, Map := D, Doms := U\<rparr>);
    ipurge_fail_aux_t_inv_2 I D U xs X (Y\<lparr>Pol := I, Map := D, Doms := U\<rparr>)\<rbrakk> \<Longrightarrow>
  ipurge_fail_aux_t_inv_2 I D U xs X Z"
proof (erule ipurge_fail_aux_t_set.induct, assumption,
 drule_tac [!] ipurge_fail_aux_t_invariance_aux,
 simp_all add: ipurge_fail_aux_t_inv_2_def)
  show "ipurge_ref_aux_less I D U xs (ipurge_ref_aux I D U [] X) =
    ipurge_ref_aux I D U xs X"
   by (rule ipurge_ref_aux_less_nil)
next
  fix x xs' X'
  assume "ipurge_ref_aux_less I D U (x # xs') X' = ipurge_ref_aux I D U xs X"
   (is "?A = ?C")
  moreover assume "\<exists>u \<in> U. (u, D x) \<in> I"
  hence "?A = ipurge_ref_aux_less I D U (ipurge_tr I D (D x) xs')
    (ipurge_ref I D (D x) xs' X')"
   (is "_ = ?B") by (rule ipurge_ref_aux_less_cons_1)
  ultimately show "?B = ?C" by simp
next
  fix x xs' X'
  assume "ipurge_ref_aux_less I D U (x # xs') X' = ipurge_ref_aux I D U xs X"
   (is "?A = ?C")
  moreover assume "\<forall>u \<in> U. (u, D x) \<notin> I"
  hence "\<not> (\<exists>u \<in> U. (u, D x) \<in> I)" by simp
  hence "?A = ipurge_ref_aux_less I D U xs' X'"
   (is "_ = ?B") by (rule ipurge_ref_aux_less_cons_2)
  ultimately show "?B = ?C" by simp
qed

lemma ipurge_fail_aux_t_invariance_3:
 "\<lbrakk>Z \<in> ipurge_fail_aux_t_set (Y\<lparr>Pol := I, Map := D\<rparr>);
    ipurge_fail_aux_t_inv_3 P I D xs X (Y\<lparr>Pol := I, Map := D\<rparr>)\<rbrakk> \<Longrightarrow>
  ipurge_fail_aux_t_inv_3 P I D xs X Z"
proof (erule ipurge_fail_aux_t_set.induct, assumption,
 drule_tac [!] ipurge_fail_aux_t_invariance_aux,
 simp_all add: ipurge_fail_aux_t_inv_3_def, (rule_tac [!] impI)+)
  fix xs' X'
  assume
   "secure P I D" and
   "(xs, X) \<in> failures P" and
   "secure P I D \<longrightarrow> (xs, X) \<in> failures P \<longrightarrow> (xs', X') \<in> failures P"
  hence "(xs', X') \<in> failures P"
   by simp
  moreover have "ipurge_ref_aux I D (Doms Y) [] X' \<subseteq> X'"
   by (rule ipurge_ref_aux_subset)
  ultimately show "(xs', ipurge_ref_aux I D (Doms Y) [] X') \<in> failures P"
   by (rule process_rule_3)
next
  fix x xs' ys X'
  assume S: "secure P I D" and
   "(xs, X) \<in> failures P" and
   "secure P I D \<longrightarrow> (xs, X) \<in> failures P \<longrightarrow> (ys @ x # xs', X') \<in> failures P"
  hence "(ys @ x # xs', X') \<in> failures P"
   by simp
  hence "(x # xs', X') \<in> futures P ys"
   by (simp add: futures_def)
  hence "(ipurge_tr I D (D x) xs', ipurge_ref I D (D x) xs' X') \<in> futures P ys"
   using S by (simp add: secure_def)
  thus "(ys @ ipurge_tr I D (D x) xs', ipurge_ref I D (D x) xs' X') \<in> failures P"
   by (simp add: futures_def)
qed

subsubsection "Step 10"

text \<open>
Here below are the proofs of lemmas \<open>ipurge_fail_aux_t_eq_tr\<close>,
\<open>ipurge_fail_aux_t_eq_ref\<close>, and \<open>ipurge_fail_aux_t_failures\<close>, which are then applied to
demonstrate the target closure lemma.

\null
\<close>

lemma ipurge_fail_aux_t_eq_tr:
 "fst (ipurge_fail_aux_t I D U xs X) = ipurge_tr_aux I D U xs"
proof -
  let ?Y = "\<lparr>Pol = I, Map = D, Doms = U, List = xs, ListOp = None,
    Set = X\<rparr>"
  have "ipurge_fail_aux_t_aux ?Y
    \<in> ipurge_fail_aux_t_set (?Y\<lparr>Pol := I, Map := D, Doms := U\<rparr>)"
   by (simp add: ipurge_fail_aux_t_aux_set del: ipurge_fail_aux_t_aux.simps)
  moreover have
   "ipurge_fail_aux_t_inv_1 I D U xs (?Y\<lparr>Pol := I, Map := D, Doms := U\<rparr>)"
   by (simp add: ipurge_fail_aux_t_input_1)
  ultimately have "ipurge_fail_aux_t_inv_1 I D U xs (ipurge_fail_aux_t_aux ?Y)"
   by (rule ipurge_fail_aux_t_invariance_1)
  moreover have "ipurge_fail_aux_t_form (ipurge_fail_aux_t_aux ?Y)"
   by (rule ipurge_fail_aux_t_form_aux)
  ultimately have "fst (ipurge_fail_aux_t_out (ipurge_fail_aux_t_aux ?Y)) =
    ipurge_tr_aux I D U xs"
   by (rule ipurge_fail_aux_t_intro_1)
  moreover have "?Y = ipurge_fail_aux_t_in I D U xs X"
   by (simp add: ipurge_fail_aux_t_in_def)
  ultimately show ?thesis
   by (simp add: ipurge_fail_aux_t_def)
qed

lemma ipurge_fail_aux_t_eq_ref:
 "snd (ipurge_fail_aux_t I D U xs X) = ipurge_ref_aux I D U xs X"
proof -
  let ?Y = "\<lparr>Pol = I, Map = D, Doms = U, List = xs, ListOp = None,
    Set = X\<rparr>"
  have "ipurge_fail_aux_t_aux ?Y
    \<in> ipurge_fail_aux_t_set (?Y\<lparr>Pol := I, Map := D, Doms := U\<rparr>)"
   by (simp add: ipurge_fail_aux_t_aux_set del: ipurge_fail_aux_t_aux.simps)
  moreover have
   "ipurge_fail_aux_t_inv_2 I D U xs X (?Y\<lparr>Pol := I, Map := D, Doms := U\<rparr>)"
   by (simp add: ipurge_fail_aux_t_input_2)
  ultimately have "ipurge_fail_aux_t_inv_2 I D U xs X (ipurge_fail_aux_t_aux ?Y)"
   by (rule ipurge_fail_aux_t_invariance_2)
  moreover have "ipurge_fail_aux_t_form (ipurge_fail_aux_t_aux ?Y)"
   by (rule ipurge_fail_aux_t_form_aux)
  ultimately have "snd (ipurge_fail_aux_t_out (ipurge_fail_aux_t_aux ?Y)) =
    ipurge_ref_aux I D U xs X"
   by (rule ipurge_fail_aux_t_intro_2)
  moreover have "?Y = ipurge_fail_aux_t_in I D U xs X"
   by (simp add: ipurge_fail_aux_t_in_def)
  ultimately show ?thesis
   by (simp add: ipurge_fail_aux_t_def)
qed

lemma ipurge_fail_aux_t_failures [rule_format]:
 "secure P I D \<longrightarrow> (xs, X) \<in> failures P \<longrightarrow>
    ipurge_fail_aux_t I D U xs X \<in> failures P"
proof -
  let ?Y = "\<lparr>Pol = I, Map = D, Doms = U, List = xs, ListOp = None,
    Set = X\<rparr>"
  have "ipurge_fail_aux_t_aux ?Y
    \<in> ipurge_fail_aux_t_set (?Y\<lparr>Pol := I, Map := D\<rparr>)"
   by (simp add: ipurge_fail_aux_t_aux_set del: ipurge_fail_aux_t_aux.simps)
  moreover have
   "ipurge_fail_aux_t_inv_3 P I D xs X (?Y\<lparr>Pol := I, Map := D\<rparr>)"
   by (simp add: ipurge_fail_aux_t_input_3)
  ultimately have "ipurge_fail_aux_t_inv_3 P I D xs X (ipurge_fail_aux_t_aux ?Y)"
   by (rule ipurge_fail_aux_t_invariance_3)
  moreover have "ipurge_fail_aux_t_form (ipurge_fail_aux_t_aux ?Y)"
   by (rule ipurge_fail_aux_t_form_aux)
  ultimately have "secure P I D \<longrightarrow> (xs, X) \<in> failures P \<longrightarrow>
    ipurge_fail_aux_t_out (ipurge_fail_aux_t_aux ?Y) \<in> failures P"
   by (rule ipurge_fail_aux_t_intro_3)
  moreover have "?Y = ipurge_fail_aux_t_in I D U xs X"
   by (simp add: ipurge_fail_aux_t_in_def)
  ultimately show ?thesis
   by (simp add: ipurge_fail_aux_t_def)
qed

lemma ipurge_tr_ref_aux_failures:
 "\<lbrakk>secure P I D; (xs, X) \<in> failures P\<rbrakk> \<Longrightarrow>
    (ipurge_tr_aux I D U xs, ipurge_ref_aux I D U xs X) \<in> failures P"
proof (drule ipurge_fail_aux_t_failures [where U = U], assumption,
 cases "ipurge_fail_aux_t I D U xs X")
qed (simp add: ipurge_fail_aux_t_eq_tr [where X = X, symmetric]
 ipurge_fail_aux_t_eq_ref [symmetric])


subsection "Additional propaedeutic lemmas"

text \<open>
In what follows, additional lemmas required for the demonstration of the target security
conservation theorem are proven.

Here below is the proof of some properties of functions @{term ipurge_tr_aux} and
@{term ipurge_ref_aux}. Particularly, it is shown that in case an event list and its intransitive
purge for some set of domains are both traces of a secure process, and the purged list has a future
not affected by any purged event, then that future is also a future for the full event list.

\null
\<close>

lemma ipurge_tr_aux_idem:
 "ipurge_tr_aux I D U (ipurge_tr_aux I D U xs) = ipurge_tr_aux I D U xs"
by (simp add: ipurge_tr_aux_union [symmetric])

lemma ipurge_tr_aux_set:
 "set (ipurge_tr_aux I D U xs) \<subseteq> set xs"
proof (induction xs rule: rev_induct, simp_all)
qed blast

lemma ipurge_tr_aux_nil [rule_format]:
  assumes A: "u \<in> U"
  shows "(\<forall>x \<in> set xs. (u, D x) \<in> I) \<longrightarrow> ipurge_tr_aux I D U xs = []"
proof (induction xs rule: rev_induct, simp, rule impI)
  fix x xs
  assume "(\<forall>x' \<in> set xs. (u, D x') \<in> I) \<longrightarrow> ipurge_tr_aux I D U xs = []"
  moreover assume B: "\<forall>x' \<in> set (xs @ [x]). (u, D x') \<in> I"
  ultimately have C: "ipurge_tr_aux I D U xs = []"
   by simp
  have "(u, D x) \<in> I"
   using B by simp
  moreover have "U \<subseteq> sinks_aux I D U xs"
   by (rule sinks_aux_subset)
  hence "u \<in> sinks_aux I D U xs"
   using A ..
  ultimately have "\<exists>u \<in> sinks_aux I D U xs. (u, D x) \<in> I" ..
  hence "ipurge_tr_aux I D U (xs @ [x]) = ipurge_tr_aux I D U xs"
   by simp
  thus "ipurge_tr_aux I D U (xs @ [x]) = []"
   using C by simp
qed

lemma ipurge_tr_aux_del_failures [rule_format]:
  assumes S: "secure P I D"
  shows "(\<forall>u \<in> sinks_aux_less I D U ys. \<forall>z \<in> Z \<union> set zs. (u, D z) \<notin> I) \<longrightarrow>
    (xs @ ipurge_tr_aux I D U ys @ zs, Z) \<in> failures P \<longrightarrow>
    xs @ ys \<in> traces P \<longrightarrow>
    (xs @ ys @ zs, Z) \<in> failures P"
proof (induction ys arbitrary: zs rule: rev_induct, simp, (rule impI)+)
  fix y ys zs
  assume
    A: "\<And>zs. (\<forall>u \<in> sinks_aux_less I D U ys. \<forall>z \<in> Z \<union> set zs. (u, D z) \<notin> I) \<longrightarrow>
      (xs @ ipurge_tr_aux I D U ys @ zs, Z) \<in> failures P \<longrightarrow>
      xs @ ys \<in> traces P \<longrightarrow>
        (xs @ ys @ zs, Z) \<in> failures P" and
    B: "\<forall>u \<in> sinks_aux_less I D U (ys @ [y]). \<forall>z \<in> Z \<union> set zs. (u, D z) \<notin> I" and
    C: "(xs @ ipurge_tr_aux I D U (ys @ [y]) @ zs, Z) \<in> failures P" and
    D: "xs @ (ys @ [y]) \<in> traces P"
  show "(xs @ (ys @ [y]) @ zs, Z) \<in> failures P"
  proof (cases "\<exists>u \<in> sinks_aux I D U ys. (u, D y) \<in> I", simp_all (no_asm))
    case True
    have
     "(\<forall>u \<in> sinks_aux_less I D U ys. \<forall>z \<in> Z \<union> set zs. (u, D z) \<notin> I) \<longrightarrow>
      (xs @ ipurge_tr_aux I D U ys @ zs, Z) \<in> failures P \<longrightarrow>
      xs @ ys \<in> traces P \<longrightarrow>
        (xs @ ys @ zs, Z) \<in> failures P"
     using A .
    moreover have "\<exists>u \<in> U \<union> sinks_aux_less I D U ys. (u, D y) \<in> I"
     using True by (simp add: sinks_aux_sinks_aux_less)
    hence E: "\<forall>u \<in> insert (D y) (sinks_aux_less I D U ys). \<forall>z \<in> Z \<union> set zs.
      (u, D z) \<notin> I"
     using B by (simp only: sinks_aux_less.simps if_True)
    hence "\<forall>u \<in> sinks_aux_less I D U ys. \<forall>z \<in> Z \<union> set zs. (u, D z) \<notin> I"
     by simp
    moreover have "(xs @ ipurge_tr_aux I D U ys @ zs, Z) \<in> failures P"
     using C and True by simp
    moreover have "(xs @ ys) @ [y] \<in> traces P"
     using D by simp
    hence "xs @ ys \<in> traces P"
     by (rule process_rule_2_traces)
    ultimately have "(xs @ ys @ zs, Z) \<in> failures P"
     by simp
    hence "(zs, Z) \<in> futures P (xs @ ys)"
     by (simp add: futures_def)
    moreover have "(xs @ ys @ [y], {}) \<in> failures P"
     using D by (rule traces_failures)
    hence "([y], {}) \<in> futures P (xs @ ys)"
     by (simp add: futures_def)
    ultimately have "(y # ipurge_tr I D (D y) zs, ipurge_ref I D (D y) zs Z)
      \<in> futures P (xs @ ys)"
     using S by (simp add: secure_def)
    moreover have "ipurge_tr I D (D y) zs = zs"
     by (subst ipurge_tr_all, simp add: E)
    moreover have "ipurge_ref I D (D y) zs Z = Z"
     by (rule ipurge_ref_all, simp add: E)
    ultimately have "(y # zs, Z) \<in> futures P (xs @ ys)"
     by simp
    thus "(xs @ ys @ y # zs, Z) \<in> failures P"
     by (simp add: futures_def)
  next
    case False
    have E:
     "(\<forall>u \<in> sinks_aux_less I D U ys. \<forall>z \<in> Z \<union> set (y # zs). (u, D z) \<notin> I) \<longrightarrow>
      (xs @ ipurge_tr_aux I D U ys @ (y # zs), Z) \<in> failures P \<longrightarrow>
      xs @ ys \<in> traces P \<longrightarrow>
        (xs @ ys @ (y # zs), Z) \<in> failures P"
     using A .
    have F: "\<not> (\<exists>u \<in> U \<union> sinks_aux_less I D U ys. (u, D y) \<in> I)"
     using False by (simp add: sinks_aux_sinks_aux_less)
    hence "\<forall>u \<in> sinks_aux_less I D U ys. \<forall>z \<in> Z \<union> set zs. (u, D z) \<notin> I"
     using B by (simp only: sinks_aux_less.simps if_False)
    moreover have "\<forall>u \<in> sinks_aux_less I D U ys. (u, D y) \<notin> I"
     using F by simp
    ultimately have
     "\<forall>u \<in> sinks_aux_less I D U ys. \<forall>z \<in> Z \<union> set (y # zs). (u, D z) \<notin> I"
     by simp
    with E have
     "(xs @ ipurge_tr_aux I D U ys @ (y # zs), Z) \<in> failures P \<longrightarrow>
      xs @ ys \<in> traces P \<longrightarrow>
        (xs @ ys @ (y # zs), Z) \<in> failures P" ..
    moreover have "(xs @ ipurge_tr_aux I D U ys @ (y # zs), Z) \<in> failures P"
     using C and False by simp
    moreover have "(xs @ ys) @ [y] \<in> traces P"
     using D by simp
    hence "xs @ ys \<in> traces P"
     by (rule process_rule_2_traces)
    ultimately show "(xs @ ys @ (y # zs), Z) \<in> failures P"
     by simp
  qed
qed

lemma ipurge_ref_aux_append:
 "ipurge_ref_aux I D U (xs @ ys) X = ipurge_ref_aux I D (sinks_aux I D U xs) ys X"
by (simp add: ipurge_ref_aux_def sinks_aux_append)

lemma ipurge_ref_aux_empty [rule_format]:
  assumes
    A: "u \<in> sinks_aux I D U xs" and
    B: "\<forall>x \<in> X. (u, D x) \<in> I"
  shows "ipurge_ref_aux I D U xs X = {}"
proof (rule equals0I, simp add: ipurge_ref_aux_def, erule conjE)
  fix x
  assume "x \<in> X"
  with B have "(u, D x) \<in> I" ..
  moreover assume "\<forall>u \<in> sinks_aux I D U xs. (u, D x) \<notin> I"
  hence "(u, D x) \<notin> I"
   using A ..
  ultimately show False
   by contradiction
qed

text \<open>
\null

Here below is the proof of some properties of functions @{term sinks}, @{term ipurge_tr}, and
@{term ipurge_ref}. Particularly, using the previous analogous result on function
@{term ipurge_tr_aux}, it is shown that in case an event list and its intransitive purge for some
domain are both traces of a secure process, and the purged list has a future not affected by any
purged event, then that future is also a future for the full event list.

\null
\<close>

lemma sinks_idem:
 "sinks I D u (ipurge_tr I D u xs) = {}"
by (induction xs rule: rev_induct, simp_all)

lemma sinks_elem [rule_format]:
 "v \<in> sinks I D u xs \<longrightarrow> (\<exists>x \<in> set xs. v = D x)"
by (induction xs rule: rev_induct, simp_all)

lemma ipurge_tr_append:
 "ipurge_tr I D u (xs @ ys) =
  ipurge_tr I D u xs @ ipurge_tr_aux I D (insert u (sinks I D u xs)) ys"
proof (simp add: sinks_aux_single_dom [symmetric]
 ipurge_tr_aux_single_dom [symmetric])
qed (simp add: ipurge_tr_aux_append)

lemma ipurge_tr_idem:
 "ipurge_tr I D u (ipurge_tr I D u xs) = ipurge_tr I D u xs"
by (simp add: ipurge_tr_aux_single_dom [symmetric] ipurge_tr_aux_idem)

lemma ipurge_tr_set:
 "set (ipurge_tr I D u xs) \<subseteq> set xs"
by (simp add: ipurge_tr_aux_single_dom [symmetric] ipurge_tr_aux_set)

lemma ipurge_tr_del_failures [rule_format]:
  assumes
    S: "secure P I D" and
    A: "\<forall>v \<in> sinks I D u ys. \<forall>z \<in> Z \<union> set zs. (v, D z) \<notin> I" and
    B: "(xs @ ipurge_tr I D u ys @ zs, Z) \<in> failures P" and
    C: "xs @ ys \<in> traces P"
  shows "(xs @ ys @ zs, Z) \<in> failures P"
proof (rule ipurge_tr_aux_del_failures [OF S _ _ C, where U = "{u}"])
qed (simp add: A sinks_aux_less_single_dom, simp add: B ipurge_tr_aux_single_dom)

lemma ipurge_tr_del_traces [rule_format]:
  assumes
    S: "secure P I D" and
    A: "\<forall>v \<in> sinks I D u ys. \<forall>z \<in> set zs. (v, D z) \<notin> I" and
    B: "xs @ ipurge_tr I D u ys @ zs \<in> traces P" and
    C: "xs @ ys \<in> traces P"
  shows "xs @ ys @ zs \<in> traces P"
proof (rule failures_traces [where X = "{}"],
 rule ipurge_tr_del_failures [OF S _ _ C, where u = u])
qed (simp add: A, rule traces_failures [OF B])

lemma ipurge_ref_append:
 "ipurge_ref I D u (xs @ ys) X =
  ipurge_ref_aux I D (insert u (sinks I D u xs)) ys X"
proof (simp add: sinks_aux_single_dom [symmetric]
 ipurge_ref_aux_single_dom [symmetric])
qed (simp add: ipurge_ref_aux_append)

lemma ipurge_ref_distrib_inter:
 "ipurge_ref I D u xs (X \<inter> Y) = ipurge_ref I D u xs X \<inter> ipurge_ref I D u xs Y"
proof (simp add: ipurge_ref_def)
qed blast

lemma ipurge_ref_distrib_union:
 "ipurge_ref I D u xs (X \<union> Y) = ipurge_ref I D u xs X \<union> ipurge_ref I D u xs Y"
proof (simp add: ipurge_ref_def)
qed blast

lemma ipurge_ref_subset:
 "ipurge_ref I D u xs X \<subseteq> X"
by (subst ipurge_ref_def, rule subsetI, simp)

lemma ipurge_ref_subset_union:
 "ipurge_ref I D u xs (X \<union> Y) \<subseteq> X \<union> ipurge_ref I D u xs Y"
proof (simp add: ipurge_ref_def)
qed blast

lemma ipurge_ref_subset_insert:
 "ipurge_ref I D u xs (insert x X) \<subseteq> insert x (ipurge_ref I D u xs X)"
by (simp only: insert_def ipurge_ref_subset_union)

lemma ipurge_ref_empty [rule_format]:
  assumes
    A: "v = u \<or> v \<in> sinks I D u xs" and
    B: "\<forall>x \<in> X. (v, D x) \<in> I"
  shows "ipurge_ref I D u xs X = {}"
proof (subst ipurge_ref_aux_single_dom [symmetric],
 rule ipurge_ref_aux_empty [of v])
  show "v \<in> sinks_aux I D {u} xs"
   using A by (simp add: sinks_aux_single_dom)
next
  fix x
  assume "x \<in> X"
  with B show "(v, D x) \<in> I" ..
qed

text \<open>
\null

Finally, in what follows, properties @{term process_prop_1}, @{term process_prop_5}, and
@{term process_prop_6} of processes (cf. \cite{R2}) are put into the form of introduction rules.

\null
\<close>

lemma process_rule_1:
 "([], {}) \<in> failures P"
proof (simp add: failures_def)
  have "Rep_process P \<in> process_set" (is "?P' \<in> _")
   by (rule Rep_process)
  thus "([], {}) \<in> fst ?P'"
   by (simp add: process_set_def process_prop_1_def)
qed

lemma process_rule_5 [rule_format]:
 "xs \<in> divergences P \<longrightarrow> xs @ [x] \<in> divergences P"
proof (simp add: divergences_def)
  have "Rep_process P \<in> process_set" (is "?P' \<in> _")
   by (rule Rep_process)
  hence "\<forall>xs x. xs \<in> snd ?P' \<longrightarrow> xs @ [x] \<in> snd ?P'"
   by (simp add: process_set_def process_prop_5_def)
  thus "xs \<in> snd ?P' \<longrightarrow> xs @ [x] \<in> snd ?P'"
   by blast
qed

lemma process_rule_6 [rule_format]:
 "xs \<in> divergences P \<longrightarrow> (xs, X) \<in> failures P"
proof (simp add: failures_def divergences_def)
  have "Rep_process P \<in> process_set" (is "?P' \<in> _")
   by (rule Rep_process)
  hence "\<forall>xs X. xs \<in> snd ?P' \<longrightarrow> (xs, X) \<in> fst ?P'"
   by (simp add: process_set_def process_prop_6_def)
  thus "xs \<in> snd ?P' \<longrightarrow> (xs, X) \<in> fst ?P'"
   by blast
qed

end
