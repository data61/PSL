(*  Title:       A Definitional Encoding of TLA in Isabelle/HOL
    Authors:     Gudmund Grov <ggrov at inf.ed.ac.uk>
                 Stephan Merz <Stephan.Merz at loria.fr>
    Year:        2011
    Maintainer:  Gudmund Grov <ggrov at inf.ed.ac.uk>
*)

section \<open>(Infinite) Sequences\<close> 

theory Sequence
imports Main
begin

text \<open>
  Lamport's Temporal Logic of Actions (TLA) is a linear-time temporal logic,
  and its semantics is defined over infinite sequence of states, which we
  simply represent by the type \<open>'a seq\<close>, defined as an abbreviation
  for the type \<open>nat \<Rightarrow> 'a\<close>, where \<open>'a\<close> is the type of sequence 
  elements.

  This theory defines some useful notions about such sequences, and in particular
  concepts related to stuttering (finite repetitions of states), which are
  important for the semantics of TLA. We identify a finite sequence with an
  infinite sequence that ends in infinite stuttering. In this way, we avoid the
  complications of having to handle both finite and infinite sequences of states:
  see e.g. Devillers et al \cite{Devillers97} who discuss several variants of
  representing possibly infinite sequences in HOL, Isabelle and PVS.
\<close>

type_synonym 'a seq = "nat \<Rightarrow> 'a"

subsection "Some operators on sequences"

text \<open>Some general functions on sequences are provided\<close>

definition first :: "'a seq \<Rightarrow> 'a" 
where "first s \<equiv> s 0"

definition second :: "('a seq) \<Rightarrow> 'a"
where "second s \<equiv> s 1"

definition suffix :: "'a seq \<Rightarrow> nat \<Rightarrow> 'a seq" (infixl "|\<^sub>s" 60)
where "s |\<^sub>s i \<equiv> \<lambda> n. s (n+i)"

definition tail :: "'a seq \<Rightarrow> 'a seq"
where "tail s \<equiv> s |\<^sub>s 1"

definition
 app :: "'a \<Rightarrow> ('a seq) \<Rightarrow> ('a seq)" (infixl "##" 60)
where
 "s ## \<sigma>  \<equiv> \<lambda> n. if n=0 then s else \<sigma> (n - 1)"

text \<open>
  \<open>s |\<^sub>s i\<close> returns the suffix of sequence @{term s} from
  index @{term i}.  @{term first} returns the first element of a sequence
  while  @{term second} returns the second element. @{term tail} returns the
  sequence starting at the second element. @{term "s ## \<sigma>"} prefixes the
  sequence @{term \<sigma>} by element @{term s}.
\<close>

subsubsection "Properties of @{term first} and @{term second}"

lemma first_tail_second: "first(tail s) = second s"
  by (simp add: first_def second_def tail_def suffix_def)


subsubsection "Properties of @{term suffix}"

lemma suffix_first: "first (s |\<^sub>s n) = s n"
  by (auto simp add: suffix_def first_def)

lemma suffix_second: "second (s |\<^sub>s n) = s (Suc n)"
  by (auto simp add: suffix_def second_def)

lemma suffix_plus: "s |\<^sub>s n |\<^sub>s m = s |\<^sub>s (m + n)"
  by (simp add: suffix_def add.assoc)

lemma suffix_commute: "((s |\<^sub>s n) |\<^sub>s m) = ((s |\<^sub>s m) |\<^sub>s n)"
  by (simp add: suffix_plus add.commute)

lemma suffix_plus_com: "s |\<^sub>s m |\<^sub>s n = s |\<^sub>s (m + n)"
proof -
  have "s |\<^sub>s n |\<^sub>s m = s |\<^sub>s (m + n)" by (rule suffix_plus)
  thus "s |\<^sub>s m |\<^sub>s n = s |\<^sub>s (m + n)" by (simp add: suffix_commute)
qed

lemma suffix_zero[simp]: "s |\<^sub>s 0 = s"
  by (simp add: suffix_def)

lemma suffix_tail: "s |\<^sub>s 1 = tail s"
  by (simp add: tail_def)

lemma tail_suffix_suc: "s |\<^sub>s (Suc n) = tail (s |\<^sub>s n)"
  by (simp add: suffix_def tail_def)

subsubsection "Properties of  @{term app}"

lemma seq_app_second: "(s ## \<sigma>) 1 = \<sigma> 0"
  by (simp add: app_def)

lemma seq_app_first: "(s ## \<sigma>) 0 = s" 
  by (simp add: app_def)

lemma seq_app_first_tail: "(first s) ## (tail s) = s"
proof (rule ext)
  fix x
  show "(first s ## tail s) x = s x"
    by (simp add: first_def app_def suffix_def tail_def)
qed

lemma seq_app_tail: "tail (x ## s) = s"
  by (simp add: app_def tail_def suffix_def)

lemma seq_app_greater_than_zero: "n > 0 \<Longrightarrow> (s ## \<sigma>) n = \<sigma> (n - 1)" 
  by (simp add: app_def)


subsection "Finite and Empty Sequences"

text\<open>
  We identify finite and empty sequences and prove lemmas about them. 
\<close>

definition fin :: "('a seq) \<Rightarrow> bool"
where "fin s \<equiv> \<exists> i. \<forall> j \<ge> i. s j = s i"

abbreviation inf :: "('a seq) \<Rightarrow> bool"
where "inf s \<equiv> \<not>(fin s)"

definition last :: "('a seq) \<Rightarrow> nat"
where "last s \<equiv> LEAST i. (\<forall> j \<ge> i. s j = s i)" 

definition laststate :: "('a seq) \<Rightarrow> 'a"
where "laststate s \<equiv> s (last s)"

definition emptyseq :: "('a seq) \<Rightarrow> bool"
where "emptyseq \<equiv> \<lambda> s. \<forall> i. s i = s 0"

abbreviation notemptyseq :: "('a seq) \<Rightarrow> bool"
where "notemptyseq s \<equiv> \<not>(emptyseq s)"

text \<open>
  Predicate @{term fin} holds if there is an element
  in the sequence such that all subsequent elements are identical,
  i.e. the sequence is finite. @{term "last s"} returns the smallest index
  from which on all elements of a finite sequence @{term s} are identical. Note that 
  if \<open>s\<close> is not finite then an arbitrary number is returned.
  @{term laststate} returns the last element of a finite sequence. We assume 
  that the sequence is finite when using  @{term last} and  @{term laststate}.
  Predicate @{term emptyseq} identifies empty sequences -- i.e. all states in
  the sequence are identical to the initial one, while @{term notemptyseq} holds
  if the given sequence is not empty.
\<close>

subsubsection "Properties of @{term emptyseq}"

lemma empty_is_finite: assumes "emptyseq s" shows "fin s"
  using assms by (auto simp: fin_def emptyseq_def)

lemma empty_suffix_is_empty: assumes H: "emptyseq s" shows "emptyseq (s |\<^sub>s n)"
proof (clarsimp simp: emptyseq_def)
 fix i
 from H have "(s |\<^sub>s n) i = s 0" by (simp add: emptyseq_def suffix_def)
 moreover
 from H have "(s |\<^sub>s n) 0 = s 0" by (simp add: emptyseq_def suffix_def)
 ultimately
 show "(s |\<^sub>s n) i = (s |\<^sub>s n) 0" by simp
qed

lemma suc_empty: assumes H1: "emptyseq (s |\<^sub>s m)" shows "emptyseq (s |\<^sub>s (Suc m))"
proof -
  from H1 have "emptyseq ((s |\<^sub>s m) |\<^sub>s 1)" by (rule empty_suffix_is_empty)
  thus ?thesis by (simp add: suffix_plus)
qed

lemma empty_suffix_exteq: assumes H:"emptyseq s" shows "(s |\<^sub>s n) m = s m"
proof (unfold suffix_def)
  from H have "s (m+n) = s 0" by (simp add: emptyseq_def)
  moreover
  from H have "s m = s 0" by (simp add: emptyseq_def)
  ultimately show "s (m + n) = s m" by simp
qed

lemma empty_suffix_eq: assumes H: "emptyseq s" shows "(s |\<^sub>s n) = s"
proof (rule ext)
  fix m
  from H show "(s |\<^sub>s n) m = s m" by (rule empty_suffix_exteq)
qed

lemma seq_empty_all: assumes H: "emptyseq s" shows "s i = s j"
proof -
  from H have "s i = s 0" by (simp add: emptyseq_def)
  moreover
  from H have "s j = s 0" by (simp add: emptyseq_def)
  ultimately
  show ?thesis by simp
qed

subsubsection "Properties of @{term last} and @{term laststate}" 

lemma fin_stut_after_last: assumes H: "fin s" shows "\<forall>j \<ge> last s. s j = s (last s)"
proof (clarify)
  fix j
  assume j: "j \<ge> last s"
  from H obtain i where "\<forall>j \<ge> i. s j = s i" (is "?P i") by (auto simp: fin_def)
  hence "?P (last s)" unfolding last_def by (rule LeastI)
  with j show "s j = s (last s)" by blast
qed


subsection "Stuttering Invariance"

text \<open>
  This subsection provides functions for removing stuttering
  steps of sequences, i.e. we formalise Lamports \<open>\<natural>\<close> operator.
  Our formal definition is close to that of Wahab in the PVS prover.

  The key novelty with the @{term "Sequence"} theory, is the treatment of
  stuttering invariance, which enables verification of stuttering invariance of
  the operators derived using it. Such proofs require comparing sequences
  up to stuttering. Here, Lamport's \cite{Lamport94} method is used to
  mechanise the equality of sequences up to stuttering: he defines 
  the \<open>\<natural>\<close> operator, which collapses a sequence by removing
  all stuttering steps, except possibly infinite stuttering at the end of the sequence. 
  These are left unchanged.
\<close>

definition nonstutseq :: "('a seq) \<Rightarrow> bool"
where "nonstutseq s \<equiv> \<forall> i. s i = s (Suc i) \<longrightarrow> (\<forall> j > i. s i = s j)"

definition stutstep :: "('a seq) \<Rightarrow> nat \<Rightarrow> bool"
where "stutstep s n \<equiv> (s n = s (Suc n))"

definition nextnat :: "('a seq) \<Rightarrow> nat"
where "nextnat s \<equiv> if emptyseq s then 0 else LEAST i. s i \<noteq> s 0"

definition nextsuffix :: "('a seq) \<Rightarrow> ('a seq)"
where "nextsuffix s \<equiv> s |\<^sub>s (nextnat s)"

fun "next" :: "nat \<Rightarrow> ('a seq) \<Rightarrow> ('a seq)" where
  "next 0 = id"
| "next (Suc n) = nextsuffix o (next n)"

definition collapse :: "('a seq) \<Rightarrow> ('a seq)" ("\<natural>")
where "\<natural> s \<equiv> \<lambda> n. (next n s) 0"

text \<open>
  Predicate @{term nonstutseq} identifies sequences without any 
  stuttering steps -- except possibly for infinite stuttering at the end.
  Further, @{term "stutstep s n"} is a predicate which holds if the element
  after @{term "s n"} is equal to @{term "s n"}, i.e. @{term "Suc n"} is
  a stuttering step.
  @{term "collapse s"} formalises Lamports  @{term "\<natural>"}
  operator. It returns the first state of the result of @{term "next n s"}. 
  @{term "next n s"} finds suffix of the $n^{th}$ change. Hence the first
  element, which @{term "\<natural> s"} returns, is the state after the $n^{th}$ 
  change.  @{term "next n s"} is defined by primitive recursion on 
  @{term "n"} using function composition of function @{term nextsuffix}. E.g.
  @{term "next 3 s"} equals @{term "nextsuffix (nextsuffix (nextsuffix s))"}.
  @{term "nextsuffix s"} returns the suffix of the sequence starting at the
  next changing state. It uses @{term "nextnat"} to obtain this. All the real
  computation is done in this function. Firstly, an empty sequence will obviously
  not contain any changes, and \<open>0\<close> is therefore returned. In this case 
  @{term "nextsuffix"} behaves like the identify function. If the sequence is not
  empty then the smallest number @{term "i"} such that @{term "s i"} is different
  from the initial state is returned. This is achieved by @{term "Least"}.
\<close>

subsubsection "Properties of @{term nonstutseq}"

lemma seq_empty_is_nonstut: 
  assumes H: "emptyseq s" shows "nonstutseq s"
  using H by (auto simp: nonstutseq_def seq_empty_all)

lemma notempty_exist_nonstut: 
  assumes H: "\<not> emptyseq (s |\<^sub>s m)" shows "\<exists> i. s i \<noteq> s m \<and> i > m"
using H proof (auto simp: emptyseq_def suffix_def)
  fix i
  assume i: "s (i + m) \<noteq> s m"
  hence "i \<noteq> 0" by (intro notI, simp)
  with i show ?thesis by auto
qed

subsubsection "Properties of @{term nextnat}"

lemma nextnat_le_unch: assumes H: "n < nextnat s" shows "s n = s 0"
proof (cases "emptyseq s")
  assume "emptyseq s"
  hence "nextnat s = 0" by (simp add: nextnat_def)
  with H show ?thesis by auto
next
  assume "\<not> emptyseq s"
  hence a1: "nextnat s = (LEAST i. s i \<noteq> s 0)" by (simp add: nextnat_def) 
  show ?thesis
  proof (rule ccontr)
    assume a2: "s n \<noteq> s 0" (is "?P n")
    hence "(LEAST i. s i \<noteq> s 0) \<le> n" by (rule Least_le)
    hence "\<not>(n < (LEAST i. s i \<noteq> s 0))" by auto
    also from H a1 have "n < (LEAST i. s i \<noteq> s 0)" by simp
    ultimately show False by auto
  qed
qed

lemma stutnempty: 
  assumes H: "\<not> stutstep s n" shows "\<not> emptyseq (s |\<^sub>s n)"
proof (unfold emptyseq_def suffix_def)
  from H have "s (Suc n) \<noteq> s n" by (auto simp add: stutstep_def)
  hence "s (1+n) \<noteq> s (0+n)" by simp
  thus "\<not>(\<forall> i. s (i+n) = s (0+n))" by blast
qed

lemma notstutstep_nexnat1: 
  assumes H: "\<not> stutstep s n" shows "nextnat (s |\<^sub>s n) = 1"
proof -
  from H have h': "nextnat (s |\<^sub>s n) = (LEAST i. (s |\<^sub>s n) i \<noteq> (s |\<^sub>s n) 0)" 
    by (auto simp add: nextnat_def stutnempty)
  from H have "s (Suc n) \<noteq> s n" by (auto simp add: stutstep_def)
  hence "(s |\<^sub>s n) 1 \<noteq> (s |\<^sub>s n) 0" (is "?P 1") by (auto simp add: suffix_def)
  hence "Least ?P \<le> 1" by (rule Least_le)
  hence g1: "Least ?P = 0 \<or> Least ?P = 1" by auto
  with h' have g1': "nextnat (s |\<^sub>s n) = 0 \<or> nextnat (s |\<^sub>s n) = 1" by auto
  also have "nextnat (s |\<^sub>s n) \<noteq> 0" 
  proof -
    from H have "\<not> emptyseq (s |\<^sub>s n)" by (rule stutnempty)
    then obtain i where "(s |\<^sub>s n) i \<noteq>  (s |\<^sub>s n) 0" by (auto simp add: emptyseq_def)
    hence "(s |\<^sub>s n) (LEAST i. (s |\<^sub>s n) i \<noteq> (s |\<^sub>s n) 0) \<noteq> (s |\<^sub>s n) 0" by (rule LeastI)
    with h' have g2: "(s |\<^sub>s n) (nextnat (s |\<^sub>s n)) \<noteq> (s |\<^sub>s n) 0" by auto
    show "(nextnat (s |\<^sub>s n)) \<noteq> 0" 
    proof
      assume "(nextnat (s |\<^sub>s n)) = 0"
      with g2 show "False" by simp
    qed
  qed
  ultimately show  "nextnat (s |\<^sub>s n) = 1" by auto
qed

lemma stutstep_notempty_notempty: 
  assumes h1: "emptyseq (s |\<^sub>s Suc n)" (is "emptyseq ?sn")
      and h2: "stutstep s n" 
  shows "emptyseq (s |\<^sub>s n)" (is "emptyseq ?s")
proof (auto simp: emptyseq_def)
  fix k
  show "?s k = ?s 0"
  proof (cases k)
    assume "k = 0" thus ?thesis by simp
  next
    fix m
    assume k: "k = Suc m"
    hence "?s k = ?sn m" by (simp add: suffix_def)
    also from h1 have "... = ?sn 0" by (simp add: emptyseq_def)
    also from h2 have "... = s n" by (simp add: suffix_def stutstep_def)
    finally show ?thesis by (simp add: suffix_def)
  qed
qed

lemma stutstep_empty_suc:
  assumes "stutstep s n"
  shows "emptyseq (s |\<^sub>s Suc n) = emptyseq (s |\<^sub>s n)"
using assms by (auto elim: stutstep_notempty_notempty suc_empty)

lemma stutstep_notempty_sucnextnat: 
  assumes h1: "\<not> emptyseq  (s |\<^sub>s n)" and h2: "stutstep s n" 
   shows "(nextnat (s |\<^sub>s n)) = Suc (nextnat (s |\<^sub>s (Suc n)))"
proof -
  from h2 have g1: "\<not>(s (0+n) \<noteq> s (Suc n))" (is "\<not> ?P 0") by (auto simp add: stutstep_def)
  from h1 obtain i where "s (i+n) \<noteq> s n" by (auto simp: emptyseq_def suffix_def)
  with h2 have g2: "s (i+n) \<noteq> s (Suc n)" (is "?P i") by (simp add: stutstep_def)
  from g2 g1 have "(LEAST n. ?P n) = Suc (LEAST n. ?P (Suc n))" by (rule Least_Suc)
  from g2 g1 have "(LEAST i. s (i+n) \<noteq> s (Suc n)) = Suc (LEAST i. s ((Suc i)+n) \<noteq> s (Suc n))"
    by (rule Least_Suc)
  hence G1: "(LEAST i. s (i+n) \<noteq> s (Suc n)) = Suc (LEAST i. s (i+Suc n) \<noteq> s (Suc n))" by auto
  from h1 h2 have "\<not> emptyseq  (s |\<^sub>s Suc n)" by (simp add: stutstep_empty_suc)
  hence "nextnat (s |\<^sub>s Suc n) = (LEAST i. (s |\<^sub>s Suc n) i \<noteq> (s |\<^sub>s Suc n) 0)"
    by (auto simp add: nextnat_def)
  hence g1: "nextnat (s |\<^sub>s Suc n) = (LEAST i. s (i+(Suc n)) \<noteq> s (Suc n))"
    by (simp add: suffix_def)
  from h1 have  "nextnat (s |\<^sub>s n) = (LEAST i. (s |\<^sub>s n) i \<noteq> (s |\<^sub>s n) 0)"
    by (auto simp add: nextnat_def)
  hence g2: "nextnat (s |\<^sub>s n) = (LEAST i. s (i+n) \<noteq> s n)" by (simp add: suffix_def)
  with h2 have g2': "nextnat (s |\<^sub>s n) = (LEAST i. s (i+n) \<noteq> s (Suc n))"
    by (auto simp add: stutstep_def)
  from G1 g1 g2' show ?thesis by auto
qed

lemma nextnat_empty_neq: assumes H: "\<not> emptyseq s" shows "s (nextnat s) \<noteq> s 0"
proof -
  from H have a1: "nextnat s =  (LEAST i. s i \<noteq> s 0)" by (simp add: nextnat_def)
  from H obtain i where "s i \<noteq> s 0" by (auto simp: emptyseq_def)
  hence "s (LEAST i. s i \<noteq> s 0) \<noteq> s 0" by (rule LeastI)
  with a1 show ?thesis by auto
qed

lemma nextnat_empty_gzero: assumes H: "\<not> emptyseq s" shows "nextnat s > 0"
proof -
  from H have a1: "s (nextnat s) \<noteq> s 0" by (rule nextnat_empty_neq)
  have "nextnat s \<noteq> 0"
  proof
    assume "nextnat s = 0"
    with a1 show "False" by simp
  qed
  thus "nextnat s > 0" by simp
qed

subsubsection "Properties of @{term nextsuffix}"

lemma empty_nextsuffix: 
  assumes H: "emptyseq s" shows "nextsuffix s = s"
  using H by (simp add: nextsuffix_def nextnat_def)

lemma empty_nextsuffix_id: 
  assumes H: "emptyseq s" shows "nextsuffix s = id s"
  using H by (simp add: empty_nextsuffix)

lemma notstutstep_nextsuffix1: 
  assumes H: "\<not> stutstep s n" shows "nextsuffix (s |\<^sub>s n) = s |\<^sub>s (Suc n)"
proof (unfold nextsuffix_def)
  show "(s |\<^sub>s n |\<^sub>s (nextnat (s |\<^sub>s n))) =  s |\<^sub>s (Suc n)"
  proof -
    from H have  "nextnat (s |\<^sub>s n) = 1" by (rule notstutstep_nexnat1)
    hence "(s |\<^sub>s n |\<^sub>s (nextnat (s |\<^sub>s n))) = s |\<^sub>s n |\<^sub>s 1" by auto
    thus ?thesis by (simp add: suffix_def)
  qed
qed

subsubsection "Properties of @{term next}"

lemma next_suc_suffix: "next (Suc n) s = nextsuffix (next n s)"
  by simp

lemma next_suffix_com: "nextsuffix (next n s) = (next n (nextsuffix s))"
  by (induct n, auto)

lemma next_plus: "next (m+n) s = next m (next n s)" 
  by (induct m, auto)

lemma next_empty: assumes H: "emptyseq s" shows "next n s = s"
proof (induct n)
  from H show "next 0 s = s" by auto
next
  fix n
  assume a1: "next n s = s"
  have "next (Suc n) s = nextsuffix (next n s)" by auto
  with a1 have "next (Suc n) s = nextsuffix s" by simp
  with H show "next (Suc n) s = s"
    by (simp add: nextsuffix_def nextnat_def)
qed

lemma notempty_nextnotzero: 
  assumes H: "\<not>emptyseq s" shows "(next (Suc 0) s) 0 \<noteq> s 0"
proof -
  from H have g1: "s (nextnat s) \<noteq> s 0" by (rule nextnat_empty_neq)
  have "next (Suc 0) s = nextsuffix s" by auto
  hence "(next (Suc 0) s) 0 =  s (nextnat s)" by (simp add: nextsuffix_def suffix_def)
  with g1 show ?thesis by simp
qed

lemma next_ex_id: "\<exists> i. s i = (next m s) 0"
proof -
  have "\<exists> i. (s |\<^sub>s i) = (next m s)"
  proof (induct m)
    have "s |\<^sub>s 0 = next 0 s" by simp
    thus "\<exists> i. (s |\<^sub>s i) = (next 0 s)" ..
  next
    fix m
    assume a1: "\<exists> i. (s |\<^sub>s i) = (next m s)"
    then obtain i where a1': "(s |\<^sub>s i) = (next m s)" ..
    have "next (Suc m) s = nextsuffix (next m s)" by auto
    hence "next (Suc m) s = (next m s) |\<^sub>s (nextnat (next m s))" by (simp add: nextsuffix_def)
    hence "\<exists> i. next (Suc m) s = (next m s) |\<^sub>s i" ..
    then obtain j where "next (Suc m) s = (next m s) |\<^sub>s j" ..
    with a1' have "next (Suc m) s = (s |\<^sub>s i) |\<^sub>s j" by simp
    hence "next (Suc m) s = (s |\<^sub>s (j+i))" by (simp add: suffix_plus)
    hence "(s |\<^sub>s (j+i)) = next (Suc m) s" by simp
    thus "\<exists> i. (s |\<^sub>s i) = (next (Suc m) s)" ..
  qed
  then obtain i where "(s |\<^sub>s i) = (next m s)" ..
  hence "(s |\<^sub>s i) 0 = (next m s) 0" by auto
  hence "s i = (next m s) 0" by (auto simp add: suffix_def)
  thus ?thesis ..
qed

subsubsection "Properties of @{term collapse}"

lemma emptyseq_collapse_eq: assumes A1: "emptyseq s" shows "\<natural> s = s"
proof (unfold collapse_def, rule ext)
  fix n
  from A1 have "next n s = s" by (rule next_empty)
  moreover
  from A1 have "s n = s 0" by (simp add: emptyseq_def)
  ultimately
  show "(next n s) 0 = s n" by simp
qed

lemma empty_collapse_empty: 
  assumes H: "emptyseq s" shows "emptyseq (\<natural> s)"
  using H by (simp add: emptyseq_collapse_eq)

lemma collapse_empty_empty: 
  assumes H: "emptyseq (\<natural> s)" shows "emptyseq s"
proof (rule ccontr)
  assume a1: "\<not>emptyseq s"
  from H have "\<forall> i. (next i s) 0 = s 0" by (simp add: collapse_def emptyseq_def)
  moreover
  from a1 have "(next (Suc 0) s) 0 \<noteq> s 0" by (rule notempty_nextnotzero)
  ultimately show "False" by blast
qed

lemma collapse_empty_iff_empty [simp]: "emptyseq (\<natural> s) = emptyseq s"
  by (auto elim: empty_collapse_empty collapse_empty_empty)

subsection "Similarity of Sequences"

text\<open>
  Since adding or removing stuttering steps does not change the validity 
  of a stuttering-invarant formula, equality is often too strong, 
  and the weaker equality \emph{up to stuttering} is sufficient. 
  This is often called \emph{similarity} ($\approx$) 
  of sequences in the literature, and is required to
  show that logical operators are stuttering invariant. This
  is mechanised as:
\<close>

definition seqsimilar :: "('a seq) \<Rightarrow> ('a seq) \<Rightarrow> bool" (infixl "\<approx>" 50)
where "\<sigma> \<approx> \<tau> \<equiv> (\<natural> \<sigma>) = (\<natural> \<tau>)"

subsubsection "Properties of @{term seqsimilar}"

lemma seqsim_refl [iff]: "s \<approx> s"
  by (simp add: seqsimilar_def)

lemma seqsim_sym: assumes H: "s \<approx> t" shows "t \<approx> s"
  using H by (simp add: seqsimilar_def)

lemma seqeq_imp_sim: assumes H: "s = t" shows "s \<approx> t"
  using H by simp

lemma seqsim_trans [trans]: assumes h1: "s \<approx> t" and h2: "t \<approx> z" shows "s \<approx> z" 
  using assms by (simp add: seqsimilar_def)

theorem sim_first: assumes H: "s \<approx> t" shows "first s = first t"
proof -
  from H have "(\<natural> s) 0 = (\<natural> t) 0" by (simp add: seqsimilar_def)
  thus ?thesis by (simp add: collapse_def first_def)
qed

lemmas sim_first2 = sim_first[unfolded first_def]

lemma tail_sim_second: assumes H: "tail s \<approx> tail t" shows "second s = second t"
proof -
  from H have "first (tail s) = first (tail t)" by (simp add: sim_first)
  thus "second s = second t" by (simp add: first_tail_second)
qed

lemma seqsimilarI:
  assumes 1: "first s = first t" and 2: "nextsuffix s \<approx> nextsuffix t"
  shows "s \<approx> t"
  unfolding seqsimilar_def collapse_def
proof
  fix n
  show "next n s 0 = next n t 0"
  proof (cases n)
    assume "n = 0"
    with 1 show ?thesis by (simp add: first_def)
  next
    fix m
    assume m: "n = Suc m"
    from 2 have "next m (nextsuffix s) 0 =  next m (nextsuffix t) 0"
      unfolding seqsimilar_def collapse_def by (rule fun_cong)
    with m show ?thesis by (simp add: next_suffix_com)
  qed
qed

lemma seqsim_empty_empty: 
  assumes H1: "s \<approx> t" and H2: "emptyseq s" shows "emptyseq t"
proof -
  from H2 have "emptyseq (\<natural> s)" by simp
  with H1 have "emptyseq (\<natural> t)" by (simp add: seqsimilar_def)
  thus ?thesis by simp
qed

lemma seqsim_empty_iff_empty:
  assumes H: "s \<approx> t" shows "emptyseq s = emptyseq t"
proof
  assume "emptyseq s" with H show "emptyseq t" by (rule seqsim_empty_empty)
next
  assume t: "emptyseq t"
  from H have "t \<approx> s" by (rule seqsim_sym)
  from this t show "emptyseq s" by (rule seqsim_empty_empty)
qed

lemma seq_empty_eq: 
  assumes H1: "s 0 = t 0" and H2: "emptyseq s" and H3: "emptyseq t"
  shows "s = t"
proof (rule ext)
  fix n
  from assms have "t n = s n" by (auto simp: emptyseq_def)
  thus "s n = t n" by simp
qed

lemma seqsim_notstutstep: 
  assumes H: "\<not> (stutstep s n)" shows "(s |\<^sub>s (Suc n)) \<approx> nextsuffix (s |\<^sub>s n)"
  using H by (simp add: notstutstep_nextsuffix1)

lemma stut_nextsuf_suc: 
  assumes H: "stutstep s n" shows "nextsuffix (s |\<^sub>s n) = nextsuffix (s |\<^sub>s (Suc n))"
proof (cases "emptyseq (s |\<^sub>s n)")
  case True
  hence g1: "nextsuffix (s |\<^sub>s n) = (s |\<^sub>s n)" by (simp add: nextsuffix_def nextnat_def)
  from True have g2: "nextsuffix (s |\<^sub>s Suc n) = (s |\<^sub>s Suc n)"
    by (simp add: suc_empty nextsuffix_def nextnat_def)
  have "(s |\<^sub>s n) = (s |\<^sub>s Suc n)"
  proof
    fix x
    from True have "s (x + n) = s (0 + n)" "s (Suc x + n) = s (0 + n)"
      unfolding emptyseq_def suffix_def by (blast+)
    thus "(s |\<^sub>s n) x = (s |\<^sub>s Suc n) x" by (simp add: suffix_def)
  qed
  with g1 g2 show ?thesis by auto
next
  case False
  with H have "(nextnat (s |\<^sub>s n)) = Suc (nextnat (s |\<^sub>s Suc n))"
    by (simp add: stutstep_notempty_sucnextnat)
  thus ?thesis
    by (simp add: nextsuffix_def suffix_plus)
qed

lemma seqsim_suffix_seqsim:
  assumes H: "s \<approx> t" shows "nextsuffix s \<approx> nextsuffix t"
  unfolding seqsimilar_def collapse_def
proof
  fix n
  from H have "(next (Suc n) s) 0 = (next (Suc n) t) 0"
    unfolding seqsimilar_def collapse_def by (rule fun_cong)
  thus "next n (nextsuffix s) 0 = next n (nextsuffix t) 0"
    by (simp add: next_suffix_com)
qed

lemma seqsim_stutstep:
  assumes H: "stutstep s n" shows "(s |\<^sub>s (Suc n)) \<approx> (s |\<^sub>s n)" (is "?sn \<approx> ?s")
  unfolding seqsimilar_def collapse_def
proof
  fix m
  show "next m (s |\<^sub>s Suc n) 0 = next m (s |\<^sub>s n) 0"
  proof (cases m)
    assume "m=0"
    with H show ?thesis by (simp add: suffix_def stutstep_def)
  next
    fix k
    assume m: "m = Suc k"
    with H  have "next m (s |\<^sub>s Suc n) = next k (nextsuffix  (s |\<^sub>s n))"
      by (simp add: stut_nextsuf_suc next_suffix_com)
    moreover from m have "next m (s |\<^sub>s n) = next k (nextsuffix  (s |\<^sub>s n))" 
      by (simp add: next_suffix_com)
    ultimately show "next m (s |\<^sub>s Suc n) 0 = next m (s |\<^sub>s n) 0" by simp
  qed
qed

lemma addfeqstut: "stutstep ((first t) ## t) 0"
  by (simp add: first_def stutstep_def app_def suffix_def)

lemma addfeqsim: "((first t) ## t) \<approx> t"
proof -
  have "stutstep ((first t) ## t) 0" by (rule addfeqstut)
  hence "(((first t) ## t) |\<^sub>s (Suc 0)) \<approx> (((first t) ## t) |\<^sub>s 0)" by (rule seqsim_stutstep)
  hence "tail ((first t) ## t) \<approx> ((first t) ## t)" by (simp add: suffix_def tail_def)
  hence "t \<approx> ((first t) ## t)" by (simp add: tail_def app_def suffix_def)
  thus ?thesis by (rule seqsim_sym)
qed

lemma addfirststut:
  assumes H: "first s = second s" shows "s \<approx> tail s"
proof -
  have g1: "(first s) ## (tail s) = s" by (rule seq_app_first_tail)
  from H have "(first s) = first (tail s)"
    by (simp add: first_def second_def tail_def suffix_def)
  hence "(first s) ## (tail s) \<approx> (tail s)" by (simp add: addfeqsim)
  with g1 show ?thesis by simp
qed

lemma app_seqsimilar:
  assumes h1: "s \<approx> t" shows "(x ## s) \<approx> (x ## t)"
proof (cases "stutstep (x ## s) 0")
  case True
  from h1 have "first s = first t" by (rule sim_first)
  with True have a2: "stutstep (x ## t) 0"
    by (simp add: stutstep_def first_def app_def)
  from True have "((x ## s) |\<^sub>s (Suc 0)) \<approx> ((x ## s) |\<^sub>s 0)" by (rule seqsim_stutstep)
  hence "tail (x ## s) \<approx> (x ## s)" by (simp add: tail_def suffix_def)
  hence g1: "s \<approx> (x ## s)" by (simp add: app_def tail_def suffix_def)
  from a2 have "((x ## t) |\<^sub>s (Suc 0)) \<approx> ((x ## t) |\<^sub>s 0)" by (rule seqsim_stutstep)
  hence "tail (x ## t) \<approx> (x ## t)" by (simp add: tail_def suffix_def)
  hence g2: "t \<approx> (x ## t)" by (simp add: app_def tail_def suffix_def)
  from h1 g2 have "s \<approx> (x ## t)" by (rule seqsim_trans)
  from this[THEN seqsim_sym] g1 show "(x ## s) \<approx> (x ## t)"
    by (rule seqsim_sym[OF seqsim_trans])
next
  case False
  from h1 have "first s = first t" by (rule sim_first)
  with False have a2: "\<not> stutstep (x ## t) 0"
    by (simp add: stutstep_def first_def app_def)
  from False have "((x ## s) |\<^sub>s (Suc 0)) \<approx> nextsuffix ((x ## s) |\<^sub>s 0)"
    by (rule seqsim_notstutstep)
  hence "(tail (x ## s)) \<approx> nextsuffix (x ## s)" 
    by (simp add: tail_def)
  hence g1: "s \<approx> nextsuffix (x ## s)" by (simp add: seq_app_tail)
  from a2 have "((x ## t) |\<^sub>s (Suc 0)) \<approx> nextsuffix ((x ## t) |\<^sub>s 0)"
    by (rule seqsim_notstutstep)
  hence "(tail (x ## t)) \<approx> nextsuffix (x ## t)" by (simp add: tail_def)
  hence g2: "t \<approx> nextsuffix (x ## t)" by (simp add: seq_app_tail)
  with h1 have "s \<approx> nextsuffix (x ## t)" by (rule seqsim_trans)
  from this[THEN seqsim_sym] g1 have g3: "nextsuffix (x ## s) \<approx> nextsuffix (x ## t)"
    by (rule seqsim_sym[OF seqsim_trans])
  have "first (x ## s) = first (x ## t)" by (simp add: first_def app_def)
  from this g3 show ?thesis by (rule seqsimilarI)
qed

text \<open>
  If two sequences are similar then for any suffix of one of them there
  exists a similar suffix of the other one. We will prove a stronger
  result below.
\<close>

lemma simstep_disj1: assumes H: "s \<approx> t" shows "\<exists> m. ((s |\<^sub>s n) \<approx> (t |\<^sub>s m))"
proof (induct n)
  from H have "((s |\<^sub>s 0) \<approx> (t |\<^sub>s 0))" by auto
  thus "\<exists> m. ((s |\<^sub>s 0) \<approx> (t |\<^sub>s m))" ..
next
  fix n
  assume "\<exists> m. ((s |\<^sub>s n) \<approx> (t |\<^sub>s m))"
  then obtain m where a1': "(s |\<^sub>s n) \<approx> (t |\<^sub>s m)" ..
  show "\<exists> m. ((s |\<^sub>s (Suc n)) \<approx> (t |\<^sub>s m))"
  proof (cases "stutstep s n")
    case True
    hence "(s |\<^sub>s (Suc n)) \<approx> (s |\<^sub>s n)" by (rule seqsim_stutstep)
    from this a1' have "((s |\<^sub>s (Suc n)) \<approx> (t |\<^sub>s m))" by (rule seqsim_trans)
    thus ?thesis ..
  next
    case False
    hence "(s |\<^sub>s (Suc n)) \<approx> nextsuffix (s |\<^sub>s n)" by (rule seqsim_notstutstep)
    moreover
    from a1' have "nextsuffix (s |\<^sub>s n) \<approx> nextsuffix (t |\<^sub>s m)" 
      by (simp add: seqsim_suffix_seqsim)
    ultimately have "(s |\<^sub>s (Suc n)) \<approx> nextsuffix (t |\<^sub>s m)" by (rule seqsim_trans)
    hence "(s |\<^sub>s (Suc n)) \<approx> t |\<^sub>s (m + (nextnat (t |\<^sub>s m)))"
      by (simp add: nextsuffix_def suffix_plus_com)
    thus "\<exists> m. (s |\<^sub>s (Suc n)) \<approx> t |\<^sub>s m" ..
  qed
qed

lemma nextnat_le_seqsim: 
  assumes n: "n < nextnat s" shows "s \<approx> (s |\<^sub>s n)"
proof (cases "emptyseq s")
  case True   \<comment> \<open>case impossible\<close>
  with n show ?thesis by (simp add: nextnat_def)
next
  case False
  from n show ?thesis
  proof (induct n)
    show "s \<approx> (s |\<^sub>s 0)" by simp
  next
    fix n
    assume a2: "n < nextnat s \<Longrightarrow> s \<approx> (s |\<^sub>s n)" and a3: "Suc n < nextnat s"
    from a3 have g1: "s (Suc n) = s 0" by (rule nextnat_le_unch)
    from a3 have a3': "n < nextnat s" by simp
    hence "s n = s 0" by (rule nextnat_le_unch)
    with g1 have "stutstep s n" by (simp add: stutstep_def)
    hence g2: "(s |\<^sub>s n) \<approx> (s |\<^sub>s (Suc n))" by (rule seqsim_stutstep[THEN seqsim_sym])
    with a3' a2 show "s \<approx> (s |\<^sub>s (Suc n))" by (auto elim: seqsim_trans)
  qed
qed

lemma seqsim_prev_nextnat: "s \<approx> s |\<^sub>s ((nextnat s) - 1)"
proof (cases "emptyseq s")
  case True
  hence "s |\<^sub>s ((nextnat s)-(1::nat)) = s |\<^sub>s 0" by (simp add: nextnat_def)
  thus ?thesis by simp
next
  case False
  hence "nextnat s > 0" by (rule nextnat_empty_gzero)
  thus ?thesis by (simp add: nextnat_le_seqsim)
qed

text \<open>
  Given a suffix \<open>s |\<^sub>s n\<close> of some sequence \<open>s\<close> that is
  similar to some suffix \<open>t |\<^sub>s m\<close> of sequence \<open>t\<close>, there
  exists some suffix \<open>t |\<^sub>s m'\<close> of \<open>t\<close> such that
  \<open>s |\<^sub>s n\<close> and \<open>t |\<^sub>s m'\<close> are similar and also
  \<open>s |\<^sub>s (n+1)\<close> is similar to either \<open>t |\<^sub>s m'\<close> or to
  \<open>t |\<^sub>s (m'+1)\<close>.
\<close>

lemma seqsim_suffix_suc:
  assumes H: "s |\<^sub>s n \<approx> t |\<^sub>s m"
  shows "\<exists>m'. s |\<^sub>s n \<approx> t |\<^sub>s m' \<and> ((s |\<^sub>s Suc n \<approx> t |\<^sub>s Suc m') \<or> (s |\<^sub>s Suc n \<approx> t |\<^sub>s m'))"
proof (cases "stutstep s n")
  case True
  hence "s |\<^sub>s Suc n \<approx> s |\<^sub>s n" by (rule seqsim_stutstep)
  from this H have "s |\<^sub>s Suc n \<approx> t |\<^sub>s m" by (rule seqsim_trans)
  with H show ?thesis by blast
next
  case False
  hence "\<not> emptyseq (s |\<^sub>s n)" by (rule stutnempty)
  with H have a2: "\<not> emptyseq (t |\<^sub>s m)" by (simp add: seqsim_empty_iff_empty)
  hence g4: "nextsuffix (t |\<^sub>s m) = (t |\<^sub>s m) |\<^sub>s Suc (nextnat (t |\<^sub>s m) - 1)"
    by (simp add: nextnat_empty_gzero nextsuffix_def)
  have g3: "(t |\<^sub>s m) \<approx> (t |\<^sub>s m) |\<^sub>s (nextnat (t |\<^sub>s m) - 1)"
    by (rule seqsim_prev_nextnat)
  with H have G1: "s |\<^sub>s n \<approx> (t |\<^sub>s m) |\<^sub>s (nextnat (t |\<^sub>s m) - 1)"
    by (rule seqsim_trans)
  from False have G1': "(s |\<^sub>s Suc n) = nextsuffix (s |\<^sub>s n)" 
    by (rule notstutstep_nextsuffix1[THEN sym])
  from H have "nextsuffix (s |\<^sub>s n) \<approx> nextsuffix (t |\<^sub>s m)"
    by (rule seqsim_suffix_seqsim)
  with G1 G1' g4
  have "s |\<^sub>s n \<approx> t |\<^sub>s (m + (nextnat (t |\<^sub>s m) - 1))
      \<and> s |\<^sub>s (Suc n) \<approx> t |\<^sub>s Suc (m + (nextnat (t |\<^sub>s m) - 1))"
    by (simp add: suffix_plus_com)
  thus ?thesis by blast
qed

text \<open>
  The following main result about similar sequences shows that if
  \<open>s \<approx> t\<close> holds then for any suffix \<open>s |\<^sub>s n\<close> of \<open>s\<close>
  there exists a suffix \<open>t |\<^sub>s m\<close> such that
  \begin{itemize}
  \item \<open>s |\<^sub>s n\<close> and \<open>t |\<^sub>s m\<close> are similar, and
  \item \<open>s |\<^sub>s (n+1)\<close> is similar to either \<open>t |\<^sub>s (m+1)\<close>
    or \<open>t |\<^sub>s m\<close>.
  \end{itemize}
  The idea is to pick the largest \<open>m\<close> such that \<open>s |\<^sub>s n \<approx> t |\<^sub>s m\<close>
  (or some such \<open>m\<close> if \<open>s |\<^sub>s n\<close> is empty).
\<close>

theorem sim_step: 
  assumes H: "s \<approx> t" 
  shows "\<exists> m. s |\<^sub>s n \<approx> t |\<^sub>s m \<and> 
              ((s |\<^sub>s Suc n \<approx> t |\<^sub>s Suc m) \<or> (s |\<^sub>s Suc n \<approx> t |\<^sub>s m))"
    (is "\<exists>m. ?Sim n m")
proof (induct n)
  from H have "s |\<^sub>s 0 \<approx> t |\<^sub>s 0" by simp
  thus "\<exists> m. ?Sim 0 m" by (rule seqsim_suffix_suc)
next
  fix n
  assume "\<exists> m. ?Sim n m"
  hence "\<exists>k. s |\<^sub>s Suc n \<approx> t |\<^sub>s k" by blast
  thus "\<exists> m. ?Sim (Suc n) m" by (blast dest: seqsim_suffix_suc)
qed

end
