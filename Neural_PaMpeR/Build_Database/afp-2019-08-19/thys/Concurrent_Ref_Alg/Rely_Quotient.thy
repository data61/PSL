section \<open>Rely Quotient Operator \label{S:rely-quotient}\<close>

text \<open>
  The rely quotient operator is used to generalise a Jones-style rely condition
  to a process \cite{jon83a}.
  It is defined in terms of the parallel operator and a process $i$
  representing interference from the environment.
\<close>

theory Rely_Quotient
imports
  CRA
  Conjunctive_Iteration
begin

subsection \<open>Basic rely quotient\<close>

text \<open>
  The rely quotient of a process $c$ and an interference process $i$
  is the most general process $d$ such that $c$ is refined by $d \parallel i$.
  The following locale introduces the definition of the 
  rely quotient $c \quotient i$ as a non-deterministic choice over 
  all processes $d$ such that $c$ is refined by $d \parallel i$. 
\<close>

locale rely_quotient = par_distrib + conjunction_parallel
begin

definition
  rely_quotient :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "'/'/" 85)
where
  "c // i \<equiv> \<Sqinter>{ d. (c \<sqsubseteq> d \<parallel> i)}"

text \<open>
  Any process $c$ is implemented by itself if the interference is skip.
\<close>
lemma quotient_identity: "c // skip = c"
proof -
  have "c // skip = \<Sqinter>{ d. (c \<sqsubseteq> d \<parallel> skip) }" by (metis rely_quotient_def)
  then have "c // skip = \<Sqinter>{ d. (c \<sqsubseteq> d)  }" by (metis (mono_tags, lifting) Collect_cong par_skip) 
  thus ?thesis by (metis Inf_greatest Inf_lower2 dual_order.antisym dual_order.refl mem_Collect_eq) 
qed

text \<open>
  Provided the interference process $i$ is non-aborting (i.e. it refines chaos), 
  any process $c$ is refined by its rely quotient with $i$ in parallel with $i$.
  If interference $i$ was allowed to be aborting then, 
  because $(c \quotient \bot) \parallel \bot$ equals $\bot$,
  it does not refine $c$ in general. 
\<close>
theorem rely_quotient: 
  assumes nonabort_i: "chaos \<sqsubseteq> i"
  shows "c \<sqsubseteq> (c // i) \<parallel> i"
proof -
  define D where "D = { d \<parallel> i | d. (c \<sqsubseteq> d \<parallel> i)}"
  define C where "C = {c}"
  have "(\<forall>d \<in> D. (\<exists> c \<in> C. c \<sqsubseteq> d))" using D_def C_def CollectD singletonI by auto
  then have "\<Sqinter> C \<sqsubseteq> (\<Sqinter> D)" by (simp add: Inf_mono) 
  then have "c \<sqsubseteq> \<Sqinter>{ d \<parallel> i | d. (c \<sqsubseteq> d \<parallel> i)}" by (simp add: C_def D_def) 
  also have "... = \<Sqinter>{ d \<parallel> i | d. d \<in> {d. (c \<sqsubseteq> d \<parallel> i)}}" by simp
  also have "... = (\<Sqinter>d \<in> {d. (c \<sqsubseteq> d \<parallel> i)}. d \<parallel> i)" by (simp add: INF_Inf)
  also have "... = \<Sqinter>{ d | d. (c \<sqsubseteq> d \<parallel> i)} \<parallel> i"
  proof (cases "{ d | d. (c \<sqsubseteq> d \<parallel> i)} = {}")
    assume "{ d | d. (c \<sqsubseteq> d \<parallel> i)} = {}"
    then show "(\<Sqinter>d \<in> {d. (c \<sqsubseteq> d \<parallel> i)}. d \<parallel> i) = \<Sqinter>{ d | d. (c \<sqsubseteq> d \<parallel> i)} \<parallel> i"
      using nonabort_i Collect_empty_eq top_greatest
            nonabort_par_top par_commute by fastforce 
  next 
    assume a: "{ d | d. (c \<sqsubseteq> d \<parallel> i)} \<noteq> {}"
    have b: "{d. (c \<sqsubseteq> d \<parallel> i)}  \<noteq> {}" using a by blast 
    then have "(\<Sqinter>d \<in> {d. (c \<sqsubseteq> d \<parallel> i)}. d \<parallel> i) = \<Sqinter>{ d. (c \<sqsubseteq> d \<parallel> i)} \<parallel> i"
      using Inf_par_distrib by simp
    then show ?thesis by auto 
  qed
  also have "... = (c // i) \<parallel> i" by (metis rely_quotient_def)
  finally show ?thesis .
qed

text \<open>
  The following theorem represents the Galois connection between 
  the parallel operator (upper adjoint) and the rely quotient operator
  (lower adjoint). This basic relationship is used to prove the majority
  of the theorems about rely quotient.
\<close>

theorem rely_refinement: 
  assumes nonabort_i: "chaos \<sqsubseteq> i"
  shows "c // i \<sqsubseteq> d \<longleftrightarrow> c \<sqsubseteq> d \<parallel> i"
proof
  assume a: "c // i \<sqsubseteq> d"
  have "c \<sqsubseteq> (c // i) \<parallel> i" using rely_quotient nonabort_i by simp
  thus "c \<sqsubseteq> d \<parallel> i" using par_mono a
    by (metis inf.absorb_iff2 inf_commute le_infI2 order_refl) 
next
  assume b: "c \<sqsubseteq> d \<parallel> i"
  then have "\<Sqinter>{ d. (c \<sqsubseteq> d \<parallel> i)} \<sqsubseteq> d" by (simp add: Inf_lower)
  thus "c // i \<sqsubseteq> d" by (metis rely_quotient_def) 
qed

text \<open>
  Refining the ``numerator'' in a quotient, refines the quotient.
\<close>

lemma rely_mono:
  assumes c_refsto_d: "c \<sqsubseteq> d"
  shows "(c // i) \<sqsubseteq> (d // i)"
proof -
  have "\<And> f. ((d \<sqsubseteq> f \<parallel> i) \<Longrightarrow> \<exists> e. (c \<sqsubseteq> e \<parallel> i) \<and> (e \<sqsubseteq> f))"
    using c_refsto_d order.trans by blast 
  then have b: "\<Sqinter>{ e. (c \<sqsubseteq> e \<parallel> i)} \<sqsubseteq>  \<Sqinter>{ f. (d \<sqsubseteq> f \<parallel> i)}"
    by (metis Inf_mono mem_Collect_eq) 
  show ?thesis using rely_quotient_def b by simp
qed

text \<open>
  Refining the ``denominator'' in a quotient, gives a reverse refinement 
  for the quotients. This corresponds to weaken rely condition law of
  Jones \cite{jon83a}, 
  i.e. assuming less about the environment.
\<close>

lemma weaken_rely: 
  assumes i_refsto_j: "i \<sqsubseteq> j"
  shows "(c // j) \<sqsubseteq> (c // i)"
proof -
  have "\<And> f. ((c \<sqsubseteq> f \<parallel> i) \<Longrightarrow> \<exists> e. (c \<sqsubseteq> e \<parallel> j) \<and> (e \<sqsubseteq> f))"
    using i_refsto_j order.trans
    by (metis inf.absorb_iff2 inf_le1 inf_par_distrib inf_sup_ord(2) par_commute) 
  then have b: "\<Sqinter>{ e. (c \<sqsubseteq> e \<parallel> j)} \<sqsubseteq>  \<Sqinter>{ f. (c \<sqsubseteq> f \<parallel> i)}"
    by (metis Inf_mono mem_Collect_eq) 
  show ?thesis using rely_quotient_def b by simp
qed

lemma par_nonabort: 
  assumes nonabort_i: "chaos \<sqsubseteq> i"
  assumes nonabort_j: "chaos \<sqsubseteq> j"
  shows "chaos \<sqsubseteq> i \<parallel> j"
  by (meson chaos_par_chaos nonabort_i nonabort_j order_trans par_mono) 

text \<open>
  Nesting rely quotients of $j$ and $i$ means the same as a single quotient
  which is the parallel composition of $i$ and $j$.
\<close>

lemma nested_rely: 
  assumes j_nonabort: "chaos \<sqsubseteq> j"
  shows "((c // j) // i) = c // (i \<parallel> j)"
proof (rule antisym)
  show "((c // j) // i) \<sqsubseteq> c // (i \<parallel> j)" 
  proof -
    have "\<And> f. ((c \<sqsubseteq> f \<parallel> i \<parallel> j) \<Longrightarrow> \<exists> e. (c \<sqsubseteq> e \<parallel> j) \<and> (e \<sqsubseteq> f \<parallel> i))" by blast
    then have "\<Sqinter>{ d. (\<Sqinter>{ e. (c \<sqsubseteq> e \<parallel> j)} \<sqsubseteq> d \<parallel> i)} \<sqsubseteq>  \<Sqinter>{ f. (c \<sqsubseteq> f \<parallel> i \<parallel> j)}"
      by (simp add: Collect_mono Inf_lower Inf_superset_mono)
    thus ?thesis using local.rely_quotient_def par_assoc by auto 
  qed
next
  show "c // (i \<parallel> j) \<sqsubseteq> ((c // j) // i) "
  proof -
    have "c \<sqsubseteq> \<Sqinter>{ e. (c \<sqsubseteq> e \<parallel> j)} \<parallel> j"
      using j_nonabort local.rely_quotient_def rely_quotient by auto 
    then have "\<And> d. \<Sqinter>{ e. (c \<sqsubseteq> e \<parallel> j)} \<sqsubseteq> d \<parallel> i  \<Longrightarrow> (c \<sqsubseteq> d \<parallel> i \<parallel> j)"
      by (meson j_nonabort order_trans rely_refinement)
    thus ?thesis
      by (simp add: Collect_mono Inf_superset_mono local.rely_quotient_def par_assoc) 
  qed
qed

end


subsection \<open>Distributed rely quotient\<close>

locale rely_distrib = rely_quotient + conjunction_sequential
begin

text \<open>
  The following is a fundamental law for introducing a parallel composition
  of process to refine a conjunction of specifications. 
  It represents an abstract view of the parallel introduction law of Jones \cite{jon83a}.
\<close>

lemma introduce_parallel: 
  assumes nonabort_i: "chaos \<sqsubseteq>  i"
  assumes nonabort_j: "chaos \<sqsubseteq>  j"
  shows "c \<iinter> d \<sqsubseteq>  (j \<iinter> (c // i)) \<parallel> (i \<iinter> (d // j))"
proof -
  have a: "c \<sqsubseteq> (c // i) \<parallel> i" using nonabort_i nonabort_j rely_quotient by auto
  have b: "d \<sqsubseteq> j \<parallel> (d // j)" using rely_quotient par_commute 
    by (simp add: nonabort_j) 
  have "c \<iinter> d \<sqsubseteq>  ((c // i) \<parallel> i) \<iinter> ( j \<parallel> (d // j))" using a b by (metis conj_mono) 
  also have interchange: "c \<iinter> d \<sqsubseteq>  ((c // i) \<iinter> j) \<parallel> ( i \<iinter> (d // j))" 
   using parallel_interchange refine_trans calculation by blast 
  show ?thesis using interchange by (simp add: local.conj_commute) 
qed

text \<open>
  Rely quotients satisfy a range of distribution properties with respect
  to the other operators.
\<close>

lemma distribute_rely_conjunction: 
  assumes nonabort_i: "chaos \<sqsubseteq>  i"
  shows "(c \<iinter> d) // i  \<sqsubseteq>  (c // i) \<iinter> (d // i)"
proof -
  have "c \<iinter> d \<sqsubseteq> ((c // i) \<parallel> i) \<iinter> ((d // i) \<parallel> i)" using conj_mono rely_quotient
    by (simp add: nonabort_i) 
  then have "c \<iinter> d \<sqsubseteq> ((c // i) \<iinter> (d // i)) \<parallel> (i \<iinter> i)"
    by (metis parallel_interchange refine_trans) 
  then have "c \<iinter> d \<sqsubseteq> ((c // i) \<iinter> (d // i)) \<parallel> i" by (metis conj_idem) 
  thus ?thesis using rely_refinement by (simp add: nonabort_i)
qed

lemma distribute_rely_choice: 
  assumes nonabort_i: "chaos \<sqsubseteq>  i"
  shows "(c \<sqinter> d) // i  \<sqsubseteq>  (c // i) \<sqinter> (d // i)"
proof -
  have "c \<sqinter> d \<sqsubseteq> ((c // i) \<parallel> i) \<sqinter> ((d // i) \<parallel> i)" 
    by (metis nonabort_i inf_mono rely_quotient) 
  then have "c \<sqinter> d \<sqsubseteq> ((c // i) \<sqinter> (d // i)) \<parallel> i" by (metis inf_par_distrib) 
  thus ?thesis by (metis nonabort_i rely_refinement) 
qed

lemma distribute_rely_parallel1: 
  assumes nonabort_i: "chaos \<sqsubseteq>  i"
  assumes nonabort_j: "chaos \<sqsubseteq>  j"
  shows "(c \<parallel> d) // (i \<parallel> j)  \<sqsubseteq>  (c // i) \<parallel> (d // j)"
proof -
  have "(c \<parallel> d) \<sqsubseteq> ((c // i) \<parallel> i) \<parallel> ((d // j) \<parallel> j)" 
    using par_mono rely_quotient nonabort_i nonabort_j by simp
  then have "(c \<parallel> d) \<sqsubseteq> (c // i) \<parallel> (d // j) \<parallel> j \<parallel> i" by (metis par_assoc par_commute) 
  thus ?thesis using par_assoc par_commute rely_refinement
    by (metis nonabort_i nonabort_j par_nonabort) 
qed

lemma distribute_rely_parallel2: 
  assumes nonabort_i: "chaos \<sqsubseteq> i"
  assumes i_par_i: "i \<parallel> i \<sqsubseteq> i"
  shows "(c \<parallel> d) // i  \<sqsubseteq>  (c // i) \<parallel> (d // i)"
proof -
  have "(c \<parallel> d) // i \<sqsubseteq> ((c \<parallel> d) // (i \<parallel> i))" using assms(1) using weaken_rely
    by (simp add: i_par_i par_nonabort)
  thus ?thesis by (metis distribute_rely_parallel1 refine_trans nonabort_i) 
qed

lemma distribute_rely_sequential: 
  assumes nonabort_i: "chaos \<sqsubseteq> i"
  assumes "(\<forall> c. (\<forall> d. ((c \<parallel> i);(d \<parallel> i) \<sqsubseteq> (c;d) \<parallel> i)))"
  shows "(c;d) // i \<sqsubseteq> (c // i);(d // i)"
proof -
  have "c;d \<sqsubseteq> ((c // i) \<parallel> i);((d // i) \<parallel> i)" 
    by (metis rely_quotient nonabort_i seq_mono) 
  then have "c;d \<sqsubseteq> (c // i) ; (d // i) \<parallel> i" using assms(2) by (metis refine_trans)
  thus ?thesis by (metis rely_refinement nonabort_i) 
qed

lemma distribute_rely_sequential_event: 
  assumes nonabort_i: "chaos \<sqsubseteq> i"
  assumes nonabort_j: "chaos \<sqsubseteq> j"
  assumes nonabort_e: "chaos \<sqsubseteq> e"
  assumes "(\<forall> c. (\<forall> d. ((c \<parallel> i);e;(d \<parallel> j) \<sqsubseteq> (c;e;d) \<parallel> (i;e;j))))" 
  shows "(c;e;d) // (i;e;j) \<sqsubseteq> (c // i);e;(d // j)"
proof -
  have "c;e;d \<sqsubseteq> ((c // i) \<parallel> i);e;((d // j) \<parallel> j)" 
    by (metis order.refl rely_quotient nonabort_i nonabort_j seq_mono) 
  then have "c;e;d \<sqsubseteq> ((c // i);e;(d // j)) \<parallel> (i;e;j)" using assms 
    by (metis refine_trans) 
  thus ?thesis using rely_refinement nonabort_i nonabort_j nonabort_e
    by (simp add: Inf_lower local.rely_quotient_def)
qed

lemma introduce_parallel_with_rely: 
  assumes nonabort_i: "chaos \<sqsubseteq> i"
  assumes nonabort_j0: "chaos \<sqsubseteq>  j\<^sub>0"
  assumes nonabort_j1: "chaos \<sqsubseteq>  j\<^sub>1"
  shows "(c \<iinter> d) // i \<sqsubseteq> (j\<^sub>1 \<iinter> (c // (j\<^sub>0 \<parallel> i))) \<parallel> (j\<^sub>0 \<iinter> (d // (j\<^sub>1 \<parallel> i)))"
proof -
  have "(c \<iinter> d) // i \<sqsubseteq> (c // i) \<iinter> (d // i)" 
    by (metis distribute_rely_conjunction nonabort_i) 
  then have "(c \<iinter> d) // i \<sqsubseteq> (j\<^sub>1 \<iinter> ((c // i) // j\<^sub>0)) \<parallel> (j\<^sub>0 \<iinter> ((d // i) // j\<^sub>1))" 
    by (metis introduce_parallel nonabort_j0 nonabort_j1 inf_assoc inf.absorb_iff1) 
  thus ?thesis by (simp add: nested_rely nonabort_i) 
qed

lemma introduce_parallel_with_rely_guarantee: 
  assumes nonabort_i: "chaos \<sqsubseteq>  i"
  assumes nonabort_j0: "chaos \<sqsubseteq>  j\<^sub>0"
  assumes nonabort_j1: "chaos \<sqsubseteq>  j\<^sub>1"
  shows "(j\<^sub>1 \<parallel> j\<^sub>0) \<iinter> (c \<iinter> d) // i \<sqsubseteq> (j\<^sub>1 \<iinter> (c // (j\<^sub>0 \<parallel> i))) \<parallel> (j\<^sub>0 \<iinter> (d // (j\<^sub>1 \<parallel> i)))"
proof -
  have "(j\<^sub>1 \<parallel> j\<^sub>0) \<iinter> (c \<iinter> d) // i \<sqsubseteq> (j\<^sub>1 \<parallel> j\<^sub>0) \<iinter> ((j\<^sub>1 \<iinter> (c // (j\<^sub>0 \<parallel> i))) \<parallel> (j\<^sub>0 \<iinter> (d // (j\<^sub>1 \<parallel> i))))" 
    by (metis introduce_parallel_with_rely nonabort_i nonabort_j0 nonabort_j1 
        conj_mono order.refl) 
  also have "... \<sqsubseteq> (j\<^sub>1 \<iinter> j\<^sub>1 \<iinter> (c // (j\<^sub>0 \<parallel> i))) \<parallel> (j\<^sub>0 \<iinter> j\<^sub>0 \<iinter> (d // (j\<^sub>1 \<parallel> i)))" 
    by (metis conj_assoc parallel_interchange) 
  finally show ?thesis by (metis conj_idem)
qed

lemma wrap_rely_guar:
  assumes nonabort_rg: "chaos \<sqsubseteq> rg" 
  and skippable: "rg \<sqsubseteq> skip"
  shows "c \<sqsubseteq> rg \<iinter> c // rg"
proof -
  have "c = c // skip" by (simp add: quotient_identity)
  also have "... \<sqsubseteq> c // rg" by (simp add: skippable weaken_rely nonabort_rg)
  also have "... \<sqsubseteq> rg \<iinter> c // rg" using conjoin_non_aborting conj_commute nonabort_rg 
    by auto
  finally show "c \<sqsubseteq> rg \<iinter> c // rg" .
qed

end


locale rely_distrib_iteration = rely_distrib + iteration_finite_conjunctive

begin

lemma distribute_rely_iteration: 
  assumes nonabort_i: "chaos \<sqsubseteq> i"
  assumes "(\<forall> c. (\<forall> d. ((c \<parallel> i);(d \<parallel> i) \<sqsubseteq> (c;d) \<parallel> i)))"
  shows "(c\<^sup>\<omega>;d) // i \<sqsubseteq> (c // i)\<^sup>\<omega>;(d // i)"
proof -
  have "d \<sqinter> c ; ((c // i)\<^sup>\<omega>;(d // i) \<parallel> i) \<sqsubseteq> ((d // i) \<parallel> i) \<sqinter> ((c // i) \<parallel> i);((c // i)\<^sup>\<omega>;(d // i) \<parallel> i)"
    by (metis inf_mono order.refl rely_quotient nonabort_i seq_mono) 
  also have "... \<sqsubseteq> ((d // i) \<parallel> i) \<sqinter> ((c // i);(c // i)\<^sup>\<omega>;(d // i) \<parallel> i )"
    using assms inf_mono_right seq_assoc by fastforce
  also have "... \<sqsubseteq> ((d // i) \<sqinter> (c // i);(c // i)\<^sup>\<omega>;(d // i)) \<parallel> i"
    by (simp add: inf_par_distrib) 
  also have "... = ((c // i)\<^sup>\<omega>;(d // i)) \<parallel> i"
    by (metis iter_unfold inf_seq_distrib seq_nil_left)
  finally show ?thesis by (metis rely_refinement nonabort_i iter_induct) 
qed

end

end
