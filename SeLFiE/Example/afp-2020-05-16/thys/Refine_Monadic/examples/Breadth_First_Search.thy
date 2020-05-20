section \<open>Breadth First Search\<close>
theory Breadth_First_Search
imports "../Refine_Monadic"
begin
  
text \<open>
  This is a slightly modified version of Task~5 of our submission to
  the VSTTE 2011 verification competition 
  (@{url "https://sites.google.com/site/vstte2012/compet"}). The task was to
  formalize a breadth-first-search algorithm.
\<close>

text \<open>
  With Isabelle's locale-construct, we put ourselves into a context where 
  the \<open>succ\<close>-function is fixed. 
  We assume finitely branching graphs here, as our
  foreach-construct is only defined for finite sets.
\<close>
locale Graph =
  fixes succ :: "'vertex \<Rightarrow> 'vertex set"
  assumes [simp, intro!]: "finite (succ v)"
begin


  subsection \<open>Distances in a Graph\<close>
  text \<open>
    We start over by defining the basic notions of paths and shortest paths.
\<close>

  text \<open>A path is expressed by the \<open>dist\<close>-predicate. Intuitively,
    \<open>dist v d v'\<close> means that there is a path of length \<open>d\<close>
    between \<open>v\<close> and \<open>v'\<close>.

    The definition of the \<open>dist\<close>-predicate is done inductively, i.e.,
    as the least solution of the following constraints:
\<close>
  inductive dist :: "'vertex \<Rightarrow> nat \<Rightarrow> 'vertex \<Rightarrow> bool" where
    dist_z: "dist v 0 v" |
    dist_suc: "\<lbrakk>dist v d vh; v' \<in> succ vh \<rbrakk> \<Longrightarrow> dist v (Suc d) v'"

  text \<open>
    Next, we define a predicate that expresses that the shortest path between
    \<open>v\<close> and \<open>v'\<close> has length \<open>d\<close>.
    This is the case if there is a path of length \<open>d\<close>, but there
    is no shorter path.
\<close>
  definition "min_dist v v' = (LEAST d. dist v d v')"
  definition "conn v v' = (\<exists>d. dist v d v')"

  subsubsection \<open>Properties\<close>
  text \<open>
    In this subsection, we prove some properties of paths.
\<close>

  lemma
    shows connI[intro]: "dist v d v' \<Longrightarrow> conn v v'"
      and connI_id[intro]: "conn v v"
      and connI_succ[intro]: "conn v v' \<Longrightarrow> v'' \<in> succ v' \<Longrightarrow> conn v v''"
    by (auto simp: conn_def intro: dist_suc dist_z)

  lemma min_distI2: 
    "\<lbrakk> conn v v' ; \<And>d. \<lbrakk> dist v d v'; \<And>d'. dist v d' v' \<Longrightarrow> d \<le> d' \<rbrakk> \<Longrightarrow> Q d \<rbrakk> 
      \<Longrightarrow> Q (min_dist v v')"
    unfolding min_dist_def
    by (rule LeastI2_wellorder[where Q=Q and a="SOME d. dist v d v'"])
       (auto simp: conn_def intro: someI)

  lemma min_distI_eq:
    "\<lbrakk> dist v d v'; \<And>d'. dist v d' v' \<Longrightarrow> d \<le> d' \<rbrakk> \<Longrightarrow> min_dist v v' = d"
    by (force intro: min_distI2 simp: conn_def)

  text \<open>Two nodes are connected by a path of length \<open>0\<close>, 
    iff they are equal.\<close>
  lemma dist_z_iff[simp]: "dist v 0 v' \<longleftrightarrow> v'=v"
    by (auto elim: dist.cases intro: dist.intros)

  text \<open>The same holds for \<open>min_dist\<close>, i.e., 
    the shortest path between two nodes has length \<open>0\<close>, 
    iff these nodes are equal.\<close>
  lemma min_dist_z[simp]: "min_dist v v = 0"
    by (rule min_distI2) (auto intro: dist_z)

  lemma min_dist_z_iff[simp]: "conn v v' \<Longrightarrow> min_dist v v' = 0 \<longleftrightarrow> v'=v" 
    by (rule min_distI2) (auto intro: dist_z)
    
  lemma min_dist_is_dist: "conn v v' \<Longrightarrow> dist v (min_dist v v') v'"
    by (auto intro: min_distI2)
  lemma min_dist_minD: "dist v d v' \<Longrightarrow> min_dist v v' \<le> d"
    by (auto intro: min_distI2)

  text \<open>We also provide introduction and destruction rules for the
    pattern \<open>min_dist v v' = Suc d\<close>.
\<close>

  lemma min_dist_succ: 
    "\<lbrakk> conn v v'; v'' \<in> succ v' \<rbrakk> \<Longrightarrow> min_dist v v'' \<le> Suc (min_dist v v') "
    by (rule min_distI2[where v'=v'])
       (auto elim: dist.cases intro!: min_dist_minD dist_suc)

  lemma min_dist_suc:
    assumes c: "conn v v'" "min_dist v v' = Suc d"
    shows "\<exists>v''. conn v v'' \<and> v' \<in> succ v'' \<and> min_dist v v'' = d"
  proof -
    from min_dist_is_dist[OF c(1)]
    have "min_dist v v' = Suc d \<longrightarrow> ?thesis"
    proof cases
      case (dist_suc d' v'') then show ?thesis
        using min_dist_succ[of v v'' v'] min_dist_minD[of v d v'']
        by (auto simp: connI)
    qed simp
    with c show ?thesis by simp
  qed

  text \<open>
    If there is a node with a shortest path of length \<open>d\<close>, 
    then, for any \<open>d'<d\<close>, there is also a node with a shortest path
    of length \<open>d'\<close>.
\<close>
  lemma min_dist_less:
    assumes "conn src v" "min_dist src v = d" and "d' < d"
    shows "\<exists>v'. conn src v' \<and> min_dist src v' = d'"
    using assms
  proof (induct d arbitrary: v)
    case (Suc d) with min_dist_suc[of src v] show ?case
      by (cases "d' = d") auto
  qed auto

  text \<open>
    Lemma \<open>min_dist_less\<close> can be weakened to \<open>d'\<le>d\<close>.
\<close>

  corollary min_dist_le:
    assumes c: "conn src v" and d': "d' \<le> min_dist src v"
    shows "\<exists>v'. conn src v' \<and> min_dist src v' = d'"
    using min_dist_less[OF c, of "min_dist src v" d'] d' c
    by (auto simp: le_less)
  
  subsection \<open>Invariants\<close>
  text \<open>
    In our framework, it is convenient to annotate the invariants and 
    auxiliary assertions into the program. Thus, we have to define the
    invariants first.
\<close>

  text \<open>
    The invariant for the outer loop is split into two parts:
    The first part already holds before 
    the \<open>if C={}\<close> check, the second part only holds again 
    at the end of the loop body.
\<close>

  text \<open>
    The first part of the invariant, \<open>bfs_invar'\<close>,
    intuitively states the following:
    If the loop is not {\em break}ed, then we have:
    \begin{itemize}
      \item The next-node set \<open>N\<close> is a subset of \<open>V\<close>, and
        the destination node is not contained into \<open>V-(C\<union>N)\<close>,
      \item all nodes in the current-node set \<open>C\<close> have a shortest
        path of length \<open>d\<close>,
      \item all nodes in the next-node set \<open>N\<close> have a shortest path
        of length \<open>d+1\<close>,
      \item all nodes in the visited set \<open>V\<close> have a shortest path
        of length at most \<open>d+1\<close>,
      \item all nodes with a path shorter than \<open>d\<close> are already in 
        \<open>V\<close>, and
      \item all nodes with a shortest path of length \<open>d+1\<close> are either
        in the next-node set \<open>N\<close>, or they are undiscovered successors
        of a node in the current-node set.
    \end{itemize}
    
    If the loop has been {\em break}ed, \<open>d\<close> is the distance of the
    shortest path between \<open>src\<close> and \<open>dst\<close>.
\<close>

  definition "bfs_invar' src dst \<sigma> \<equiv> let (f,V,C,N,d)=\<sigma> in
    (\<not>f \<longrightarrow> (
      N \<subseteq> V \<and> dst \<notin> V - (C \<union> N) \<and>
      (\<forall>v\<in>C. conn src v \<and> min_dist src v = d) \<and>
      (\<forall>v\<in>N. conn src v \<and> min_dist src v = Suc d) \<and>
      (\<forall>v\<in>V. conn src v \<and> min_dist src v \<le> Suc d) \<and>
      (\<forall>v. conn src v \<and> min_dist src v \<le> d \<longrightarrow> v \<in> V) \<and>
      (\<forall>v. conn src v \<and> min_dist src v = Suc d \<longrightarrow> v \<in> N \<union> ((\<Union>(succ`C)) - V))
    )) \<and> (
    f \<longrightarrow> conn src dst \<and> min_dist src dst = d
    )"

  text \<open>
    The second part of the invariant, \<open>empty_assm\<close>, just states 
    that \<open>C\<close> can only be empty if \<open>N\<close> is also empty.
\<close>
  definition "empty_assm \<sigma> \<equiv> let (f,V,C,N,d)=\<sigma> in
    C={} \<longrightarrow> N={}"

  text \<open>
    Finally, we define the invariant of the outer loop, \<open>bfs_invar\<close>, 
    as the conjunction of both parts:
\<close>
  definition "bfs_invar src dst \<sigma> \<equiv> bfs_invar' src dst \<sigma> \<and> 
    empty_assm \<sigma>"

  text \<open>
    The invariant of the inner foreach-loop states that
    the successors that have already been processed (\<open>succ v - it\<close>),
    have been added to \<open>V\<close> and have also been added to 
    \<open>N'\<close> if they are not in \<open>V\<close>.
\<close>
  definition "FE_invar V N v it \<sigma> \<equiv> let (V',N')=\<sigma> in 
    V'=V \<union> (succ v - it) \<and>
    N'=N \<union> ((succ v - it) - V)"

  subsection \<open>Algorithm\<close>
  text \<open>
    The following algorithm is a straightforward transcription of the 
    algorithm given in the assignment to the monadic style featured by our 
    framework.
    We briefly explain the (mainly syntactic) differences:
    \begin{itemize}
      \item The initialization of the variables occur after the loop in
          our formulation. This is just a syntactic difference, as our loop
          construct has the form \<open>WHILEI I c f \<sigma>\<^sub>0\<close>, where \<open>\<sigma>\<^sub>0\<close>
          is the initial state, and \<open>I\<close> is the loop invariant;
      \item We translated the textual specification 
        {\em remove one vertex \<open>v\<close> from \<open>C\<close>} as accurately as
        possible: The statement \<open>v \<leftarrow> SPEC (\<lambda>v. v\<in>C)\<close> 
        nondeterministically assigns a node from \<open>C\<close> to \<open>v\<close>, 
        that is then removed in the next statement;
      \item In our monad, we have no notion of loop-breaking (yet). Hence we
        added an additional boolean variable \<open>f\<close> that indicates that
        the loop shall terminate. The \<open>RETURN\<close>-statements used in our
        program are the return-operator of the monad, and must not be mixed up
        with the return-statement given in the original program, that is 
        modeled by breaking the loop. The if-statement after the loop takes
        care to return the right value;
      \item We added an else-branch to the if-statement that checks
        whether we reached the destination node;
      \item We added an assertion of the first part of the invariant to the
        program text, moreover, we annotated invariants at the loops.
        We also added an assertion \<open>w\<notin>N\<close> into the inner loop. This
        is merely an optimization, that will allow us to implement the
        insert operation more efficiently;
      \item Each conditional branch in the loop body ends with a 
        \<open>RETURN\<close>-statement. This is required by the monadic style;
      \item Failure is modeled by an option-datatype. The result 
        \<open>Some d\<close> means that the integer \<open>d\<close> is returned,
        the result \<open>None\<close> means that a failure is returned.
    \end{itemize}
\<close>

  text_raw \<open>\clearpage\<close>

  definition bfs :: "'vertex \<Rightarrow> 'vertex \<Rightarrow> 
    (nat option nres)"
    where "bfs src dst \<equiv> do {
    (f,_,_,_,d) \<leftarrow> WHILEI (bfs_invar src dst) (\<lambda>(f,V,C,N,d). f=False \<and> C\<noteq>{})
      (\<lambda>(f,V,C,N,d). do {
        v \<leftarrow> SPEC (\<lambda>v. v\<in>C); let C = C-{v};
        if v=dst then RETURN (True,{},{},{},d)
        else do {
          (V,N) \<leftarrow> FOREACHi (FE_invar V N v) (succ v) (\<lambda>w (V,N). 
            if (w\<notin>V) then do { 
              ASSERT (w\<notin>N);
              RETURN (insert w V, insert w N) 
            } else RETURN (V,N)
          ) (V,N);
          ASSERT (bfs_invar' src dst (f,V,C,N,d));
          if (C={}) then do {
            let C=N; 
            let N={}; 
            let d=d+1;
            RETURN (f,V,C,N,d)
          } else RETURN (f,V,C,N,d)
        }
      })
      (False,{src},{src},{},0::nat);
    if f then RETURN (Some d) else RETURN None
    }"

  subsection "Verification Tasks"
  text \<open>
    In order to make the proof more readable, we have extracted the
    difficult verification conditions and proved them in separate lemmas.
    The other verification conditions are proved automatically by Isabelle/HOL
    during the proof of the main theorem.

    Due to the timing constraints of the competition, the verification 
    conditions are mostly proved in Isabelle's apply-style, that is faster
    to write for the experienced user, but harder to read by a human.

    Exemplarily, we formulated the last proof in the proof language 
    {\em Isar}, that allows one to write human-readable proofs and verify
    them with Isabelle/HOL.
\<close>

  text \<open>
    The first part of the invariant is preserved if we take a node from 
    \<open>C\<close>, and add its successors that are not in \<open>V\<close> to 
    \<open>N\<close>.
    This is the verification condition for the assertion after the 
    foreach-loop.
\<close>
  lemma invar_succ_step:
    assumes "bfs_invar' src dst (False, V, C, N, d)"
    assumes "v\<in>C"
    assumes "v\<noteq>dst"
    shows "bfs_invar' src dst 
            (False, V \<union> succ v, C - {v}, N \<union> (succ v - V), d)"
    using assms
  proof (simp (no_asm_use) add: bfs_invar'_def, intro conjI, goal_cases)
    case 6 then show ?case
      by (metis Un_iff Diff_iff connI_succ le_SucE min_dist_succ)
  next
    case 7 then show ?case
      by (metis Un_iff connI_succ min_dist_succ)
  qed blast+

  text \<open>
    The first part of the invariant is preserved if the 
    \<open>if C={}\<close>-statement is executed.
    This is the verification condition for the 
    loop-invariant. Note that preservation of the second part of the 
    invariant is proven easily inside the main proof.
\<close>
  lemma invar_empty_step: 
    assumes "bfs_invar' src dst (False, V, {}, N, d)"
    shows "bfs_invar' src dst (False, V, N, {}, Suc d)"
    using assms
  proof (simp (no_asm_use) add: bfs_invar'_def, intro conjI impI allI, goal_cases)
    case 3 then show ?case
      by (metis le_SucI)
  next
    case 4 then show ?case
      by (metis le_SucE subsetD)
  next
    case (5 v) then show ?case
      using min_dist_suc[of src v "Suc d"] by metis
  next
    case 6 then show ?case
      by (metis Suc_n_not_le_n)
  qed blast+

  text \<open>The invariant holds initially.\<close>
  lemma invar_init: "bfs_invar src dst (False, {src}, {src}, {}, 0)"
    by (auto simp: bfs_invar_def bfs_invar'_def empty_assm_def)
       (metis min_dist_suc min_dist_z_iff)

  text \<open>The invariant is preserved if we break the loop.\<close>
  lemma invar_break: 
    assumes "bfs_invar src dst (False, V, C, N, d)"
    assumes "dst\<in>C"
    shows "bfs_invar src dst (True, {}, {}, {}, d)"
    using assms unfolding bfs_invar_def bfs_invar'_def empty_assm_def
    by auto

  text \<open>If we have {\em break}ed the loop, the invariant implies
    that we, indeed, returned the shortest path.\<close>
  lemma invar_final_succeed:
    assumes "bfs_invar' src dst (True, V, C, N, d)"  
    shows "min_dist src dst = d"
    using assms unfolding bfs_invar'_def
    by auto

  text \<open>If the loop terminated normally, there is no path between 
    \<open>src\<close> and \<open>dst\<close>. 

    The lemma is formulated as deriving a contradiction from the fact
    that there is a path and the loop terminated normally.

    Note the proof language {\em Isar} that was used here.
    It allows one to write human-readable proofs in a theorem prover.
\<close>
  lemma invar_final_fail: 
    assumes C: "conn src dst" \<comment> \<open>There is a path between 
      @{text "src"} and @{text "dst"}.\<close>
    assumes INV: "bfs_invar' src dst (False, V, {}, {}, d)"
    shows False
  proof -
    txt \<open>We make a case-distinction whether \<open>d'\<le>d\<close>:\<close>
    have "min_dist src dst \<le> d \<or> d + 1 \<le> min_dist src dst" by auto
    moreover {
      txt \<open>Due to the invariant, any node with a path of 
        length at most \<open>d\<close> is contained in \<open>V\<close>
\<close>
      from INV have "\<forall>v. conn src v \<and> min_dist src v \<le> d \<longrightarrow> v\<in>V"
        unfolding bfs_invar'_def by auto
      moreover
      txt \<open>This applies in the first case, hence we obtain that 
        \<open>dst\<in>V\<close>\<close>
      assume A: "min_dist src dst \<le> d"
      moreover from C have "dist src (min_dist src dst) dst" 
        by (blast intro: min_dist_is_dist)
      ultimately have "dst\<in>V" by blast
      txt \<open>However, as \<open>C\<close> and \<open>N\<close> are empty, the invariant
        also implies that \<open>dst\<close> is not in \<open>V\<close>:\<close>
      moreover from INV have "dst\<notin>V" unfolding bfs_invar'_def by auto
      txt \<open>This yields a contradiction:\<close>
      ultimately have False by blast
    } moreover {
      txt \<open>In the case \<open>d+1 \<le> d'\<close>, we also obtain a node
        that has a shortest path of length \<open>d+1\<close>:\<close>
      assume "d+1 \<le> min_dist src dst"
      with min_dist_le[OF C] obtain v' where 
        "conn src v'" "min_dist src v' = d + 1"
        by auto
      txt \<open>However, the invariant states that such nodes are either in
        \<open>N\<close> or are successors of \<open>C\<close>. As \<open>N\<close> 
        and \<open>C\<close> are both empty, we again get a contradiction.\<close>
      with INV have False unfolding bfs_invar'_def by auto
    } ultimately show ?thesis by blast
  qed

  text \<open>
    Finally, we prove our algorithm correct:
    The following theorem solves both verification tasks.

    Note that a proposition of the form \<open>S \<sqsubseteq> SPEC \<Phi>\<close> states partial 
    correctness in our framework, i.e., \<open>S\<close> refines the 
    specification \<open>\<Phi>\<close>.

    The actual specification that we prove here
    precisely reflects the two verification tasks: {\em If the algorithm fails,
    there is no path between \<open>src\<close> and \<open>dst\<close>, otherwise
    it returns the length of the shortest path.}

    The proof of this theorem first applies the verification condition 
    generator (\<open>apply (intro refine_vcg)\<close>), and then uses the
    lemmas proved beforehand to discharge the verification conditions.
    During the \<open>auto\<close>-methods, some trivial verification conditions,
    e.g., those concerning the invariant of the inner loop, are discharged
    automatically.
    During the proof, we gradually unfold the definition of the loop
    invariant.
\<close>
  definition "bfs_spec src dst \<equiv> SPEC (
    \<lambda>r. case r of None \<Rightarrow> \<not> conn src dst
              | Some d \<Rightarrow> conn src dst \<and> min_dist src dst = d)"
  theorem bfs_correct: "bfs src dst \<le> bfs_spec src dst"
    unfolding bfs_def bfs_spec_def
    apply (intro refine_vcg)

    unfolding FE_invar_def
    apply (auto simp: 
      intro: invar_init invar_break )

    unfolding bfs_invar_def 
    apply (auto simp: 
      intro: invar_succ_step invar_empty_step invar_final_succeed)

    unfolding empty_assm_def
    apply (auto intro: invar_final_fail)

    unfolding bfs_invar'_def
    apply auto
    done

end

end
