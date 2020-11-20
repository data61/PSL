(*<*)
theory KBPsAlg
imports KBPsAuto DFS MapOps
begin
(*>*)

subsection\<open>An algorithm for automata synthesis\<close>

text\<open>

\label{sec:kbps-alg}

We now show how to construct the automaton defined by @{term
"mkAutoSim"} (\S\ref{sec:kbps-automata-synthesis-alg}) using the DFS
of \S\ref{sec:dfs}.

From here on we assume that the environment consists of only a finite
set of states:

\<close>

locale FiniteEnvironment =
  Environment jkbp envInit envAction envTrans envVal envObs
    for jkbp :: "('a, 'p, 'aAct) JKBP"
    and envInit :: "('s :: finite) list"
    and envAction :: "'s \<Rightarrow> 'eAct list"
    and envTrans :: "'eAct \<Rightarrow> ('a \<Rightarrow> 'aAct) \<Rightarrow> 's \<Rightarrow> 's"
    and envVal :: "'s \<Rightarrow> 'p \<Rightarrow> bool"
    and envObs :: "'a \<Rightarrow> 's \<Rightarrow> 'obs"

text_raw\<open>
\begin{figure}[p]
\begin{isabellebody}%
\<close>
locale Algorithm =
  FiniteEnvironment jkbp envInit envAction envTrans envVal envObs
+ AlgSimIncrEnvironment jkbp envInit envAction envTrans envVal jview envObs
               jviewInit jviewIncr
               simf simRels simVal simAbs simObs simInit simTrans simAction
    for jkbp :: "('a, 'p, 'aAct) JKBP"
    and envInit :: "('s :: finite) list"
    and envAction :: "'s \<Rightarrow> 'eAct list"
    and envTrans :: "'eAct \<Rightarrow> ('a \<Rightarrow> 'aAct) \<Rightarrow> 's \<Rightarrow> 's"
    and envVal :: "'s \<Rightarrow> 'p \<Rightarrow> bool"
    and jview :: "('a, 's, 'tobs) JointView"

    and envObs :: "'a \<Rightarrow> 's \<Rightarrow> 'obs"
    and jviewInit :: "('a, 'obs, 'tobs) InitialIncrJointView"
    and jviewIncr :: "('a, 'obs, 'tobs) IncrJointView"

    and simf :: "'s Trace \<Rightarrow> 'ss :: finite"
    and simRels :: "'a \<Rightarrow> 'ss Relation"
    and simVal :: "'ss \<Rightarrow> 'p \<Rightarrow> bool"

    and simAbs :: "'rep \<Rightarrow> 'ss set"

    and simObs :: "'a \<Rightarrow> 'rep \<Rightarrow> 'obs"
    and simInit :: "'a \<Rightarrow> 'obs \<Rightarrow> 'rep"
    and simTrans :: "'a \<Rightarrow> 'rep \<Rightarrow> 'rep list"
    and simAction :: "'a \<Rightarrow> 'rep \<Rightarrow> 'aAct list"

+ fixes aOps :: "('ma, 'rep, 'aAct list) MapOps"
    and tOps :: "('mt, 'rep \<times> 'obs, 'rep) MapOps"

  assumes aOps: "MapOps simAbs jkbpSEC aOps"
      and tOps: "MapOps (\<lambda>k. (simAbs (fst k), snd k)) (jkbpSEC \<times> UNIV) tOps"
text_raw\<open>
  \end{isabellebody}%
  \caption{The \<open>Algorithm\<close> locale.}
  \label{fig:kbps-alg-alg-locale}
\end{figure}
\<close>

text (in Algorithm) \<open>

The @{term "Algorithm"} locale, shown in
Figure~\ref{fig:kbps-alg-alg-locale}, also extends the @{term
"AlgSimIncrEnvironment"} locale with a pair of finite map operations:
@{term "aOps"} is used to map automata states to lists of actions, and
@{term "tOps"} handles simulated transitions. In both cases the maps
are only required to work on the abstract domain of simulated
canonical traces. Note also that the space of simulated equivalence
classes of type @{typ "'ss"} must be finite, but there is no
restriction on the representation type @{typ "'rep"}.

We develop the algorithm for a single, fixed agent, which requires us
to define a new locale @{term "AlgorithmForAgent"} that extends \<open>Algorithm\<close> with an extra parameter designating the agent:

\<close>

locale AlgorithmForAgent =
  Algorithm jkbp envInit envAction envTrans envVal jview envObs
            jviewInit jviewIncr
            simf simRels simVal simAbs simObs simInit simTrans simAction
            aOps tOps(*<*)
    for jkbp :: "('a, 'p, 'aAct) JKBP"
    and envInit :: "('s :: finite) list"
    and envAction :: "'s \<Rightarrow> 'eAct list"
    and envTrans :: "'eAct \<Rightarrow> ('a \<Rightarrow> 'aAct) \<Rightarrow> 's \<Rightarrow> 's"
    and envVal :: "'s \<Rightarrow> 'p \<Rightarrow> bool"
    and jview :: "('a, 's, 'tobs) JointView"

    and envObs :: "'a \<Rightarrow> 's \<Rightarrow> 'obs"
    and jviewInit :: "('a, 'obs, 'tobs) InitialIncrJointView"
    and jviewIncr :: "('a, 'obs, 'tobs) IncrJointView"

    and simf :: "'s Trace \<Rightarrow> 'ss :: finite"
    and simRels :: "'a \<Rightarrow> 'ss Relation"
    and simVal :: "'ss \<Rightarrow> 'p \<Rightarrow> bool"

    and simAbs :: "'rep \<Rightarrow> 'ss set"

    and simObs :: "'a \<Rightarrow> 'rep \<Rightarrow> 'obs"
    and simInit :: "'a \<Rightarrow> 'obs \<Rightarrow> 'rep"
    and simTrans :: "'a \<Rightarrow> 'rep \<Rightarrow> 'rep list"
    and simAction :: "'a \<Rightarrow> 'rep \<Rightarrow> 'aAct list"

    and aOps :: "('ma, 'rep, 'aAct list) MapOps"
    and tOps :: "('mt, 'rep \<times> 'obs, 'rep) MapOps"
(*>*)

  \<comment> \<open>...\<close>
+ fixes a :: "'a"

subsubsection\<open>DFS operations\<close>

text\<open>

We represent the automaton under construction using a record:

\<close>

record ('ma, 'mt) AlgState =
  aActs :: "'ma"
  aTrans :: "'mt"

context AlgorithmForAgent
begin

text\<open>

We instantiate the DFS theory with the following functions.

A node is an equivalence class of represented simulated traces.

\<close>

definition k_isNode :: "'rep \<Rightarrow> bool" where
  "k_isNode ec \<equiv> simAbs ec \<in> sim_equiv_class a ` jkbpC"

text\<open>

The successors of a node are those produced by the simulated
transition function.

\<close>

abbreviation k_succs :: "'rep \<Rightarrow> 'rep list" where
  "k_succs \<equiv> simTrans a"

text\<open>

The initial automaton has no transitions and no actions.

\<close>

definition k_empt :: "('ma, 'mt) AlgState" where
  "k_empt \<equiv> \<lparr> aActs = empty aOps, aTrans = empty tOps \<rparr>"

text\<open>

We use the domain of the action map to track the set of nodes the DFS
has visited.

\<close>

definition k_memb :: "'rep \<Rightarrow> ('ma, 'mt) AlgState \<Rightarrow> bool" where
  "k_memb s A \<equiv> isSome (lookup aOps (aActs A) s)"

text\<open>

We integrate a new equivalence class into the automaton by updating
the action and transition maps:

\<close>

definition actsUpdate :: "'rep \<Rightarrow> ('ma, 'mt) AlgState \<Rightarrow> 'ma" where
  "actsUpdate ec A \<equiv> update aOps ec (simAction a ec) (aActs A)"

definition transUpdate :: "'rep \<Rightarrow> 'rep \<Rightarrow> 'mt \<Rightarrow> 'mt" where
  "transUpdate ec ec' at \<equiv> update tOps (ec, simObs a ec') ec' at"

definition k_ins :: "'rep \<Rightarrow> ('ma, 'mt) AlgState \<Rightarrow> ('ma, 'mt) AlgState" where
  "k_ins ec A \<equiv> \<lparr> aActs = actsUpdate ec A,
                   aTrans = foldr (transUpdate ec) (k_succs ec) (aTrans A) \<rparr>"

text\<open>

The required properties are straightforward to show.

\<close>

(*<*)

lemma k_isNode_cong:
  "simAbs ec' = simAbs ec \<Longrightarrow> k_isNode ec' \<longleftrightarrow> k_isNode ec"
  unfolding k_isNode_def by simp

lemma alg_MapOps_empty[simp]:
  "k_isNode ec \<Longrightarrow> lookup aOps (empty aOps) ec = None"
  "k_isNode (fst k) \<Longrightarrow> lookup tOps (empty tOps) k = None"
  unfolding k_isNode_def
  using MapOps_emptyD[OF _ aOps] MapOps_emptyD[OF _ tOps] by blast+

lemma alg_aOps_lookup_update[simp]:
  "\<lbrakk> k_isNode ec; k_isNode ec' \<rbrakk> \<Longrightarrow> lookup aOps (update aOps ec e M) ec' = (if simAbs ec' = simAbs ec then Some e else lookup aOps M ec')"
  unfolding k_isNode_def
  using MapOps_lookup_updateD[OF _ _ aOps] by blast

lemma alg_tOps_lookup_update[simp]:
  "\<lbrakk> k_isNode (fst k); k_isNode (fst k') \<rbrakk> \<Longrightarrow> lookup tOps (update tOps k e M) k' = (if (simAbs (fst k'), snd k') = (simAbs (fst k), snd k) then Some e else lookup tOps M k')"
  unfolding k_isNode_def
  using MapOps_lookup_updateD[OF _ _ tOps] by blast

lemma k_succs_is_node[intro, simp]:
  assumes x: "k_isNode x"
  shows "list_all k_isNode (k_succs x)"
proof -
  from x obtain t
    where tC: "t \<in> jkbpC"
      and sx: "simAbs x = sim_equiv_class a t"
    unfolding k_isNode_def by blast
  have F: "\<And>y. y \<in> set (k_succs x) \<Longrightarrow> simAbs y \<in> simAbs ` set (k_succs x)" by simp
  show ?thesis
    using simTrans[rule_format, where a=a and t=t] tC sx
    unfolding k_isNode_def [abs_def]
    apply (auto iff: list_all_iff)
    apply (frule F)
    apply (auto)
    done
qed

lemma k_memb_empt[simp]:
  "k_isNode x \<Longrightarrow> \<not>k_memb x k_empt"
  unfolding k_memb_def k_empt_def by simp

(*>*)

subsubsection\<open>Algorithm invariant\<close>

text\<open>

The invariant for the automata construction is straightforward, viz
that at each step of the process the state represents an automaton
that concords with @{term "mkAutoSim"} on the visited equivalence
classes. We also need to know that the state has preserved the @{term
"MapOps"} invariants.

\<close>

definition k_invariant :: "('ma, 'mt) AlgState \<Rightarrow> bool" where
  "k_invariant A \<equiv>
      (\<forall>ec ec'. k_isNode ec \<and> k_isNode ec' \<and> simAbs ec' = simAbs ec
        \<longrightarrow> lookup aOps (aActs A) ec = lookup aOps (aActs A) ec')
    \<and> (\<forall>ec ec' obs. k_isNode ec \<and> k_isNode ec' \<and> simAbs ec' = simAbs ec
        \<longrightarrow> lookup tOps (aTrans A) (ec, obs) = lookup tOps (aTrans A) (ec', obs))
    \<and> (\<forall>ec. k_isNode ec \<and> k_memb ec A
        \<longrightarrow> (\<exists>acts. lookup aOps (aActs A) ec = Some acts
                   \<and> set acts = set (simAction a ec)))
    \<and> (\<forall>ec obs. k_isNode ec \<and> k_memb ec A
              \<and> obs \<in> simObs a ` set (simTrans a ec)
        \<longrightarrow> (\<exists>ec'. lookup tOps (aTrans A) (ec, obs) = Some ec'
                  \<and> simAbs ec' \<in> simAbs ` set (simTrans a ec)
                  \<and> simObs a ec' = obs))"
(*<*)

lemma k_invariantI[intro]:
  "\<lbrakk> \<And>ec ec'. \<lbrakk> k_isNode ec; k_isNode ec'; simAbs ec' = simAbs ec \<rbrakk>
       \<Longrightarrow> lookup aOps (aActs A) ec = lookup aOps (aActs A) ec';
     \<And>ec ec' obs. \<lbrakk> k_isNode ec; k_isNode ec'; simAbs ec' = simAbs ec \<rbrakk>
       \<Longrightarrow> lookup tOps (aTrans A) (ec, obs) = lookup tOps (aTrans A) (ec', obs);
     \<And>ec. \<lbrakk> k_isNode ec; k_memb ec A \<rbrakk>
       \<Longrightarrow> \<exists>acts. lookup aOps (aActs A) ec = Some acts \<and> set acts = set (simAction a ec);
     \<And>ec obs ecs'. \<lbrakk> k_isNode ec; k_memb ec A; obs \<in> simObs a ` set (simTrans a ec) \<rbrakk>
       \<Longrightarrow> \<exists>ec'. lookup tOps (aTrans A) (ec, obs) = Some ec'
               \<and> simAbs ec' \<in> simAbs ` set (simTrans a ec)
               \<and> simObs a ec' = obs \<rbrakk>
  \<Longrightarrow> k_invariant A"
  unfolding k_invariant_def by (simp (no_asm_simp))

lemma k_invariantAOD:
  "\<lbrakk> k_isNode ec; k_isNode ec'; simAbs ec' = simAbs ec; k_invariant A \<rbrakk>
     \<Longrightarrow> lookup aOps (aActs A) ec = lookup aOps (aActs A) ec'"
  unfolding k_invariant_def by blast

lemma k_invariantTOD:
  "\<lbrakk> k_isNode ec; k_isNode ec'; simAbs ec' = simAbs ec; k_invariant A \<rbrakk>
     \<Longrightarrow> lookup tOps (aTrans A) (ec, obs) = lookup tOps (aTrans A) (ec', obs)"
  unfolding k_invariant_def by blast

lemma k_invariantAD:
  "\<lbrakk> k_isNode ec; k_memb ec A; k_invariant A \<rbrakk>
     \<Longrightarrow> \<exists>acts. lookup aOps (aActs A) ec = Some acts \<and> set acts = set (simAction a ec)"
  unfolding k_invariant_def by blast

lemma k_invariantTD:
  "\<lbrakk> k_isNode ec; k_memb ec A; obs \<in> simObs a ` set (simTrans a ec); k_invariant A \<rbrakk>
     \<Longrightarrow> \<exists>ec'. lookup tOps (aTrans A) (ec, obs) = Some ec'
             \<and> simAbs ec' \<in> simAbs ` set (simTrans a ec)
             \<and> simObs a ec' = obs"
  unfolding k_invariant_def by blast

lemma k_invariant_empt[simp]:
  "k_invariant k_empt"
  apply rule
  apply auto
  apply (auto iff: k_empt_def)
  done

lemma k_invariant_step_new_aux:
  assumes X: "set X \<subseteq> set (k_succs x)"
      and x: "k_isNode x"
      and ec: "k_isNode ec"
      and ec': "simAbs ec' \<in> simAbs ` set X"
      and S: "simAbs ec = simAbs x"
  shows "\<exists>r. lookup tOps (foldr (transUpdate x) X Y) (ec, simObs a ec') = Some r
           \<and> simAbs r \<in> simAbs ` set (k_succs ec)
           \<and> simObs a r = simObs a ec'"
using X ec'
proof(induct X arbitrary: Y)
  case Nil thus ?case by simp
next
  case (Cons y ys) show ?case
  proof(cases "simAbs ec' = simAbs y")
    case False with x ec S Cons show ?thesis
      unfolding transUpdate_def
      apply clarsimp
      unfolding k_isNode_def
      apply (erule imageE)+
      apply (cut_tac a=a and t=ta and ec=x and ec'=ec in simTrans_simAbs_cong[symmetric])
      apply simp_all
      done
  next
    case True
    with Cons have F: "simAbs y \<in> simAbs ` set (k_succs x)"
      by auto
    from x obtain t
      where tC: "t \<in> jkbpC"
        and x': "simAbs x = sim_equiv_class a t"
      unfolding k_isNode_def by blast
    from F obtain t' s
      where "simAbs y = sim_equiv_class a (t' \<leadsto> s)"
        and tsC: "t' \<leadsto> s \<in> jkbpC"
        and tt': "jview a t = jview a t'"
      using simTrans[rule_format, where a=a and t=t] tC x' by auto
    with Cons.hyps[where Y11=Y] Cons(2) Cons(3) True S x ec show ?thesis
      unfolding transUpdate_def
      apply auto
      apply (subst simTrans_simAbs_cong[where t=t' and ec'=x])
       apply blast

       using x' tt'
       apply auto[1]

       apply simp

       apply (rule image_eqI[where x=y])
       apply simp
       apply simp
      using simObs[rule_format, where a=a and t="t'\<leadsto>s"]
      apply simp
      done
  qed
qed

lemma k_invariant_step_new:
  assumes x: "k_isNode x"
      and ec: "k_isNode ec"
      and ec': "ec' \<in> set (k_succs ec)"
      and S: "simAbs ec = simAbs x"
  shows "\<exists>ec''. lookup tOps (aTrans (k_ins x A)) (ec, simObs a ec') = Some ec''
              \<and> simAbs ec'' \<in> simAbs ` set (k_succs ec)
              \<and> simObs a ec'' = simObs a ec'"
proof -
  from x ec'
  have ec': "simAbs ec' \<in> simAbs ` set (k_succs x)"
    unfolding k_isNode_def
    apply clarsimp
    apply (subst simTrans_simAbs_cong[OF _ _ S, symmetric])
    using S
    apply auto
    done
  thus ?thesis
    using k_invariant_step_new_aux[OF subset_refl x ec _ S, where ec'=ec']
    unfolding k_ins_def
    apply auto
    done
qed

lemma k_invariant_step_old_aux:
  assumes x: "k_isNode x"
      and ec: "k_isNode ec"
      and S: "simAbs ec \<noteq> simAbs x"
  shows "lookup tOps (foldr (transUpdate x) X Y) (ec, obs)
       = lookup tOps Y (ec, obs)"
proof(induct X)
  case (Cons z zs) with x ec S show ?case
    by (cases "lookup tOps Y (ec, obs)") (simp_all add: transUpdate_def)
qed simp

lemma k_invariant_step_old:
  assumes x: "k_isNode x"
      and ec: "k_isNode ec"
      and S: "simAbs ec \<noteq> simAbs x"
  shows "lookup tOps (aTrans (k_ins x A)) (ec, obs)
       = lookup tOps (aTrans A) (ec, obs)"
  unfolding k_ins_def
  using k_invariant_step_old_aux[OF x ec S]
  by simp

lemma k_invariant_frame:
  assumes B: "lookup tOps Y (ec, obs) = lookup tOps Y (ec', obs)"
      and x: "k_isNode x"
      and ec: "k_isNode ec"
      and ec': "k_isNode ec'"
      and S: "simAbs ec' = simAbs ec"
  shows "lookup tOps (foldr (transUpdate x) X Y) (ec, obs) = lookup tOps (foldr (transUpdate x) X Y) (ec', obs)"
  apply (induct X)
  unfolding transUpdate_def
   using B
   apply simp
  using x ec ec' S
  apply simp
  done

lemma k_invariant_step[simp]:
  assumes N: "k_isNode x"
      and I: "k_invariant A"
      and M: "\<not> k_memb x A"
  shows "k_invariant (k_ins x A)"
(*<*)
proof
  fix ec ec'
  assume ec: "k_isNode ec" and ec': "k_isNode ec'" and X: "simAbs ec' = simAbs ec"
  with N show "lookup aOps (aActs (k_ins x A)) ec = lookup aOps (aActs (k_ins x A)) ec'"
    unfolding k_ins_def actsUpdate_def
    using k_invariantAOD[OF ec ec' X I]
    apply simp
    done
next
  fix ec ec' obs
  assume ec: "k_isNode ec" and ec': "k_isNode ec'" and X: "simAbs ec' = simAbs ec"
  show "lookup tOps (aTrans (k_ins x A)) (ec, obs) = lookup tOps (aTrans (k_ins x A)) (ec', obs)"
    unfolding k_ins_def
    using k_invariant_frame[OF k_invariantTOD[OF ec ec' X I] N ec ec' X]
    apply simp
    done
next
  fix ec obs ecs'
  assume n: "k_isNode ec"
    and ec: "k_memb ec (k_ins x A)"
    and obs: "obs \<in> simObs a ` set (simTrans a ec)"
  show "\<exists>ec'. lookup tOps (aTrans (k_ins x A)) (ec, obs) = Some ec'
            \<and> simAbs ec' \<in> simAbs ` set (k_succs ec)
            \<and> simObs a ec' = obs"
  proof(cases "simAbs ec = simAbs x")
    case True with N n obs show ?thesis
      using k_invariant_step_new by auto
  next
    case False with I N n ec obs show ?thesis
      apply (simp add: k_invariant_step_old)
      apply (rule k_invariantTD)
      apply simp_all
      unfolding k_ins_def k_memb_def actsUpdate_def
      apply simp
      done
  qed
next
  fix ec
  assume n: "k_isNode ec"
     and ec: "k_memb ec (k_ins x A)"
  show "\<exists>acts. lookup aOps (aActs (k_ins x A)) ec = Some acts \<and> set acts = set (simAction a ec)"
  proof(cases "simAbs ec = simAbs x")
    case True with aOps N n show ?thesis
      unfolding k_ins_def actsUpdate_def
      apply clarsimp
      unfolding k_isNode_def
      apply clarsimp
      apply (erule jAction_simAbs_cong)
      apply auto
      done
  next
    case False with aOps N I M n ec show ?thesis
      unfolding k_ins_def actsUpdate_def
      apply simp
      apply (rule k_invariantAD)
      unfolding k_memb_def
      apply simp_all
      done
  qed
qed
(*>*)

(*>*)

text\<open>

Showing that the invariant holds of @{term "k_empt"} and is respected
by @{term "k_ins"} is routine.

The initial frontier is the partition of the set of initial states
under the initial observation function.

\<close>

definition (in Algorithm) k_frontier :: "'a \<Rightarrow> 'rep list" where
  "k_frontier a \<equiv> map (simInit a \<circ> envObs a) envInit"
(*<*)

lemma k_frontier_is_node[intro, simp]:
  "list_all k_isNode (k_frontier a)"
  unfolding k_frontier_def
  by (auto iff: simInit list_all_iff k_isNode_def jviewInit jviewIncr)
(*>*)

end (* context AlgorithmForAgent *)

text\<open>

We now instantiate the @{term "DFS"} locale with respect to the @{term
"AlgorithmForAgent"} locale. The instantiated lemmas are given the
mandatory prefix \<open>KBPAlg\<close> in the @{term "AlgorithmForAgent"}
locale.

\<close>

sublocale AlgorithmForAgent
        < KBPAlg: DFS k_succs k_isNode k_invariant k_ins k_memb k_empt simAbs

(*<*)
  apply (unfold_locales)
  apply simp_all

  unfolding k_memb_def k_ins_def actsUpdate_def
  using aOps
  apply (auto iff: isSome_eq)[1]

  unfolding k_isNode_def
  apply clarsimp
  apply (erule simTrans_simAbs_cong)
  apply auto
  done
(*>*)

text_raw\<open>
\begin{figure}
\begin{isabellebody}%
\<close>
definition
  alg_dfs :: "('ma, 'rep, 'aAct list) MapOps
         \<Rightarrow> ('mt, 'rep \<times> 'obs, 'rep) MapOps
         \<Rightarrow> ('rep \<Rightarrow> 'obs)
         \<Rightarrow> ('rep \<Rightarrow> 'rep list)
         \<Rightarrow> ('rep \<Rightarrow> 'aAct list)
         \<Rightarrow> 'rep list
         \<Rightarrow> ('ma, 'mt) AlgState"
where
  "alg_dfs aOps tOps simObs simTrans simAction \<equiv>
    let k_empt = \<lparr> aActs = empty aOps, aTrans = empty tOps \<rparr>;
       k_memb = (\<lambda>s A. isSome (lookup aOps (aActs A) s));
       k_succs = simTrans;
       actsUpdate = \<lambda>ec A. update aOps ec (simAction ec) (aActs A);
       transUpdate = \<lambda>ec ec' at. update tOps (ec, simObs ec') ec' at;
       k_ins = \<lambda>ec A. \<lparr> aActs = actsUpdate ec A,
                         aTrans = foldr (transUpdate ec) (k_succs ec) (aTrans A) \<rparr>
     in gen_dfs k_succs k_ins k_memb k_empt"

text\<open>\<close>

definition
  mkAlgAuto :: "('ma, 'rep, 'aAct list) MapOps
            \<Rightarrow> ('mt, 'rep \<times> 'obs, 'rep) MapOps
            \<Rightarrow> ('a \<Rightarrow> 'rep \<Rightarrow> 'obs)
            \<Rightarrow> ('a \<Rightarrow> 'obs \<Rightarrow> 'rep)
            \<Rightarrow> ('a \<Rightarrow> 'rep \<Rightarrow> 'rep list)
            \<Rightarrow> ('a \<Rightarrow> 'rep \<Rightarrow> 'aAct list)
            \<Rightarrow> ('a \<Rightarrow> 'rep list)
            \<Rightarrow> ('a, 'obs, 'aAct, 'rep) JointProtocol"
where
  "mkAlgAuto aOps tOps simObs simInit simTrans simAction frontier \<equiv> \<lambda>a.
    let auto = alg_dfs aOps tOps (simObs a) (simTrans a) (simAction a)
                       (frontier a)
     in \<lparr> pInit = simInit a,
          pTrans = \<lambda>obs ec. the (lookup tOps (aTrans auto) (ec, obs)),
          pAct = \<lambda>ec. the (lookup aOps (aActs auto) ec) \<rparr>"

text_raw\<open>
  \end{isabellebody}%
  \caption{The algorithm. The function @{term "the"} projects a value from the
    @{typ "'a option"} type, diverging on @{term "None"}.}
  \label{fig:kbps-alg-algorithm}
\end{figure}
\<close>
(*<*)
lemma mkAutoSim_simps[simp]:
  "pInit (mkAlgAuto aOps tOps simObs simInit simTrans simAction frontier a) = simInit a"
  "pTrans (mkAlgAuto aOps tOps simObs simInit simTrans simAction frontier a)
 = (\<lambda>obs ec. the (lookup tOps (aTrans (alg_dfs aOps tOps (simObs a) (simTrans a) (simAction a) (frontier a))) (ec, obs)))"
  "pAct (mkAlgAuto aOps tOps simObs simInit simTrans simAction frontier a)
 = (\<lambda>ec. the (lookup aOps (aActs (alg_dfs aOps tOps (simObs a) (simTrans a) (simAction a) (frontier a))) ec))"
  unfolding mkAlgAuto_def
  apply (simp_all add: Let_def)
  done

(* Later we want to show that a particular DFS implementation does the
right thing. *)

definition
  alg_mk_auto :: "('ma, 'rep, 'aAct list) MapOps
                \<Rightarrow> ('mt, 'rep \<times> 'obs, 'rep) MapOps
                \<Rightarrow> ('obs \<Rightarrow> 'rep)
                \<Rightarrow> ('ma, 'mt) AlgState
                \<Rightarrow> ('obs, 'aAct, 'rep) Protocol"
where
  "alg_mk_auto aOps tOps simInit k_dfs \<equiv>
    \<lparr> pInit = simInit,
      pTrans = \<lambda>obs ec. the (lookup tOps (aTrans k_dfs) (ec, obs)),
      pAct = \<lambda>ec. the (lookup aOps (aActs k_dfs) ec)
    \<rparr>"

(*>*)
context AlgorithmForAgent
begin

text\<open>

The final algorithm, with the constants inlined, is shown in
Figure~\ref{fig:kbps-alg-algorithm}. The rest of this section shows
its correctness.

Firstly it follows immediately from \<open>dfs_invariant\<close> that the
invariant holds of the result of the DFS:

\<close>
(*<*)

abbreviation
  "k_dfs \<equiv> KBPsAlg.alg_dfs aOps tOps (simObs a) (simTrans a) (simAction a) (k_frontier a)"

(* This is a syntactic nightmare. *)

lemma k_dfs_gen_dfs_unfold[simp]:
  "k_dfs = gen_dfs k_succs k_ins k_memb k_empt (k_frontier a)"
  unfolding alg_dfs_def
  apply (fold k_empt_def k_memb_def actsUpdate_def transUpdate_def)
  apply (simp add: k_ins_def[symmetric])
  done

(*>*)
lemma k_dfs_invariant: "k_invariant k_dfs"
(*<*)
  using KBPAlg.dfs_invariant[where S="k_empt" and xs="k_frontier a"]
  by simp

(*>*)
text\<open>

Secondly we can see that the set of reachable equivalence classes
coincides with the partition of @{term "jkbpC"} under the simulation
and representation functions:

\<close>

lemma k_reachable:
  "simAbs ` KBPAlg.reachable (set (k_frontier a)) = sim_equiv_class a ` jkbpC"
(*<*)(is "?lhs = ?rhs")
proof
  show "?lhs \<subseteq> ?rhs"
  proof
    fix sx assume "sx \<in> ?lhs"
    then obtain x
      where x: "x \<in> KBPAlg.reachable (set (k_frontier a))"
        and sx: "simAbs x = sx"
      by auto
    hence "x \<in> ({ (x, y). y \<in> set (k_succs x) })\<^sup>*
                 `` set (map (simInit a \<circ> envObs a) envInit)"
      unfolding KBPAlg.reachable_def k_frontier_def by simp
    then obtain s iobs
      where R: "(simInit a iobs, x) \<in> ({ (x, y). y \<in> set (k_succs x)})\<^sup>*"
        and sI: "s \<in> set envInit"
        and iobs: "envObs a s = iobs"
      by auto
    from R x have "simAbs x \<in> ?rhs"
    proof(induct arbitrary: sx rule: rtrancl_induct)
      case base
      with sI iobs show ?case by (auto simp: jviewInit simInit)
    next
      case (step x y)
      with sI iobs
      have "simAbs x \<in> sim_equiv_class a ` jkbpC"
        unfolding KBPAlg.reachable_def Image_def k_frontier_def
        by auto
      then obtain t
        where tC: "t \<in> jkbpC"
          and F: "simAbs x = sim_equiv_class a t"
        by auto
      from step
      have "simAbs y \<in> simAbs ` set (k_succs x)" by auto
      thus  ?case
        using simTrans[rule_format, where a=a and t=t] tC F by auto
    qed
    with sx show "sx \<in> ?rhs" by simp
  qed
next
  show "?rhs \<subseteq> ?lhs"
  proof
    fix ec assume "ec \<in> ?rhs"
    then obtain t
      where tC: "t \<in> jkbpC"
        and ec: "ec = sim_equiv_class a t"
      by auto
    thus "ec \<in> ?lhs"
    proof(induct t arbitrary: ec)
      case (tInit s) thus ?case
        unfolding KBPAlg.reachable_def (* FIXME ouch this is touchy *)
        unfolding k_frontier_def
        apply simp
        apply (rule image_eqI[where x="simInit a (envObs a s)"])
         apply (simp add: simInit jviewInit)
        apply (rule ImageI[where a="simInit a (envObs a s)"])
        apply auto
        done
    next
      case (tStep t s)
      hence tsC: "t \<leadsto> s \<in> jkbpC"
        and ec: "ec = sim_equiv_class a (t \<leadsto> s)"
        and "sim_equiv_class a t
           \<in> simAbs ` DFS.reachable k_succs (set (k_frontier a))"
        by auto
      then obtain rect
        where rect: "rect \<in> DFS.reachable k_succs (set (k_frontier a))"
          and srect: "simAbs rect = sim_equiv_class a t"
        by auto
      from tsC ec srect
      have "ec \<in> simAbs ` set (simTrans a rect)"
        using simTrans[rule_format, where a=a and t="t" and ec="rect"] srect by auto
      then obtain rec
        where rec: "ec = simAbs rec"
          and F: "rec \<in> set (simTrans a rect)"
        by auto
      from rect obtain rec0
        where rec0: "rec0 \<in> set (k_frontier a)"
          and rec0rect: "(rec0, rect) \<in> ({ (x, y). y \<in> set (k_succs x)})\<^sup>*"
        unfolding KBPAlg.reachable_def by auto
      show ?case
        apply -
        apply (rule image_eqI[where x="rec"])
         apply (rule rec)
        unfolding KBPAlg.reachable_def
        apply (rule ImageI[where a="rec0"])
         apply (rule rtrancl_into_rtrancl[where b="rect"])
          apply (rule rec0rect)
         apply clarsimp
         apply (rule F)
         apply (rule rec0)
         done
     qed
   qed
qed
(*>*)
text\<open>

Left to right follows from an induction on the reflexive, transitive
closure, and right to left by induction over canonical traces.

This result immediately yields the same result at the level of
representations:

\<close>

lemma k_memb_rep:
  assumes N: "k_isNode rec"
  shows "k_memb rec k_dfs"
(*<*)
proof -
  from N obtain rec'
    where r: "rec' \<in> DFS.reachable k_succs (set (k_frontier a))"
      and rec': "simAbs rec = simAbs rec'"
    unfolding k_isNode_def by (auto iff: k_reachable[symmetric])

  from N k_isNode_cong[OF rec', symmetric]
  have N': "k_isNode rec'"
    unfolding k_isNode_def by auto

  show "k_memb rec k_dfs"
    using KBPAlg.reachable_imp_dfs[OF N' k_frontier_is_node r]
    apply clarsimp
    apply (subst k_memb_def)
    apply (subst (asm) k_memb_def)
    using k_invariantAOD[OF N' N rec' k_dfs_invariant, symmetric]
    apply (cut_tac ec=y' and ec'=rec' in k_invariantAOD[OF _ _ _ k_dfs_invariant, symmetric])
     apply simp_all

     apply (cut_tac ec=rec' and ec'=y' in k_isNode_cong)
     apply simp
     using N'
     apply simp
     apply (rule N')
     done
qed
(*>*)

end (* context AlgorithmForAgent *)

text\<open>

This concludes our agent-specific reasoning; we now show that the
algorithm works for all agents. The following command generalises all
our lemmas in the @{term "AlgorithmForAgent"} to the @{term
"Algorithm"} locale, giving them the mandatory prefix \<open>KBP\<close>:

\<close>

sublocale Algorithm
        < KBP: AlgorithmForAgent
            jkbp envInit envAction envTrans envVal jview envObs
            jviewInit jviewIncr simf simRels simVal simAbs simObs
            simInit simTrans simAction aOps tOps a for a
(*<*)
  by unfold_locales
(*>*)

context Algorithm
begin

abbreviation
  "k_mkAlgAuto \<equiv>
    mkAlgAuto aOps tOps simObs simInit simTrans simAction k_frontier"
(*<*)

lemma k_mkAlgAuto_mkAutoSim_equiv:
  assumes tC: "t \<in> jkbpC"
  shows "simAbs (runJP k_mkAlgAuto t a) = simAbs (runJP mkAutoSim t a)"
using tC
proof(induct t)
  case (tInit s) thus ?case by simp
next
  case (tStep t s)
  hence tC: "t \<in> jkbpC" by blast

  from tStep
  have N: "KBP.k_isNode a (runJP k_mkAlgAuto t a)"
    unfolding KBP.k_isNode_def
    by (simp only: mkAutoSim_ec) auto

  from tStep
  have ect: "simAbs (runJP k_mkAlgAuto t a) = sim_equiv_class a t"
    by (simp only: mkAutoSim_ec) auto

  from tStep
  have "sim_equiv_class a (t \<leadsto> s) \<in> simAbs ` set (simTrans a (runJP k_mkAlgAuto t a))"
    using simTrans[rule_format, where a=a and t=t] tC ect by auto
  then obtain ec
    where ec: "ec \<in> set (simTrans a (runJP k_mkAlgAuto t a))"
      and sec: "simAbs ec = sim_equiv_class a (t \<leadsto> s)"
    by auto

  from tStep
  have F: "envObs a s \<in> simObs a ` set (simTrans a (runJP k_mkAlgAuto t a))"
    using simObs[rule_format, where a=a and t="t\<leadsto>s", symmetric] sec ec by auto
  from KBP.k_memb_rep[OF N]
  have E: "KBP.k_memb (runJP k_mkAlgAuto t a) (KBP.k_dfs a)" by blast

  have G: "simAbs (runJP k_mkAlgAuto (t \<leadsto> s) a) = sim_equiv_class a (t \<leadsto> s)"
    using KBP.k_invariantTD[OF N E F KBP.k_dfs_invariant]
    apply (clarsimp simp: jviewIncr)
    using simTrans[rule_format, where a=a and t=t and ec="runJP k_mkAlgAuto t a"] tC ect
    apply (subgoal_tac "simAbs x \<in> simAbs ` set (simTrans a (runJP k_mkAlgAuto t a))")
     apply (clarsimp simp: jviewIncr)
     apply (cut_tac a=a and ec=ec' and t="t'\<leadsto>sa" in simObs[rule_format])
      apply (simp add: jviewIncr)
     apply simp
    apply blast
    done

  from tStep show ?case by (simp only: G mkAutoSim_ec)
qed

(*>*)
text\<open>

Running the automata produced by the DFS on a canonical trace @{term
"t"} yields some representation of the expected equivalence class:

\<close>

lemma k_mkAlgAuto_ec:
  assumes tC: "t \<in> jkbpC"
  shows "simAbs (runJP k_mkAlgAuto t a) = sim_equiv_class a t"
(*<*)
  using k_mkAlgAuto_mkAutoSim_equiv[OF tC] mkAutoSim_ec[OF tC]
  by simp

(*>*)
text\<open>

This involves an induction over the canonical trace @{term "t"}.

That the DFS and @{term "mkAutoSim"} yield the same actions on
canonical traces follows immediately from this result and the
invariant:

\<close>

lemma k_mkAlgAuto_mkAutoSim_act_eq:
  assumes tC: "t \<in> jkbpC"
  shows "set \<circ> actJP k_mkAlgAuto t = set \<circ> actJP mkAutoSim t"
(*<*)
proof
  fix a
  let ?ec = "sim_equiv_class a t"
  let ?rec = "runJP k_mkAlgAuto t a"

  from tC have E: "?ec \<in> sim_equiv_class a ` jkbpC"
    by auto

  from tC E have N: "KBP.k_isNode a (runJP k_mkAlgAuto t a)"
    unfolding KBP.k_isNode_def by (simp add: k_mkAlgAuto_ec[OF tC])

  from KBP.k_memb_rep[OF N]
  have E: "KBP.k_memb ?rec (KBP.k_dfs a)" by blast

  obtain acts
    where "lookup aOps (aActs (KBP.k_dfs a)) ?rec = Some acts"
      and "set acts = set (simAction a ?rec)"
    using KBP.k_invariantAD[OF N E KBP.k_dfs_invariant] by blast

  thus "(set \<circ> actJP k_mkAlgAuto t) a = (set \<circ> actJP mkAutoSim t) a"
    by (auto intro!: jAction_simAbs_cong[OF tC]
               simp: k_mkAlgAuto_ec[OF tC] mkAutoSim_ec[OF tC])
qed
(*>*)

text\<open>

Therefore these two constructions are behaviourally equivalent, and so
the DFS generates an implementation of @{term "jkbp"} in the given
environment:

\<close>

theorem k_mkAlgAuto_implements: "implements k_mkAlgAuto"
(*<*)
proof -
  have "behaviourally_equiv mkAutoSim k_mkAlgAuto"
    by rule (simp only: k_mkAlgAuto_mkAutoSim_act_eq)
  with mkAutoSim_implements show ?thesis
    by (simp add: behaviourally_equiv_implements)
qed
(*>*)

end (* context Algorithm *)

text\<open>

Clearly the automata generated by this algorithm are large. We discuss
this issue in \S\ref{sec:kbps-alg-auto-min}.

\FloatBarrier

\<close>

(*<*)
end
(*>*)
