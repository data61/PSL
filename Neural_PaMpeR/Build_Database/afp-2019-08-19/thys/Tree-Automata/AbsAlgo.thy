(*  Title:       Tree Automata
    Author:      Peter Lammich <peter dot lammich at uni-muenster.de>
    Maintainer:  Peter Lammich <peter dot lammich at uni-muenster.de>
*)
section "Abstract Tree Automata Algorithms"
theory AbsAlgo
imports 
  Ta 
  Collections_Examples.Exploration
  Collections.CollectionsV1
begin

no_notation fun_rel_syn (infixr "\<rightarrow>" 60)

text_raw \<open>\label{sec:absalgo}\<close>
text \<open>This theory defines tree automata algorithms on an abstract level, 
  that is using non-executable datatypes and constructs like sets, 
  set-collecting operations, etc. 
    
  These algorithms are then refined to executable algorithms in 
  Section~\ref{sec:taimpl}.
\<close>

subsection \<open>Word Problem\<close>
  
text \<open>
  First, a recursive version of the @{const accs}-predicate is defined.
\<close>

fun r_match :: "'a set list \<Rightarrow> 'a list \<Rightarrow> bool" where
  "r_match [] [] \<longleftrightarrow> True" |
  "r_match (A#AS) (a#as) \<longleftrightarrow> a\<in>A \<and> r_match AS as" |
  "r_match _ _ \<longleftrightarrow> False"

\<comment> \<open>@{const r_match} accepts two lists, if they have the same length and 
  the elements in the second list are contained in the respective 
  elements of the first list:\<close>
lemma r_match_alt: 
  "r_match L l \<longleftrightarrow> length L = length l \<and> (\<forall>i<length l. l!i \<in> L!i)"
  apply (induct L l rule: r_match.induct)
  apply auto
  apply (case_tac i)
  apply auto
  done

\<comment> \<open>Whether a rule matches the given state, label and list of sets of states\<close>
fun r_matchc where
  "r_matchc q l Qs (qr \<rightarrow> lr qsr) \<longleftrightarrow> q=qr \<and> l=lr \<and> r_match Qs qsr"

\<comment> \<open>recursive version of @{const accs}-predicate\<close>  
fun faccs :: "('Q,'L) ta_rule set \<Rightarrow> 'L tree \<Rightarrow> 'Q set" where
  "faccs \<delta> (NODE f ts) = (
    let Qs = map (faccs \<delta>) (ts) in
      {q. \<exists>r\<in>\<delta>. r_matchc q f Qs r }
  )"

lemma faccs_correct_aux: 
  "q\<in>faccs \<delta> n = accs \<delta> n q" (is ?T1)
  "(map (faccs \<delta>) ts = map (\<lambda>t. { q . accs \<delta> t q}) ts)" (is ?T2)
proof -
  have "(\<forall>q. q\<in>faccs \<delta> n = accs \<delta> n q) 
        \<and> (map (faccs \<delta>) ts = map (\<lambda>t. { q . accs \<delta> t q}) ts)"
  proof (induct rule: compat_tree_tree_list.induct)
    case (NODE f ts)
    thus ?case
      apply (intro allI iffI)
      apply simp
      apply (erule bexE)
      apply (case_tac x)
      apply simp
      apply (rule accs.intros)
      apply assumption
      apply (unfold r_match_alt)
      apply simp
      apply fastforce
      apply simp
      apply (erule accs.cases)
      apply auto
      apply (rule_tac x="qa \<rightarrow> f qs" in bexI)
      apply simp
      apply (unfold r_match_alt)
      apply auto
      done
  qed auto
  thus ?T1 ?T2 by auto
qed

theorem faccs_correct1: "q\<in>faccs \<delta> n \<Longrightarrow> accs \<delta> n q" 
  by (simp add: faccs_correct_aux)
theorem faccs_correct2: "accs \<delta> n q \<Longrightarrow> q\<in>faccs \<delta> n" 
  by (simp add: faccs_correct_aux)

lemmas faccs_correct = faccs_correct1 faccs_correct2

lemma faccs_alt: "faccs \<delta> t = {q. accs \<delta> t q}" by (auto intro: faccs_correct)

subsection \<open>Backward Reduction and Emptiness Check\<close>
subsubsection "Auxiliary Definitions"

\<comment> \<open>Step function, that maps a set of states to those states 
  that are reachable via one backward step.\<close>
inductive_set bacc_step :: "('Q,'L) ta_rule set \<Rightarrow> 'Q set \<Rightarrow> 'Q set" 
  for \<delta> Q 
  where
  "\<lbrakk> r\<in>\<delta>; set (rhsq r) \<subseteq> Q \<rbrakk> \<Longrightarrow> lhs r \<in> bacc_step \<delta> Q"

\<comment> \<open>If a set is closed under adding all states that are reachable from the set 
  by one backward step, then this set contains all backward accessible states.\<close>
lemma b_accs_as_closed:
  assumes A: "bacc_step \<delta> Q \<subseteq> Q"  
  shows "b_accessible \<delta> \<subseteq> Q"
proof (rule subsetI)
  fix q
  assume "q\<in>b_accessible \<delta>"
  thus "q\<in>Q" 
  proof (induct rule: b_accessible.induct)
    fix q f qs
    assume BC: "(q\<rightarrow>f qs)\<in>\<delta>" 
               "!!x. x\<in>set qs \<Longrightarrow> x\<in>b_accessible \<delta>" 
               "!!x. x\<in>set qs \<Longrightarrow> x\<in>Q"
    from bacc_step.intros[OF BC(1)] BC(3) have "q\<in>bacc_step \<delta> Q" by auto
    with A show "q\<in>Q" by blast
  qed
qed

subsubsection "Algorithms"

text \<open>
  First, the basic workset algorithm is specified. 
  Then, it is refined to contain a counter for each rule, 
  that counts the number of undiscovered states on the RHS. 
  For both levels of abstraction, a version that computes the 
  backwards reduction, and a version that checks for emptiness is specified.

  Additionally, a version of the algorithm that computes a witness
  for non-emptiness is provided.
  
  Levels of abstraction:
  \begin{itemize} 
    \item[\<open>\<alpha>\<close>] On this level, the state consists of a set of 
      discovered states and a workset.
    \item[\<open>\<alpha>'\<close>] On this level, the state consists of a set of 
      discovered states, a workset and a map from rules to number of 
      undiscovered rhs states. This map can be used to make the discovery of
      rules that have to be considered more efficient.
  \end{itemize}
\<close>

text_raw \<open>\paragraph {\<open>\<alpha>\<close> - Level:}\<close>

  \<comment> \<open>A state contains the set of discovered states and a workset\<close>
type_synonym ('Q,'L) br_state = "'Q set \<times> 'Q set"

  \<comment> \<open>Set of states that are non-empty (accept a tree) after adding the 
  state $q$ to the set of discovered states\<close>
definition br_dsq 
  :: "('Q,'L) ta_rule set \<Rightarrow> 'Q \<Rightarrow> ('Q,'L) br_state \<Rightarrow> 'Q set" 
  where  
  "br_dsq \<delta> q == \<lambda>(Q,W). { lhs r | r. r\<in>\<delta> \<and> set (rhsq r) \<subseteq> (Q-(W-{q})) }"

  \<comment> \<open>Description of a step: One state is removed from the workset, and all 
  new states that become non-empty due to this state are added to, both, 
  the workset and the set of discovered states\<close>
inductive_set br_step 
  :: "('Q,'L) ta_rule set \<Rightarrow> (('Q,'L) br_state \<times> ('Q,'L) br_state) set" 
  for \<delta> where
  "\<lbrakk>
     q\<in>W;
     Q' = Q \<union> br_dsq \<delta> q (Q,W);
     W' = W - {q} \<union> (br_dsq \<delta> q (Q,W) - Q)
   \<rbrakk> \<Longrightarrow> ((Q,W),(Q',W'))\<in>br_step \<delta>"

  \<comment> \<open>Termination condition for backwards reduction: The workset is empty\<close>
definition br_cond :: "('Q,'L) br_state set" 
  where "br_cond == {(Q,W). W\<noteq>{}}"

  \<comment> \<open>Termination condition for emptiness check: 
      The workset is empty or a non-empty initial state has been discovered\<close>
definition bre_cond :: "'Q set \<Rightarrow> ('Q,'L) br_state set" 
  where "bre_cond Qi == {(Q,W). W\<noteq>{} \<and> (Qi\<inter>Q={})}"

  \<comment> \<open>Set of all states that occur on the lhs of a constant-rule\<close>
definition br_iq :: "('Q,'L) ta_rule set \<Rightarrow> 'Q set" 
  where "br_iq \<delta> == { lhs r | r. r\<in>\<delta> \<and> rhsq r = [] }"

  \<comment> \<open>Initial state for the iteration\<close>
definition br_initial :: "('Q,'L) ta_rule set \<Rightarrow> ('Q,'L) br_state" 
  where "br_initial \<delta> == (br_iq \<delta>, br_iq \<delta>)"

  \<comment> \<open>Invariant for the iteration: 
    \begin{itemize}
      \item States on the workset have been discovered
      \item Only accessible states have been discovered
      \item If a state is non-empty due to a rule whose 
            rhs-states have been discovered and processed 
            (i.e. are in $Q-W$), then the lhs state of the 
            rule has also been discovered.
      \item The set of discovered states is finite
    \end{itemize}\<close>
definition br_invar :: "('Q,'L) ta_rule set \<Rightarrow> ('Q,'L) br_state set" 
  where "br_invar \<delta> == {(Q,W). 
    W\<subseteq>Q \<and> 
    Q \<subseteq> b_accessible \<delta> \<and> 
    bacc_step \<delta> (Q - W) \<subseteq> Q \<and> 
    finite Q}"

definition "br_algo \<delta> == \<lparr>
  wa_cond = br_cond,
  wa_step = br_step \<delta>,
  wa_initial = {br_initial \<delta>},
  wa_invar = br_invar \<delta>
\<rparr>"

definition "bre_algo Qi \<delta> == \<lparr>
  wa_cond = bre_cond Qi,
  wa_step = br_step \<delta>,
  wa_initial = {br_initial \<delta>},
  wa_invar = br_invar \<delta>
\<rparr>"


  \<comment> \<open>Termination: Either a new state is added, or the workset decreases.\<close>
definition "br_termrel \<delta> == 
  ({(Q',Q). Q \<subset> Q' \<and> Q' \<subseteq> b_accessible \<delta>}) <*lex*> finite_psubset"

lemma bre_cond_imp_br_cond[intro, simp]: "bre_cond Qi \<subseteq> br_cond" 
  by (auto simp add: br_cond_def bre_cond_def)

lemma br_termrel_wf[simp, intro!]: "finite \<delta> \<Longrightarrow> wf (br_termrel \<delta>)"
  apply (unfold br_termrel_def)
  apply (auto simp add: wf_bounded_supset)
  done

  \<comment> \<open>Only accessible states are discovered\<close>
lemma br_dsq_ss:
  assumes A: "(Q,W)\<in>br_invar \<delta>" "W \<noteq> {}" "q\<in>W"
  shows "br_dsq \<delta> q (Q,W) \<subseteq> b_accessible \<delta>"
proof (rule subsetI)
  fix q'
  assume B: "q'\<in>br_dsq \<delta> q (Q,W)"
  then obtain r where 
    R: "q' = lhs r" "r\<in>\<delta>" and 
    S: "set (rhsq r) \<subseteq> (Q-(W-{q}))" 
    by (unfold br_dsq_def) auto
  note S
  also have "(Q-(W-{q})) \<subseteq> b_accessible \<delta>" using A(1,3)
    by (auto simp add: br_invar_def)
  finally show "q'\<in>b_accessible \<delta>" using R
    by (cases r)
  (auto intro: b_accessible.intros)
qed

lemma br_step_in_termrel: 
  assumes A: "\<Sigma>\<in>br_cond" "\<Sigma>\<in>br_invar \<delta>" "(\<Sigma>,\<Sigma>')\<in>br_step \<delta>"
  shows "(\<Sigma>', \<Sigma>)\<in>br_termrel \<delta>"
proof -
  obtain Q W Q' W' where 
    [simp]: "\<Sigma>=(Q,W)" "\<Sigma>'=(Q',W')" 
    by (cases \<Sigma>, cases \<Sigma>', auto)
  obtain q where 
    QIW: "q\<in>W" and 
    ASSFMT[simp]: "Q' = Q \<union> br_dsq \<delta> q (Q, W)"
                  "W' = W - {q} \<union> (br_dsq \<delta> q (Q, W) - Q)"
    by (auto intro: br_step.cases[OF A(3)[simplified]])

  from A(2) have [simp]: "finite Q" 
    by (auto simp add: br_invar_def)
  from A(2)[unfolded br_invar_def] have [simp]: "finite W" 
    by (auto simp add: finite_subset)
  from A(1) have WNE: "W\<noteq>{}" by (unfold br_cond_def) auto

  note DSQSS = br_dsq_ss[OF A(2)[simplified] WNE QIW]
  {
    assume "br_dsq \<delta> q (Q,W) - Q = {}"
    hence ?thesis using QIW
      by (simp add: br_termrel_def set_simps)
  } moreover {
    assume "br_dsq \<delta> q (Q,W) - Q \<noteq> {}"
    hence "Q \<subset> Q'" by auto
    moreover from DSQSS A(2)[unfolded br_invar_def] have 
      "Q' \<subseteq> b_accessible \<delta>" 
      by auto
    ultimately have ?thesis 
      by (simp add: br_termrel_def)
  } ultimately show ?thesis by blast
qed

lemma br_invar_initial[simp]: "finite \<delta> \<Longrightarrow> (br_initial \<delta>)\<in>br_invar \<delta>"
  apply (auto simp add: br_initial_def br_invar_def br_iq_def)
    
  apply (case_tac r)
  apply (fastforce intro: b_accessible.intros)
  apply (fastforce elim!: bacc_step.cases)
  done

lemma br_invar_step: 
  assumes [simp]: "finite \<delta>"
  assumes A: "\<Sigma>\<in>br_cond" "\<Sigma>\<in>br_invar \<delta>" "(\<Sigma>,\<Sigma>')\<in>br_step \<delta>"
  shows "\<Sigma>'\<in>br_invar \<delta>"
proof -
  obtain Q W Q' W' where SF[simp]: "\<Sigma>=(Q,W)" "\<Sigma>'=(Q',W')" 
    by (cases \<Sigma>, cases \<Sigma>', auto)
  obtain q where 
    QIW: "q\<in>W" and 
    ASSFMT[simp]: "Q' = Q \<union> br_dsq \<delta> q (Q, W)"
                  "W' = W - {q} \<union> (br_dsq \<delta> q (Q, W) - Q)"
    by (auto intro: br_step.cases[OF A(3)[simplified]])

  from A(1) have WNE: "W\<noteq>{}" by (unfold br_cond_def) auto

  have DSQSS: "br_dsq \<delta> q (Q,W) \<subseteq> b_accessible \<delta>"
    using br_dsq_ss[OF A(2)[simplified] WNE QIW] .

  show ?thesis
    apply (simp add: br_invar_def del: ASSFMT)
  proof (intro conjI)
    from A(2) have "W \<subseteq> Q" by (simp add: br_invar_def)
    thus "W' \<subseteq> Q'" by auto
  next
    from A(2) have "Q \<subseteq> b_accessible \<delta>" by (simp add: br_invar_def)
    with DSQSS show "Q' \<subseteq> b_accessible \<delta>" by auto
  next
    show "bacc_step \<delta> (Q' - W') \<subseteq> Q'"
      apply (rule subsetI)
      apply (erule bacc_step.cases)
      apply (auto simp add: br_dsq_def)
      done
  next
    show "finite Q'" using A(2) by (simp add: br_invar_def br_dsq_def)
  qed
qed


lemma br_invar_final:
  "\<forall>\<Sigma>. \<Sigma>\<in>wa_invar (br_algo \<delta>) \<and> \<Sigma>\<notin>wa_cond (br_algo \<delta>) 
   \<longrightarrow> fst \<Sigma> = b_accessible \<delta>"
  apply (simp add: br_invar_def br_cond_def br_algo_def)
  apply (auto intro: rev_subsetD[OF _ b_accs_as_closed])
  done
(*  shows "\<lbrakk>(Q,W)\<in>br_invar \<delta>; (Q,W)\<notin>br_cond\<rbrakk> \<Longrightarrow> Q = b_accessible \<delta>"
  apply (simp add: br_invar_def br_cond_def)
  apply (auto intro: rev_subsetD[OF _ b_accs_as_closed])
  done*)

theorem br_while_algo: 
  assumes FIN[simp]: "finite \<delta>"
  shows "while_algo (br_algo \<delta>)"
  apply (unfold_locales)
  apply (simp_all add: br_algo_def br_invar_step br_invar_initial 
                       br_step_in_termrel)
  apply (rule_tac r="br_termrel \<delta>" in wf_subset)
  apply (auto intro: br_step_in_termrel)
  done

lemma bre_invar_final:
  "\<forall>\<Sigma>. \<Sigma>\<in>wa_invar (bre_algo Qi \<delta>) \<and> \<Sigma>\<notin>wa_cond (bre_algo Qi \<delta>) 
     \<longrightarrow> ((Qi\<inter>fst \<Sigma>={}) \<longleftrightarrow> (Qi \<inter> b_accessible \<delta> = {}))"
  apply (simp add: br_invar_def bre_cond_def bre_algo_def)
  apply safe
  apply (auto dest!: b_accs_as_closed)
  done

theorem bre_while_algo:
  assumes FIN[simp]: "finite \<delta>"
  shows "while_algo (bre_algo Qi \<delta>)"
  apply (unfold_locales)
  apply (unfold bre_algo_def)
  apply (auto simp add: br_invar_initial br_step_in_termrel
    intro: br_invar_step 
    dest: rev_subsetD[OF _ bre_cond_imp_br_cond])
  apply (rule_tac r="br_termrel \<delta>" in wf_subset)
  apply (auto intro: br_step_in_termrel
              dest: rev_subsetD[OF _ bre_cond_imp_br_cond])
  done

text_raw \<open>\paragraph{\<open>\<alpha>'\<close> - Level}\<close>
text \<open>
  Here, an optimization is added:
    For each rule, the algorithm now maintains a counter that counts the number
    of undiscovered states on the rules RHS. Whenever a new state is discovered,
    this counter is decremented for all rules where the state occurs on the RHS.
    The LHS states of rules where the counter falls to 0 are added to the 
    worklist. The idea is that decrementing the counter is more efficient than 
    checking whether all states on the rule's RHS have been discovered.

  A similar algorithm is sketched in \cite{tata2007}(Exercise~1.18).
\<close>
type_synonym ('Q,'L) br'_state = "'Q set \<times> 'Q set \<times> (('Q,'L) ta_rule \<rightharpoonup> nat)"

  \<comment> \<open>Abstraction to @{text \<alpha>}-level\<close>
definition br'_\<alpha> :: "('Q,'L) br'_state \<Rightarrow> ('Q,'L) br_state" 
  where "br'_\<alpha> = (\<lambda>(Q,W,rcm). (Q,W))"

definition br'_invar_add :: "('Q,'L) ta_rule set \<Rightarrow> ('Q,'L) br'_state set"
  where "br'_invar_add \<delta> == {(Q,W,rcm). 
    (\<forall>r\<in>\<delta>. rcm r = Some (card (set (rhsq r) - (Q - W)))) \<and> 
    {lhs r | r. r\<in>\<delta> \<and> the (rcm r) = 0} \<subseteq> Q
  }"

definition br'_invar :: "('Q,'L) ta_rule set \<Rightarrow> ('Q,'L) br'_state set"
  where "br'_invar \<delta> == br'_invar_add \<delta> \<inter> {\<Sigma>. br'_\<alpha> \<Sigma> \<in> br_invar \<delta>}"

inductive_set br'_step 
  :: "('Q,'L) ta_rule set \<Rightarrow> (('Q,'L) br'_state \<times> ('Q,'L) br'_state) set" 
  for \<delta> where
  "\<lbrakk> q\<in>W;
     Q' = Q \<union> { lhs r | r. r\<in>\<delta> \<and> q \<in> set (rhsq r) \<and> the (rcm r) \<le> 1 };
     W' = (W-{q}) 
          \<union> ({ lhs r | r. r\<in>\<delta> \<and> q \<in> set (rhsq r) \<and> the (rcm r) \<le> 1 } 
              - Q);
     !!r. r\<in>\<delta> \<Longrightarrow> rcm' r = ( if q \<in> set (rhsq r) then 
                               Some (the (rcm r) - 1) 
                             else rcm r
                           )
   \<rbrakk> \<Longrightarrow> ((Q,W,rcm),(Q',W',rcm')) \<in> br'_step \<delta>"

definition br'_cond :: "('Q,'L) br'_state set" 
  where "br'_cond == {(Q,W,rcm). W\<noteq>{}}"
definition bre'_cond :: "'Q set \<Rightarrow> ('Q,'L) br'_state set" 
  where "bre'_cond Qi == {(Q,W,rcm). W\<noteq>{} \<and> (Qi\<inter>Q={})}"

inductive_set br'_initial :: "('Q,'L) ta_rule set \<Rightarrow> ('Q,'L) br'_state set" 
  for \<delta> where
  "\<lbrakk> !!r. r\<in>\<delta> \<Longrightarrow> rcm r = Some (card (set (rhsq r))) \<rbrakk> 
     \<Longrightarrow> (br_iq \<delta>, br_iq \<delta>, rcm)\<in>br'_initial \<delta>"

definition "br'_algo \<delta> == \<lparr>
  wa_cond=br'_cond,
  wa_step = br'_step \<delta>,
  wa_initial = br'_initial \<delta>,
  wa_invar = br'_invar \<delta>
\<rparr>"

definition "bre'_algo Qi \<delta> == \<lparr>
  wa_cond=bre'_cond Qi,
  wa_step = br'_step \<delta>,
  wa_initial = br'_initial \<delta>,
  wa_invar = br'_invar \<delta>
\<rparr>"

lemma br'_step_invar: 
  assumes finite[simp]: "finite \<delta>"
  assumes INV: "\<Sigma>\<in>br'_invar_add \<delta>" "br'_\<alpha> \<Sigma> \<in> br_invar \<delta>"
  assumes STEP: "(\<Sigma>,\<Sigma>') \<in> br'_step \<delta>"
  shows "\<Sigma>'\<in>br'_invar_add \<delta>"
proof -
  obtain Q W rcm where [simp]: "\<Sigma>=(Q,W,rcm)"
    by (cases \<Sigma>) auto
  obtain Q' W' rcm' where [simp]: "\<Sigma>'=(Q',W',rcm')"
    by (cases \<Sigma>') auto

  from STEP obtain q where
    STEPF:
    "q\<in>W"
    "Q' = Q \<union> { lhs r | r. r\<in>\<delta> \<and> q \<in> set (rhsq r) \<and> the (rcm r) \<le> 1 }"
    "W' = (W-{q}) 
          \<union> ({ lhs r | r. r\<in>\<delta> \<and> q \<in> set (rhsq r) \<and> the (rcm r) \<le> 1 } 
              - Q)"
    "!!r. r\<in>\<delta> \<Longrightarrow> rcm' r = ( if q \<in> set (rhsq r) then 
                               Some (the (rcm r) - 1) 
                             else rcm r
                           )"
    by (auto elim: br'_step.cases)

  from INV[unfolded br'_invar_def br_invar_def br'_invar_add_def br'_\<alpha>_def, 
           simplified] 
  have INV:
    "(\<forall>r\<in>\<delta>. rcm r = Some (card (set (rhsq r) - (Q - W))))" 
    "{lhs r |r. r \<in> \<delta> \<and> the (rcm r) = 0} \<subseteq> Q" 
    "W \<subseteq> Q" 
    "Q \<subseteq> b_accessible \<delta>" 
    "bacc_step \<delta> (Q - W) \<subseteq> Q" 
    "finite Q"
    by auto

  {
    fix r
    assume A: "r\<in>\<delta>"
    with INV(1) have RCMR: "rcm r = Some (card (set (rhsq r) - (Q - W)))" 
      by auto

    have "rcm' r = Some (card (set (rhsq r) - (Q' - W')))"
    proof (cases "q\<in>set (rhsq r)")
      case False
      with A STEPF(4) have "rcm' r = rcm r" by auto
      moreover from STEPF INV(3) False have 
        "set (rhsq r) - (Q-W) = set (rhsq r) - (Q'-W')" 
        by auto
      ultimately show ?thesis
        by (simp add: RCMR)
    next
      case True
      with A STEPF(4) RCMR have 
        "rcm' r = Some ((card (set (rhsq r) - (Q - W))) - 1)"
        by simp
      moreover from STEPF INV(3) True have 
        "set (rhsq r) - (Q-W) = insert q (set (rhsq r) - (Q'-W'))"
        "q\<notin>(set (rhsq r) - (Q'-W'))"
        by auto
      ultimately show ?thesis
        by (simp add: RCMR card_insert_disjoint')
    qed
  } moreover {
    fix r
    assume A: "r\<in>\<delta>" "the (rcm' r) = 0"
    have "lhs r \<in> Q'" proof (cases "q\<in>set (rhsq r)")
      case True
      with A(1) STEPF(4) have "rcm' r = Some (the (rcm r) - 1)" by auto
      with A(2) have "the (rcm r) - 1 = 0" by auto
      hence "the (rcm r) \<le> 1" by auto
      with STEPF(2) A(1) True show ?thesis by auto
    next
      case False
      with A(1) STEPF(4) have "rcm' r = rcm r" by auto
      with A(2) have "the (rcm r) = 0" by auto
      with A(1) INV(2) have "lhs r \<in> Q" by auto
      with STEPF(2) show ?thesis by auto
    qed
  } ultimately show ?thesis
    by (auto simp add: br'_invar_add_def)
qed

lemma br'_invar_initial: 
  "br'_initial \<delta> \<subseteq> br'_invar_add \<delta>"
  apply safe
  apply (erule br'_initial.cases)
  apply (unfold br'_invar_add_def)
  apply (auto simp add: br_iq_def)
  done

lemma br'_rcm_aux': 
  "\<lbrakk> (Q,W,rcm)\<in>br'_invar \<delta>; q\<in>W \<rbrakk> 
    \<Longrightarrow> {r \<in> \<delta>. q \<in> set (rhsq r) \<and> the (rcm r) \<le> Suc 0} 
         = {r\<in>\<delta>. q\<in>set (rhsq r) \<and> set (rhsq r) \<subseteq> (Q - (W-{q}))}"
proof (intro subsetI equalityI, goal_cases)
  case prems: (1 r)
  hence  B: "r\<in>\<delta>" "q\<in>set (rhsq r)" "the (rcm r) \<le> Suc 0" by auto
  from B(1,3) prems(1)[unfolded br'_invar_def br'_invar_add_def] have 
    CARD: "card (set (rhsq r) - (Q - W)) \<le> Suc 0" 
    by auto
  from prems(1)[unfolded br'_invar_def br_invar_def br'_\<alpha>_def] have WSQ: "W\<subseteq>Q" 
    by auto
  have "set (rhsq r) - (Q - W) = {q}" 
  proof -
    from B(2) prems(2) have R1: "q\<in>set (rhsq r) - (Q - W)" by auto
    moreover
    {
      fix x
      assume A: "x\<noteq>q" "x\<in>set (rhsq r) - (Q - W)"
      with R1 have "{x,q} \<subseteq> set (rhsq r) - (Q - W)" by auto
      hence "card {x,q} \<le> card (set (rhsq r) - (Q - W))" 
        by (auto simp add: card_mono)
      with CARD A(1) have False by auto
    }
    ultimately show ?thesis by auto
  qed
  with prems(2) WSQ have "set (rhsq r) \<subseteq> Q - (W - {q})" by auto
  thus ?case using B(1,2) by auto 
next
  case prems: (2 r)
  hence B: "r\<in>\<delta>" "q\<in>set (rhsq r)" "set (rhsq r) \<subseteq> Q - (W - {q})" by auto
  with prems(1)[unfolded br'_invar_def br'_invar_add_def 
                         br'_\<alpha>_def br_invar_def] 
  have 
    IC: "W\<subseteq>Q" "the (rcm r) = card (set (rhsq r) - (Q - W))" 
    by auto
  have "set (rhsq r) - (Q - W) \<subseteq> {q}" using B(2,3) IC(1) by auto
  from card_mono[OF _ this] have "the (rcm r) \<le> Suc 0" by (simp add: IC(2))
  with B(1,2) show ?case by auto
qed

lemma br'_rcm_aux: 
  assumes A: "(Q,W,rcm)\<in>br'_invar \<delta>" "q\<in>W"  
  shows "{lhs r |r. r \<in> \<delta> \<and> q \<in> set (rhsq r) \<and> the (rcm r) \<le> Suc 0} 
         = {lhs r | r. r\<in>\<delta> \<and> q\<in>set (rhsq r) \<and> set (rhsq r) \<subseteq> (Q - (W-{q}))}"
proof -
  have "{lhs r |r. r \<in> \<delta> \<and> q \<in> set (rhsq r) \<and> the (rcm r) \<le> Suc 0} 
        = lhs ` {r \<in> \<delta>. q \<in> set (rhsq r) \<and> the (rcm r) \<le> Suc 0}" 
    by auto
  also from br'_rcm_aux'[OF A] have 
    "\<dots> = lhs ` {r \<in> \<delta>. q \<in> set (rhsq r) \<and> set (rhsq r) \<subseteq> Q - (W - {q})}" 
    by simp
  also have 
    "\<dots> = {lhs r | r. r\<in>\<delta> \<and> q\<in>set (rhsq r) \<and> set (rhsq r) \<subseteq> (Q - (W-{q}))}" 
    by auto
  finally show ?thesis .
qed
  
lemma br'_invar_QcD: 
  "(Q,W,rcm) \<in> br'_invar \<delta> \<Longrightarrow> {lhs r | r. r\<in>\<delta> \<and> set (rhsq r) \<subseteq> (Q-W)} \<subseteq> Q"
proof (safe)
  fix r
  assume A: "(Q,W,rcm)\<in>br'_invar \<delta>" "r\<in>\<delta>" "set (rhsq r) \<subseteq> Q - W"
  from A(1)[unfolded br'_invar_def br'_invar_add_def br'_\<alpha>_def br_invar_def, 
            simplified] 
  have 
    IC: "W \<subseteq> Q" 
        "finite Q" 
        "(\<forall>r\<in>\<delta>. rcm r = Some (card (set (rhsq r) - (Q - W))))" 
        "{lhs r |r. r \<in> \<delta> \<and> the (rcm r) = 0} \<subseteq> Q" by auto
  from IC(3) A(2,3) have "the (rcm r) = 0" by auto
  with IC(4) A(2) show "lhs r \<in> Q" by auto
qed

lemma br'_rcm_aux2: 
  "\<lbrakk> (Q,W,rcm)\<in>br'_invar \<delta>; q\<in>W \<rbrakk> 
    \<Longrightarrow> Q \<union> br_dsq \<delta> q (Q,W) 
        = Q \<union> {lhs r |r. r \<in> \<delta> \<and> q \<in> set (rhsq r) \<and> the (rcm r) \<le> Suc 0}"
  apply (simp only: br'_rcm_aux)
  apply (unfold br_dsq_def)
  apply simp
  apply (frule br'_invar_QcD)
  apply auto
  done

lemma br'_rcm_aux3: 
  "\<lbrakk> (Q,W,rcm)\<in>br'_invar \<delta>; q\<in>W \<rbrakk> 
    \<Longrightarrow> br_dsq \<delta> q (Q,W) - Q 
        = {lhs r |r. r \<in> \<delta> \<and> q \<in> set (rhsq r) \<and> the (rcm r) \<le> Suc 0} - Q"
  apply (simp only: br'_rcm_aux)
  apply (unfold br_dsq_def)
  apply simp
  apply (frule br'_invar_QcD)
  apply auto
  done

lemma br'_step_abs: 
  "\<lbrakk> 
     \<Sigma>\<in>br'_invar \<delta>; 
     (\<Sigma>,\<Sigma>') \<in> br'_step \<delta> 
   \<rbrakk> \<Longrightarrow> (br'_\<alpha> \<Sigma>, br'_\<alpha> \<Sigma>')\<in>br_step \<delta>"
  apply (cases \<Sigma>, cases \<Sigma>', simp)
  apply (erule br'_step.cases)
  apply (simp add: br'_\<alpha>_def)
  apply (rule_tac q=q in br_step.intros)
  apply simp
  apply (simp only: br'_rcm_aux2)
  apply (simp only: br'_rcm_aux3)
  done
  

lemma br'_initial_abs: "br'_\<alpha>`(br'_initial \<delta>) = {br_initial \<delta>}"
  apply (force simp add: br_initial_def br'_\<alpha>_def
               elim: br'_initial.cases 
               intro: br'_initial.intros)
  done

lemma br'_cond_abs: "\<Sigma>\<in>br'_cond \<longleftrightarrow> (br'_\<alpha> \<Sigma>) \<in> br_cond"
  by (cases \<Sigma>) 
     (simp add: br'_cond_def br_cond_def br'_\<alpha>_def image_Collect 
                br'_algo_def br_algo_def)

lemma bre'_cond_abs: "\<Sigma>\<in>bre'_cond Qi \<longleftrightarrow> (br'_\<alpha> \<Sigma>)\<in>bre_cond Qi"
  by (cases \<Sigma>) (simp add: bre'_cond_def bre_cond_def br'_\<alpha>_def image_Collect 
                          bre'_algo_def bre_algo_def)

lemma br'_invar_abs: "br'_\<alpha>`br'_invar \<delta> \<subseteq> br_invar \<delta>"
  by (auto simp add: br'_invar_def)

theorem br'_pref_br: "wa_precise_refine (br'_algo \<delta>) (br_algo \<delta>) br'_\<alpha>"
  apply unfold_locales
  apply (simp_all add: br'_algo_def br_algo_def)
  apply (simp_all add: br'_cond_abs br'_step_abs br'_invar_abs br'_initial_abs)
  done

interpretation br'_pref: wa_precise_refine "br'_algo \<delta>" "br_algo \<delta>" "br'_\<alpha>" 
  using br'_pref_br .

theorem br'_while_algo: 
  "finite \<delta> \<Longrightarrow> while_algo (br'_algo \<delta>)"
  apply (rule br'_pref.wa_intro)
  apply (simp add: br_while_algo)
  apply (simp_all add: br'_algo_def br_algo_def)
  apply (simp add: br'_invar_def)
  apply (erule (3) br'_step_invar)
  apply (simp add: br'_invar_initial)
  done

lemma fst_br'_\<alpha>: "fst (br'_\<alpha> s) = fst s" by (cases s) (simp add: br'_\<alpha>_def)

lemmas br'_invar_final = 
  br'_pref.transfer_correctness[OF br_invar_final, unfolded fst_br'_\<alpha>]

theorem bre'_pref_br: "wa_precise_refine (bre'_algo Qi \<delta>) (bre_algo Qi \<delta>) br'_\<alpha>"
  apply unfold_locales
  apply (simp_all add: bre'_algo_def bre_algo_def)
  apply (simp_all add: bre'_cond_abs br'_step_abs br'_invar_abs br'_initial_abs)
  done

interpretation bre'_pref: 
  wa_precise_refine "bre'_algo Qi \<delta>" "bre_algo Qi \<delta>" "br'_\<alpha>" 
  using bre'_pref_br .

theorem bre'_while_algo: 
  "finite \<delta> \<Longrightarrow> while_algo (bre'_algo Qi \<delta>)"
  apply (rule bre'_pref.wa_intro)
  apply (simp add: bre_while_algo)
  apply (simp_all add: bre'_algo_def bre_algo_def)
  apply (simp add: br'_invar_def)
  apply (erule (3) br'_step_invar)
  apply (simp add: br'_invar_initial)
  done

lemmas bre'_invar_final = 
  bre'_pref.transfer_correctness[OF bre_invar_final, unfolded fst_br'_\<alpha>]

text_raw \<open>\paragraph{Implementing a Step}\<close>
text \<open>
  In this paragraph, it is shown how to implement a step of the br'-algorithm 
  by iteration over the rules that have the discovered state on their RHS.
\<close>

definition br'_inner_step 
  :: "('Q,'L) ta_rule \<Rightarrow> ('Q,'L) br'_state \<Rightarrow> ('Q,'L) br'_state" 
  where
  "br'_inner_step == \<lambda>r (Q,W,rcm). let c=the (rcm r) in (
    if c\<le>1 then insert (lhs r) Q else Q,
    if c\<le>1 \<and> (lhs r) \<notin> Q then insert (lhs r) W else W,
    rcm ( r \<mapsto> (c-(1::nat)))
  )
"

definition br'_inner_invar 
  :: "('Q,'L) ta_rule set \<Rightarrow> 'Q \<Rightarrow> ('Q,'L) br'_state 
      \<Rightarrow> ('Q,'L) ta_rule set \<Rightarrow> ('Q,'L) br'_state \<Rightarrow> bool" 
  where
  "br'_inner_invar rules q == \<lambda>(Q,W,rcm) it (Q',W',rcm'). 
    Q' = Q \<union> { lhs r | r. r\<in>rules-it \<and> the (rcm r) \<le> 1 } \<and> 
    W' = (W-{q}) \<union> ({ lhs r | r. r\<in>rules-it \<and> the (rcm r) \<le> 1 } - Q) \<and> 
    (\<forall>r. rcm' r = (if r\<in>rules-it then Some (the (rcm r) - 1) else rcm r))
  "

lemma br'_inner_invar_imp_final: 
  "\<lbrakk> q\<in>W; br'_inner_invar {r\<in>\<delta>. q\<in>set (rhsq r)} q (Q,W-{q},rcm) {} \<Sigma>' \<rbrakk> 
     \<Longrightarrow> ((Q,W,rcm),\<Sigma>') \<in> br'_step \<delta>"
  apply (unfold br'_inner_invar_def)
  apply auto
  apply (rule br'_step.intros)
  apply assumption
  apply auto
  done

lemma br'_inner_invar_step: 
  "\<lbrakk> q\<in>W; br'_inner_invar {r\<in>\<delta>. q\<in>set (rhsq r)} q (Q,W-{q},rcm) it \<Sigma>'; 
     r\<in>it; it\<subseteq>{r\<in>\<delta>. q\<in>set (rhsq r)} 
   \<rbrakk> \<Longrightarrow> br'_inner_invar {r\<in>\<delta>. q\<in>set (rhsq r)} q (Q,W-{q},rcm) 
                         (it-{r}) (br'_inner_step r \<Sigma>')
  "
  apply (cases \<Sigma>', simp)
  apply (unfold br'_inner_invar_def br'_inner_step_def Let_def)
  apply auto
  done

lemma br'_inner_invar_initial: 
  "\<lbrakk> q\<in>W \<rbrakk> \<Longrightarrow> br'_inner_invar {r\<in>\<delta>. q\<in>set (rhsq r)} q (Q,W-{q},rcm) 
                               {r\<in>\<delta>. q\<in>set (rhsq r)} (Q,W-{q},rcm)"
  apply (simp add: br'_inner_invar_def)
  apply auto
  done

lemma br'_inner_step_proof:
  fixes \<alpha>s :: "'\<Sigma> \<Rightarrow> ('Q,'L) br'_state"
  fixes cstep :: "('Q,'L) ta_rule \<Rightarrow> '\<Sigma> \<Rightarrow> '\<Sigma>"
  fixes \<Sigma>h :: "'\<Sigma>"
  fixes cinvar :: "('Q,'L) ta_rule set \<Rightarrow> '\<Sigma> \<Rightarrow> bool"

  assumes iterable_set: "set_iteratei \<alpha> invar iteratei"
  assumes invar_initial: "cinvar {r\<in>\<delta>. q\<in>set (rhsq r)} \<Sigma>h"
  assumes invar_step: 
    "!!it r \<Sigma>. \<lbrakk> r\<in>it; it \<subseteq> {r\<in>\<delta>. q\<in>set (rhsq r)}; cinvar it \<Sigma> \<rbrakk> 
                 \<Longrightarrow> cinvar (it-{r}) (cstep r \<Sigma>)"
  assumes step_desc: 
    "!!it r \<Sigma>. \<lbrakk> r\<in>it; it\<subseteq>{r\<in>\<delta>. q\<in>set (rhsq r)}; cinvar it \<Sigma> \<rbrakk> 
                 \<Longrightarrow> \<alpha>s (cstep r \<Sigma>) = br'_inner_step r (\<alpha>s \<Sigma>)"
  assumes it_set_desc: "invar it_set" "\<alpha> it_set = {r\<in>\<delta>. q\<in>set (rhsq r)}"

  assumes QIW[simp]: "q\<in>W"

  assumes \<Sigma>_desc[simp]: "\<alpha>s \<Sigma> = (Q,W,rcm)"
  assumes \<Sigma>h_desc[simp]: "\<alpha>s \<Sigma>h = (Q,W-{q},rcm)"

  shows "(\<alpha>s \<Sigma>, \<alpha>s (iteratei it_set (\<lambda>_. True) cstep \<Sigma>h))\<in>br'_step \<delta>"
proof -
  interpret set_iteratei \<alpha> invar iteratei by fact

  show ?thesis
    apply (rule_tac 
      I="\<lambda>it \<Sigma>. cinvar it \<Sigma> 
                \<and> br'_inner_invar {r\<in>\<delta>. q\<in>set (rhsq r)} q (Q,W-{q},rcm) 
                                  it (\<alpha>s \<Sigma>)" 
      in iterate_rule_P)
    apply (simp_all 
      add: it_set_desc invar_initial br'_inner_invar_initial invar_step 
           step_desc br'_inner_invar_step)
    apply (rule br'_inner_invar_imp_final)
    apply (rule QIW)
    apply simp
    done
qed


text_raw \<open>\paragraph{Computing Witnesses}\<close>
text \<open>
  The algorithm is now refined further, such that it stores, for each discovered
  state, a witness for non-emptiness, i.e. a tree that is accepted with the
  discovered state.
\<close>

\<comment> \<open>A map from states to trees has the witness-property, if it maps states to 
    trees that are accepted with that state:\<close>
definition "witness_prop \<delta> m == \<forall>q t. m q = Some t \<longrightarrow> accs \<delta> t q"

\<comment> \<open>Construct a witness for the LHS of a rule, provided that the map contains 
    witnesses for all states on the RHS:\<close>
definition construct_witness 
  :: "('Q \<rightharpoonup> 'L tree) \<Rightarrow> ('Q,'L) ta_rule \<Rightarrow> 'L tree"
  where 
  "construct_witness Q r == NODE (rhsl r) (List.map (\<lambda>q. the (Q q)) (rhsq r))"

lemma witness_propD: "\<lbrakk>witness_prop \<delta> m; m q = Some t\<rbrakk> \<Longrightarrow> accs \<delta> t q" 
  by (auto simp add: witness_prop_def)

lemma construct_witness_correct: 
  "\<lbrakk> witness_prop \<delta> Q; r\<in>\<delta>; set (rhsq r) \<subseteq> dom Q \<rbrakk> 
    \<Longrightarrow> accs \<delta> (construct_witness Q r) (lhs r)"
  apply (unfold construct_witness_def witness_prop_def)
  apply (cases r)
  apply simp
  apply (erule accs.intros)
  apply (auto dest: nth_mem)
  done

lemma construct_witness_eq: 
  "\<lbrakk> Q |` set (rhsq r) = Q' |` set (rhsq r) \<rbrakk> \<Longrightarrow> 
    construct_witness Q r = construct_witness Q' r"
  apply (unfold construct_witness_def)
  apply auto
  apply (subgoal_tac "Q x = Q' x")
  apply (simp)
  apply (drule_tac x=x in fun_cong)
  apply auto
  done

text \<open>
  The set of discovered states is refined by a map from discovered states to 
  their witnesses:
\<close>
type_synonym ('Q,'L) brw_state = "('Q\<rightharpoonup>'L tree) \<times> 'Q set \<times> (('Q,'L) ta_rule \<rightharpoonup> nat)"

definition brw_\<alpha> :: "('Q,'L) brw_state \<Rightarrow> ('Q,'L) br'_state" 
  where "brw_\<alpha> = (\<lambda>(Q,W,rcm). (dom Q,W,rcm))"

definition brw_invar_add :: "('Q,'L) ta_rule set \<Rightarrow> ('Q,'L) brw_state set"
  where "brw_invar_add \<delta> == {(Q,W,rcm). witness_prop \<delta> Q}"

definition "brw_invar \<delta> == brw_invar_add \<delta> \<inter> {s. brw_\<alpha> s \<in> br'_invar \<delta>}"

(* TODO:
    This step description does not allow full flexibility, because
    we may want to construct new witnesses from other witnesses constructed 
    in the same step!
    
    However, if we say t = construct_witness Q' r, may we run into cyclicity 
    problems, where a cycle of witnesses
    may witness itself?. Hmm? As these cyclic witnesses would have to
    be infinite, they cannot exist?

    But, if we use a BFS search strategy, the current step description will 
    compute minimal depth witnesses.
    The argumentation is, that:
      Initially, all witnesses of depth 1 (definitely minimal) are discovered
      A witness of depth n has children of length < n
      The states that are initially on the workset are all those with 
      witnesses of depth 1. Thus,
      after they have been processed, all states with witnesses of depth 2 have
      been discovered. This argument can be iterated inductively.
*)
inductive_set brw_step 
  :: "('Q,'L) ta_rule set \<Rightarrow> (('Q,'L) brw_state \<times> ('Q,'L) brw_state) set" 
  for \<delta> where
  "\<lbrakk> 
     q\<in>W;
     dsqr = { r\<in>\<delta>. q \<in> set (rhsq r) \<and> the (rcm r) \<le> 1 };
     dom Q' = dom Q \<union> lhs`dsqr;
     !!q t. Q' q = Some t \<Longrightarrow> Q q = Some t 
                              \<or> (\<exists>r\<in>dsqr. q=lhs r \<and> t=construct_witness Q r);
     W' = (W-{q}) \<union> (lhs`dsqr - dom Q);
     !!r. r\<in>\<delta> \<Longrightarrow> rcm' r = ( if q \<in> set (rhsq r) then 
                               Some (the (rcm r) - 1) 
                             else rcm r
                           )
   \<rbrakk> \<Longrightarrow> ((Q,W,rcm),(Q',W',rcm')) \<in> brw_step \<delta>"


definition brw_cond :: "'Q set \<Rightarrow> ('Q,'L) brw_state set" 
  where "brw_cond Qi == {(Q,W,rcm). W\<noteq>{} \<and> (Qi\<inter>dom Q={})}"

inductive_set brw_iq :: "('Q,'L) ta_rule set \<Rightarrow> ('Q \<rightharpoonup> 'L tree) set" 
  for \<delta> where 
  "\<lbrakk> 
    \<forall>q t. Q q = Some t \<longrightarrow> (\<exists>r\<in>\<delta>. rhsq r = [] \<and> q = lhs r 
                                  \<and> t = NODE (rhsl r) []);
    \<forall>r\<in>\<delta>. rhsq r = [] \<longrightarrow> Q (lhs r) \<noteq> None
   \<rbrakk> \<Longrightarrow> Q \<in> brw_iq \<delta>"

inductive_set brw_initial :: "('Q,'L) ta_rule set \<Rightarrow> ('Q,'L) brw_state set" 
  for \<delta> where
  "\<lbrakk> !!r. r\<in>\<delta> \<Longrightarrow> rcm r = Some (card (set (rhsq r))); Q\<in>brw_iq \<delta> \<rbrakk> 
     \<Longrightarrow> (Q, br_iq \<delta>, rcm)\<in>brw_initial \<delta>"

definition "brw_algo Qi \<delta> == \<lparr>
  wa_cond=brw_cond Qi,
  wa_step = brw_step \<delta>,
  wa_initial = brw_initial \<delta>,
  wa_invar = brw_invar \<delta>
\<rparr>"

lemma brw_cond_abs: "\<Sigma>\<in>brw_cond Qi \<longleftrightarrow> (brw_\<alpha> \<Sigma>)\<in>bre'_cond Qi"
  apply (cases \<Sigma>)
  apply (simp add: brw_cond_def bre'_cond_def brw_\<alpha>_def)
  done

lemma brw_initial_abs: "\<Sigma>\<in>brw_initial \<delta> \<Longrightarrow> brw_\<alpha> \<Sigma> \<in> br'_initial \<delta>"
  apply (cases \<Sigma>, simp)
  apply (erule brw_initial.cases)
  apply (erule brw_iq.cases)
  apply (auto simp add: brw_\<alpha>_def)
  apply (subgoal_tac "dom Qa = br_iq \<delta>")
  apply simp
  apply (rule br'_initial.intros)
  apply auto [1]
  apply (force simp add: br_iq_def)
  done


lemma brw_invar_initial: "brw_initial \<delta> \<subseteq> brw_invar_add \<delta>"
  apply safe
  apply (unfold brw_invar_add_def)
  apply (auto simp add: witness_prop_def)
  apply (erule brw_initial.cases)
  apply (erule brw_iq.cases)
  apply auto
proof goal_cases
  case prems: (1 q t rcm Q)
  from prems(3)[rule_format, OF prems(1)] obtain r where 
    [simp]: "r\<in>\<delta>" "rhsq r = []" "q=lhs r" "t=NODE (rhsl r) []" 
    by blast
  have RF[simplified]: "r=((lhs r) \<rightarrow> (rhsl r) (rhsq r))" by (cases r) simp
  show ?case 
    apply (simp)
    apply (rule accs.intros)
    apply (subst RF[symmetric])
    apply auto
    done
qed
    
lemma brw_step_abs:
  "\<lbrakk> (\<Sigma>,\<Sigma>')\<in>brw_step \<delta> \<rbrakk> \<Longrightarrow> (brw_\<alpha> \<Sigma>, brw_\<alpha> \<Sigma>')\<in>br'_step \<delta>"
  apply (cases \<Sigma>, cases \<Sigma>', simp)
  apply (erule brw_step.cases)
  apply (simp add: brw_\<alpha>_def)
  apply hypsubst
  apply (rule br'_step.intros)
  apply assumption
  apply auto
  done

lemma brw_step_invar:
  assumes FIN[simp]: "finite \<delta>"
  assumes INV: "\<Sigma>\<in>brw_invar_add \<delta>" and BR'INV: "brw_\<alpha> \<Sigma> \<in> br'_invar \<delta>"
  assumes STEP: "(\<Sigma>,\<Sigma>') \<in> brw_step \<delta>"
  shows "\<Sigma>'\<in>brw_invar_add \<delta>"
proof -
  obtain Q W rcm Q' W' rcm' where 
    [simp]: "\<Sigma>=(Q,W,rcm)" "\<Sigma>'=(Q',W',rcm')" 
    by (cases \<Sigma>, cases \<Sigma>') force

  from INV have WP: "witness_prop \<delta> Q" 
    by (simp_all add: brw_invar_add_def)

  obtain qw dsqr where SPROPS:
    "dsqr = {r \<in> \<delta>. qw \<in> set (rhsq r) \<and> the (rcm r) \<le> 1}"
    "qw\<in>W"
    "dom Q' = dom Q \<union> lhs ` dsqr"
    "!!q t. Q' q = Some t \<Longrightarrow> Q q = Some t 
                              \<or> (\<exists>r\<in>dsqr. q=lhs r \<and> t=construct_witness Q r)"
    by (auto intro: brw_step.cases[OF STEP[simplified]])
  from br'_rcm_aux'[OF BR'INV[unfolded brw_\<alpha>_def, simplified] SPROPS(2)] have 
    DSQR_ALT: "dsqr = {r \<in> \<delta>. qw \<in> set (rhsq r) 
                              \<and> set (rhsq r) \<subseteq> dom Q - (W - {qw})}" 
    by (simp add: SPROPS(1))
  have "witness_prop \<delta> Q'" 
  proof (unfold witness_prop_def, safe)
    fix q t
    assume A: "Q' q = Some t"

    from SPROPS(4)[OF A] have 
      "Q q = Some t \<or> (\<exists>r\<in>dsqr. q = lhs r \<and> t = construct_witness Q r)" .
    moreover {
      assume C: "Q q = Some t"
      from witness_propD[OF WP, OF C] have "accs \<delta> t q" .
    } moreover {
      fix r
      assume "r\<in>dsqr" and [simp]: "q=lhs r" "t=construct_witness Q r"
      from \<open>r\<in>dsqr\<close> have 1: "r\<in>\<delta>" "set (rhsq r) \<subseteq> dom Q" 
        by (auto simp add: DSQR_ALT)
      from construct_witness_correct[OF WP 1] have "accs \<delta> t q" by simp
    } ultimately show "accs \<delta> t q" by blast
  qed
  thus ?thesis by (simp add: brw_invar_add_def)
qed
      
theorem brw_pref_bre': "wa_precise_refine (brw_algo Qi \<delta>) (bre'_algo Qi \<delta>) brw_\<alpha>"
  apply (unfold_locales)
  apply (simp_all add: brw_algo_def bre'_algo_def)
  apply (auto simp add: brw_cond_abs brw_step_abs brw_initial_abs brw_invar_def)
  done

interpretation brw_pref: 
  wa_precise_refine "brw_algo Qi \<delta>" "bre'_algo Qi \<delta>" "brw_\<alpha>" 
  using brw_pref_bre' .

theorem brw_while_algo: "finite \<delta> \<Longrightarrow> while_algo (brw_algo Qi \<delta>)"
  apply (rule brw_pref.wa_intro)
  apply (simp add: bre'_while_algo)
  apply (simp_all add: brw_algo_def bre'_algo_def)
  apply (simp add: brw_invar_def)
  apply (auto intro: brw_step_invar simp add: brw_invar_initial)
  done

lemma fst_brw_\<alpha>: "fst (brw_\<alpha> s) = dom (fst s)" 
  by (cases s) (simp add: brw_\<alpha>_def)

theorem brw_invar_final: 
  "\<forall>sc. sc \<in> wa_invar (brw_algo Qi \<delta>) \<and> sc \<notin> wa_cond (brw_algo Qi \<delta>) 
    \<longrightarrow> (Qi \<inter> dom (fst sc) = {}) = (Qi \<inter> b_accessible \<delta> = {}) 
        \<and> (witness_prop \<delta> (fst sc))"
  apply (intro conjI allI impI)
  using brw_pref.transfer_correctness[OF bre'_invar_final, unfolded fst_brw_\<alpha>] 
    apply blast
  apply (auto simp add: brw_algo_def brw_invar_def brw_invar_add_def)
  done
     

text_raw \<open>\paragraph{Implementing a Step}\<close>
inductive_set brw_inner_step 
  :: "('Q,'L) ta_rule \<Rightarrow> (('Q,'L) brw_state \<times> ('Q,'L) brw_state) set" 
  for r where
  "\<lbrakk>  c = the (rcm r); \<Sigma> = (Q,W,rcm); \<Sigma>'=(Q',W',rcm');
     if c\<le>1 \<and> (lhs r) \<notin> dom Q then 
       Q' = Q(lhs r \<mapsto> construct_witness Q r) 
     else Q' = Q;
     if c\<le>1 \<and> (lhs r) \<notin> dom Q then 
       W' = insert (lhs r) W 
     else W' = W;
     rcm' = rcm ( r \<mapsto> (c-(1::nat)))
   \<rbrakk> \<Longrightarrow> (\<Sigma>,\<Sigma>')\<in>brw_inner_step r"

definition brw_inner_invar 
  :: "('Q,'L) ta_rule set \<Rightarrow> 'Q \<Rightarrow> ('Q,'L) brw_state \<Rightarrow> ('Q,'L) ta_rule set 
      \<Rightarrow> ('Q,'L) brw_state \<Rightarrow> bool" 
  where
  "brw_inner_invar rules q == \<lambda>(Q,W,rcm) it (Q',W',rcm').
    (br'_inner_invar rules q (brw_\<alpha> (Q,W,rcm)) it (brw_\<alpha> (Q',W',rcm')) \<and>  
    (Q'|`dom Q = Q) \<and> 
    (let dsqr = { r\<in>rules - it. the (rcm r) \<le> 1 } in
      (\<forall>q t. Q' q = Some t \<longrightarrow> (Q q = Some t 
           \<or> (Q q = None \<and> (\<exists>r\<in>dsqr. q=lhs r \<and> t=construct_witness Q r))
                                )
      )))
  "

lemma brw_inner_step_abs: 
  "(\<Sigma>,\<Sigma>')\<in>brw_inner_step r \<Longrightarrow> br'_inner_step r (brw_\<alpha> \<Sigma>) = brw_\<alpha> \<Sigma>'"
  apply (erule brw_inner_step.cases)
  apply (unfold br'_inner_step_def brw_\<alpha>_def Let_def)
  apply auto
  done


lemma brw_inner_invar_imp_final: 
  "\<lbrakk> q\<in>W; brw_inner_invar {r\<in>\<delta>. q\<in>set (rhsq r)} q (Q,W-{q},rcm) {} \<Sigma>' \<rbrakk> 
    \<Longrightarrow> ((Q,W,rcm),\<Sigma>') \<in> brw_step \<delta>"
  apply (unfold brw_inner_invar_def br'_inner_invar_def brw_\<alpha>_def)
  apply (auto simp add: Let_def)
  apply (rule brw_step.intros)
  apply assumption
  apply (rule refl)
  apply auto
  done


lemma brw_inner_invar_step: 
  assumes INVI: "(Q,W,rcm)\<in>brw_invar \<delta>"
  assumes A: "q\<in>W" "r\<in>it" "it\<subseteq>{r\<in>\<delta>. q\<in>set (rhsq r)}" 
  assumes INVH: "brw_inner_invar {r\<in>\<delta>. q\<in>set (rhsq r)} q (Q,W-{q},rcm) it \<Sigma>h"
  assumes STEP: "(\<Sigma>h,\<Sigma>')\<in>brw_inner_step r" 
  shows "brw_inner_invar {r\<in>\<delta>. q\<in>set (rhsq r)} q (Q,W-{q},rcm) (it-{r}) \<Sigma>'"
proof -
  from INVI have BR'_INV: "(dom Q,W,rcm)\<in>br'_invar \<delta>"
    by (simp add: brw_invar_def brw_\<alpha>_def)

  obtain c Qh Wh rcmh Q' W' rcm' where
    SIGMAF[simp]: "\<Sigma>h=(Qh,Wh,rcmh)" "\<Sigma>'=(Q',W',rcm')" and
    CF[simp]: "c = the (rcmh r)" and
    SF: "if c\<le>1 \<and> (lhs r) \<notin> dom Qh then 
           Q' = Qh(lhs r \<mapsto> (construct_witness Qh r)) 
         else Q' = Qh"

        "if c\<le>1 \<and> (lhs r) \<notin> dom Qh then 
           W' = insert (lhs r) Wh 
         else W' = Wh"

        "rcm' = rcmh ( r \<mapsto> (c-(1::nat)))"
    by (blast intro: brw_inner_step.cases[OF STEP])
  let ?rules = "{r\<in>\<delta>. q\<in>set (rhsq r)}"
  let ?dsqr = "\<lambda>it. { r\<in>?rules - it. the (rcm r) \<le> 1 }"
  from INVH have INVHF:
    "br'_inner_invar ?rules q (dom Q, W-{q}, rcm) (it) (dom Qh,Wh,rcmh)"
    "Qh|`dom Q = Q"
    "(\<forall>q t. Qh q = Some t \<longrightarrow> (Q q = Some t 
         \<or> (Q q = None \<and> (\<exists>r\<in>?dsqr it. q=lhs r \<and> t=construct_witness Q r))
                               )
     )"
    by (auto simp add: brw_inner_invar_def Let_def brw_\<alpha>_def)
  from INVHF(1)[unfolded br'_inner_invar_def] have INV'HF:
    "dom Qh = dom Q \<union> lhs`?dsqr it"
    "(\<forall>r. rcmh r = (if r \<in> ?rules - it then 
                      Some (the (rcm r) - 1) 
                    else rcm r))"
    by auto
  from brw_inner_step_abs[OF STEP] 
       br'_inner_invar_step[OF A(1) INVHF(1) A(2,3)] have 
    G1: "br'_inner_invar ?rules q (dom Q, W-{q}, rcm) (it-{r}) (dom Q',W',rcm')"
    by (simp add: brw_\<alpha>_def)
  moreover have
    "(\<forall>q t. Q' q = Some t \<longrightarrow> (Q q = Some t 
        \<or> ( Q q = None 
            \<and> (\<exists>r\<in>?dsqr (it-{r}). q=lhs r \<and> t=construct_witness Q r)
           ) 
                              ) 
     )" (is ?G1)

    "Q'|`dom Q = Q" (is ?G2)
  proof -
    {
      assume C: "\<not> c\<le>1 \<or> lhs r \<in> dom Qh"
      with SF have "Q'=Qh" by auto
      with INVHF(2,3) have ?G1 ?G2 by auto
    } moreover {
      assume C: "c\<le>1" "lhs r\<notin> dom Qh"
      with SF have Q'F: "Q'=Qh(lhs r \<mapsto> (construct_witness Qh r))" by auto
      from C(2) INVHF(2) INV'HF(1) have G2: ?G2 by (auto simp add: Q'F)
      from C(1) INV'HF A have 
        RI: "r\<in>?dsqr (it-{r})" and 
        DSS: "dom Q \<subseteq> dom Qh" 
        by (auto)
      from br'_rcm_aux'[OF BR'_INV A(1)] RI have 
        RDQ: "set (rhsq r) \<subseteq> dom Q" 
        by auto
      with INVHF(2) have "Qh |` set (rhsq r) = Q |` set (rhsq r)"
        by (blast intro: restrict_map_subset_eq)
      hence [simp]: "construct_witness Qh r = construct_witness Q r" 
        by (blast dest: construct_witness_eq)

      from DSS C(2) have [simp]: "Q (lhs r) = None" "Qh (lhs r) = None" by auto
      have G1: ?G1
      proof (intro allI impI, goal_cases)
        case prems: (1 q t)
        {
          assume [simp]: "q=lhs r"
          from prems Q'F have [simp]: "t = (construct_witness Qh r)" by simp
          from RI have ?case by auto
        } moreover {
          assume "q\<noteq>lhs r"
          with Q'F prems have "Qh q = Some t" by auto
          with INVHF(3) have ?case by auto
        } ultimately show ?case by blast
      qed
      note G1 G2
    } ultimately show ?G1 ?G2 by blast+
  qed
  ultimately show ?thesis
    by (unfold brw_inner_invar_def Let_def brw_\<alpha>_def) auto
qed


lemma brw_inner_invar_initial: 
  "\<lbrakk>q\<in>W\<rbrakk> \<Longrightarrow> brw_inner_invar {r\<in>\<delta>. q\<in>set (rhsq r)} q (Q,W-{q},rcm) 
                             {r\<in>\<delta>. q\<in>set (rhsq r)} (Q,W-{q},rcm)"
  by (simp add: brw_inner_invar_def br'_inner_invar_initial brw_\<alpha>_def)

theorem brw_inner_step_proof:
  fixes \<alpha>s :: "'\<Sigma> \<Rightarrow> ('Q,'L) brw_state"
  fixes cstep :: "('Q,'L) ta_rule \<Rightarrow> '\<Sigma> \<Rightarrow> '\<Sigma>"
  fixes \<Sigma>h :: "'\<Sigma>"
  fixes cinvar :: "('Q,'L) ta_rule set \<Rightarrow> '\<Sigma> \<Rightarrow> bool"

  assumes set_iterate: "set_iteratei \<alpha> invar iteratei"
  assumes invar_start: "(\<alpha>s \<Sigma>)\<in>brw_invar \<delta>"
  assumes invar_initial: "cinvar {r\<in>\<delta>. q\<in>set (rhsq r)} \<Sigma>h"
  assumes invar_step: 
    "!!it r \<Sigma>. \<lbrakk> r\<in>it; it \<subseteq> {r\<in>\<delta>. q\<in>set (rhsq r)}; cinvar it \<Sigma> \<rbrakk> 
                \<Longrightarrow> cinvar (it-{r}) (cstep r \<Sigma>)"
  assumes step_desc: 
    "!!it r \<Sigma>. \<lbrakk> r\<in>it; it\<subseteq>{r\<in>\<delta>. q\<in>set (rhsq r)}; cinvar it \<Sigma> \<rbrakk> 
                \<Longrightarrow> (\<alpha>s \<Sigma>, \<alpha>s (cstep r \<Sigma>)) \<in> brw_inner_step r"
  assumes it_set_desc: "invar it_set" "\<alpha> it_set = {r\<in>\<delta>. q\<in>set (rhsq r)}"

  assumes QIW[simp]: "q\<in>W"

  assumes \<Sigma>_desc[simp]: "\<alpha>s \<Sigma> = (Q,W,rcm)"
  assumes \<Sigma>h_desc[simp]: "\<alpha>s \<Sigma>h = (Q,W-{q},rcm)"

  shows "(\<alpha>s \<Sigma>, \<alpha>s (iteratei it_set (\<lambda>_. True) cstep \<Sigma>h))\<in>brw_step \<delta>"
proof -
  interpret set_iteratei \<alpha> invar iteratei by fact

  show ?thesis
    apply (rule_tac 
      I="\<lambda>it \<Sigma>. cinvar it \<Sigma> \<and> brw_inner_invar {r\<in>\<delta>. q\<in>set (rhsq r)} q 
                                                (Q,W-{q},rcm) it (\<alpha>s \<Sigma>)" 
      in iterate_rule_P)
    apply (auto 
      simp add: it_set_desc invar_initial brw_inner_invar_initial invar_step 
                step_desc brw_inner_invar_step[OF invar_start[simplified]] 
                brw_inner_invar_imp_final[OF QIW])
    done
qed

subsection \<open>Product Automaton\<close>

text \<open>
  The forward-reduced product automaton can be described as a state-space
  exploration problem. 

  In this section, the DFS-algorithm for state-space exploration 
  (cf. Theory~@{theory Collections_Examples.Exploration} in the Isabelle Collections Framework) is refined to compute the product automaton.
\<close>

type_synonym ('Q1,'Q2,'L) frp_state = 
  "('Q1\<times>'Q2) set \<times> ('Q1\<times>'Q2) list \<times> (('Q1\<times>'Q2),'L) ta_rule set"

definition frp_\<alpha> :: "('Q1,'Q2,'L) frp_state \<Rightarrow> ('Q1\<times>'Q2) dfs_state"
  where "frp_\<alpha> S == let (Q,W,\<delta>)=S in (Q, W)"

definition "frp_invar_add \<delta>1 \<delta>2 == 
  { (Q,W,\<delta>d). \<delta>d = { r. r\<in>\<delta>_prod \<delta>1 \<delta>2 \<and> lhs r \<in> Q - set W} }"

definition frp_invar 
  :: "('Q1, 'L) tree_automaton_rec \<Rightarrow> ('Q2, 'L) tree_automaton_rec 
      \<Rightarrow> ('Q1,'Q2,'L) frp_state set"
  where "frp_invar T1 T2 == 
  frp_invar_add (ta_rules T1) (ta_rules T2) 
  \<inter> { s. frp_\<alpha> s \<in> dfs_invar (ta_initial T1 \<times> ta_initial T2) 
                              (f_succ (\<delta>_prod (ta_rules T1) (ta_rules T2))) }"

inductive_set frp_step 
  :: "('Q1,'L) ta_rule set \<Rightarrow> ('Q2,'L) ta_rule set 
      \<Rightarrow> (('Q1,'Q2,'L) frp_state \<times> ('Q1,'Q2,'L) frp_state) set" 
  for \<delta>1 \<delta>2 where
  "\<lbrakk> W=(q1,q2)#Wtl;
     distinct Wn;
     set Wn = f_succ (\<delta>_prod \<delta>1 \<delta>2) `` {(q1,q2)} - Q;
     W'=Wn@Wtl;
     Q'=Q \<union> f_succ (\<delta>_prod \<delta>1 \<delta>2) `` {(q1,q2)};
     \<delta>d'=\<delta>d \<union> {r\<in>\<delta>_prod \<delta>1 \<delta>2. lhs r = (q1,q2) }
  \<rbrakk> \<Longrightarrow> ((Q,W,\<delta>d),(Q',W',\<delta>d'))\<in>frp_step \<delta>1 \<delta>2"

inductive_set frp_initial :: "'Q1 set \<Rightarrow> 'Q2 set \<Rightarrow> ('Q1,'Q2,'L) frp_state set"
  for Q10 Q20 where 
  "\<lbrakk> distinct W; set W = Q10\<times>Q20 \<rbrakk> \<Longrightarrow> (Q10\<times>Q20,W,{}) \<in> frp_initial Q10 Q20"

definition frp_cond :: "('Q1,'Q2,'L) frp_state set" where
  "frp_cond == {(Q,W,\<delta>d). W\<noteq>[]}"

definition "frp_algo T1 T2 == \<lparr>
  wa_cond = frp_cond,
  wa_step = frp_step (ta_rules T1) (ta_rules T2),
  wa_initial = frp_initial (ta_initial T1) (ta_initial T2),
  wa_invar = frp_invar T1 T2
\<rparr>"

  \<comment> \<open>The algorithm refines the DFS-algorithm\<close>
theorem frp_pref_dfs: 
  "wa_precise_refine (frp_algo T1 T2) 
     (dfs_algo (ta_initial T1 \<times> ta_initial T2) 
               (f_succ (\<delta>_prod (ta_rules T1) (ta_rules T2))))
     frp_\<alpha>"
  apply unfold_locales
  apply (auto simp add: frp_algo_def frp_\<alpha>_def frp_cond_def dfs_algo_def 
                        dfs_cond_def frp_invar_def
    elim!: frp_step.cases frp_initial.cases
    intro: dfs_step.intros dfs_initial.intros
  )
  done 

interpretation frp_ref: wa_precise_refine "(frp_algo T1 T2)"
                  "(dfs_algo (ta_initial T1 \<times> ta_initial T2) 
                             (f_succ (\<delta>_prod (ta_rules T1) (ta_rules T2))))"
                  "frp_\<alpha>" using frp_pref_dfs .

\<comment> \<open>The algorithm is a well-defined while-algorithm\<close>
theorem frp_while_algo:
  assumes TA: "tree_automaton T1" 
              "tree_automaton T2"
  shows "while_algo (frp_algo T1 T2)"
proof -
  interpret t1: tree_automaton T1 by fact
  interpret t2: tree_automaton T2 by fact

  have finite: "finite ((f_succ (\<delta>_prod (ta_rules T1) (ta_rules T2)))\<^sup>* 
               `` (ta_initial T1 \<times> ta_initial T2))"
  proof -
    have "((f_succ (\<delta>_prod (ta_rules T1) (ta_rules T2)))\<^sup>* 
               `` (ta_initial T1 \<times> ta_initial T2)) 
          \<subseteq> ((ta_initial T1 \<times> ta_initial T2) 
             \<union> \<delta>_states (\<delta>_prod (ta_rules T1) (ta_rules T2)))"
      apply rule
      apply (drule f_accessible_subset[unfolded f_accessible_def])
      apply auto
      done
    moreover have "finite \<dots>"
      by auto
    ultimately show ?thesis by (simp add: finite_subset)
  qed

  show ?thesis
    apply (rule frp_ref.wa_intro)
    apply (rule dfs_while_algo[OF finite])
    apply (simp add: frp_algo_def dfs_algo_def frp_invar_def)
    apply (auto simp add: dfs_algo_def frp_algo_def frp_\<alpha>_def 
                          dfs_\<alpha>_def frp_invar_add_def dfs_invar_def 
                          dfs_invar_add_def sse_invar_def 
                elim!: frp_step.cases) [1]
    apply (force simp add: frp_algo_def frp_invar_add_def 
                 elim!: frp_initial.cases)
    done
qed

(* unused
lemma f_succ_adv: 
  "\<lbrakk>lhs r \<in> (f_succ \<delta>)\<^sup>* `` Q0; r\<in>\<delta>\<rbrakk> \<Longrightarrow> set (rhsq r) \<subseteq> (f_succ \<delta>)\<^sup>* `` Q0"
  by (case_tac r) (auto dest: rtrancl_into_rtrancl intro: f_succ.intros)
*)

\<comment> \<open>If the algorithm terminates, the forward reduced product automaton 
    can be constructed from the result\<close>
theorem frp_inv_final:
  "\<forall>s. s\<in>wa_invar (frp_algo T1 T2) \<and> s\<notin>wa_cond (frp_algo T1 T2)
       \<longrightarrow> (case s of (Q,W,\<delta>d) \<Rightarrow> 
             \<lparr> ta_initial = ta_initial T1 \<times> ta_initial T2, 
               ta_rules = \<delta>d 
             \<rparr> = ta_fwd_reduce (ta_prod T1 T2))"
  apply (intro allI impI)
  apply (case_tac s)
  apply simp
  apply (simp add: ta_reduce_def ta_prod_def frp_algo_def)
proof -
  fix Q W \<delta>d
  assume A: "(Q,W,\<delta>d)\<in>frp_invar T1 T2 \<and> (Q,W,\<delta>d)\<notin>frp_cond"

  from frp_ref.transfer_correctness[OF dfs_invar_final, 
                                    unfolded frp_algo_def, simplified, 
                                    rule_format, OF A]
  have [simp]: "Q = f_accessible (\<delta>_prod (ta_rules T1) (ta_rules T2)) 
                                 (ta_initial T1 \<times> ta_initial T2)"
    by (simp add: f_accessible_def dfs_\<alpha>_def frp_\<alpha>_def)

  from A show "\<delta>d = reduce_rules 
    (\<delta>_prod (ta_rules T1) (ta_rules T2)) 
    (f_accessible (\<delta>_prod (ta_rules T1) (ta_rules T2)) 
                  (ta_initial T1 \<times> ta_initial T2))"
    apply (auto simp add: reduce_rules_def f_accessible_def frp_invar_def 
                          frp_invar_add_def frp_\<alpha>_def frp_cond_def)
    apply (case_tac x) 
    apply (auto dest: rtrancl_into_rtrancl intro: f_succ.intros)
    done
qed


end
