section \<open>Slicing guarantees IFC Noninterference\<close>

theory NonInterferenceIntra imports 
  Slicing.Slice 
  Slicing.CFGExit_wf
begin

subsection \<open>Assumptions of this Approach\<close>

text \<open>
Classical IFC noninterference, a special case of a noninterference
definition using partial equivalence relations (per)
\cite{SabelfeldS:01}, partitions the variables (i.e.\ locations) into
security levels. Usually, only levels for secret or high, written
\<open>H\<close>, and public or low, written \<open>L\<close>, variables are
used. Basically, a program that is noninterferent has to fulfil one
basic property: executing the program in two different initial states
that may differ in the values of their \<open>H\<close>-variables yields two
final states that again only differ in the values of their 
\<open>H\<close>-variables; thus the values of the \<open>H\<close>-variables did not
influence those of the \<open>L\<close>-variables.

Every per-based approach makes certain
assumptions: (i) all \mbox{\<open>H\<close>-variables} are defined at the
beginning of the program, (ii) all \<open>L\<close>-variables are observed (or
used in our terms) at the end and (iii) every variable is either
\<open>H\<close> or \<open>L\<close>. This security label is fixed for a variable
and can not be altered during a program run. Thus, we have to extend 
the prerequisites of the slicing framework in \cite{Wasserrab:08} accordingly
in a new locale:

\<close>

locale NonInterferenceIntraGraph = 
  BackwardSlice sourcenode targetnode kind valid_edge Entry Def Use state_val 
  backward_slice +
  CFGExit_wf sourcenode targetnode kind valid_edge Entry Def Use state_val Exit
  for sourcenode :: "'edge \<Rightarrow> 'node" and targetnode :: "'edge \<Rightarrow> 'node"
  and kind :: "'edge \<Rightarrow> 'state edge_kind" and valid_edge :: "'edge \<Rightarrow> bool"
  and Entry :: "'node" ("'('_Entry'_')") and Def :: "'node \<Rightarrow> 'var set"
  and Use :: "'node \<Rightarrow> 'var set" and state_val :: "'state \<Rightarrow> 'var \<Rightarrow> 'val"
  and backward_slice :: "'node set \<Rightarrow> 'node set" 
  and Exit :: "'node" ("'('_Exit'_')") +
  fixes H :: "'var set"
  fixes L :: "'var set"
  fixes High :: "'node"  ("'('_High'_')")
  fixes Low :: "'node"   ("'('_Low'_')")
  assumes Entry_edge_Exit_or_High:
  "\<lbrakk>valid_edge a; sourcenode a = (_Entry_)\<rbrakk> 
    \<Longrightarrow> targetnode a = (_Exit_) \<or> targetnode a = (_High_)"
  and High_target_Entry_edge:
  "\<exists>a. valid_edge a \<and> sourcenode a = (_Entry_) \<and> targetnode a = (_High_) \<and>
       kind a = (\<lambda>s. True)\<^sub>\<surd>"
  and Entry_predecessor_of_High:
  "\<lbrakk>valid_edge a; targetnode a = (_High_)\<rbrakk> \<Longrightarrow> sourcenode a = (_Entry_)"
  and Exit_edge_Entry_or_Low: "\<lbrakk>valid_edge a; targetnode a = (_Exit_)\<rbrakk> 
    \<Longrightarrow> sourcenode a = (_Entry_) \<or> sourcenode a = (_Low_)"
  and Low_source_Exit_edge:
  "\<exists>a. valid_edge a \<and> sourcenode a = (_Low_) \<and> targetnode a = (_Exit_) \<and> 
       kind a = (\<lambda>s. True)\<^sub>\<surd>"
  and Exit_successor_of_Low:
  "\<lbrakk>valid_edge a; sourcenode a = (_Low_)\<rbrakk> \<Longrightarrow> targetnode a = (_Exit_)"
  and DefHigh: "Def (_High_) = H" 
  and UseHigh: "Use (_High_) = H"
  and UseLow: "Use (_Low_) = L"
  and HighLowDistinct: "H \<inter> L = {}"
  and HighLowUNIV: "H \<union> L = UNIV"

begin

lemma Low_neq_Exit: assumes "L \<noteq> {}" shows "(_Low_) \<noteq> (_Exit_)"
proof
  assume "(_Low_) = (_Exit_)"
  have "Use (_Exit_) = {}" by fastforce
  with UseLow \<open>L \<noteq> {}\<close> \<open>(_Low_) = (_Exit_)\<close> show False by simp
qed

lemma Entry_path_High_path:
  assumes "(_Entry_) -as\<rightarrow>* n" and "inner_node n"
  obtains a' as' where "as = a'#as'" and "(_High_) -as'\<rightarrow>* n" 
  and "kind a' = (\<lambda>s. True)\<^sub>\<surd>"
proof(atomize_elim)
  from \<open>(_Entry_) -as\<rightarrow>* n\<close> \<open>inner_node n\<close>
  show "\<exists>a' as'. as = a'#as' \<and> (_High_) -as'\<rightarrow>* n \<and> kind a' = (\<lambda>s. True)\<^sub>\<surd>"
  proof(induct n'\<equiv>"(_Entry_)" as n rule:path.induct)
    case (Cons_path n'' as n' a)
    from \<open>n'' -as\<rightarrow>* n'\<close> \<open>inner_node n'\<close> have "n'' \<noteq> (_Exit_)" 
      by(fastforce simp:inner_node_def)
    with \<open>valid_edge a\<close> \<open>targetnode a = n''\<close> \<open>sourcenode a = (_Entry_)\<close>
    have "n'' = (_High_)" by -(drule Entry_edge_Exit_or_High,auto)
    from High_target_Entry_edge
    obtain a' where "valid_edge a'" and "sourcenode a' = (_Entry_)"
      and "targetnode a' = (_High_)" and "kind a' = (\<lambda>s. True)\<^sub>\<surd>"
      by blast
    with \<open>valid_edge a\<close> \<open>sourcenode a = (_Entry_)\<close> \<open>targetnode a = n''\<close>
      \<open>n'' = (_High_)\<close>
    have "a = a'" by(auto dest:edge_det)
    with \<open>n'' -as\<rightarrow>* n'\<close> \<open>n'' = (_High_)\<close> \<open>kind a' = (\<lambda>s. True)\<^sub>\<surd>\<close> show ?case by blast
  qed fastforce
qed



lemma Exit_path_Low_path:
  assumes "n -as\<rightarrow>* (_Exit_)" and "inner_node n"
  obtains a' as' where "as = as'@[a']" and "n -as'\<rightarrow>* (_Low_)"
  and "kind a' = (\<lambda>s. True)\<^sub>\<surd>"
proof(atomize_elim)
  from \<open>n -as\<rightarrow>* (_Exit_)\<close>
  show "\<exists>as' a'. as = as'@[a'] \<and> n -as'\<rightarrow>* (_Low_) \<and> kind a' = (\<lambda>s. True)\<^sub>\<surd>"
  proof(induct as rule:rev_induct)
    case Nil
    with \<open>inner_node n\<close> show ?case by fastforce
  next
    case (snoc a' as')
    from \<open>n -as'@[a']\<rightarrow>* (_Exit_)\<close>
    have "n -as'\<rightarrow>* sourcenode a'" and "valid_edge a'" and "targetnode a' = (_Exit_)"
      by(auto elim:path_split_snoc)
    { assume "sourcenode a' = (_Entry_)"
      with \<open>n -as'\<rightarrow>* sourcenode a'\<close> have "n = (_Entry_)"
        by(blast intro!:path_Entry_target)
      with \<open>inner_node n\<close> have False by(simp add:inner_node_def) }
    with \<open>valid_edge a'\<close> \<open>targetnode a' = (_Exit_)\<close> have "sourcenode a' = (_Low_)"
      by(blast dest!:Exit_edge_Entry_or_Low)
    from Low_source_Exit_edge
    obtain ax where "valid_edge ax" and "sourcenode ax = (_Low_)"
      and "targetnode ax = (_Exit_)" and "kind ax = (\<lambda>s. True)\<^sub>\<surd>"
      by blast
    with \<open>valid_edge a'\<close> \<open>targetnode a' = (_Exit_)\<close> \<open>sourcenode a' = (_Low_)\<close>
    have "a' = ax" by(fastforce intro:edge_det)
    with \<open>n -as'\<rightarrow>* sourcenode a'\<close> \<open>sourcenode a' = (_Low_)\<close> \<open>kind ax = (\<lambda>s. True)\<^sub>\<surd>\<close>
    show ?case by blast
  qed
qed


lemma not_Low_High: "V \<notin> L \<Longrightarrow> V \<in> H"
  using HighLowUNIV
  by fastforce

lemma not_High_Low: "V \<notin> H \<Longrightarrow> V \<in> L"
  using HighLowUNIV
  by fastforce


subsection \<open>Low Equivalence\<close>

text \<open>
In classical noninterference, an external observer can only see public values,
in our case the \<open>L\<close>-variables. If two states agree in the values of all 
\<open>L\<close>-variables, these states are indistinguishable for him. 
\emph{Low equivalence} groups those states in an equivalence class using 
the relation \<open>\<approx>\<^sub>L\<close>:
\<close>

definition lowEquivalence :: "'state \<Rightarrow> 'state \<Rightarrow> bool" (infixl "\<approx>\<^sub>L" 50)
  where "s \<approx>\<^sub>L s' \<equiv> \<forall>V \<in> L. state_val s V = state_val s' V"

text \<open>The following lemmas connect low equivalent states with
relevant variables as necessary in the correctness proof for slicing.\<close>

lemma relevant_vars_Entry:
  assumes "V \<in> rv S (_Entry_)" and "(_High_) \<notin> backward_slice S"
  shows "V \<in> L"
proof -
  from \<open>V \<in> rv S (_Entry_)\<close> obtain as n' where "(_Entry_) -as\<rightarrow>* n'"
    and "n' \<in> backward_slice S" and "V \<in> Use n'"
    and "\<forall>nx \<in> set(sourcenodes as). V \<notin> Def nx" by(erule rvE)
  from \<open>(_Entry_) -as\<rightarrow>* n'\<close> have "valid_node n'" by(rule path_valid_node)
  thus ?thesis
  proof(cases n' rule:valid_node_cases)
    case Entry
    with \<open>V \<in> Use n'\<close> have False by(simp add:Entry_empty)
    thus ?thesis by simp
  next
    case Exit
    with \<open>V \<in> Use n'\<close> have False by(simp add:Exit_empty)
    thus ?thesis by simp
  next
    case inner
    with \<open>(_Entry_) -as\<rightarrow>* n'\<close> obtain a' as' where "as = a'#as'"
      and "(_High_) -as'\<rightarrow>* n'" by -(erule Entry_path_High_path)
    from \<open>(_Entry_) -as\<rightarrow>* n'\<close> \<open>as = a'#as'\<close>
    have "sourcenode a' = (_Entry_)" by(fastforce elim:path.cases)
    show ?thesis
    proof(cases "as' = []")
      case True
      with \<open>(_High_) -as'\<rightarrow>* n'\<close> have "n' = (_High_)" by fastforce
      with \<open>n' \<in> backward_slice S\<close> \<open>(_High_) \<notin> backward_slice S\<close>
      have False by simp
      thus ?thesis by simp
    next
      case False
      with \<open>(_High_) -as'\<rightarrow>* n'\<close> have "hd (sourcenodes as') = (_High_)"
        by(rule path_sourcenode)
      from False have "hd (sourcenodes as') \<in> set (sourcenodes as')"
        by(fastforce intro:hd_in_set simp:sourcenodes_def)
      with \<open>as = a'#as'\<close> have "hd (sourcenodes as') \<in> set (sourcenodes as)"
        by(simp add:sourcenodes_def)
      with \<open>hd (sourcenodes as') = (_High_)\<close> \<open>\<forall>nx \<in> set(sourcenodes as). V \<notin> Def nx\<close>
      have "V \<notin> Def (_High_)" by fastforce
      hence "V \<notin> H" by(simp add:DefHigh)
      thus ?thesis by(rule not_High_Low)
    qed
  qed
qed



lemma lowEquivalence_relevant_nodes_Entry:
  assumes "s \<approx>\<^sub>L s'" and "(_High_) \<notin> backward_slice S"
  shows "\<forall>V \<in> rv S (_Entry_). state_val s V = state_val s' V"
proof
  fix V assume "V \<in> rv S (_Entry_)"
  with \<open>(_High_) \<notin> backward_slice S\<close> have "V \<in> L" by -(rule relevant_vars_Entry)
  with \<open>s \<approx>\<^sub>L s'\<close> show "state_val s V = state_val s' V" by(simp add:lowEquivalence_def)
qed



lemma rv_Low_Use_Low:
  assumes "(_Low_) \<in> S"
  shows "\<lbrakk>n -as\<rightarrow>* (_Low_); n -as'\<rightarrow>* (_Low_);
    \<forall>V \<in> rv S n. state_val s V = state_val s' V;
    preds (slice_kinds S as) s; preds (slice_kinds S as') s'\<rbrakk>
  \<Longrightarrow> \<forall>V \<in> Use (_Low_). state_val (transfers (slice_kinds S as) s) V =
                       state_val (transfers (slice_kinds S as') s') V"
proof(induct n as n\<equiv>"(_Low_)" arbitrary:as' s s' rule:path.induct)
  case empty_path
  { fix V assume "V \<in> Use (_Low_)"
    moreover
    from \<open>valid_node (_Low_)\<close> have "(_Low_) -[]\<rightarrow>* (_Low_)"
      by(fastforce intro:path.empty_path)
    moreover
    from \<open>valid_node (_Low_)\<close> \<open>(_Low_) \<in> S\<close> have "(_Low_) \<in> backward_slice S"
      by(fastforce intro:refl)
    ultimately have "V \<in> rv S (_Low_)"
      by(fastforce intro:rvI simp:sourcenodes_def) }
  hence "\<forall>V \<in> Use (_Low_). V \<in> rv S (_Low_)" by simp
  show ?case
  proof(cases "L = {}")
    case True with UseLow show ?thesis by simp
  next
    case False
    from \<open>(_Low_) -as'\<rightarrow>* (_Low_)\<close> have "as' = []"
    proof(induct n\<equiv>"(_Low_)" as' n'\<equiv>"(_Low_)" rule:path.induct)
      case (Cons_path n'' as a)
      from \<open>valid_edge a\<close> \<open>sourcenode a = (_Low_)\<close>
      have "targetnode a = (_Exit_)" by -(rule Exit_successor_of_Low,simp+)
      with \<open>targetnode a = n''\<close> \<open>n'' -as\<rightarrow>* (_Low_)\<close>
      have "(_Low_) = (_Exit_)" by -(rule path_Exit_source,fastforce)
      with False have False by -(drule Low_neq_Exit,simp)
      thus ?case by simp
    qed simp
    with \<open>\<forall>V \<in> Use (_Low_). V \<in> rv S (_Low_)\<close> 
      \<open>\<forall>V\<in>rv S (_Low_). state_val s V = state_val s' V\<close>
    show ?thesis by(auto simp:slice_kinds_def)
  qed
next
  case (Cons_path n'' as a n)
  note IH = \<open>\<And>as' s s'. \<lbrakk>n'' -as'\<rightarrow>* (_Low_);
    \<forall>V\<in>rv S n''. state_val s V = state_val s' V;
   preds (slice_kinds S as) s; preds (slice_kinds S as') s'\<rbrakk>
  \<Longrightarrow> \<forall>V\<in>Use (_Low_). state_val (transfers (slice_kinds S as) s) V =
                     state_val (transfers (slice_kinds S as') s') V\<close>
  show ?case
  proof(cases "L = {}")
    case True with UseLow show ?thesis by simp
  next
    case False
    show ?thesis
    proof(cases as')
      case Nil
      with \<open>n -as'\<rightarrow>* (_Low_)\<close> have "n = (_Low_)" by fastforce
      with \<open>valid_edge a\<close> \<open>sourcenode a = n\<close> have "targetnode a = (_Exit_)"
        by -(rule Exit_successor_of_Low,simp+)
      from Low_source_Exit_edge obtain ax where "valid_edge ax"
        and "sourcenode ax = (_Low_)" and "targetnode ax = (_Exit_)"
        and "kind ax = (\<lambda>s. True)\<^sub>\<surd>" by blast
      from \<open>valid_edge a\<close> \<open>sourcenode a = n\<close> \<open>n = (_Low_)\<close> \<open>targetnode a = (_Exit_)\<close>
        \<open>valid_edge ax\<close> \<open>sourcenode ax = (_Low_)\<close> \<open>targetnode ax = (_Exit_)\<close>
      have "a = ax" by(fastforce dest:edge_det)
      with \<open>kind ax = (\<lambda>s. True)\<^sub>\<surd>\<close> have "kind a = (\<lambda>s. True)\<^sub>\<surd>" by simp
      with \<open>targetnode a = (_Exit_)\<close> \<open>targetnode a = n''\<close> \<open>n'' -as\<rightarrow>* (_Low_)\<close>
      have "(_Low_) = (_Exit_)" by -(rule path_Exit_source,auto)
      with False have False by -(drule Low_neq_Exit,simp)
      thus ?thesis by simp
    next
      case (Cons ax asx)
      with \<open>n -as'\<rightarrow>* (_Low_)\<close> have "n = sourcenode ax" and "valid_edge ax" 
        and "targetnode ax -asx\<rightarrow>* (_Low_)" by(auto elim:path_split_Cons)
      show ?thesis
      proof(cases "targetnode ax = n''")
        case True
        with \<open>targetnode ax -asx\<rightarrow>* (_Low_)\<close> have "n'' -asx\<rightarrow>* (_Low_)" by simp
        from \<open>valid_edge ax\<close> \<open>valid_edge a\<close> \<open>n = sourcenode ax\<close> \<open>sourcenode a = n\<close>
          True \<open>targetnode a = n''\<close> have "ax = a" by(fastforce intro:edge_det)
        from \<open>preds (slice_kinds S (a#as)) s\<close> 
        have preds1:"preds (slice_kinds S as) (transfer (slice_kind S a) s)"
          by(simp add:slice_kinds_def)
        from \<open>preds (slice_kinds S as') s'\<close> Cons \<open>ax = a\<close>
        have preds2:"preds (slice_kinds S asx) 
          (transfer (slice_kind S a) s')"
          by(simp add:slice_kinds_def)
        from \<open>valid_edge a\<close> \<open>sourcenode a = n\<close> \<open>targetnode a = n''\<close>
          \<open>preds (slice_kinds S (a#as)) s\<close> \<open>preds (slice_kinds S as') s'\<close>
          \<open>ax = a\<close> Cons \<open>\<forall>V\<in>rv S n. state_val s V = state_val s' V\<close>
        have "\<forall>V\<in>rv S n''. state_val (transfer (slice_kind S a) s) V =
                                 state_val (transfer (slice_kind S a) s') V"
          by -(rule rv_edge_slice_kinds,auto)
        from IH[OF \<open>n'' -asx\<rightarrow>* (_Low_)\<close> this preds1 preds2] 
          Cons \<open>ax = a\<close> show ?thesis by(simp add:slice_kinds_def)
      next
        case False
        with \<open>valid_edge a\<close> \<open>valid_edge ax\<close> \<open>sourcenode a = n\<close> \<open>n = sourcenode ax\<close>
          \<open>targetnode a = n''\<close> \<open>preds (slice_kinds S (a#as)) s\<close>
          \<open>preds (slice_kinds S as') s'\<close> Cons
          \<open>\<forall>V\<in>rv S n. state_val s V = state_val s' V\<close>
        have False by -(rule rv_branching_edges_slice_kinds_False,auto)
        thus ?thesis by simp
      qed
    qed
  qed
qed


subsection \<open>The Correctness Proofs\<close>

text \<open>
In the following, we present two correctness proofs that slicing guarantees
IFC noninterference. In both theorems, 
\<open>(_High_) \<notin> backward_slice S\<close>, where \<open>(_Low_) \<in> S\<close>,
makes sure that no high variable (which are all defined in \<open>(_High_)\<close>) 
can influence a low variable (which are all used in \<open>(_Low_)\<close>).

First, a theorem regarding 
\<open>(_Entry_) -as\<rightarrow>* (_Exit_)\<close> paths in the control flow graph (CFG),
which agree to a complete program execution:\<close>

lemma nonInterference_path_to_Low:
  assumes "s \<approx>\<^sub>L s'" and "(_High_) \<notin> backward_slice S" and "(_Low_) \<in> S"
  and "(_Entry_) -as\<rightarrow>* (_Low_)" and "preds (kinds as) s"
  and "(_Entry_) -as'\<rightarrow>* (_Low_)" and "preds (kinds as') s'"
  shows "transfers (kinds as) s \<approx>\<^sub>L transfers (kinds as') s'"
proof -
  from \<open>(_Entry_) -as\<rightarrow>* (_Low_)\<close> \<open>preds (kinds as) s\<close> \<open>(_Low_) \<in> S\<close>
  obtain asx where "preds (slice_kinds S asx) s"
    and "\<forall>V \<in> Use (_Low_). state_val(transfers (slice_kinds S asx) s) V = 
                           state_val(transfers (kinds as) s) V"
    and "slice_edges S as = slice_edges S asx"
    and "(_Entry_) -asx\<rightarrow>* (_Low_)" by(erule fundamental_property_of_static_slicing)
  from \<open>(_Entry_) -as'\<rightarrow>* (_Low_)\<close> \<open>preds (kinds as') s'\<close> \<open>(_Low_) \<in> S\<close>
  obtain asx' where "preds (slice_kinds S asx') s'"
    and "\<forall>V \<in> Use (_Low_). state_val (transfers (slice_kinds S asx') s') V = 
                           state_val (transfers (kinds as') s') V"
    and "slice_edges S as' = slice_edges S asx'"
    and "(_Entry_) -asx'\<rightarrow>* (_Low_)" by(erule fundamental_property_of_static_slicing)
  from \<open>s \<approx>\<^sub>L s'\<close> \<open>(_High_) \<notin> backward_slice S\<close>
  have "\<forall>V \<in> rv S (_Entry_). state_val s V = state_val s' V" 
    by(rule lowEquivalence_relevant_nodes_Entry)
  with \<open>(_Entry_) -asx\<rightarrow>* (_Low_)\<close> \<open>(_Entry_) -asx'\<rightarrow>* (_Low_)\<close> \<open>(_Low_) \<in> S\<close>
    \<open>preds (slice_kinds S asx) s\<close> \<open>preds (slice_kinds S asx') s'\<close>
  have "\<forall>V \<in> Use (_Low_). state_val (transfers (slice_kinds S asx) s) V =
                          state_val (transfers (slice_kinds S asx') s') V"
    by -(rule rv_Low_Use_Low,auto)
  with \<open>\<forall>V \<in> Use (_Low_). state_val(transfers (slice_kinds S asx) s) V = 
                          state_val(transfers (kinds as) s) V\<close>
    \<open>\<forall>V \<in> Use (_Low_). state_val (transfers (slice_kinds S asx') s') V = 
                       state_val (transfers (kinds as') s') V\<close>
  show ?thesis by(auto simp:lowEquivalence_def UseLow)
qed


theorem nonInterference_path:
  assumes "s \<approx>\<^sub>L s'" and "(_High_) \<notin> backward_slice S" and "(_Low_) \<in> S"
  and "(_Entry_) -as\<rightarrow>* (_Exit_)" and "preds (kinds as) s"
  and "(_Entry_) -as'\<rightarrow>* (_Exit_)" and "preds (kinds as') s'"
  shows "transfers (kinds as) s \<approx>\<^sub>L transfers (kinds as') s'"
proof -
  from \<open>(_Entry_) -as\<rightarrow>* (_Exit_)\<close> obtain x xs where "as = x#xs"
    and "(_Entry_) = sourcenode x" and "valid_edge x" 
    and "targetnode x -xs\<rightarrow>* (_Exit_)"
    apply(cases "as = []")
     apply(simp,drule empty_path_nodes,drule Entry_noteq_Exit,simp)
    by(erule path_split_Cons)
  from \<open>valid_edge x\<close> have "valid_node (targetnode x)" by simp
  hence "inner_node (targetnode x)"
  proof(cases rule:valid_node_cases)
    case Entry
    with \<open>valid_edge x\<close> have False by(rule Entry_target)
    thus ?thesis by simp
  next
    case Exit
    with \<open>targetnode x -xs\<rightarrow>* (_Exit_)\<close> have "xs = []"
      by -(rule path_Exit_source,simp)
    from Entry_Exit_edge obtain z where "valid_edge z"
      and "sourcenode z = (_Entry_)" and "targetnode z = (_Exit_)"
      and "kind z = (\<lambda>s. False)\<^sub>\<surd>" by blast
    from \<open>valid_edge x\<close> \<open>valid_edge z\<close> \<open>(_Entry_) = sourcenode x\<close> 
      \<open>sourcenode z = (_Entry_)\<close> Exit \<open>targetnode z = (_Exit_)\<close>
    have "x = z" by(fastforce intro:edge_det)
    with \<open>preds (kinds as) s\<close> \<open>as = x#xs\<close> \<open>xs = []\<close> \<open>kind z = (\<lambda>s. False)\<^sub>\<surd>\<close> 
    have False by(simp add:kinds_def)
    thus ?thesis by simp
  qed simp
  with \<open>targetnode x -xs\<rightarrow>* (_Exit_)\<close> obtain x' xs' where "xs = xs'@[x']"
    and "targetnode x -xs'\<rightarrow>* (_Low_)" and "kind x' = (\<lambda>s. True)\<^sub>\<surd>"
    by(fastforce elim:Exit_path_Low_path)
  with \<open>(_Entry_) = sourcenode x\<close> \<open>valid_edge x\<close>
  have "(_Entry_) -x#xs'\<rightarrow>* (_Low_)" by(fastforce intro:Cons_path)
  from \<open>as = x#xs\<close> \<open>xs = xs'@[x']\<close> have "as = (x#xs')@[x']" by simp
  with \<open>preds (kinds as) s\<close> have "preds (kinds (x#xs')) s"
    by(simp add:kinds_def preds_split)
  from \<open>(_Entry_) -as'\<rightarrow>* (_Exit_)\<close> obtain y ys where "as' = y#ys"
    and "(_Entry_) = sourcenode y" and "valid_edge y" 
    and "targetnode y -ys\<rightarrow>* (_Exit_)"
    apply(cases "as' = []")
     apply(simp,drule empty_path_nodes,drule Entry_noteq_Exit,simp)
    by(erule path_split_Cons)
  from \<open>valid_edge y\<close> have "valid_node (targetnode y)" by simp
  hence "inner_node (targetnode y)"
  proof(cases rule:valid_node_cases)
    case Entry
    with \<open>valid_edge y\<close> have False by(rule Entry_target)
    thus ?thesis by simp
  next
    case Exit
    with \<open>targetnode y -ys\<rightarrow>* (_Exit_)\<close> have "ys = []"
      by -(rule path_Exit_source,simp)
    from Entry_Exit_edge obtain z where "valid_edge z"
      and "sourcenode z = (_Entry_)" and "targetnode z = (_Exit_)"
      and "kind z = (\<lambda>s. False)\<^sub>\<surd>" by blast
    from \<open>valid_edge y\<close> \<open>valid_edge z\<close> \<open>(_Entry_) = sourcenode y\<close> 
      \<open>sourcenode z = (_Entry_)\<close> Exit \<open>targetnode z = (_Exit_)\<close>
    have "y = z" by(fastforce intro:edge_det)
    with \<open>preds (kinds as') s'\<close> \<open>as' = y#ys\<close> \<open>ys = []\<close> \<open>kind z = (\<lambda>s. False)\<^sub>\<surd>\<close> 
    have False by(simp add:kinds_def)
    thus ?thesis by simp
  qed simp
  with \<open>targetnode y -ys\<rightarrow>* (_Exit_)\<close> obtain y' ys' where "ys = ys'@[y']"
    and "targetnode y -ys'\<rightarrow>* (_Low_)" and "kind y' = (\<lambda>s. True)\<^sub>\<surd>"
    by(fastforce elim:Exit_path_Low_path)
  with \<open>(_Entry_) = sourcenode y\<close> \<open>valid_edge y\<close>
  have "(_Entry_) -y#ys'\<rightarrow>* (_Low_)" by(fastforce intro:Cons_path)
  from \<open>as' = y#ys\<close> \<open>ys = ys'@[y']\<close> have "as' = (y#ys')@[y']" by simp
  with \<open>preds (kinds as') s'\<close> have "preds (kinds (y#ys')) s'"
    by(simp add:kinds_def preds_split)
  from \<open>s \<approx>\<^sub>L s'\<close> \<open>(_High_) \<notin> backward_slice S\<close> \<open>(_Low_) \<in> S\<close>
    \<open>(_Entry_) -x#xs'\<rightarrow>* (_Low_)\<close> \<open>preds (kinds (x#xs')) s\<close>
    \<open>(_Entry_) -y#ys'\<rightarrow>* (_Low_)\<close> \<open>preds (kinds (y#ys')) s'\<close>
  have "transfers (kinds (x#xs')) s \<approx>\<^sub>L transfers (kinds (y#ys')) s'"
    by(rule nonInterference_path_to_Low)
  with \<open>as = x#xs\<close> \<open>xs = xs'@[x']\<close> \<open>kind x' = (\<lambda>s. True)\<^sub>\<surd>\<close>
    \<open>as' = y#ys\<close> \<open>ys = ys'@[y']\<close> \<open>kind y' = (\<lambda>s. True)\<^sub>\<surd>\<close>
  show ?thesis by(simp add:kinds_def transfers_split)
qed


end

text \<open>The second theorem assumes that we have a operational semantics,
whose evaluations are written \<open>\<langle>c,s\<rangle> \<Rightarrow> \<langle>c',s'\<rangle>\<close> and which conforms 
to the CFG. The correctness theorem then states that if no high variable
influenced a low variable and the initial states were low equivalent, the
reulting states are again low equivalent:\<close>


locale NonInterferenceIntra = 
  NonInterferenceIntraGraph sourcenode targetnode kind valid_edge Entry 
    Def Use state_val backward_slice Exit H L High Low +
  BackwardSlice_wf sourcenode targetnode kind valid_edge Entry Def Use state_val 
    backward_slice sem identifies
  for sourcenode :: "'edge \<Rightarrow> 'node" and targetnode :: "'edge \<Rightarrow> 'node"
  and kind :: "'edge \<Rightarrow> 'state edge_kind" and valid_edge :: "'edge \<Rightarrow> bool"
  and Entry :: "'node" ("'('_Entry'_')") and Def :: "'node \<Rightarrow> 'var set"
  and Use :: "'node \<Rightarrow> 'var set" and state_val :: "'state \<Rightarrow> 'var \<Rightarrow> 'val"
  and backward_slice :: "'node set \<Rightarrow> 'node set"
  and sem :: "'com \<Rightarrow> 'state \<Rightarrow> 'com \<Rightarrow> 'state \<Rightarrow> bool" 
    ("((1\<langle>_,/_\<rangle>) \<Rightarrow>/ (1\<langle>_,/_\<rangle>))" [0,0,0,0] 81)
  and identifies :: "'node \<Rightarrow> 'com \<Rightarrow> bool" ("_ \<triangleq> _" [51, 0] 80)
  and Exit :: "'node" ("'('_Exit'_')")
  and H :: "'var set" and L :: "'var set" 
  and High :: "'node"  ("'('_High'_')") and Low :: "'node"   ("'('_Low'_')") +
  fixes final :: "'com \<Rightarrow> bool"
  assumes final_edge_Low: "\<lbrakk>final c; n \<triangleq> c\<rbrakk> 
  \<Longrightarrow> \<exists>a. valid_edge a \<and> sourcenode a = n \<and> targetnode a = (_Low_) \<and> kind a = \<Up>id"
begin

text\<open>The following theorem needs the explicit edge from \<open>(_High_)\<close>
  to \<open>n\<close>. An approach using a \<open>init\<close> predicate for initial statements,
  being reachable from \<open>(_High_)\<close> via a \<open>(\<lambda>s. True)\<^sub>\<surd>\<close> edge,
  does not work as the same statement could be identified by several nodes, some
  initial, some not. E.g., in the program \texttt{while (True) Skip;;Skip}
  two nodes identify this inital statement: the initial node and the node
  within the loop (because of loop unrolling).\<close>

theorem nonInterference:
  assumes "s\<^sub>1 \<approx>\<^sub>L s\<^sub>2" and "(_High_) \<notin> backward_slice S" and "(_Low_) \<in> S"
  and "valid_edge a" and "sourcenode a = (_High_)" and "targetnode a = n" 
  and "kind a = (\<lambda>s. True)\<^sub>\<surd>" and "n \<triangleq> c" and "final c'"
  and "\<langle>c,s\<^sub>1\<rangle> \<Rightarrow> \<langle>c',s\<^sub>1'\<rangle>" and "\<langle>c,s\<^sub>2\<rangle> \<Rightarrow> \<langle>c',s\<^sub>2'\<rangle>"
  shows "s\<^sub>1' \<approx>\<^sub>L s\<^sub>2'"
proof -
  from High_target_Entry_edge obtain ax where "valid_edge ax"
    and "sourcenode ax = (_Entry_)" and "targetnode ax = (_High_)"
    and "kind ax = (\<lambda>s. True)\<^sub>\<surd>" by blast
  from \<open>n \<triangleq> c\<close> \<open>\<langle>c,s\<^sub>1\<rangle> \<Rightarrow> \<langle>c',s\<^sub>1'\<rangle>\<close>
  obtain n\<^sub>1 as\<^sub>1 where "n -as\<^sub>1\<rightarrow>* n\<^sub>1" and "transfers (kinds as\<^sub>1) s\<^sub>1 = s\<^sub>1'"
    and "preds (kinds as\<^sub>1) s\<^sub>1" and "n\<^sub>1 \<triangleq> c'"
    by(fastforce dest:fundamental_property)
  from \<open>n -as\<^sub>1\<rightarrow>* n\<^sub>1\<close> \<open>valid_edge a\<close> \<open>sourcenode a = (_High_)\<close> \<open>targetnode a = n\<close>
  have "(_High_) -a#as\<^sub>1\<rightarrow>* n\<^sub>1" by(rule Cons_path)
  from \<open>final c'\<close> \<open>n\<^sub>1 \<triangleq> c'\<close>
  obtain a\<^sub>1 where "valid_edge a\<^sub>1" and "sourcenode a\<^sub>1 = n\<^sub>1" 
    and "targetnode a\<^sub>1 = (_Low_)" and "kind a\<^sub>1 = \<Up>id" by(fastforce dest:final_edge_Low)
  hence "n\<^sub>1 -[a\<^sub>1]\<rightarrow>* (_Low_)" by(fastforce intro:path_edge)
  with \<open>(_High_) -a#as\<^sub>1\<rightarrow>* n\<^sub>1\<close> have "(_High_) -(a#as\<^sub>1)@[a\<^sub>1]\<rightarrow>* (_Low_)"
    by(rule path_Append)
  with \<open>valid_edge ax\<close> \<open>sourcenode ax = (_Entry_)\<close> \<open>targetnode ax = (_High_)\<close>
  have "(_Entry_) -ax#((a#as\<^sub>1)@[a\<^sub>1])\<rightarrow>* (_Low_)" by -(rule Cons_path)
  from \<open>kind ax = (\<lambda>s. True)\<^sub>\<surd>\<close> \<open>kind a = (\<lambda>s. True)\<^sub>\<surd>\<close> \<open>preds (kinds as\<^sub>1) s\<^sub>1\<close>
    \<open>kind a\<^sub>1 = \<Up>id\<close> have "preds (kinds (ax#((a#as\<^sub>1)@[a\<^sub>1]))) s\<^sub>1"
    by (simp add:kinds_def preds_split)
  from \<open>n \<triangleq> c\<close> \<open>\<langle>c,s\<^sub>2\<rangle> \<Rightarrow> \<langle>c',s\<^sub>2'\<rangle>\<close>
  obtain n\<^sub>2 as\<^sub>2 where "n -as\<^sub>2\<rightarrow>* n\<^sub>2" and "transfers (kinds as\<^sub>2) s\<^sub>2 = s\<^sub>2'"
    and "preds (kinds as\<^sub>2) s\<^sub>2" and "n\<^sub>2 \<triangleq> c'"
    by(fastforce dest:fundamental_property)
  from \<open>n -as\<^sub>2\<rightarrow>* n\<^sub>2\<close> \<open>valid_edge a\<close> \<open>sourcenode a = (_High_)\<close> \<open>targetnode a = n\<close>
  have "(_High_) -a#as\<^sub>2\<rightarrow>* n\<^sub>2" by(rule Cons_path)
  from \<open>final c'\<close> \<open>n\<^sub>2 \<triangleq> c'\<close>
  obtain a\<^sub>2 where "valid_edge a\<^sub>2" and "sourcenode a\<^sub>2 = n\<^sub>2" 
    and "targetnode a\<^sub>2 = (_Low_)" and "kind a\<^sub>2 = \<Up>id" by(fastforce dest:final_edge_Low)
  hence "n\<^sub>2 -[a\<^sub>2]\<rightarrow>* (_Low_)" by(fastforce intro:path_edge)
  with \<open>(_High_) -a#as\<^sub>2\<rightarrow>* n\<^sub>2\<close> have "(_High_) -(a#as\<^sub>2)@[a\<^sub>2]\<rightarrow>* (_Low_)"
    by(rule path_Append)
  with \<open>valid_edge ax\<close> \<open>sourcenode ax = (_Entry_)\<close> \<open>targetnode ax = (_High_)\<close>
  have "(_Entry_) -ax#((a#as\<^sub>2)@[a\<^sub>2])\<rightarrow>* (_Low_)" by -(rule Cons_path)
  from \<open>kind ax = (\<lambda>s. True)\<^sub>\<surd>\<close> \<open>kind a = (\<lambda>s. True)\<^sub>\<surd>\<close> \<open>preds (kinds as\<^sub>2) s\<^sub>2\<close>
    \<open>kind a\<^sub>2 = \<Up>id\<close> have "preds (kinds (ax#((a#as\<^sub>2)@[a\<^sub>2]))) s\<^sub>2"
    by (simp add:kinds_def preds_split)
  from \<open>s\<^sub>1 \<approx>\<^sub>L s\<^sub>2\<close> \<open>(_High_) \<notin> backward_slice S\<close> \<open>(_Low_) \<in> S\<close>
    \<open>(_Entry_) -ax#((a#as\<^sub>1)@[a\<^sub>1])\<rightarrow>* (_Low_)\<close> \<open>preds (kinds (ax#((a#as\<^sub>1)@[a\<^sub>1]))) s\<^sub>1\<close>
    \<open>(_Entry_) -ax#((a#as\<^sub>2)@[a\<^sub>2])\<rightarrow>* (_Low_)\<close> \<open>preds (kinds (ax#((a#as\<^sub>2)@[a\<^sub>2]))) s\<^sub>2\<close>
  have "transfers (kinds (ax#((a#as\<^sub>1)@[a\<^sub>1]))) s\<^sub>1 \<approx>\<^sub>L 
        transfers (kinds (ax#((a#as\<^sub>2)@[a\<^sub>2]))) s\<^sub>2"
    by(rule nonInterference_path_to_Low)
  with \<open>kind ax = (\<lambda>s. True)\<^sub>\<surd>\<close> \<open>kind a = (\<lambda>s. True)\<^sub>\<surd>\<close> \<open>kind a\<^sub>1 = \<Up>id\<close> \<open>kind a\<^sub>2 = \<Up>id\<close>
    \<open>transfers (kinds as\<^sub>1) s\<^sub>1 = s\<^sub>1'\<close> \<open>transfers (kinds as\<^sub>2) s\<^sub>2 = s\<^sub>2'\<close>
  show ?thesis by(simp add:kinds_def transfers_split)
qed


end

end

