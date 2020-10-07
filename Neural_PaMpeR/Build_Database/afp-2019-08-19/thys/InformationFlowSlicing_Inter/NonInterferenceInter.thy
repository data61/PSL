section \<open>HRB Slicing guarantees IFC Noninterference\<close>

theory NonInterferenceInter 
  imports "HRB-Slicing.FundamentalProperty"
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
the prerequisites of the slicing framework in \cite{Wasserrab:09} accordingly
in a new locale:

\<close>

locale NonInterferenceInterGraph =
  SDG sourcenode targetnode kind valid_edge Entry 
    get_proc get_return_edges procs Main Exit Def Use ParamDefs ParamUses 
  for sourcenode :: "'edge \<Rightarrow> 'node" and targetnode :: "'edge \<Rightarrow> 'node"
  and kind :: "'edge \<Rightarrow> ('var,'val,'ret,'pname) edge_kind" 
  and valid_edge :: "'edge \<Rightarrow> bool"
  and Entry :: "'node" ("'('_Entry'_')")  and get_proc :: "'node \<Rightarrow> 'pname"
  and get_return_edges :: "'edge \<Rightarrow> 'edge set"
  and procs :: "('pname \<times> 'var list \<times> 'var list) list" and Main :: "'pname"
  and Exit::"'node"  ("'('_Exit'_')") 
  and Def :: "'node \<Rightarrow> 'var set" and Use :: "'node \<Rightarrow> 'var set"
  and ParamDefs :: "'node \<Rightarrow> 'var list" and ParamUses :: "'node \<Rightarrow> 'var set list" +
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


lemma valid_node_High [simp]:"valid_node (_High_)"
  using High_target_Entry_edge by fastforce

lemma valid_node_Low [simp]:"valid_node (_Low_)"
  using Low_source_Exit_edge by fastforce


lemma get_proc_Low:
  "get_proc (_Low_) = Main"
proof -
  from Low_source_Exit_edge obtain a where "valid_edge a"
    and "sourcenode a = (_Low_)" and "targetnode a = (_Exit_)"
    and "intra_kind (kind a)" by(fastforce simp:intra_kind_def)
  from \<open>valid_edge a\<close> \<open>intra_kind (kind a)\<close>
  have "get_proc (sourcenode a) = get_proc (targetnode a)" by(rule get_proc_intra)
  with \<open>sourcenode a = (_Low_)\<close> \<open>targetnode a = (_Exit_)\<close> get_proc_Exit
  show ?thesis by simp
qed

lemma get_proc_High:
  "get_proc (_High_) = Main"
proof -
  from High_target_Entry_edge obtain a where "valid_edge a"
    and "sourcenode a = (_Entry_)" and "targetnode a = (_High_)"
    and "intra_kind (kind a)" by(fastforce simp:intra_kind_def)
  from \<open>valid_edge a\<close> \<open>intra_kind (kind a)\<close>
  have "get_proc (sourcenode a) = get_proc (targetnode a)" by(rule get_proc_intra)
  with \<open>sourcenode a = (_Entry_)\<close> \<open>targetnode a = (_High_)\<close> get_proc_Entry
  show ?thesis by simp
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
    with \<open>valid_edge a\<close> \<open>sourcenode a = (_Entry_)\<close> \<open>targetnode a = n''\<close>
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

definition lowEquivalence :: "('var \<rightharpoonup> 'val) list \<Rightarrow> ('var \<rightharpoonup> 'val) list \<Rightarrow> bool" 
(infixl "\<approx>\<^sub>L" 50)
  where "s \<approx>\<^sub>L s' \<equiv> \<forall>V \<in> L. hd s V = hd s' V"

text \<open>The following lemmas connect low equivalent states with
relevant variables as necessary in the correctness proof for slicing.\<close>

lemma relevant_vars_Entry:
  assumes "V \<in> rv S (CFG_node (_Entry_))" and "(_High_) \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
  shows "V \<in> L"
proof -
  from \<open>V \<in> rv S (CFG_node (_Entry_))\<close> obtain as n' 
    where "(_Entry_) -as\<rightarrow>\<^sub>\<iota>* parent_node n'" 
    and "n' \<in> HRB_slice S" and "V \<in> Use\<^bsub>SDG\<^esub> n'"
    and "\<forall>n''. valid_SDG_node n'' \<and> parent_node n'' \<in> set (sourcenodes as) 
          \<longrightarrow> V \<notin> Def\<^bsub>SDG\<^esub> n''" by(fastforce elim:rvE)
  from \<open>(_Entry_) -as\<rightarrow>\<^sub>\<iota>* parent_node n'\<close> have "valid_node (parent_node n')"
    by(fastforce intro:path_valid_node simp:intra_path_def)
  thus ?thesis
  proof(cases "parent_node n'" rule:valid_node_cases)
    case Entry
    with \<open>V \<in> Use\<^bsub>SDG\<^esub> n'\<close> have False
      by -(drule SDG_Use_parent_Use,simp add:Entry_empty)
    thus ?thesis by simp
  next
    case Exit
    with \<open>V \<in> Use\<^bsub>SDG\<^esub> n'\<close> have False
      by -(drule SDG_Use_parent_Use,simp add:Exit_empty)
    thus ?thesis by simp
  next
    case inner
    with \<open>(_Entry_) -as\<rightarrow>\<^sub>\<iota>* parent_node n'\<close> obtain a' as' where "as = a'#as'"
      and "(_High_) -as'\<rightarrow>\<^sub>\<iota>* parent_node n'"
      by(fastforce elim:Entry_path_High_path simp:intra_path_def)
    from \<open>(_Entry_) -as\<rightarrow>\<^sub>\<iota>* parent_node n'\<close> \<open>as = a'#as'\<close>
    have "sourcenode a' = (_Entry_)" by(fastforce elim:path.cases simp:intra_path_def)
    show ?thesis
    proof(cases "as' = []")
      case True
      with \<open>(_High_) -as'\<rightarrow>\<^sub>\<iota>* parent_node n'\<close> have "parent_node n' = (_High_)"
        by(fastforce simp:intra_path_def)
      with \<open>n' \<in> HRB_slice S\<close> \<open>(_High_) \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close>
      have False 
        by(fastforce dest:valid_SDG_node_in_slice_parent_node_in_slice 
                    simp:SDG_to_CFG_set_def)
      thus ?thesis by simp
    next
      case False
      with \<open>(_High_) -as'\<rightarrow>\<^sub>\<iota>* parent_node n'\<close> have "hd (sourcenodes as') = (_High_)"
        by(fastforce intro:path_sourcenode simp:intra_path_def)
      from False have "hd (sourcenodes as') \<in> set (sourcenodes as')"
        by(fastforce intro:hd_in_set simp:sourcenodes_def)
      with \<open>as = a'#as'\<close> have "hd (sourcenodes as') \<in> set (sourcenodes as)"
        by(simp add:sourcenodes_def)
      from \<open>hd (sourcenodes as') = (_High_)\<close>
      have "valid_node (hd (sourcenodes as'))" by simp
      have "valid_SDG_node (CFG_node (_High_))" by simp
      with \<open>hd (sourcenodes as') = (_High_)\<close>
        \<open>hd (sourcenodes as') \<in> set (sourcenodes as)\<close>
        \<open>\<forall>n''. valid_SDG_node n'' \<and> parent_node n'' \<in> set (sourcenodes as) 
        \<longrightarrow> V \<notin> Def\<^bsub>SDG\<^esub> n''\<close>
      have "V \<notin> Def (_High_)"
        by(fastforce dest:CFG_Def_SDG_Def[OF \<open>valid_node (hd (sourcenodes as'))\<close>])
      hence "V \<notin> H" by(simp add:DefHigh)
      thus ?thesis by(rule not_High_Low)
    qed
  qed
qed



lemma lowEquivalence_relevant_nodes_Entry:
  assumes "s \<approx>\<^sub>L s'" and "(_High_) \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
  shows "\<forall>V \<in> rv S (CFG_node (_Entry_)). hd s V = hd s' V"
proof
  fix V assume "V \<in> rv S (CFG_node (_Entry_))"
  with \<open>(_High_) \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close> have "V \<in> L" by -(rule relevant_vars_Entry)
  with \<open>s \<approx>\<^sub>L s'\<close> show "hd s V = hd s' V" by(simp add:lowEquivalence_def)
qed


subsection \<open>The Correctness Proofs\<close>

text \<open>
In the following, we present two correctness proofs that slicing
guarantees IFC noninterference. In both theorems, \<open>CFG_node
(_High_) \<notin> HRB_slice S\<close>, where \<open>CFG_node (_Low_) \<in> S\<close>, makes
sure that no high variable (which are all defined in \<open>(_High_)\<close>)
can influence a low variable (which are all used in \<open>(_Low_)\<close>).


First, a theorem regarding \<open>(_Entry_) -as\<rightarrow>* (_Exit_)\<close> paths in the 
control flow graph (CFG), which agree to a complete program execution:\<close>


lemma slpa_rv_Low_Use_Low:
  assumes "CFG_node (_Low_) \<in> S"
  shows "\<lbrakk>same_level_path_aux cs as; upd_cs cs as = []; same_level_path_aux cs as';
    \<forall>c \<in> set cs. valid_edge c; m -as\<rightarrow>* (_Low_); m -as'\<rightarrow>* (_Low_);
   \<forall>i < length cs. \<forall>V \<in> rv S (CFG_node (sourcenode (cs!i))). 
    fst (s!Suc i) V = fst (s'!Suc i) V; \<forall>i < Suc (length cs). snd (s!i) = snd (s'!i);
   \<forall>V \<in> rv S (CFG_node m). state_val s V = state_val s' V;
   preds (slice_kinds S as) s; preds (slice_kinds S as') s';
   length s = Suc (length cs); length s' = Suc (length cs)\<rbrakk>
   \<Longrightarrow> \<forall>V \<in> Use (_Low_). state_val (transfers(slice_kinds S as) s) V =
                      state_val (transfers(slice_kinds S as') s') V"
proof(induct arbitrary:m as' s s' rule:slpa_induct)
  case (slpa_empty cs)
  from \<open>m -[]\<rightarrow>* (_Low_)\<close> have "m = (_Low_)" by fastforce
  from \<open>m -[]\<rightarrow>* (_Low_)\<close> have "valid_node m"
    by(rule path_valid_node)+
  { fix V assume "V \<in> Use (_Low_)"
    moreover
    from \<open>valid_node m\<close> \<open>m = (_Low_)\<close> have "(_Low_) -[]\<rightarrow>\<^sub>\<iota>* (_Low_)"
      by(fastforce intro:empty_path simp:intra_path_def)
    moreover
    from \<open>valid_node m\<close> \<open>m = (_Low_)\<close> \<open>CFG_node (_Low_) \<in> S\<close>
    have "CFG_node (_Low_) \<in> HRB_slice S"
      by(fastforce intro:HRB_slice_refl)
    ultimately have "V \<in> rv S (CFG_node m)" 
      using \<open>m = (_Low_)\<close>
      by(auto intro!:rvI CFG_Use_SDG_Use simp:sourcenodes_def) }
  hence "\<forall>V \<in> Use (_Low_). V \<in> rv S (CFG_node m)" by simp
  show ?case
  proof(cases "L = {}")
    case True with UseLow show ?thesis by simp
  next
    case False
    from \<open>m -as'\<rightarrow>* (_Low_)\<close> \<open>m = (_Low_)\<close> have "as' = []"
    proof(induct m as' m'\<equiv>"(_Low_)" rule:path.induct)
      case (Cons_path m'' as a m)
      from \<open>valid_edge a\<close> \<open>sourcenode a = m\<close> \<open>m = (_Low_)\<close>
      have "targetnode a = (_Exit_)" by -(rule Exit_successor_of_Low,simp+)
      with \<open>targetnode a = m''\<close> \<open>m'' -as\<rightarrow>* (_Low_)\<close>
      have "(_Low_) = (_Exit_)" by -(drule path_Exit_source,auto)
      with False have False by -(drule Low_neq_Exit,simp)
      thus ?case by simp
    qed simp
    with \<open>\<forall>V \<in> Use (_Low_). V \<in> rv S (CFG_node m)\<close>
      \<open>\<forall>V \<in> rv S (CFG_node m). state_val s V = state_val s' V\<close> Nil
    show ?thesis by(auto simp:slice_kinds_def)
  qed
next
  case (slpa_intra cs a as)
  note IH = \<open>\<And>m as' s s'. \<lbrakk>upd_cs cs as = []; same_level_path_aux cs as'; 
    \<forall>a\<in>set cs. valid_edge a; m -as\<rightarrow>* (_Low_); m -as'\<rightarrow>* (_Low_);
    \<forall>i<length cs. \<forall>V\<in>rv S (CFG_node (sourcenode (cs ! i))).
    fst (s ! Suc i) V = fst (s' ! Suc i) V; 
    \<forall>i<Suc (length cs). snd (s ! i) = snd (s' ! i);
    \<forall>V\<in>rv S (CFG_node m). state_val s V = state_val s' V;
    preds (slice_kinds S as) s; preds (slice_kinds S as') s';
    length s = Suc (length cs); length s' = Suc (length cs)\<rbrakk>
    \<Longrightarrow> \<forall>V\<in>Use (_Low_). state_val (transfers(slice_kinds S as) s) V =
    state_val (transfers(slice_kinds S as') s') V\<close>
  note rvs = \<open>\<forall>i<length cs. \<forall>V\<in>rv S (CFG_node (sourcenode (cs ! i))).
    fst (s ! Suc i) V = fst (s' ! Suc i) V\<close>
  from \<open>m -a # as\<rightarrow>* (_Low_)\<close> have "sourcenode a = m" and "valid_edge a"
    and "targetnode a -as\<rightarrow>* (_Low_)" by(auto elim:path_split_Cons)
  show ?case
  proof(cases "L = {}")
    case True with UseLow show ?thesis by simp
  next
    case False
    show ?thesis
    proof(cases as')
      case Nil
      with \<open>m -as'\<rightarrow>* (_Low_)\<close> have "m = (_Low_)" by fastforce
      with \<open>valid_edge a\<close> \<open>sourcenode a = m\<close> have "targetnode a = (_Exit_)"
        by -(rule Exit_successor_of_Low,simp+)
      from Low_source_Exit_edge obtain a' where "valid_edge a'"
        and "sourcenode a' = (_Low_)" and "targetnode a' = (_Exit_)"
        and "kind a' = (\<lambda>s. True)\<^sub>\<surd>" by blast
      from \<open>valid_edge a\<close> \<open>sourcenode a = m\<close> \<open>m = (_Low_)\<close> 
        \<open>targetnode a = (_Exit_)\<close> \<open>valid_edge a'\<close> \<open>sourcenode a' = (_Low_)\<close> 
        \<open>targetnode a' = (_Exit_)\<close>
      have "a = a'" by(fastforce dest:edge_det)
      with \<open>kind a' = (\<lambda>s. True)\<^sub>\<surd>\<close> have "kind a = (\<lambda>s. True)\<^sub>\<surd>" by simp
      with \<open>targetnode a = (_Exit_)\<close> \<open>targetnode a -as\<rightarrow>* (_Low_)\<close>
      have "(_Low_) = (_Exit_)" by -(drule path_Exit_source,auto)
      with False have False by -(drule Low_neq_Exit,simp)
      thus ?thesis by simp
    next
      case (Cons ax asx)
      with \<open>m -as'\<rightarrow>* (_Low_)\<close> have "sourcenode ax = m" and "valid_edge ax"
        and "targetnode ax -asx\<rightarrow>* (_Low_)" by(auto elim:path_split_Cons)
      from \<open>preds (slice_kinds S (a # as)) s\<close>
      obtain cf cfs where [simp]:"s = cf#cfs" by(cases s)(auto simp:slice_kinds_def)
      from \<open>preds (slice_kinds S as') s'\<close> \<open>as' = ax # asx\<close> 
      obtain cf' cfs' where [simp]:"s' = cf'#cfs'"
        by(cases s')(auto simp:slice_kinds_def)
      have "intra_kind (kind ax)"
      proof(cases "kind ax" rule:edge_kind_cases)
        case (Call Q r p fs)
        have False
        proof(cases "sourcenode a \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>")
          case True
          with \<open>intra_kind (kind a)\<close> have "slice_kind S a = kind a"
            by -(rule slice_intra_kind_in_slice)
          from \<open>valid_edge ax\<close> \<open>kind ax = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close>
          have unique:"\<exists>!a'. valid_edge a' \<and> sourcenode a' = sourcenode ax \<and> 
            intra_kind(kind a')" by(rule call_only_one_intra_edge)
          from \<open>valid_edge ax\<close> \<open>kind ax = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close> obtain x 
            where "x \<in> get_return_edges ax" by(fastforce dest:get_return_edge_call)
          with \<open>valid_edge ax\<close> obtain a' where "valid_edge a'" 
            and "sourcenode a' = sourcenode ax" and "kind a' = (\<lambda>cf. False)\<^sub>\<surd>"
            by(fastforce dest:call_return_node_edge)
          with \<open>valid_edge a\<close> \<open>sourcenode a = m\<close> \<open>sourcenode ax = m\<close>
            \<open>intra_kind (kind a)\<close> unique
          have "a' = a" by(fastforce simp:intra_kind_def)
          with \<open>kind a' = (\<lambda>cf. False)\<^sub>\<surd>\<close> \<open>slice_kind S a = kind a\<close>
            \<open>preds (slice_kinds S (a#as)) s\<close>
          have False by(cases s)(auto simp:slice_kinds_def)
          thus ?thesis by simp
        next
          case False
          with \<open>kind ax = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close> \<open>sourcenode a = m\<close> \<open>sourcenode ax = m\<close>
          have "slice_kind S ax = (\<lambda>cf. False):r\<hookrightarrow>\<^bsub>p\<^esub>fs"
            by(fastforce intro:slice_kind_Call)
          with \<open>as' = ax # asx\<close> \<open>preds (slice_kinds S as') s'\<close>
          have False by(cases s')(auto simp:slice_kinds_def)
          thus ?thesis by simp
        qed
        thus ?thesis by simp
      next
        case (Return Q p f)
        from \<open>valid_edge ax\<close> \<open>kind ax = Q\<hookleftarrow>\<^bsub>p\<^esub>f\<close> \<open>valid_edge a\<close> \<open>intra_kind (kind a)\<close>
          \<open>sourcenode a = m\<close> \<open>sourcenode ax = m\<close>
        have False by -(drule return_edges_only,auto simp:intra_kind_def)
        thus ?thesis by simp
      qed simp
      with \<open>same_level_path_aux cs as'\<close> \<open>as' = ax#asx\<close>
      have "same_level_path_aux cs asx" by(fastforce simp:intra_kind_def)
      show ?thesis
      proof(cases "targetnode a = targetnode ax")
        case True
        with \<open>valid_edge a\<close> \<open>valid_edge ax\<close> \<open>sourcenode a = m\<close> \<open>sourcenode ax = m\<close>
        have "a = ax" by(fastforce intro:edge_det)
        with \<open>valid_edge a\<close> \<open>intra_kind (kind a)\<close> \<open>sourcenode a = m\<close>
          \<open>\<forall>V\<in>rv S (CFG_node m). state_val s V = state_val s' V\<close>
          \<open>preds (slice_kinds S (a # as)) s\<close>
          \<open>preds (slice_kinds S as') s'\<close> \<open>as' = ax # asx\<close>
        have rv:"\<forall>V\<in>rv S (CFG_node (targetnode a)). 
          state_val (transfer (slice_kind S a) s) V =
          state_val (transfer (slice_kind S a) s') V"
          by -(rule rv_edge_slice_kinds,auto)
        from \<open>upd_cs cs (a # as) = []\<close> \<open>intra_kind (kind a)\<close>
        have "upd_cs cs as = []" by(fastforce simp:intra_kind_def)
        from \<open>targetnode ax -asx\<rightarrow>* (_Low_)\<close> \<open>a = ax\<close>
        have "targetnode a -asx\<rightarrow>* (_Low_)" by simp
        from \<open>valid_edge a\<close> \<open>intra_kind (kind a)\<close>
        obtain cfx 
          where cfx:"transfer (slice_kind S a) s = cfx#cfs \<and> snd cfx = snd cf"
          apply(cases cf)
          apply(cases "sourcenode a \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>") apply auto
          apply(fastforce dest:slice_intra_kind_in_slice simp:intra_kind_def)
          apply(auto simp:intra_kind_def)
          apply(drule slice_kind_Upd) apply auto 
          by(erule kind_Predicate_notin_slice_slice_kind_Predicate) auto
        from \<open>valid_edge a\<close> \<open>intra_kind (kind a)\<close>
        obtain cfx' 
          where cfx':"transfer (slice_kind S a) s' = cfx'#cfs' \<and> snd cfx' = snd cf'"
          apply(cases cf')
          apply(cases "sourcenode a \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>") apply auto
          apply(fastforce dest:slice_intra_kind_in_slice simp:intra_kind_def)
          apply(auto simp:intra_kind_def)
          apply(drule slice_kind_Upd) apply auto 
          by(erule kind_Predicate_notin_slice_slice_kind_Predicate) auto
        with cfx \<open>\<forall>i < Suc (length cs). snd (s!i) = snd (s'!i)\<close>
        have snds:"\<forall>i<Suc(length cs).
          snd (transfer (slice_kind S a) s ! i) = 
          snd (transfer (slice_kind S a) s' ! i)" 
          by auto(case_tac i,auto)
        from rvs cfx cfx' have rvs':"\<forall>i<length cs.
          \<forall>V\<in>rv S (CFG_node (sourcenode (cs ! i))).
          fst (transfer (slice_kind S a) s ! Suc i) V =
          fst (transfer (slice_kind S a) s' ! Suc i) V"
          by fastforce
        from \<open>preds (slice_kinds S (a # as)) s\<close>
        have "preds (slice_kinds S as) 
          (transfer (slice_kind S a) s)" by(simp add:slice_kinds_def)
        moreover
        from \<open>preds (slice_kinds S as') s'\<close> \<open>as' = ax # asx\<close> \<open>a = ax\<close>
        have "preds (slice_kinds S asx) (transfer (slice_kind S a) s')" 
          by(simp add:slice_kinds_def)
        moreover
        from \<open>valid_edge a\<close> \<open>intra_kind (kind a)\<close>
        have "length (transfer (slice_kind S a) s) = length s"
          by(cases "sourcenode a \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>")
        (auto dest:slice_intra_kind_in_slice slice_kind_Upd
          elim:kind_Predicate_notin_slice_slice_kind_Predicate simp:intra_kind_def)
        with \<open>length s = Suc (length cs)\<close>
        have "length (transfer (slice_kind S a) s) = Suc (length cs)"
          by simp
        moreover
        from \<open>a = ax\<close> \<open>valid_edge a\<close> \<open>intra_kind (kind a)\<close>
        have "length (transfer (slice_kind S a) s') = length s'"
          by(cases "sourcenode ax \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>")
        (auto dest:slice_intra_kind_in_slice slice_kind_Upd
          elim:kind_Predicate_notin_slice_slice_kind_Predicate simp:intra_kind_def)
        with \<open>length s' = Suc (length cs)\<close>
        have "length (transfer (slice_kind S a) s') = Suc (length cs)"
          by simp
        moreover
        from IH[OF \<open>upd_cs cs as = []\<close> \<open>same_level_path_aux cs asx\<close> 
          \<open>\<forall>c\<in>set cs. valid_edge c\<close> \<open>targetnode a -as\<rightarrow>* (_Low_)\<close> 
          \<open>targetnode a -asx\<rightarrow>* (_Low_)\<close> rvs' snds rv calculation]
          \<open>as' = ax # asx\<close> \<open>a = ax\<close>
        show ?thesis by(simp add:slice_kinds_def)
      next
        case False
        from \<open>\<forall>i < Suc(length cs). snd (s!i) = snd (s'!i)\<close>
        have "snd (hd s) = snd (hd s')" by(erule_tac x="0" in allE) fastforce
        with \<open>valid_edge a\<close> \<open>valid_edge ax\<close> \<open>sourcenode a = m\<close>
          \<open>sourcenode ax = m\<close> \<open>as' = ax # asx\<close> False
          \<open>intra_kind (kind a)\<close> \<open>intra_kind (kind ax)\<close>
          \<open>preds (slice_kinds S (a # as)) s\<close>
          \<open>preds (slice_kinds S as') s'\<close>
          \<open>\<forall>V\<in>rv S (CFG_node m). state_val s V = state_val s' V\<close>
          \<open>length s = Suc (length cs)\<close> \<open>length s' = Suc (length cs)\<close>
        have False by(fastforce intro!:rv_branching_edges_slice_kinds_False[of a ax])
        thus ?thesis by simp
      qed
    qed
  qed
next
  case (slpa_Call cs a as Q r p fs)
  note IH = \<open>\<And>m as' s s'. 
    \<lbrakk>upd_cs (a # cs) as = []; same_level_path_aux (a # cs) as';
    \<forall>c\<in>set (a # cs). valid_edge c; m -as\<rightarrow>* (_Low_); m -as'\<rightarrow>* (_Low_);
    \<forall>i<length (a # cs). \<forall>V\<in>rv S (CFG_node (sourcenode ((a # cs) ! i))).
    fst (s ! Suc i) V = fst (s' ! Suc i) V;
    \<forall>i<Suc (length (a # cs)). snd (s ! i) = snd (s' ! i);
    \<forall>V\<in>rv S (CFG_node m). state_val s V = state_val s' V;
    preds (slice_kinds S as) s; preds (slice_kinds S as') s';
    length s = Suc (length (a # cs)); length s' = Suc (length (a # cs))\<rbrakk>
    \<Longrightarrow> \<forall>V\<in>Use (_Low_). state_val (transfers(slice_kinds S as) s) V =
    state_val (transfers(slice_kinds S as') s') V\<close>
  note rvs = \<open>\<forall>i<length cs. \<forall>V\<in>rv S (CFG_node (sourcenode (cs ! i))).
    fst (s ! Suc i) V = fst (s' ! Suc i) V\<close>
  from \<open>m -a # as\<rightarrow>* (_Low_)\<close> have "sourcenode a = m" and "valid_edge a"
    and "targetnode a -as\<rightarrow>* (_Low_)" by(auto elim:path_split_Cons)
  from \<open>\<forall>c\<in>set cs. valid_edge c\<close> \<open>valid_edge a\<close>
  have "\<forall>c\<in>set (a # cs). valid_edge c" by simp
  show ?case
   proof(cases "L = {}")
    case True with UseLow show ?thesis by simp
  next
    case False
    show ?thesis
    proof(cases as')
      case Nil
      with \<open>m -as'\<rightarrow>* (_Low_)\<close> have "m = (_Low_)" by fastforce
      with \<open>valid_edge a\<close> \<open>sourcenode a = m\<close> have "targetnode a = (_Exit_)"
        by -(rule Exit_successor_of_Low,simp+)
      from Low_source_Exit_edge obtain a' where "valid_edge a'"
        and "sourcenode a' = (_Low_)" and "targetnode a' = (_Exit_)"
        and "kind a' = (\<lambda>s. True)\<^sub>\<surd>" by blast
      from \<open>valid_edge a\<close> \<open>sourcenode a = m\<close> \<open>m = (_Low_)\<close> 
        \<open>targetnode a = (_Exit_)\<close> \<open>valid_edge a'\<close> \<open>sourcenode a' = (_Low_)\<close> 
        \<open>targetnode a' = (_Exit_)\<close>
      have "a = a'" by(fastforce dest:edge_det)
      with \<open>kind a' = (\<lambda>s. True)\<^sub>\<surd>\<close> have "kind a = (\<lambda>s. True)\<^sub>\<surd>" by simp
      with \<open>targetnode a = (_Exit_)\<close> \<open>targetnode a -as\<rightarrow>* (_Low_)\<close>
      have "(_Low_) = (_Exit_)" by -(drule path_Exit_source,auto)
      with False have False by -(drule Low_neq_Exit,simp)
      thus ?thesis by simp
    next
      case (Cons ax asx)
      with \<open>m -as'\<rightarrow>* (_Low_)\<close> have "sourcenode ax = m" and "valid_edge ax"
        and "targetnode ax -asx\<rightarrow>* (_Low_)" by(auto elim:path_split_Cons)
      from \<open>preds (slice_kinds S (a # as)) s\<close>
      obtain cf cfs where [simp]:"s = cf#cfs" by(cases s)(auto simp:slice_kinds_def)
      from \<open>preds (slice_kinds S as') s'\<close> \<open>as' = ax # asx\<close> 
      obtain cf' cfs' where [simp]:"s' = cf'#cfs'"
        by(cases s')(auto simp:slice_kinds_def)
      have "\<exists>Q r p fs. kind ax = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs"
      proof(cases "kind ax" rule:edge_kind_cases)
        case Intra
        have False
        proof(cases "sourcenode ax \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>")
          case True
          with \<open>intra_kind (kind ax)\<close> 
          have "slice_kind S ax = kind ax"
            by -(rule slice_intra_kind_in_slice)
          from \<open>valid_edge a\<close> \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close>
          have unique:"\<exists>!a'. valid_edge a' \<and> sourcenode a' = sourcenode a \<and> 
            intra_kind(kind a')" by(rule call_only_one_intra_edge)
          from \<open>valid_edge a\<close> \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close> obtain x 
            where "x \<in> get_return_edges a" by(fastforce dest:get_return_edge_call)
          with \<open>valid_edge a\<close> obtain a' where "valid_edge a'" 
            and "sourcenode a' = sourcenode a" and "kind a' = (\<lambda>cf. False)\<^sub>\<surd>"
            by(fastforce dest:call_return_node_edge)
          with \<open>valid_edge ax\<close> \<open>sourcenode ax = m\<close> \<open>sourcenode a = m\<close>
            \<open>intra_kind (kind ax)\<close> unique
          have "a' = ax" by(fastforce simp:intra_kind_def)
          with \<open>kind a' = (\<lambda>cf. False)\<^sub>\<surd>\<close> 
            \<open>slice_kind S ax = kind ax\<close> \<open>as' = ax # asx\<close>
            \<open>preds (slice_kinds S as') s'\<close>
          have False by(simp add:slice_kinds_def)
          thus ?thesis by simp
        next
          case False
          with \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close> \<open>sourcenode ax = m\<close> \<open>sourcenode a = m\<close>
          have "slice_kind S a = (\<lambda>cf. False):r\<hookrightarrow>\<^bsub>p\<^esub>fs"
            by(fastforce intro:slice_kind_Call)
          with \<open>preds (slice_kinds S (a # as)) s\<close>
          have False by(simp add:slice_kinds_def)
          thus ?thesis by simp
        qed
        thus ?thesis by simp
      next
        case (Return Q' p' f')
        from \<open>valid_edge ax\<close> \<open>kind ax = Q'\<hookleftarrow>\<^bsub>p'\<^esub>f'\<close> \<open>valid_edge a\<close> \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close>
          \<open>sourcenode a = m\<close> \<open>sourcenode ax = m\<close>
        have False by -(drule return_edges_only,auto)
        thus ?thesis by simp
      qed simp
      have "sourcenode a \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
      proof(rule ccontr)
        assume "sourcenode a \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
        from this \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close>
        have "slice_kind S a = (\<lambda>cf. False):r\<hookrightarrow>\<^bsub>p\<^esub>fs"
          by(rule slice_kind_Call)
        with \<open>preds (slice_kinds S (a # as)) s\<close>
        show False by(simp add:slice_kinds_def)
      qed
      with \<open>preds (slice_kinds S (a # as)) s\<close> \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close>
      have "pred (kind a) s" 
        by(fastforce dest:slice_kind_Call_in_slice simp:slice_kinds_def)
      from \<open>sourcenode a \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close>
        \<open>sourcenode a = m\<close> \<open>sourcenode ax = m\<close>
      have "sourcenode ax \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>" by simp
      with \<open>as' = ax # asx\<close> \<open>preds (slice_kinds S as') s'\<close> 
        \<open>\<exists>Q r p fs. kind ax = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close>
      have "pred (kind ax) s'"
        by(fastforce dest:slice_kind_Call_in_slice simp:slice_kinds_def)
      { fix V assume "V \<in> Use (sourcenode a)"
        from \<open>valid_edge a\<close> have "sourcenode a -[]\<rightarrow>\<^sub>\<iota>* sourcenode a"
          by(fastforce intro:empty_path simp:intra_path_def)
        with \<open>sourcenode a \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close>
          \<open>valid_edge a\<close> \<open>V \<in> Use (sourcenode a)\<close>
        have "V \<in> rv S (CFG_node (sourcenode a))"
          by(auto intro!:rvI CFG_Use_SDG_Use simp:SDG_to_CFG_set_def sourcenodes_def) }
      with \<open>\<forall>V\<in>rv S (CFG_node m). state_val s V = state_val s' V\<close>
        \<open>sourcenode a = m\<close>
      have Use:"\<forall>V \<in> Use (sourcenode a). state_val s V = state_val s' V" by simp
      from \<open>\<forall>i<Suc (length cs). snd (s ! i) = snd (s' ! i)\<close>
      have "snd (hd s) = snd (hd s')"  by fastforce
      with \<open>valid_edge a\<close> \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close> \<open>valid_edge ax\<close>
        \<open>\<exists>Q r p fs. kind ax = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close> \<open>sourcenode a = m\<close> \<open>sourcenode ax = m\<close>
        \<open>pred (kind a) s\<close> \<open>pred (kind ax) s'\<close> Use \<open>length s = Suc (length cs)\<close>
        \<open>length s' = Suc (length cs)\<close>
      have [simp]:"ax = a" by(fastforce intro!:CFG_equal_Use_equal_call)
      from \<open>same_level_path_aux cs as'\<close> \<open>as' = ax#asx\<close> \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close>
        \<open>\<exists>Q r p fs. kind ax = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close>
      have "same_level_path_aux (a # cs) asx" by simp
      from \<open>targetnode ax -asx\<rightarrow>* (_Low_)\<close> have "targetnode a -asx\<rightarrow>* (_Low_)" by simp
      from \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close> \<open>upd_cs cs (a # as) = []\<close> 
      have "upd_cs (a # cs) as = []" by simp
      from \<open>sourcenode a \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close> \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close>
      have slice_kind:"slice_kind S a = 
        Q:r\<hookrightarrow>\<^bsub>p\<^esub>(cspp (targetnode a) (HRB_slice S) fs)"
        by(rule slice_kind_Call_in_slice)
      from \<open>\<forall>i<Suc (length cs). snd (s ! i) = snd (s' ! i)\<close> slice_kind
      have snds:"\<forall>i<Suc (length (a # cs)).
        snd (transfer (slice_kind S a) s ! i) =
        snd (transfer (slice_kind S a) s' ! i)"
        by auto(case_tac i,auto)
      from \<open>valid_edge a\<close> \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close> obtain ins outs 
        where "(p,ins,outs) \<in> set procs" by(fastforce dest!:callee_in_procs)
      with \<open>valid_edge a\<close> \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close>
      have "length (ParamUses (sourcenode a)) = length ins"
        by(fastforce intro:ParamUses_call_source_length)
      with \<open>valid_edge a\<close>
      have "\<forall>i < length ins. \<forall>V \<in> (ParamUses (sourcenode a))!i. V \<in> Use (sourcenode a)"
        by(fastforce intro:ParamUses_in_Use)
      with \<open>\<forall>V \<in> Use (sourcenode a). state_val s V = state_val s' V\<close>
      have "\<forall>i < length ins. \<forall>V \<in> (ParamUses (sourcenode a))!i. 
        state_val s V = state_val s' V"
        by fastforce
      with \<open>valid_edge a\<close> \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close> \<open>(p,ins,outs) \<in> set procs\<close>
        \<open>pred (kind a) s\<close> \<open>pred (kind ax) s'\<close>
      have "\<forall>i < length ins. (params fs (fst (hd s)))!i = (params fs (fst (hd s')))!i"
        by(fastforce intro!:CFG_call_edge_params)
      from \<open>valid_edge a\<close> \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close> \<open>(p,ins,outs) \<in> set procs\<close>
      have "length fs = length ins" by(rule CFG_call_edge_length)
      { fix i assume "i < length fs"
        with \<open>length fs = length ins\<close> have "i < length ins" by simp
        from \<open>i < length fs\<close> have "(params fs (fst cf))!i = (fs!i) (fst cf)"
          by(rule params_nth)
        moreover
        from \<open>i < length fs\<close> have "(params fs (fst cf'))!i = (fs!i) (fst cf')"
          by(rule params_nth)
        ultimately have "(fs!i) (fst (hd s)) = (fs!i) (fst (hd s'))"
          using \<open>i < length ins\<close>
            \<open>\<forall>i < length ins. (params fs (fst (hd s)))!i = (params fs (fst (hd s')))!i\<close>
          by simp }
      hence "\<forall>i < length fs. (fs ! i) (fst cf) = (fs ! i) (fst cf')" by simp
      { fix i assume "i < length fs"
        with \<open>\<forall>i < length fs. (fs ! i) (fst cf) = (fs ! i) (fst cf')\<close>
        have "(fs ! i) (fst cf) = (fs ! i) (fst cf')" by simp
        have "((csppa (targetnode a) (HRB_slice S) 0 fs)!i)(fst cf) =
          ((csppa (targetnode a) (HRB_slice S) 0 fs)!i)(fst cf')"
        proof(cases "Formal_in(targetnode a,i + 0) \<in>  HRB_slice S")
          case True
          with \<open>i < length fs\<close> 
          have "(csppa (targetnode a) (HRB_slice S) 0 fs)!i = fs!i"
            by(rule csppa_Formal_in_in_slice)
          with \<open>(fs ! i) (fst cf) = (fs ! i) (fst cf')\<close> show ?thesis by simp
        next
          case False
          with \<open>i < length fs\<close> 
          have "(csppa (targetnode a) (HRB_slice S) 0 fs)!i = Map.empty"
            by(rule csppa_Formal_in_notin_slice)
          thus ?thesis by simp
        qed }
      hence eq:"\<forall>i < length fs.
        ((cspp (targetnode a) (HRB_slice S) fs)!i)(fst cf) =
        ((cspp (targetnode a) (HRB_slice S) fs)!i)(fst cf')"
        by(simp add:cspp_def)
      { fix i assume "i < length fs"
        hence "(params (cspp (targetnode a) (HRB_slice S) fs)
          (fst cf))!i =
          ((cspp (targetnode a) (HRB_slice S) fs)!i)(fst cf)"
          by(fastforce intro:params_nth)
        moreover
        from \<open>i < length fs\<close>
        have "(params (cspp (targetnode a) (HRB_slice S) fs)
          (fst cf'))!i =
          ((cspp (targetnode a) (HRB_slice S) fs)!i)(fst cf')"
          by(fastforce intro:params_nth)
        ultimately 
        have "(params (cspp (targetnode a) (HRB_slice S) fs)
          (fst cf))!i =
          (params (cspp (targetnode a) (HRB_slice S) fs)(fst cf'))!i"
          using eq \<open>i < length fs\<close> by simp }
      hence "params (cspp (targetnode a) (HRB_slice S) fs)(fst cf) =
        params (cspp (targetnode a) (HRB_slice S) fs)(fst cf')"
        by(simp add:list_eq_iff_nth_eq)
      with slice_kind \<open>(p,ins,outs) \<in> set procs\<close>
      obtain cfx where [simp]:
        "transfer (slice_kind S a) (cf#cfs) = cfx#cf#cfs"
        "transfer (slice_kind S a) (cf'#cfs') = cfx#cf'#cfs'"
        by auto
      hence rv:"\<forall>V\<in>rv S (CFG_node (targetnode a)).
        state_val (transfer (slice_kind S a) s) V = 
        state_val (transfer (slice_kind S a) s') V" by simp
      from rvs \<open>\<forall>V\<in>rv S (CFG_node m). state_val s V = state_val s' V\<close> 
        \<open>sourcenode a = m\<close>
      have rvs':"\<forall>i<length (a # cs). 
        \<forall>V\<in>rv S (CFG_node (sourcenode ((a # cs) ! i))).
        fst ((transfer (slice_kind S a) s) ! Suc i) V = 
        fst ((transfer (slice_kind S a) s') ! Suc i) V"
        by auto(case_tac i,auto)
      from \<open>preds (slice_kinds S (a # as)) s\<close>
      have "preds (slice_kinds S as)
        (transfer (slice_kind S a) s)" by(simp add:slice_kinds_def)
      moreover
      from \<open>preds (slice_kinds S as') s'\<close> \<open>as' = ax#asx\<close>
      have "preds (slice_kinds S asx)
        (transfer (slice_kind S a) s')" by(simp add:slice_kinds_def)
      moreover
      from \<open>length s = Suc (length cs)\<close>
      have "length (transfer (slice_kind S a) s) = 
        Suc (length (a # cs))" by simp
      moreover
      from \<open>length s' = Suc (length cs)\<close>
      have "length (transfer (slice_kind S a) s') = 
        Suc (length (a # cs))" by simp
      moreover
      from IH[OF \<open>upd_cs (a # cs) as = []\<close> \<open>same_level_path_aux (a # cs) asx\<close>
        \<open>\<forall>c\<in>set (a # cs). valid_edge c\<close> \<open>targetnode a -as\<rightarrow>* (_Low_)\<close>
        \<open>targetnode a -asx\<rightarrow>* (_Low_)\<close> rvs' snds rv calculation] \<open>as' = ax#asx\<close>
      show ?thesis by(simp add:slice_kinds_def)
    qed
  qed
next
  case (slpa_Return cs a as Q p f c' cs')
  note IH = \<open>\<And>m as' s s'. \<lbrakk>upd_cs cs' as = []; same_level_path_aux cs' as'; 
    \<forall>c\<in>set cs'. valid_edge c; m -as\<rightarrow>* (_Low_); m -as'\<rightarrow>* (_Low_);
    \<forall>i<length cs'. \<forall>V\<in>rv S (CFG_node (sourcenode (cs' ! i))).
    fst (s ! Suc i) V = fst (s' ! Suc i) V; 
    \<forall>i<Suc (length cs'). snd (s ! i) = snd (s' ! i);
    \<forall>V\<in>rv S (CFG_node m). state_val s V = state_val s' V;
    preds (slice_kinds S as) s; preds (slice_kinds S as') s';
    length s = Suc (length cs'); length s' = Suc (length cs')\<rbrakk>
    \<Longrightarrow> \<forall>V\<in>Use (_Low_). state_val (transfers(slice_kinds S as) s) V =
                       state_val (transfers(slice_kinds S as') s') V\<close>
  note rvs = \<open> \<forall>i<length cs. \<forall>V\<in>rv S (CFG_node (sourcenode (cs ! i))).
    fst (s ! Suc i) V = fst (s' ! Suc i) V\<close>
  from \<open>m -a # as\<rightarrow>* (_Low_)\<close> have "sourcenode a = m" and "valid_edge a"
    and "targetnode a -as\<rightarrow>* (_Low_)" by(auto elim:path_split_Cons)
  from \<open>\<forall>c\<in>set cs. valid_edge c\<close> \<open>cs = c' # cs'\<close>
  have "valid_edge c'" and "\<forall>c\<in>set cs'. valid_edge c" by simp_all
  show ?case
  proof(cases "L = {}")
    case True with UseLow show ?thesis by simp
  next
    case False
    show ?thesis
    proof(cases as')
      case Nil
      with \<open>m -as'\<rightarrow>* (_Low_)\<close> have "m = (_Low_)" by fastforce
      with \<open>valid_edge a\<close> \<open>sourcenode a = m\<close> have "targetnode a = (_Exit_)"
        by -(rule Exit_successor_of_Low,simp+)
      from Low_source_Exit_edge obtain a' where "valid_edge a'"
        and "sourcenode a' = (_Low_)" and "targetnode a' = (_Exit_)"
        and "kind a' = (\<lambda>s. True)\<^sub>\<surd>" by blast
      from \<open>valid_edge a\<close> \<open>sourcenode a = m\<close> \<open>m = (_Low_)\<close> 
        \<open>targetnode a = (_Exit_)\<close> \<open>valid_edge a'\<close> \<open>sourcenode a' = (_Low_)\<close> 
        \<open>targetnode a' = (_Exit_)\<close>
      have "a = a'" by(fastforce dest:edge_det)
      with \<open>kind a' = (\<lambda>s. True)\<^sub>\<surd>\<close> have "kind a = (\<lambda>s. True)\<^sub>\<surd>" by simp
      with \<open>targetnode a = (_Exit_)\<close> \<open>targetnode a -as\<rightarrow>* (_Low_)\<close>
      have "(_Low_) = (_Exit_)" by -(drule path_Exit_source,auto)
      with False have False by -(drule Low_neq_Exit,simp)
      thus ?thesis by simp
    next
      case (Cons ax asx)
      with \<open>m -as'\<rightarrow>* (_Low_)\<close> have "sourcenode ax = m" and "valid_edge ax"
        and "targetnode ax -asx\<rightarrow>* (_Low_)" by(auto elim:path_split_Cons)
      from \<open>valid_edge a\<close> \<open>valid_edge ax\<close> \<open>kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f\<close>
        \<open>sourcenode a = m\<close> \<open>sourcenode ax = m\<close>
      have "\<exists>Q f. kind ax = Q\<hookleftarrow>\<^bsub>p\<^esub>f" by(auto dest:return_edges_only)
      with \<open>same_level_path_aux cs as'\<close> \<open>as' = ax#asx\<close> \<open>cs = c' # cs'\<close>
      have "ax \<in> get_return_edges c'" and "same_level_path_aux cs' asx" by auto
      from \<open>valid_edge c'\<close> \<open>ax \<in> get_return_edges c'\<close> \<open>a \<in> get_return_edges c'\<close>
      have [simp]:"ax = a" by(rule get_return_edges_unique)
      from \<open>targetnode ax -asx\<rightarrow>* (_Low_)\<close> have "targetnode a -asx\<rightarrow>* (_Low_)" by simp
      from \<open>upd_cs cs (a # as) = []\<close> \<open>kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f\<close> \<open>cs = c' # cs'\<close>
        \<open>a \<in> get_return_edges c'\<close>
      have "upd_cs cs' as = []" by simp
      from \<open>length s = Suc (length cs)\<close> \<open>cs = c' # cs'\<close>
      obtain cf cfx cfs where "s = cf#cfx#cfs"
        by(cases s,auto,case_tac list,fastforce+)
      from \<open>length s' = Suc (length cs)\<close> \<open>cs = c' # cs'\<close>
      obtain cf' cfx' cfs' where "s' = cf'#cfx'#cfs'"
        by(cases s',auto,case_tac list,fastforce+)
      from rvs \<open>cs = c' # cs'\<close> \<open>s = cf#cfx#cfs\<close> \<open>s' = cf'#cfx'#cfs'\<close>
      have rvs1:"\<forall>i<length cs'. 
        \<forall>V\<in>rv S (CFG_node (sourcenode (cs' ! i))).
        fst ((cfx#cfs) ! Suc i) V = fst ((cfx'#cfs') ! Suc i) V"
        and "\<forall>V\<in>rv S (CFG_node (sourcenode c')). 
        (fst cfx) V = (fst cfx') V"
        by auto
      from \<open>valid_edge c'\<close> \<open>a \<in> get_return_edges c'\<close>
      obtain Qx rx px fsx where "kind c' = Qx:rx\<hookrightarrow>\<^bsub>px\<^esub>fsx"
        by(fastforce dest!:only_call_get_return_edges)
      have "\<forall>V \<in> rv S (CFG_node (targetnode a)).
        V \<in> rv S (CFG_node (sourcenode c'))"
      proof
        fix V assume "V \<in> rv S (CFG_node (targetnode a))"
        from \<open>valid_edge c'\<close> \<open>a \<in> get_return_edges c'\<close>
        obtain a' where edge:"valid_edge a'" "sourcenode a' = sourcenode c'"
          "targetnode a' = targetnode a" "intra_kind (kind a')"
          by -(drule call_return_node_edge,auto simp:intra_kind_def)
        from \<open>V \<in> rv S (CFG_node (targetnode a))\<close>
        obtain as n' where "targetnode a -as\<rightarrow>\<^sub>\<iota>* parent_node n'"
          and "n' \<in> HRB_slice S" and "V \<in> Use\<^bsub>SDG\<^esub> n'"
          and all:"\<forall>n''. valid_SDG_node n'' \<and> parent_node n'' \<in> set (sourcenodes as) 
          \<longrightarrow> V \<notin> Def\<^bsub>SDG\<^esub> n''" by(fastforce elim:rvE)
        from \<open>targetnode a -as\<rightarrow>\<^sub>\<iota>* parent_node n'\<close> edge
        have "sourcenode c' -a'#as\<rightarrow>\<^sub>\<iota>* parent_node n'"
          by(fastforce intro:Cons_path simp:intra_path_def)
        from \<open>valid_edge c'\<close> \<open>kind c' = Qx:rx\<hookrightarrow>\<^bsub>px\<^esub>fsx\<close> have "Def (sourcenode c') = {}"
          by(rule call_source_Def_empty)
        hence "\<forall>n''. valid_SDG_node n'' \<and> parent_node n'' = sourcenode c'
          \<longrightarrow> V \<notin> Def\<^bsub>SDG\<^esub> n''" by(fastforce dest:SDG_Def_parent_Def)
        with all \<open>sourcenode a' = sourcenode c'\<close>
        have "\<forall>n''. valid_SDG_node n'' \<and> parent_node n'' \<in> set (sourcenodes (a'#as)) 
          \<longrightarrow> V \<notin> Def\<^bsub>SDG\<^esub> n''" by(fastforce simp:sourcenodes_def)
        with \<open>sourcenode c' -a'#as\<rightarrow>\<^sub>\<iota>* parent_node n'\<close> 
          \<open>n' \<in> HRB_slice S\<close> \<open>V \<in> Use\<^bsub>SDG\<^esub> n'\<close>
        show "V \<in> rv S (CFG_node (sourcenode c'))"
          by(fastforce intro:rvI)
      qed
      show ?thesis
      proof(cases "sourcenode a \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>")
        case True
        from \<open>valid_edge c'\<close> \<open>a \<in> get_return_edges c'\<close>
        have "get_proc (targetnode c') = get_proc (sourcenode a)"
          by -(drule intra_proc_additional_edge,
            auto dest:get_proc_intra simp:intra_kind_def)
        moreover
        from \<open>valid_edge c'\<close> \<open>kind c' = Qx:rx\<hookrightarrow>\<^bsub>px\<^esub>fsx\<close>
        have "get_proc (targetnode c') = px" by(rule get_proc_call)
        moreover
        from \<open>valid_edge a\<close> \<open>kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f\<close>
        have "get_proc (sourcenode a) = p" by(rule get_proc_return)
        ultimately have [simp]:"px = p" by simp
        from \<open>valid_edge c'\<close> \<open>kind c' = Qx:rx\<hookrightarrow>\<^bsub>px\<^esub>fsx\<close>
        obtain ins outs where "(p,ins,outs) \<in> set procs"
          by(fastforce dest!:callee_in_procs)
        with \<open>sourcenode a \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close>
          \<open>valid_edge a\<close> \<open>kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f\<close>
        have slice_kind:"slice_kind S a = 
          Q\<hookleftarrow>\<^bsub>p\<^esub>(\<lambda>cf cf'. rspp (targetnode a) (HRB_slice S) outs cf' cf)"
          by(rule slice_kind_Return_in_slice)
        with \<open>s = cf#cfx#cfs\<close> \<open>s' = cf'#cfx'#cfs'\<close>
        have sx:"transfer (slice_kind S a) s = 
          (rspp (targetnode a) (HRB_slice S) outs (fst cfx) (fst cf),
          snd cfx)#cfs"
          and sx':"transfer (slice_kind S a) s' = 
          (rspp (targetnode a) (HRB_slice S) outs (fst cfx') (fst cf'),
          snd cfx')#cfs'"
          by simp_all
        with rvs1 have rvs':"\<forall>i<length cs'. 
          \<forall>V\<in>rv S (CFG_node (sourcenode (cs' ! i))).
          fst ((transfer (slice_kind S a) s) ! Suc i) V = 
          fst ((transfer (slice_kind S a) s') ! Suc i) V"
          by fastforce
        from slice_kind \<open>\<forall>i<Suc (length cs). snd (s ! i) = snd (s' ! i)\<close> \<open>cs = c' # cs'\<close>
          \<open>s = cf#cfx#cfs\<close> \<open>s' = cf'#cfx'#cfs'\<close>
        have snds:"\<forall>i<Suc (length cs').
          snd (transfer (slice_kind S a) s ! i) =
          snd (transfer (slice_kind S a) s' ! i)"
          apply auto apply(case_tac i) apply auto
          by(erule_tac x="Suc (Suc nat)" in allE) auto
        have "\<forall>V\<in>rv S (CFG_node (targetnode a)).
          (rspp (targetnode a) (HRB_slice S) outs 
          (fst cfx) (fst cf)) V =
          (rspp (targetnode a) (HRB_slice S) outs 
          (fst cfx') (fst cf')) V"
        proof
          fix V assume "V \<in> rv S (CFG_node (targetnode a))"
          show "(rspp (targetnode a) (HRB_slice S) outs 
            (fst cfx) (fst cf)) V =
            (rspp (targetnode a) (HRB_slice S) outs 
            (fst cfx') (fst cf')) V"
          proof(cases "V \<in> set (ParamDefs (targetnode a))")
            case True
            then obtain i where "i < length (ParamDefs (targetnode a))"
              and "(ParamDefs (targetnode a))!i = V"
              by(fastforce simp:in_set_conv_nth)
            from \<open>valid_edge a\<close> \<open>kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f\<close> \<open>(p,ins,outs) \<in> set procs\<close>
            have "length(ParamDefs (targetnode a)) = length outs"
              by(fastforce intro:ParamDefs_return_target_length)
            show ?thesis
            proof(cases "Actual_out(targetnode a,i) \<in> HRB_slice S")
              case True
              with \<open>i < length (ParamDefs (targetnode a))\<close> \<open>valid_edge a\<close>
                \<open>length(ParamDefs (targetnode a)) = length outs\<close>
                \<open>(ParamDefs (targetnode a))!i = V\<close>[THEN sym]
              have rspp_eq:"(rspp (targetnode a) 
                (HRB_slice S) outs (fst cfx) (fst cf)) V = 
                (fst cf)(outs!i)"
                "(rspp (targetnode a) 
                (HRB_slice S) outs (fst cfx') (fst cf')) V = 
                (fst cf')(outs!i)"
                by(auto intro:rspp_Actual_out_in_slice)
              from \<open>valid_edge a\<close> \<open>kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f\<close> \<open>(p,ins,outs) \<in> set procs\<close>
              have "\<forall>V \<in> set outs. V \<in> Use (sourcenode a)" by(fastforce dest:outs_in_Use)
              have "\<forall>V \<in> Use (sourcenode a). V \<in> rv S (CFG_node m)"
              proof
                fix V assume "V \<in> Use (sourcenode a)"
                from \<open>valid_edge a\<close> \<open>sourcenode a = m\<close>
                have "parent_node (CFG_node m) -[]\<rightarrow>\<^sub>\<iota>* parent_node (CFG_node m)"
                  by(fastforce intro:empty_path simp:intra_path_def)
                with \<open>sourcenode a \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close> 
                  \<open>V \<in> Use (sourcenode a)\<close> \<open>sourcenode a = m\<close> \<open>valid_edge a\<close>
                show "V \<in> rv S (CFG_node m)"
                  by -(rule rvI,
                    auto intro!:CFG_Use_SDG_Use simp:SDG_to_CFG_set_def sourcenodes_def)
              qed
              with \<open>\<forall>V \<in> set outs. V \<in> Use (sourcenode a)\<close>
              have "\<forall>V \<in> set outs. V \<in> rv S (CFG_node m)" by simp
              with \<open>\<forall>V\<in>rv S (CFG_node m). state_val s V = state_val s' V\<close>
                \<open>s = cf#cfx#cfs\<close> \<open>s' = cf'#cfx'#cfs'\<close>
              have "\<forall>V \<in> set outs. (fst cf) V = (fst cf') V" by simp
              with \<open>i < length (ParamDefs (targetnode a))\<close>
                \<open>length(ParamDefs (targetnode a)) = length outs\<close>
              have "(fst cf)(outs!i) = (fst cf')(outs!i)" by fastforce
              with rspp_eq show ?thesis by simp
            next
              case False
              with \<open>i < length (ParamDefs (targetnode a))\<close> \<open>valid_edge a\<close>
                \<open>length(ParamDefs (targetnode a)) = length outs\<close>
                \<open>(ParamDefs (targetnode a))!i = V\<close>[THEN sym]
              have rspp_eq:"(rspp (targetnode a) 
                (HRB_slice S) outs (fst cfx) (fst cf)) V = 
                (fst cfx)((ParamDefs (targetnode a))!i)"
                "(rspp (targetnode a) 
                (HRB_slice S) outs (fst cfx') (fst cf')) V = 
                (fst cfx')((ParamDefs (targetnode a))!i)"
                by(auto intro:rspp_Actual_out_notin_slice)
              from \<open>\<forall>V\<in>rv S (CFG_node (sourcenode c')). 
                (fst cfx) V = (fst cfx') V\<close>
                \<open>V \<in> rv S (CFG_node (targetnode a))\<close>
                \<open>\<forall>V \<in> rv S (CFG_node (targetnode a)).
                V \<in> rv S (CFG_node (sourcenode c'))\<close>
                \<open>(ParamDefs (targetnode a))!i = V\<close>[THEN sym]
              have "(fst cfx) (ParamDefs (targetnode a) ! i) =
                (fst cfx') (ParamDefs (targetnode a) ! i)" by fastforce
              with rspp_eq show ?thesis by fastforce
            qed
          next
            case False
            with \<open>\<forall>V\<in>rv S (CFG_node (sourcenode c')). 
              (fst cfx) V = (fst cfx') V\<close>
              \<open>V \<in> rv S (CFG_node (targetnode a))\<close>
              \<open>\<forall>V \<in> rv S (CFG_node (targetnode a)).
              V \<in> rv S (CFG_node (sourcenode c'))\<close>
            show ?thesis by(fastforce simp:rspp_def map_merge_def)
          qed
        qed
        with sx sx'
        have rv':"\<forall>V\<in>rv S (CFG_node (targetnode a)).
          state_val (transfer (slice_kind S a) s) V =
          state_val (transfer (slice_kind S a) s') V"
          by fastforce
        from \<open>preds (slice_kinds S (a # as)) s\<close>
        have "preds (slice_kinds S as) 
          (transfer (slice_kind S a) s)"
          by(simp add:slice_kinds_def)
        moreover
        from \<open>preds (slice_kinds S as') s'\<close> \<open>as' = ax#asx\<close>
        have "preds (slice_kinds S asx) 
          (transfer (slice_kind S a) s')"
          by(simp add:slice_kinds_def)
        moreover
        from \<open>length s = Suc (length cs)\<close> \<open>cs = c' # cs'\<close> sx
        have "length (transfer (slice_kind S a) s) = Suc (length cs')"
          by(simp,simp add:\<open>s = cf#cfx#cfs\<close>)
        moreover
        from \<open>length s' = Suc (length cs)\<close> \<open>cs = c' # cs'\<close> sx'
        have "length (transfer (slice_kind S a) s') = Suc (length cs')"
          by(simp,simp add:\<open>s' = cf'#cfx'#cfs'\<close>)
        moreover
        from IH[OF \<open>upd_cs cs' as = []\<close> \<open>same_level_path_aux cs' asx\<close> 
          \<open>\<forall>c\<in>set cs'. valid_edge c\<close> \<open>targetnode a -as\<rightarrow>* (_Low_)\<close> 
          \<open>targetnode a -asx\<rightarrow>* (_Low_)\<close> rvs' snds rv' calculation] \<open>as' = ax#asx\<close>
        show ?thesis by(simp add:slice_kinds_def)
      next
        case False
        from this \<open>kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f\<close>
        have slice_kind:"slice_kind S a = (\<lambda>cf. True)\<hookleftarrow>\<^bsub>p\<^esub>(\<lambda>cf cf'. cf')"
          by(rule slice_kind_Return)
        with \<open>s = cf#cfx#cfs\<close> \<open>s' = cf'#cfx'#cfs'\<close>
        have [simp]:"transfer (slice_kind S a) s = cfx#cfs"
          "transfer (slice_kind S a) s' = cfx'#cfs'" by simp_all
        from slice_kind \<open>\<forall>i<Suc (length cs). snd (s ! i) = snd (s' ! i)\<close> 
          \<open>cs = c' # cs'\<close> \<open>s = cf#cfx#cfs\<close> \<open>s' = cf'#cfx'#cfs'\<close>
        have snds:"\<forall>i<Suc (length cs').
          snd (transfer (slice_kind S a) s ! i) =
          snd (transfer (slice_kind S a) s' ! i)" by fastforce
        from rvs1 have rvs':"\<forall>i<length cs'. 
          \<forall>V\<in>rv S (CFG_node (sourcenode (cs' ! i))).
          fst ((transfer (slice_kind S a) s) ! Suc i) V = 
          fst ((transfer (slice_kind S a) s') ! Suc i) V"
          by fastforce
        from \<open>\<forall>V \<in> rv S (CFG_node (targetnode a)).
          V \<in> rv S (CFG_node (sourcenode c'))\<close>
          \<open>\<forall>V\<in>rv S (CFG_node (sourcenode c')). 
          (fst cfx) V = (fst cfx') V\<close>
        have rv':"\<forall>V\<in>rv S (CFG_node (targetnode a)).
          state_val (transfer (slice_kind S a) s) V =
          state_val (transfer (slice_kind S a) s') V" by simp
        from \<open>preds (slice_kinds S (a # as)) s\<close>
        have "preds (slice_kinds S as) 
          (transfer (slice_kind S a) s)"
          by(simp add:slice_kinds_def)
        moreover
        from \<open>preds (slice_kinds S as') s'\<close> \<open>as' = ax#asx\<close>
        have "preds (slice_kinds S asx) 
          (transfer (slice_kind S a) s')"
          by(simp add:slice_kinds_def)
        moreover
        from \<open>length s = Suc (length cs)\<close> \<open>cs = c' # cs'\<close>
        have "length (transfer (slice_kind S a) s) = Suc (length cs')"
          by(simp,simp add:\<open>s = cf#cfx#cfs\<close>)
        moreover
        from \<open>length s' = Suc (length cs)\<close> \<open>cs = c' # cs'\<close>
        have "length (transfer (slice_kind S a) s') = Suc (length cs')"
          by(simp,simp add:\<open>s' = cf'#cfx'#cfs'\<close>)
        moreover
        from IH[OF \<open>upd_cs cs' as = []\<close> \<open>same_level_path_aux cs' asx\<close> 
          \<open>\<forall>c\<in>set cs'. valid_edge c\<close> \<open>targetnode a -as\<rightarrow>* (_Low_)\<close> 
          \<open>targetnode a -asx\<rightarrow>* (_Low_)\<close> rvs' snds rv' calculation] \<open>as' = ax#asx\<close>
        show ?thesis by(simp add:slice_kinds_def)
      qed
    qed
  qed
qed


lemma rv_Low_Use_Low:
  assumes "m -as\<rightarrow>\<^sub>\<surd>* (_Low_)" and "m -as'\<rightarrow>\<^sub>\<surd>* (_Low_)" and "get_proc m = Main"
  and "\<forall>V \<in> rv S (CFG_node m). cf V = cf' V"
  and "preds (slice_kinds S as) [(cf,undefined)]"
  and "preds (slice_kinds S as') [(cf',undefined)]"
  and "CFG_node (_Low_) \<in> S"
  shows "\<forall>V \<in> Use (_Low_). 
    state_val (transfers(slice_kinds S as) [(cf,undefined)]) V =
    state_val (transfers(slice_kinds S as') [(cf',undefined)]) V"
proof(cases as)
  case Nil
  with \<open>m -as\<rightarrow>\<^sub>\<surd>* (_Low_)\<close> have "valid_node m" and "m = (_Low_)" 
    by(auto intro:path_valid_node simp:vp_def)
  { fix V assume "V \<in> Use (_Low_)"
    moreover
    from \<open>valid_node m\<close> \<open>m = (_Low_)\<close> have "(_Low_) -[]\<rightarrow>\<^sub>\<iota>* (_Low_)"
      by(fastforce intro:empty_path simp:intra_path_def)
    moreover
    from \<open>valid_node m\<close> \<open>m = (_Low_)\<close> \<open>CFG_node (_Low_) \<in> S\<close>
    have "CFG_node (_Low_) \<in> HRB_slice S"
      by(fastforce intro:HRB_slice_refl)
    ultimately have "V \<in> rv S (CFG_node m)" using \<open>m = (_Low_)\<close>
      by(auto intro!:rvI CFG_Use_SDG_Use simp:sourcenodes_def) }
  hence "\<forall>V \<in> Use (_Low_). V \<in> rv S (CFG_node m)" by simp
  show ?thesis
  proof(cases "L = {}")
    case True with UseLow show ?thesis by simp
  next
    case False
    from \<open>m -as'\<rightarrow>\<^sub>\<surd>* (_Low_)\<close> have "m -as'\<rightarrow>* (_Low_)" by(simp add:vp_def)
    from \<open>m -as'\<rightarrow>* (_Low_)\<close> \<open>m = (_Low_)\<close> have "as' = []"
    proof(induct m as' m'\<equiv>"(_Low_)" rule:path.induct)
      case (Cons_path m'' as a m)
      from \<open>valid_edge a\<close> \<open>sourcenode a = m\<close> \<open>m = (_Low_)\<close>
      have "targetnode a = (_Exit_)" by -(rule Exit_successor_of_Low,simp+)
      with \<open>targetnode a = m''\<close> \<open>m'' -as\<rightarrow>* (_Low_)\<close>
      have "(_Low_) = (_Exit_)" by -(drule path_Exit_source,auto)
      with False have False by -(drule Low_neq_Exit,simp)
      thus ?case by simp
    qed simp
    with Nil \<open>\<forall>V \<in> rv S (CFG_node m). cf V = cf' V\<close>
      \<open>\<forall>V \<in> Use (_Low_). V \<in> rv S (CFG_node m)\<close>
    show ?thesis by(fastforce simp:slice_kinds_def)
  qed
next
  case (Cons ax asx)
  with \<open>m -as\<rightarrow>\<^sub>\<surd>* (_Low_)\<close> have "sourcenode ax = m" and "valid_edge ax"
    and "targetnode ax -asx\<rightarrow>* (_Low_)"
    by(auto elim:path_split_Cons simp:vp_def)
  show ?thesis
  proof(cases "L = {}")
    case True with UseLow show ?thesis by simp
  next
    case False
    show ?thesis
    proof(cases as')
      case Nil
      with \<open>m -as'\<rightarrow>\<^sub>\<surd>* (_Low_)\<close> have "m = (_Low_)" by(fastforce simp:vp_def)
      with \<open>valid_edge ax\<close> \<open>sourcenode ax = m\<close> have "targetnode ax = (_Exit_)"
        by -(rule Exit_successor_of_Low,simp+)
      from Low_source_Exit_edge obtain a' where "valid_edge a'"
        and "sourcenode a' = (_Low_)" and "targetnode a' = (_Exit_)"
        and "kind a' = (\<lambda>s. True)\<^sub>\<surd>" by blast
      from \<open>valid_edge ax\<close> \<open>sourcenode ax = m\<close> \<open>m = (_Low_)\<close> 
        \<open>targetnode ax = (_Exit_)\<close> \<open>valid_edge a'\<close> \<open>sourcenode a' = (_Low_)\<close> 
        \<open>targetnode a' = (_Exit_)\<close>
      have "ax = a'" by(fastforce dest:edge_det)
      with \<open>kind a' = (\<lambda>s. True)\<^sub>\<surd>\<close> have "kind ax = (\<lambda>s. True)\<^sub>\<surd>" by simp
      with \<open>targetnode ax = (_Exit_)\<close> \<open>targetnode ax -asx\<rightarrow>* (_Low_)\<close>
      have "(_Low_) = (_Exit_)" by -(drule path_Exit_source,auto)
      with False have False by -(drule Low_neq_Exit,simp)
      thus ?thesis by simp
    next
      case (Cons ax' asx')
      from \<open>m -as\<rightarrow>\<^sub>\<surd>* (_Low_)\<close> have "valid_path_aux [] as" and "m -as\<rightarrow>* (_Low_)"
        by(simp_all add:vp_def valid_path_def)
      from this \<open>as = ax#asx\<close> \<open>get_proc m = Main\<close>
      have "same_level_path_aux [] as \<and> upd_cs [] as = []"
        by -(rule vpa_Main_slpa[of _ _ m "(_Low_)"],
        (fastforce intro!:get_proc_Low simp:valid_call_list_def)+)
      hence "same_level_path_aux [] as" and "upd_cs [] as = []" by simp_all
      from \<open>m -as'\<rightarrow>\<^sub>\<surd>* (_Low_)\<close> have "valid_path_aux [] as'" and "m -as'\<rightarrow>* (_Low_)"
        by(simp_all add:vp_def valid_path_def)
      from this \<open>as' = ax'#asx'\<close> \<open>get_proc m = Main\<close>
      have "same_level_path_aux [] as' \<and> upd_cs [] as' = []"
        by -(rule vpa_Main_slpa[of _ _ m "(_Low_)"],
        (fastforce intro!:get_proc_Low simp:valid_call_list_def)+)
      hence "same_level_path_aux [] as'" by simp
      from \<open>same_level_path_aux [] as\<close> \<open>upd_cs [] as = []\<close>
        \<open>same_level_path_aux [] as'\<close> \<open>m -as\<rightarrow>* (_Low_)\<close> \<open>m -as'\<rightarrow>* (_Low_)\<close>
        \<open>\<forall>V \<in> rv S (CFG_node m). cf V = cf' V\<close> \<open>CFG_node (_Low_) \<in> S\<close>
        \<open>preds (slice_kinds S as) [(cf,undefined)]\<close>
        \<open>preds (slice_kinds S as') [(cf',undefined)]\<close>
      show ?thesis by -(erule slpa_rv_Low_Use_Low,auto)
    qed
  qed
qed



lemma nonInterference_path_to_Low:
  assumes "[cf] \<approx>\<^sub>L [cf']" and "(_High_) \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
  and "CFG_node (_Low_) \<in> S"
  and "(_Entry_) -as\<rightarrow>\<^sub>\<surd>* (_Low_)" and "preds (kinds as) [(cf,undefined)]"
  and "(_Entry_) -as'\<rightarrow>\<^sub>\<surd>* (_Low_)" and "preds (kinds as') [(cf',undefined)]"
  shows "map fst (transfers (kinds as) [(cf,undefined)]) \<approx>\<^sub>L 
         map fst (transfers (kinds as') [(cf',undefined)])"
proof -
  from \<open>(_Entry_) -as\<rightarrow>\<^sub>\<surd>* (_Low_)\<close> \<open>preds (kinds as) [(cf,undefined)]\<close>
    \<open>CFG_node (_Low_) \<in> S\<close>
  obtain asx where "preds (slice_kinds S asx) [(cf,undefined)]"
    and "\<forall>V \<in> Use (_Low_). 
    state_val (transfers (slice_kinds S asx) [(cf,undefined)]) V = 
    state_val (transfers (kinds as) [(cf,undefined)]) V"
    and "slice_edges S [] as = slice_edges S [] asx"
    and "transfers (kinds as) [(cf,undefined)] \<noteq> []"
    and "(_Entry_) -asx\<rightarrow>\<^sub>\<surd>* (_Low_)" 
    by(erule fundamental_property_of_static_slicing)
  from \<open>(_Entry_) -as'\<rightarrow>\<^sub>\<surd>* (_Low_)\<close> \<open>preds (kinds as') [(cf',undefined)]\<close>
    \<open>CFG_node (_Low_) \<in> S\<close>
  obtain asx' where "preds (slice_kinds S asx') [(cf',undefined)]"
    and "\<forall>V \<in> Use (_Low_). 
    state_val (transfers(slice_kinds S asx') [(cf',undefined)]) V = 
    state_val (transfers(kinds as') [(cf',undefined)]) V"
    and "slice_edges S [] as' = 
    slice_edges S [] asx'"
    and "transfers (kinds as') [(cf',undefined)] \<noteq> []"
    and "(_Entry_) -asx'\<rightarrow>\<^sub>\<surd>* (_Low_)"
    by(erule fundamental_property_of_static_slicing)
  from \<open>[cf] \<approx>\<^sub>L [cf']\<close> \<open>(_High_) \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close>
  have "\<forall>V \<in> rv S (CFG_node (_Entry_)). cf V = cf' V" 
    by(fastforce dest:lowEquivalence_relevant_nodes_Entry)
  with \<open>(_Entry_) -asx \<rightarrow>\<^sub>\<surd>*(_Low_)\<close> \<open>(_Entry_) -asx'\<rightarrow>\<^sub>\<surd>* (_Low_)\<close>
    \<open>CFG_node (_Low_) \<in> S\<close> \<open>preds (slice_kinds S asx) [(cf,undefined)]\<close>
    \<open>preds (slice_kinds S asx') [(cf',undefined)]\<close>
  have "\<forall>V \<in> Use (_Low_). 
    state_val (transfers(slice_kinds S asx) [(cf,undefined)]) V =
    state_val (transfers(slice_kinds S asx') [(cf',undefined)]) V"
    by -(rule rv_Low_Use_Low,auto intro:get_proc_Entry)
  with \<open>\<forall>V \<in> Use (_Low_). 
    state_val (transfers (slice_kinds S asx) [(cf,undefined)]) V = 
    state_val (transfers (kinds as) [(cf,undefined)]) V\<close>
    \<open>\<forall>V \<in> Use (_Low_). 
    state_val (transfers(slice_kinds S asx') [(cf',undefined)]) V = 
    state_val (transfers(kinds as') [(cf',undefined)]) V\<close>
    \<open>transfers (kinds as) [(cf,undefined)] \<noteq> []\<close> 
    \<open>transfers (kinds as') [(cf',undefined)] \<noteq> []\<close>
  show ?thesis by(fastforce simp:lowEquivalence_def UseLow neq_Nil_conv)
qed


theorem nonInterference_path:
  assumes "[cf] \<approx>\<^sub>L [cf']" and "(_High_) \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
  and "CFG_node (_Low_) \<in> S"
  and "(_Entry_) -as\<rightarrow>\<^sub>\<surd>* (_Exit_)" and "preds (kinds as) [(cf,undefined)]"
  and "(_Entry_) -as'\<rightarrow>\<^sub>\<surd>* (_Exit_)" and "preds (kinds as') [(cf',undefined)]"
  shows "map fst (transfers (kinds as) [(cf,undefined)]) \<approx>\<^sub>L 
  map fst (transfers (kinds as') [(cf',undefined)])"
proof -
  from \<open>(_Entry_) -as\<rightarrow>\<^sub>\<surd>* (_Exit_)\<close> obtain x xs where "as = x#xs"
    and "(_Entry_) = sourcenode x" and "valid_edge x" 
    and "targetnode x -xs\<rightarrow>* (_Exit_)"
    apply(cases "as = []")
     apply(clarsimp simp:vp_def,drule empty_path_nodes,drule Entry_noteq_Exit,simp)
    by(fastforce elim:path_split_Cons simp:vp_def)
  from \<open>(_Entry_) -as\<rightarrow>\<^sub>\<surd>* (_Exit_)\<close> have "valid_path as" by(simp add:vp_def)
  from \<open>valid_edge x\<close> have "valid_node (targetnode x)" by simp
  hence "inner_node (targetnode x)"
  proof(cases rule:valid_node_cases)
    case Entry
    with \<open>valid_edge x\<close> have False by(rule Entry_target)
    thus ?thesis by simp
  next
    case Exit
    with \<open>targetnode x -xs\<rightarrow>* (_Exit_)\<close> have "xs = []"
      by -(drule path_Exit_source,auto)
    from Entry_Exit_edge obtain z where "valid_edge z"
      and "sourcenode z = (_Entry_)" and "targetnode z = (_Exit_)"
      and "kind z = (\<lambda>s. False)\<^sub>\<surd>" by blast
    from \<open>valid_edge x\<close> \<open>valid_edge z\<close> \<open>(_Entry_) = sourcenode x\<close> 
      \<open>sourcenode z = (_Entry_)\<close> Exit \<open>targetnode z = (_Exit_)\<close>
    have "x = z" by(fastforce intro:edge_det)
    with \<open>preds (kinds as) [(cf,undefined)]\<close> \<open>as = x#xs\<close> \<open>xs = []\<close>
      \<open>kind z = (\<lambda>s. False)\<^sub>\<surd>\<close> 
    have False by(simp add:kinds_def)
    thus ?thesis by simp
  qed simp
  with \<open>targetnode x -xs\<rightarrow>* (_Exit_)\<close> obtain x' xs' where "xs = xs'@[x']"
    and "targetnode x -xs'\<rightarrow>* (_Low_)" and "kind x' = (\<lambda>s. True)\<^sub>\<surd>"
    by(fastforce elim:Exit_path_Low_path)
  with \<open>(_Entry_) = sourcenode x\<close> \<open>valid_edge x\<close>
  have "(_Entry_) -x#xs'\<rightarrow>* (_Low_)" by(fastforce intro:Cons_path)
  from \<open>valid_path as\<close> \<open>as = x#xs\<close> \<open>xs = xs'@[x']\<close>
  have "valid_path (x#xs')"
    by(simp add:valid_path_def del:valid_path_aux.simps)
      (rule valid_path_aux_split,simp)
  with \<open>(_Entry_) -x#xs'\<rightarrow>* (_Low_)\<close> have "(_Entry_) -x#xs'\<rightarrow>\<^sub>\<surd>* (_Low_)"
    by(simp add:vp_def)
  from \<open>as = x#xs\<close> \<open>xs = xs'@[x']\<close> have "as = (x#xs')@[x']" by simp
  with \<open>preds (kinds as) [(cf,undefined)]\<close> 
  have "preds (kinds (x#xs')) [(cf,undefined)]"
    by(simp add:kinds_def preds_split)
  from \<open>(_Entry_) -as'\<rightarrow>\<^sub>\<surd>* (_Exit_)\<close> obtain y ys where "as' = y#ys"
    and "(_Entry_) = sourcenode y" and "valid_edge y" 
    and "targetnode y -ys\<rightarrow>* (_Exit_)"
    apply(cases "as' = []")
     apply(clarsimp simp:vp_def,drule empty_path_nodes,drule Entry_noteq_Exit,simp)
    by(fastforce elim:path_split_Cons simp:vp_def)
  from \<open>(_Entry_) -as'\<rightarrow>\<^sub>\<surd>* (_Exit_)\<close> have "valid_path as'" by(simp add:vp_def)
  from \<open>valid_edge y\<close> have "valid_node (targetnode y)" by simp
  hence "inner_node (targetnode y)"
  proof(cases rule:valid_node_cases)
    case Entry
    with \<open>valid_edge y\<close> have False by(rule Entry_target)
    thus ?thesis by simp
  next
    case Exit
    with \<open>targetnode y -ys\<rightarrow>* (_Exit_)\<close> have "ys = []"
      by -(drule path_Exit_source,auto)
    from Entry_Exit_edge obtain z where "valid_edge z"
      and "sourcenode z = (_Entry_)" and "targetnode z = (_Exit_)"
      and "kind z = (\<lambda>s. False)\<^sub>\<surd>" by blast
    from \<open>valid_edge y\<close> \<open>valid_edge z\<close> \<open>(_Entry_) = sourcenode y\<close> 
      \<open>sourcenode z = (_Entry_)\<close> Exit \<open>targetnode z = (_Exit_)\<close>
    have "y = z" by(fastforce intro:edge_det)
    with \<open>preds (kinds as') [(cf',undefined)]\<close> \<open>as' = y#ys\<close> \<open>ys = []\<close>
      \<open>kind z = (\<lambda>s. False)\<^sub>\<surd>\<close> 
    have False by(simp add:kinds_def)
    thus ?thesis by simp
  qed simp
  with \<open>targetnode y -ys\<rightarrow>* (_Exit_)\<close> obtain y' ys' where "ys = ys'@[y']"
    and "targetnode y -ys'\<rightarrow>* (_Low_)" and "kind y' = (\<lambda>s. True)\<^sub>\<surd>"
    by(fastforce elim:Exit_path_Low_path)
  with \<open>(_Entry_) = sourcenode y\<close> \<open>valid_edge y\<close>
  have "(_Entry_) -y#ys'\<rightarrow>* (_Low_)" by(fastforce intro:Cons_path)
  from \<open>valid_path as'\<close> \<open>as' = y#ys\<close> \<open>ys = ys'@[y']\<close>
  have "valid_path (y#ys')"
    by(simp add:valid_path_def del:valid_path_aux.simps)
      (rule valid_path_aux_split,simp)
  with \<open>(_Entry_) -y#ys'\<rightarrow>* (_Low_)\<close> have "(_Entry_) -y#ys'\<rightarrow>\<^sub>\<surd>* (_Low_)"
    by(simp add:vp_def)
  from \<open>as' = y#ys\<close> \<open>ys = ys'@[y']\<close> have "as' = (y#ys')@[y']" by simp
  with \<open>preds (kinds as') [(cf',undefined)]\<close> 
  have "preds (kinds (y#ys')) [(cf',undefined)]"
    by(simp add:kinds_def preds_split)
  from \<open>[cf] \<approx>\<^sub>L [cf']\<close> \<open>(_High_) \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close> \<open>CFG_node (_Low_) \<in> S\<close>
    \<open>(_Entry_) -x#xs'\<rightarrow>\<^sub>\<surd>* (_Low_)\<close> \<open>preds (kinds (x#xs')) [(cf,undefined)]\<close>
    \<open>(_Entry_) -y#ys'\<rightarrow>\<^sub>\<surd>* (_Low_)\<close> \<open>preds (kinds (y#ys')) [(cf',undefined)]\<close>
  have "map fst (transfers (kinds (x#xs')) [(cf,undefined)]) \<approx>\<^sub>L 
    map fst (transfers (kinds (y#ys')) [(cf',undefined)])"
    by(rule nonInterference_path_to_Low)
  with \<open>as = x#xs\<close> \<open>xs = xs'@[x']\<close> \<open>kind x' = (\<lambda>s. True)\<^sub>\<surd>\<close>
    \<open>as' = y#ys\<close> \<open>ys = ys'@[y']\<close> \<open>kind y' = (\<lambda>s. True)\<^sub>\<surd>\<close>
  show ?thesis
    apply(cases "transfers (map kind xs') (transfer (kind x) [(cf,undefined)])")
    apply (auto simp add:kinds_def transfers_split)
    by((cases "transfers (map kind ys') (transfer (kind y) [(cf',undefined)])"),
       (auto simp add:kinds_def transfers_split))+
qed


end

text \<open>The second theorem assumes that we have a operational semantics,
whose evaluations are written \<open>\<langle>c,s\<rangle> \<Rightarrow> \<langle>c',s'\<rangle>\<close> and which conforms 
to the CFG. The correctness theorem then states that if no high variable
influenced a low variable and the initial states were low equivalent, the
reulting states are again low equivalent:\<close>


locale NonInterferenceInter = 
  NonInterferenceInterGraph sourcenode targetnode kind valid_edge Entry 
    get_proc get_return_edges procs Main Exit Def Use ParamDefs ParamUses 
    H L High Low +
  SemanticsProperty sourcenode targetnode kind valid_edge Entry get_proc
    get_return_edges procs Main Exit Def Use ParamDefs ParamUses sem identifies
  for sourcenode :: "'edge \<Rightarrow> 'node" and targetnode :: "'edge \<Rightarrow> 'node"
  and kind :: "'edge \<Rightarrow> ('var,'val,'ret,'pname) edge_kind" 
  and valid_edge :: "'edge \<Rightarrow> bool"
  and Entry :: "'node" ("'('_Entry'_')")  and get_proc :: "'node \<Rightarrow> 'pname"
  and get_return_edges :: "'edge \<Rightarrow> 'edge set"
  and procs :: "('pname \<times> 'var list \<times> 'var list) list" and Main :: "'pname"
  and Exit::"'node"  ("'('_Exit'_')") 
  and Def :: "'node \<Rightarrow> 'var set" and Use :: "'node \<Rightarrow> 'var set"
  and ParamDefs :: "'node \<Rightarrow> 'var list" and ParamUses :: "'node \<Rightarrow> 'var set list"
  and sem :: "'com \<Rightarrow> ('var \<rightharpoonup> 'val) list \<Rightarrow> 'com \<Rightarrow> ('var \<rightharpoonup> 'val) list \<Rightarrow> bool" 
    ("((1\<langle>_,/_\<rangle>) \<Rightarrow>/ (1\<langle>_,/_\<rangle>))" [0,0,0,0] 81)
  and identifies :: "'node \<Rightarrow> 'com \<Rightarrow> bool" ("_ \<triangleq> _" [51,0] 80)
  and H :: "'var set" and L :: "'var set" 
  and High :: "'node"  ("'('_High'_')") and Low :: "'node" ("'('_Low'_')") +
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
  assumes "[cf\<^sub>1] \<approx>\<^sub>L [cf\<^sub>2]" and "(_High_) \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
  and "CFG_node (_Low_) \<in> S"
  and "valid_edge a" and "sourcenode a = (_High_)" and "targetnode a = n" 
  and "kind a = (\<lambda>s. True)\<^sub>\<surd>" and "n \<triangleq> c" and "final c'"
  and "\<langle>c,[cf\<^sub>1]\<rangle> \<Rightarrow> \<langle>c',s\<^sub>1\<rangle>" and "\<langle>c,[cf\<^sub>2]\<rangle> \<Rightarrow> \<langle>c',s\<^sub>2\<rangle>"
  shows "s\<^sub>1 \<approx>\<^sub>L s\<^sub>2"
proof -
  from High_target_Entry_edge obtain ax where "valid_edge ax"
    and "sourcenode ax = (_Entry_)" and "targetnode ax = (_High_)"
    and "kind ax = (\<lambda>s. True)\<^sub>\<surd>" by blast
  from \<open>n \<triangleq> c\<close> \<open>\<langle>c,[cf\<^sub>1]\<rangle> \<Rightarrow> \<langle>c',s\<^sub>1\<rangle>\<close>
  obtain n\<^sub>1 as\<^sub>1 cfs\<^sub>1 where "n -as\<^sub>1\<rightarrow>\<^sub>\<surd>* n\<^sub>1" and "n\<^sub>1 \<triangleq> c'"
    and "preds (kinds as\<^sub>1) [(cf\<^sub>1,undefined)]" 
    and "transfers (kinds as\<^sub>1) [(cf\<^sub>1,undefined)] = cfs\<^sub>1" and "map fst cfs\<^sub>1 = s\<^sub>1"
    by(fastforce dest:fundamental_property)
  from \<open>n -as\<^sub>1\<rightarrow>\<^sub>\<surd>* n\<^sub>1\<close> \<open>valid_edge a\<close> \<open>sourcenode a = (_High_)\<close> \<open>targetnode a = n\<close>
    \<open>kind a = (\<lambda>s. True)\<^sub>\<surd>\<close>
  have "(_High_) -a#as\<^sub>1\<rightarrow>\<^sub>\<surd>* n\<^sub>1" by(fastforce intro:Cons_path simp:vp_def valid_path_def)
  from \<open>final c'\<close> \<open>n\<^sub>1 \<triangleq> c'\<close>
  obtain a\<^sub>1 where "valid_edge a\<^sub>1" and "sourcenode a\<^sub>1 = n\<^sub>1" 
    and "targetnode a\<^sub>1 = (_Low_)" and "kind a\<^sub>1 = \<Up>id" by(fastforce dest:final_edge_Low)
  hence "n\<^sub>1 -[a\<^sub>1]\<rightarrow>* (_Low_)" by(fastforce intro:path_edge)
  with \<open>(_High_) -a#as\<^sub>1\<rightarrow>\<^sub>\<surd>* n\<^sub>1\<close> have "(_High_) -(a#as\<^sub>1)@[a\<^sub>1]\<rightarrow>* (_Low_)"
    by(fastforce intro!:path_Append simp:vp_def)
  with \<open>valid_edge ax\<close> \<open>sourcenode ax = (_Entry_)\<close> \<open>targetnode ax = (_High_)\<close>
  have "(_Entry_) -ax#((a#as\<^sub>1)@[a\<^sub>1])\<rightarrow>* (_Low_)" by -(rule Cons_path)
  moreover
  from \<open>(_High_) -a#as\<^sub>1\<rightarrow>\<^sub>\<surd>* n\<^sub>1\<close> have "valid_path_aux [] (a#as\<^sub>1)"
    by(simp add:vp_def valid_path_def)
  with \<open>kind a\<^sub>1 = \<Up>id\<close> have "valid_path_aux [] ((a#as\<^sub>1)@[a\<^sub>1])"
    by(fastforce intro:valid_path_aux_Append)
  with \<open>kind ax = (\<lambda>s. True)\<^sub>\<surd>\<close> have "valid_path_aux [] (ax#((a#as\<^sub>1)@[a\<^sub>1]))"
    by simp
  ultimately have "(_Entry_) -ax#((a#as\<^sub>1)@[a\<^sub>1])\<rightarrow>\<^sub>\<surd>* (_Low_)"
    by(simp add:vp_def valid_path_def)
  from \<open>valid_edge a\<close> \<open>kind a = (\<lambda>s. True)\<^sub>\<surd>\<close> \<open>sourcenode a = (_High_)\<close>
    \<open>targetnode a = n\<close>
  have "get_proc n = get_proc (_High_)"
    by(fastforce dest:get_proc_intra simp:intra_kind_def)
  with get_proc_High have "get_proc n = Main" by simp
  from \<open>valid_edge a\<^sub>1\<close> \<open>sourcenode a\<^sub>1 = n\<^sub>1\<close> \<open>targetnode a\<^sub>1 = (_Low_)\<close> \<open>kind a\<^sub>1 = \<Up>id\<close>
  have "get_proc n\<^sub>1 = get_proc (_Low_)"
    by(fastforce dest:get_proc_intra simp:intra_kind_def)
  with get_proc_Low have "get_proc n\<^sub>1 = Main" by simp
  from \<open>n -as\<^sub>1\<rightarrow>\<^sub>\<surd>* n\<^sub>1\<close> have "n -as\<^sub>1\<rightarrow>\<^bsub>sl\<^esub>* n\<^sub>1"
    by(cases as\<^sub>1)
      (auto dest!:vpa_Main_slpa intro:\<open>get_proc n\<^sub>1 = Main\<close> \<open>get_proc n = Main\<close>
             simp:vp_def valid_path_def valid_call_list_def slp_def 
                  same_level_path_def simp del:valid_path_aux.simps)
  then obtain cfx r where cfx:"transfers (map kind as\<^sub>1) [(cf\<^sub>1,undefined)] = [(cfx,r)]"
    by(fastforce elim:slp_callstack_length_equal simp:kinds_def)
  from \<open>kind ax = (\<lambda>s. True)\<^sub>\<surd>\<close> \<open>kind a = (\<lambda>s. True)\<^sub>\<surd>\<close> 
    \<open>preds (kinds as\<^sub>1) [(cf\<^sub>1,undefined)]\<close> \<open>kind a\<^sub>1 = \<Up>id\<close> cfx 
  have "preds (kinds (ax#((a#as\<^sub>1)@[a\<^sub>1]))) [(cf\<^sub>1,undefined)]"
    by(auto simp:kinds_def preds_split)
  from \<open>n \<triangleq> c\<close> \<open>\<langle>c,[cf\<^sub>2]\<rangle> \<Rightarrow> \<langle>c',s\<^sub>2\<rangle>\<close>
  obtain n\<^sub>2 as\<^sub>2 cfs\<^sub>2 where "n -as\<^sub>2\<rightarrow>\<^sub>\<surd>* n\<^sub>2" and "n\<^sub>2 \<triangleq> c'"
    and "preds (kinds as\<^sub>2) [(cf\<^sub>2,undefined)]" 
    and "transfers (kinds as\<^sub>2) [(cf\<^sub>2,undefined)] = cfs\<^sub>2" and "map fst cfs\<^sub>2 = s\<^sub>2"
    by(fastforce dest:fundamental_property)
  from \<open>n -as\<^sub>2\<rightarrow>\<^sub>\<surd>* n\<^sub>2\<close> \<open>valid_edge a\<close> \<open>sourcenode a = (_High_)\<close> \<open>targetnode a = n\<close>
    \<open>kind a = (\<lambda>s. True)\<^sub>\<surd>\<close>
  have "(_High_) -a#as\<^sub>2\<rightarrow>\<^sub>\<surd>* n\<^sub>2" by(fastforce intro:Cons_path simp:vp_def valid_path_def)
  from \<open>final c'\<close> \<open>n\<^sub>2 \<triangleq> c'\<close>
  obtain a\<^sub>2 where "valid_edge a\<^sub>2" and "sourcenode a\<^sub>2 = n\<^sub>2" 
    and "targetnode a\<^sub>2 = (_Low_)" and "kind a\<^sub>2 = \<Up>id" by(fastforce dest:final_edge_Low)
  hence "n\<^sub>2 -[a\<^sub>2]\<rightarrow>* (_Low_)" by(fastforce intro:path_edge)
  with \<open>(_High_) -a#as\<^sub>2\<rightarrow>\<^sub>\<surd>* n\<^sub>2\<close> have "(_High_) -(a#as\<^sub>2)@[a\<^sub>2]\<rightarrow>* (_Low_)"
    by(fastforce intro!:path_Append simp:vp_def)
  with \<open>valid_edge ax\<close> \<open>sourcenode ax = (_Entry_)\<close> \<open>targetnode ax = (_High_)\<close>
  have "(_Entry_) -ax#((a#as\<^sub>2)@[a\<^sub>2])\<rightarrow>* (_Low_)" by -(rule Cons_path)
  moreover
  from \<open>(_High_) -a#as\<^sub>2\<rightarrow>\<^sub>\<surd>* n\<^sub>2\<close> have "valid_path_aux [] (a#as\<^sub>2)"
    by(simp add:vp_def valid_path_def)
  with \<open>kind a\<^sub>2 = \<Up>id\<close> have "valid_path_aux [] ((a#as\<^sub>2)@[a\<^sub>2])"
    by(fastforce intro:valid_path_aux_Append)
  with \<open>kind ax = (\<lambda>s. True)\<^sub>\<surd>\<close> have "valid_path_aux [] (ax#((a#as\<^sub>2)@[a\<^sub>2]))"
    by simp
  ultimately have "(_Entry_) -ax#((a#as\<^sub>2)@[a\<^sub>2])\<rightarrow>\<^sub>\<surd>* (_Low_)"
    by(simp add:vp_def valid_path_def)
  from \<open>valid_edge a\<close> \<open>kind a = (\<lambda>s. True)\<^sub>\<surd>\<close> \<open>sourcenode a = (_High_)\<close>
    \<open>targetnode a = n\<close>
  have "get_proc n = get_proc (_High_)"
    by(fastforce dest:get_proc_intra simp:intra_kind_def)
  with get_proc_High have "get_proc n = Main" by simp
  from \<open>valid_edge a\<^sub>2\<close> \<open>sourcenode a\<^sub>2 = n\<^sub>2\<close> \<open>targetnode a\<^sub>2 = (_Low_)\<close> \<open>kind a\<^sub>2 = \<Up>id\<close>
  have "get_proc n\<^sub>2 = get_proc (_Low_)"
    by(fastforce dest:get_proc_intra simp:intra_kind_def)
  with get_proc_Low have "get_proc n\<^sub>2 = Main" by simp
  from \<open>n -as\<^sub>2\<rightarrow>\<^sub>\<surd>* n\<^sub>2\<close> have "n -as\<^sub>2\<rightarrow>\<^bsub>sl\<^esub>* n\<^sub>2"
    by(cases as\<^sub>2)
      (auto dest!:vpa_Main_slpa intro:\<open>get_proc n\<^sub>2 = Main\<close> \<open>get_proc n = Main\<close>
             simp:vp_def valid_path_def valid_call_list_def slp_def 
                  same_level_path_def simp del:valid_path_aux.simps)
  then obtain cfx' r' 
    where cfx':"transfers (map kind as\<^sub>2) [(cf\<^sub>2,undefined)] = [(cfx',r')]"
    by(fastforce elim:slp_callstack_length_equal simp:kinds_def)
  from \<open>kind ax = (\<lambda>s. True)\<^sub>\<surd>\<close> \<open>kind a = (\<lambda>s. True)\<^sub>\<surd>\<close> 
    \<open>preds (kinds as\<^sub>2) [(cf\<^sub>2,undefined)]\<close> \<open>kind a\<^sub>2 = \<Up>id\<close> cfx' 
  have "preds (kinds (ax#((a#as\<^sub>2)@[a\<^sub>2]))) [(cf\<^sub>2,undefined)]"
    by(auto simp:kinds_def preds_split)
  from \<open>[cf\<^sub>1] \<approx>\<^sub>L [cf\<^sub>2]\<close> \<open>(_High_) \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close> \<open>CFG_node (_Low_) \<in> S\<close>
    \<open>(_Entry_) -ax#((a#as\<^sub>1)@[a\<^sub>1])\<rightarrow>\<^sub>\<surd>* (_Low_)\<close> 
    \<open>preds (kinds (ax#((a#as\<^sub>1)@[a\<^sub>1]))) [(cf\<^sub>1,undefined)]\<close>
    \<open>(_Entry_) -ax#((a#as\<^sub>2)@[a\<^sub>2])\<rightarrow>\<^sub>\<surd>* (_Low_)\<close> 
    \<open>preds (kinds (ax#((a#as\<^sub>2)@[a\<^sub>2]))) [(cf\<^sub>2,undefined)]\<close>
  have "map fst (transfers (kinds (ax#((a#as\<^sub>1)@[a\<^sub>1]))) [(cf\<^sub>1,undefined)]) \<approx>\<^sub>L 
        map fst (transfers (kinds (ax#((a#as\<^sub>2)@[a\<^sub>2]))) [(cf\<^sub>2,undefined)])"
    by(rule nonInterference_path_to_Low)
  with \<open>kind ax = (\<lambda>s. True)\<^sub>\<surd>\<close> \<open>kind a = (\<lambda>s. True)\<^sub>\<surd>\<close> \<open>kind a\<^sub>1 = \<Up>id\<close> \<open>kind a\<^sub>2 = \<Up>id\<close>
    \<open>transfers (kinds as\<^sub>1) [(cf\<^sub>1,undefined)] = cfs\<^sub>1\<close> \<open>map fst cfs\<^sub>1 = s\<^sub>1\<close>
    \<open>transfers (kinds as\<^sub>2) [(cf\<^sub>2,undefined)] = cfs\<^sub>2\<close> \<open>map fst cfs\<^sub>2 = s\<^sub>2\<close>
  show ?thesis by(cases s\<^sub>1)(cases s\<^sub>2,(fastforce simp:kinds_def transfers_split)+)+
qed


end

end

