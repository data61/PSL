theory CFGExit imports CFG begin

subsection \<open>Adds an exit node to the abstract CFG\<close>

locale CFGExit = CFG sourcenode targetnode kind valid_edge Entry 
    get_proc get_return_edges procs Main
  for sourcenode :: "'edge \<Rightarrow> 'node" and targetnode :: "'edge \<Rightarrow> 'node"
  and kind :: "'edge \<Rightarrow> ('var,'val,'ret,'pname) edge_kind" 
  and valid_edge :: "'edge \<Rightarrow> bool"
  and Entry :: "'node" ("'('_Entry'_')")  and get_proc :: "'node \<Rightarrow> 'pname"
  and get_return_edges :: "'edge \<Rightarrow> 'edge set"
  and procs :: "('pname \<times> 'var list \<times> 'var list) list" and Main :: "'pname" +
  fixes Exit::"'node"  ("'('_Exit'_')")
  assumes Exit_source [dest]: "\<lbrakk>valid_edge a; sourcenode a = (_Exit_)\<rbrakk> \<Longrightarrow> False"
  and get_proc_Exit:"get_proc (_Exit_) = Main"
  and Exit_no_return_target:
    "\<lbrakk>valid_edge a; kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f; targetnode a = (_Exit_)\<rbrakk> \<Longrightarrow> False"
  and Entry_Exit_edge: "\<exists>a. valid_edge a \<and> sourcenode a = (_Entry_) \<and>
    targetnode a = (_Exit_) \<and> kind a = (\<lambda>s. False)\<^sub>\<surd>"
  

begin

lemma Entry_noteq_Exit [dest]:
  assumes eq:"(_Entry_) = (_Exit_)" shows "False"
proof -
  from Entry_Exit_edge obtain a where "sourcenode a = (_Entry_)" 
    and "valid_edge a" by blast
  with eq show False by simp(erule Exit_source)
qed

lemma Exit_noteq_Entry [dest]:"(_Exit_) = (_Entry_) \<Longrightarrow> False"
  by(rule Entry_noteq_Exit[OF sym],simp)


lemma [simp]: "valid_node (_Entry_)"
proof -
  from Entry_Exit_edge obtain a where "sourcenode a = (_Entry_)" 
    and "valid_edge a" by blast
  thus ?thesis by(fastforce simp:valid_node_def)
qed

lemma [simp]: "valid_node (_Exit_)"
proof -
  from Entry_Exit_edge obtain a where "targetnode a = (_Exit_)"
    and "valid_edge a" by blast
  thus ?thesis by(fastforce simp:valid_node_def)
qed


subsubsection \<open>Definition of \<open>method_exit\<close>\<close>

definition method_exit :: "'node \<Rightarrow> bool"
  where "method_exit n \<equiv> n = (_Exit_) \<or> 
  (\<exists>a Q p f. n = sourcenode a \<and> valid_edge a \<and> kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f)"


lemma method_exit_cases:
  "\<lbrakk>method_exit n; n = (_Exit_) \<Longrightarrow> P;
    \<And>a Q f p. \<lbrakk>n = sourcenode a; valid_edge a; kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
by(fastforce simp:method_exit_def)


lemma method_exit_inner_path:
  assumes "method_exit n" and "n -as\<rightarrow>\<^sub>\<iota>* n'" shows "as = []"
  using \<open>method_exit n\<close>
proof(rule method_exit_cases)
  assume "n = (_Exit_)"
  show ?thesis
  proof(cases as)
    case (Cons a' as')
    with \<open>n -as\<rightarrow>\<^sub>\<iota>* n'\<close> have "n = sourcenode a'" and "valid_edge a'"
      by(auto elim:path_split_Cons simp:intra_path_def)
    with \<open>n = (_Exit_)\<close> have "sourcenode a' = (_Exit_)" by simp
    with \<open>valid_edge a'\<close> have False by(rule Exit_source)
    thus ?thesis by simp
  qed simp
next
  fix a Q f p
  assume "n = sourcenode a" and "valid_edge a" and "kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f"
  show ?thesis
  proof(cases as)
    case (Cons a' as')
    with \<open>n -as\<rightarrow>\<^sub>\<iota>* n'\<close> have "n = sourcenode a'" and "valid_edge a'" 
      and "intra_kind (kind a')"
      by(auto elim:path_split_Cons simp:intra_path_def)
    from \<open>valid_edge a\<close> \<open>kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f\<close> \<open>valid_edge a'\<close> \<open>n = sourcenode a\<close> 
      \<open>n = sourcenode a'\<close> \<open>intra_kind (kind a')\<close>
    have False by(fastforce dest:return_edges_only simp:intra_kind_def)
    thus ?thesis by simp
  qed simp
qed


subsubsection \<open>Definition of \<open>inner_node\<close>\<close>

definition inner_node :: "'node \<Rightarrow> bool"
  where inner_node_def: 
  "inner_node n \<equiv> valid_node n \<and> n \<noteq> (_Entry_) \<and> n \<noteq> (_Exit_)"


lemma inner_is_valid:
  "inner_node n \<Longrightarrow> valid_node n"
by(simp add:inner_node_def valid_node_def)

lemma [dest]:
  "inner_node (_Entry_) \<Longrightarrow> False"
by(simp add:inner_node_def)

lemma [dest]:
  "inner_node (_Exit_) \<Longrightarrow> False" 
by(simp add:inner_node_def)

lemma [simp]:"\<lbrakk>valid_edge a; targetnode a \<noteq> (_Exit_)\<rbrakk> 
  \<Longrightarrow> inner_node (targetnode a)"
  by(simp add:inner_node_def,rule ccontr,simp,erule Entry_target)

lemma [simp]:"\<lbrakk>valid_edge a; sourcenode a \<noteq> (_Entry_)\<rbrakk>
  \<Longrightarrow> inner_node (sourcenode a)"
  by(simp add:inner_node_def,rule ccontr,simp,erule Exit_source)

lemma valid_node_cases [consumes 1, case_names "Entry" "Exit" "inner"]:
  "\<lbrakk>valid_node n; n = (_Entry_) \<Longrightarrow> Q; n = (_Exit_) \<Longrightarrow> Q;
    inner_node n \<Longrightarrow> Q\<rbrakk> \<Longrightarrow> Q"
apply(auto simp:valid_node_def)
 apply(case_tac "sourcenode a = (_Entry_)") apply auto
apply(case_tac "targetnode a = (_Exit_)") apply auto
done


subsubsection \<open>Lemmas on paths with \<open>(_Exit_)\<close>\<close>

lemma path_Exit_source:
  "\<lbrakk>n -as\<rightarrow>* n'; n = (_Exit_)\<rbrakk> \<Longrightarrow> n' = (_Exit_) \<and> as = []"
proof(induct rule:path.induct)
  case (Cons_path n'' as n' a n)
  from \<open>n = (_Exit_)\<close> \<open>sourcenode a = n\<close> \<open>valid_edge a\<close> have False 
    by -(rule Exit_source,simp_all)
  thus ?case by simp
qed simp

lemma [dest]:"(_Exit_) -as\<rightarrow>* n' \<Longrightarrow> n' = (_Exit_) \<and> as = []"
  by(fastforce elim!:path_Exit_source)

lemma Exit_no_sourcenode[dest]:
  assumes isin:"(_Exit_) \<in> set (sourcenodes as)" and path:"n -as\<rightarrow>* n'"
  shows False
proof -
  from isin obtain ns' ns'' where "sourcenodes as = ns'@(_Exit_)#ns''"
    by(auto dest:split_list simp:sourcenodes_def)
  then obtain as' as'' a where "as = as'@a#as''"
    and source:"sourcenode a = (_Exit_)"
    by(fastforce elim:map_append_append_maps simp:sourcenodes_def)
  with path have "valid_edge a" by(fastforce dest:path_split)
  with source show ?thesis by -(erule Exit_source)
qed



lemma vpa_no_slpa:
  "\<lbrakk>valid_path_aux cs as; n -as\<rightarrow>* n'; valid_call_list cs n; cs \<noteq> [];
    \<forall>xs ys. as = xs@ys \<longrightarrow> (\<not> same_level_path_aux cs xs \<or> upd_cs cs xs \<noteq> [])\<rbrakk>
  \<Longrightarrow> \<exists>a Q r fs. valid_edge a \<and> kind a = Q:r\<hookrightarrow>\<^bsub>get_proc n'\<^esub>fs"
proof(induct arbitrary:n rule:vpa_induct)
  case (vpa_empty cs)
  from \<open>valid_call_list cs n\<close> \<open>cs \<noteq> []\<close> obtain Q r fs where "valid_edge (hd cs)"
    and "kind (hd cs) = Q:r\<hookrightarrow>\<^bsub>get_proc n\<^esub>fs"
    apply(unfold valid_call_list_def)
    apply(drule hd_Cons_tl[THEN sym])
    apply(erule_tac x="[]" in allE) 
    apply(erule_tac x="hd cs" in allE)
    by auto
  from \<open>n -[]\<rightarrow>* n'\<close> have "n = n'" by fastforce
  with \<open>valid_edge (hd cs)\<close> \<open>kind (hd cs) = Q:r\<hookrightarrow>\<^bsub>get_proc n\<^esub>fs\<close> show ?case by blast
next
  case (vpa_intra cs a as)
  note IH = \<open>\<And>n. \<lbrakk>n -as\<rightarrow>* n'; valid_call_list cs n; cs \<noteq> [];
    \<forall>xs ys. as = xs@ys \<longrightarrow> \<not> same_level_path_aux cs xs \<or> upd_cs cs xs \<noteq> []\<rbrakk>
    \<Longrightarrow> \<exists>a' Q' r' fs'. valid_edge a' \<and> kind a' = Q':r'\<hookrightarrow>\<^bsub>get_proc n'\<^esub>fs'\<close>
  note all = \<open>\<forall>xs ys. a#as = xs@ys 
    \<longrightarrow> \<not> same_level_path_aux cs xs \<or> upd_cs cs xs \<noteq> []\<close>
  from \<open>n -a#as\<rightarrow>* n'\<close> have "sourcenode a = n" and "valid_edge a" 
    and "targetnode a -as\<rightarrow>* n'"
    by(auto intro:path_split_Cons)
  from \<open>valid_call_list cs n\<close> \<open>cs \<noteq> []\<close> obtain Q r fs where "valid_edge (hd cs)"
    and "kind (hd cs) = Q:r\<hookrightarrow>\<^bsub>get_proc n\<^esub>fs"
    apply(unfold valid_call_list_def)
    apply(drule hd_Cons_tl[THEN sym])
    apply(erule_tac x="[]" in allE) 
    apply(erule_tac x="hd cs" in allE)
    by auto
  from \<open>valid_edge a\<close> \<open>intra_kind (kind a)\<close>
  have "get_proc (sourcenode a) = get_proc (targetnode a)" by(rule get_proc_intra)
  with \<open>kind (hd cs) = Q:r\<hookrightarrow>\<^bsub>get_proc n\<^esub>fs\<close> \<open>sourcenode a = n\<close>
  have "kind (hd cs) = Q:r\<hookrightarrow>\<^bsub>get_proc (targetnode a)\<^esub>fs" by simp
  from \<open>valid_call_list cs n\<close> \<open>sourcenode a = n\<close>
    \<open>get_proc (sourcenode a) = get_proc (targetnode a)\<close>
  have "valid_call_list cs (targetnode a)"
    apply(clarsimp simp:valid_call_list_def)
    apply(erule_tac x="cs'" in allE)
    apply(erule_tac x="c" in allE)
    by(auto split:list.split)
  from all \<open>intra_kind (kind a)\<close>
  have "\<forall>xs ys. as = xs@ys \<longrightarrow> \<not> same_level_path_aux cs xs \<or> upd_cs cs xs \<noteq> []"
    apply clarsimp apply(erule_tac x="a#xs" in allE)
    by(auto simp:intra_kind_def)
  from IH[OF \<open>targetnode a -as\<rightarrow>* n'\<close> \<open>valid_call_list cs (targetnode a)\<close>
    \<open>cs \<noteq> []\<close> this] show ?case .
next
  case (vpa_Call cs a as Q r p fs)
  note IH = \<open>\<And>n. \<lbrakk>n -as\<rightarrow>* n'; valid_call_list (a#cs) n; a#cs \<noteq> [];
    \<forall>xs ys. as = xs@ys \<longrightarrow> \<not> same_level_path_aux (a#cs) xs \<or> upd_cs (a#cs) xs \<noteq> []\<rbrakk>
    \<Longrightarrow> \<exists>a' Q' r' fs'. valid_edge a' \<and> kind a' = Q':r'\<hookrightarrow>\<^bsub>get_proc n'\<^esub>fs'\<close>
  note all = \<open>\<forall>xs ys.
    a#as = xs@ys \<longrightarrow> \<not> same_level_path_aux cs xs \<or> upd_cs cs xs \<noteq> []\<close>
  from \<open>n -a#as\<rightarrow>* n'\<close> have "sourcenode a = n" and "valid_edge a" 
    and "targetnode a -as\<rightarrow>* n'"
    by(auto intro:path_split_Cons)
  from \<open>valid_edge a\<close> \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close> have "get_proc (targetnode a) = p"
    by(rule get_proc_call)
  with \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close> have "kind a = Q:r\<hookrightarrow>\<^bsub>get_proc (targetnode a)\<^esub>fs" by simp
  with \<open>valid_call_list cs n\<close> \<open>valid_edge a\<close> \<open>sourcenode a = n\<close>
  have "valid_call_list (a#cs) (targetnode a)"
    apply(clarsimp simp:valid_call_list_def)
    apply(case_tac cs') apply auto
    apply(erule_tac x="list" in allE)
    apply(erule_tac x="c" in allE)
    by(auto split:list.split simp:sourcenodes_def)
  from all \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close>
  have "\<forall>xs ys. as = xs@ys 
    \<longrightarrow> \<not> same_level_path_aux (a#cs) xs \<or> upd_cs (a#cs) xs \<noteq> []"
    apply clarsimp apply(erule_tac x="a#xs" in allE)
    by auto
  from IH[OF \<open>targetnode a -as\<rightarrow>* n'\<close> \<open>valid_call_list (a#cs) (targetnode a)\<close>
    _ this] show ?case by simp
next
  case (vpa_ReturnEmpty cs a as Q p fx)
  from \<open>cs \<noteq> []\<close> \<open>cs = []\<close> have False by simp
  thus ?case by simp
next
  case (vpa_ReturnCons cs a as Q p f c' cs')
  note IH = \<open>\<And>n. \<lbrakk>n -as\<rightarrow>* n'; valid_call_list cs' n; cs' \<noteq> [];
    \<forall>xs ys. as = xs@ys \<longrightarrow> \<not> same_level_path_aux cs' xs \<or> upd_cs cs' xs \<noteq> []\<rbrakk>
    \<Longrightarrow> \<exists>a' Q' r' fs'. valid_edge a' \<and> kind a' = Q':r'\<hookrightarrow>\<^bsub>get_proc n'\<^esub>fs'\<close>
  note all = \<open>\<forall>xs ys. a#as = xs@ys 
    \<longrightarrow> \<not> same_level_path_aux cs xs \<or> upd_cs cs xs \<noteq> []\<close>
  from \<open>n -a#as\<rightarrow>* n'\<close> have "sourcenode a = n" and "valid_edge a" 
    and "targetnode a -as\<rightarrow>* n'"
    by(auto intro:path_split_Cons)
  from \<open>valid_call_list cs n\<close> \<open>cs = c'#cs'\<close> have "valid_edge c'"
    apply(clarsimp simp:valid_call_list_def)
    apply(erule_tac x="[]" in allE)
    by auto
  show ?case
  proof(cases "cs' = []")
    case True
    with all \<open>cs = c'#cs'\<close> \<open>kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f\<close> \<open>a \<in> get_return_edges c'\<close> have False
      by(erule_tac x="[a]" in allE,fastforce)
    thus ?thesis by simp
  next
    case False
    with \<open>valid_call_list cs n\<close> \<open>cs = c'#cs'\<close>
    have "valid_call_list cs' (sourcenode c')"
      apply(clarsimp simp:valid_call_list_def)
      apply(hypsubst_thin)
      apply(erule_tac x="c'#cs'" in allE)
      apply(auto simp:sourcenodes_def)
       apply(case_tac cs') apply auto
      apply(case_tac list) apply(auto simp:sourcenodes_def)
      done
    from \<open>valid_edge c'\<close> \<open>a \<in> get_return_edges c'\<close>
    have "get_proc (sourcenode c') = get_proc (targetnode a)"
      by(rule get_proc_get_return_edge)
    with \<open>valid_call_list cs' (sourcenode c')\<close>
    have "valid_call_list cs' (targetnode a)"
      apply(clarsimp simp:valid_call_list_def)
      apply(hypsubst_thin)
    apply(erule_tac x="cs'" in allE)
    apply(erule_tac x="c" in allE)
    by(auto split:list.split)
    from all \<open>kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f\<close> \<open>cs = c'#cs'\<close> \<open>a \<in> get_return_edges c'\<close>
    have "\<forall>xs ys. as = xs@ys \<longrightarrow> \<not> same_level_path_aux cs' xs \<or> upd_cs cs' xs \<noteq> []"
      apply clarsimp apply(erule_tac x="a#xs" in allE)
      by auto  
    from IH[OF \<open>targetnode a -as\<rightarrow>* n'\<close> \<open>valid_call_list cs' (targetnode a)\<close>
      False this] show ?thesis .
  qed
qed


lemma valid_Exit_path_cases:
  assumes "n -as\<rightarrow>\<^sub>\<surd>* (_Exit_)" and "as \<noteq> []"
  shows "(\<exists>a' as'. as = a'#as' \<and> intra_kind(kind a')) \<or>
         (\<exists>a' as' Q p f. as = a'#as' \<and> kind a' = Q\<hookleftarrow>\<^bsub>p\<^esub>f) \<or>
         (\<exists>as' as'' n'. as = as'@as'' \<and> as' \<noteq> [] \<and> n -as'\<rightarrow>\<^bsub>sl\<^esub>* n')"
proof -
  from \<open>as \<noteq> []\<close> obtain a' as' where "as = a'#as'" by(cases as) auto
  thus ?thesis
  proof(cases "kind a'" rule:edge_kind_cases)
    case Intra with \<open>as = a'#as'\<close> show ?thesis by simp
  next
    case Return with \<open>as = a'#as'\<close> show ?thesis by simp
  next
    case (Call Q r p f)
    from \<open>n -as\<rightarrow>\<^sub>\<surd>* (_Exit_)\<close> have "n -as\<rightarrow>* (_Exit_)" and "valid_path_aux [] as"
      by(simp_all add:vp_def valid_path_def)
    from \<open>n -as\<rightarrow>* (_Exit_)\<close> \<open>as = a'#as'\<close>
    have "sourcenode a' = n" and "valid_edge a'" and "targetnode a' -as'\<rightarrow>* (_Exit_)"
      by(auto intro:path_split_Cons)
    from \<open>valid_path_aux [] as\<close> \<open>as = a'#as'\<close> Call
    have "valid_path_aux [a'] as'" by simp
    from \<open>valid_edge a'\<close> Call
    have "valid_call_list [a'] (targetnode a')"
      apply(clarsimp simp:valid_call_list_def)
      apply(case_tac cs') 
      by(auto intro:get_proc_call[THEN sym])
    show ?thesis
    proof(cases "\<forall>xs ys. as' = xs@ys \<longrightarrow> 
        (\<not> same_level_path_aux [a'] xs \<or> upd_cs [a'] xs \<noteq> [])")
      case True
      with \<open>valid_path_aux [a'] as'\<close> \<open>targetnode a' -as'\<rightarrow>* (_Exit_)\<close>
        \<open>valid_call_list [a'] (targetnode a')\<close>
      obtain ax Qx rx fsx where "valid_edge ax" and "kind ax = Qx:rx\<hookrightarrow>\<^bsub>get_proc (_Exit_)\<^esub>fsx"
        by(fastforce dest!:vpa_no_slpa)
      hence False by(fastforce intro:Main_no_call_target simp:get_proc_Exit)
      thus ?thesis by simp
    next
      case False
      then obtain xs ys where "as' = xs@ys" and "same_level_path_aux [a'] xs"
        and "upd_cs [a'] xs = []" by auto
      with Call have "same_level_path (a'#xs)" by(simp add:same_level_path_def)
      from \<open>upd_cs [a'] xs = []\<close> have "xs \<noteq> []" by auto
      with \<open>targetnode a' -as'\<rightarrow>* (_Exit_)\<close> \<open>as' = xs@ys\<close>
      have "targetnode a' -xs\<rightarrow>* last(targetnodes xs)"
        apply(cases xs rule:rev_cases)
        by(auto intro:path_Append path_split path_edge simp:targetnodes_def)
      with \<open>sourcenode a' = n\<close> \<open>valid_edge a'\<close> \<open>same_level_path (a'#xs)\<close>
      have "n -a'#xs\<rightarrow>\<^bsub>sl\<^esub>* last(targetnodes xs)"
        by(fastforce intro:Cons_path simp:slp_def)
      with \<open>as = a'#as'\<close> \<open>as' = xs@ys\<close> Call 
      have "\<exists>as' as'' n'. as = as'@as'' \<and> as' \<noteq> [] \<and> n -as'\<rightarrow>\<^bsub>sl\<^esub>* n'"
        by(rule_tac x="a'#xs" in exI) auto
      thus ?thesis by simp
    qed
  qed
qed


lemma valid_Exit_path_descending_path:
  assumes "n -as\<rightarrow>\<^sub>\<surd>* (_Exit_)"
  obtains as' where "n -as'\<rightarrow>\<^sub>\<surd>* (_Exit_)" 
  and "set(sourcenodes as') \<subseteq> set(sourcenodes as)"
  and "\<forall>a' \<in> set as'. intra_kind(kind a') \<or> (\<exists>Q f p. kind a' = Q\<hookleftarrow>\<^bsub>p\<^esub>f)"
proof(atomize_elim)
  from \<open>n -as\<rightarrow>\<^sub>\<surd>* (_Exit_)\<close>
  show "\<exists>as'. n -as'\<rightarrow>\<^sub>\<surd>* (_Exit_) \<and> set(sourcenodes as') \<subseteq> set(sourcenodes as)\<and>
              (\<forall>a' \<in> set as'. intra_kind(kind a') \<or> (\<exists>Q f p. kind a' = Q\<hookleftarrow>\<^bsub>p\<^esub>f))"
  proof(induct as arbitrary:n rule:length_induct)
    fix as n
    assume IH:"\<forall>as''. length as'' < length as \<longrightarrow>
      (\<forall>n'. n' -as''\<rightarrow>\<^sub>\<surd>* (_Exit_) \<longrightarrow>
       (\<exists>as'. n' -as'\<rightarrow>\<^sub>\<surd>* (_Exit_) \<and> set (sourcenodes as') \<subseteq> set (sourcenodes as'') \<and>
              (\<forall>a'\<in>set as'. intra_kind (kind a') \<or> (\<exists>Q f p. kind a' = Q\<hookleftarrow>\<^bsub>p\<^esub>f))))"
      and "n -as\<rightarrow>\<^sub>\<surd>* (_Exit_)"
    show "\<exists>as'. n -as'\<rightarrow>\<^sub>\<surd>* (_Exit_) \<and> set(sourcenodes as') \<subseteq> set(sourcenodes as)\<and>
              (\<forall>a' \<in> set as'. intra_kind(kind a') \<or> (\<exists>Q f p. kind a' = Q\<hookleftarrow>\<^bsub>p\<^esub>f))"
    proof(cases "as = []")
      case True
      with \<open>n -as\<rightarrow>\<^sub>\<surd>* (_Exit_)\<close> show ?thesis by(fastforce simp:sourcenodes_def vp_def)
    next
      case False
      with \<open>n -as\<rightarrow>\<^sub>\<surd>* (_Exit_)\<close>
      have "((\<exists>a' as'. as = a'#as' \<and> intra_kind(kind a')) \<or>
         (\<exists>a' as' Q p f. as = a'#as' \<and> kind a' = Q\<hookleftarrow>\<^bsub>p\<^esub>f)) \<or>
         (\<exists>as' as'' n'. as = as'@as'' \<and> as' \<noteq> [] \<and> n -as'\<rightarrow>\<^bsub>sl\<^esub>* n')"
        by(auto dest!:valid_Exit_path_cases)
      thus ?thesis apply -
      proof(erule disjE)+
        assume "\<exists>a' as'. as = a'#as' \<and> intra_kind(kind a')"
        then obtain a' as' where "as = a'#as'" and "intra_kind(kind a')" by blast
        from \<open>n -as\<rightarrow>\<^sub>\<surd>* (_Exit_)\<close> \<open>as = a'#as'\<close>
        have "sourcenode a' = n" and "valid_edge a'" 
          and "targetnode a' -as'\<rightarrow>\<^sub>\<surd>* (_Exit_)"
          by(auto intro:vp_split_Cons)
        from \<open>valid_edge a'\<close> \<open>intra_kind(kind a')\<close>
        have "sourcenode a' -[a']\<rightarrow>\<^bsub>sl\<^esub>* targetnode a'"
          by(fastforce intro:path_edge intras_same_level_path simp:slp_def)
        from IH \<open>targetnode a' -as'\<rightarrow>\<^sub>\<surd>* (_Exit_)\<close> \<open>as = a'#as'\<close>
        obtain xs where "targetnode a' -xs\<rightarrow>\<^sub>\<surd>* (_Exit_)" 
          and "set (sourcenodes xs) \<subseteq> set (sourcenodes as')"
          and "\<forall>a'\<in>set xs. intra_kind (kind a') \<or> (\<exists>Q f p. kind a' = Q\<hookleftarrow>\<^bsub>p\<^esub>f)"
          apply(erule_tac x="as'" in allE) by auto
        from \<open>sourcenode a' -[a']\<rightarrow>\<^bsub>sl\<^esub>* targetnode a'\<close> \<open>targetnode a' -xs\<rightarrow>\<^sub>\<surd>* (_Exit_)\<close>
        have "sourcenode a' -[a']@xs\<rightarrow>\<^sub>\<surd>* (_Exit_)" by(rule slp_vp_Append)
        with \<open>sourcenode a' = n\<close> have "n -a'#xs\<rightarrow>\<^sub>\<surd>* (_Exit_)" by simp
        moreover
        from \<open>set (sourcenodes xs) \<subseteq> set (sourcenodes as')\<close> \<open>as = a'#as'\<close>
        have "set (sourcenodes (a'#xs)) \<subseteq> set (sourcenodes as)"
          by(auto simp:sourcenodes_def)
        moreover
        from \<open>\<forall>a'\<in>set xs. intra_kind (kind a') \<or> (\<exists>Q f p. kind a' = Q\<hookleftarrow>\<^bsub>p\<^esub>f)\<close> 
          \<open>intra_kind(kind a')\<close>
        have "\<forall>a'\<in>set (a'#xs). intra_kind (kind a') \<or> (\<exists>Q f p. kind a' = Q\<hookleftarrow>\<^bsub>p\<^esub>f)"
          by fastforce
        ultimately show ?thesis by blast
      next
        assume "\<exists>a' as' Q p f. as = a'#as' \<and> kind a' = Q\<hookleftarrow>\<^bsub>p\<^esub>f"
        then obtain a' as' Q p f where "as = a'#as'" and "kind a' = Q\<hookleftarrow>\<^bsub>p\<^esub>f" by blast
        from \<open>n -as\<rightarrow>\<^sub>\<surd>* (_Exit_)\<close> \<open>as = a'#as'\<close>
        have "sourcenode a' = n" and "valid_edge a'" 
          and "targetnode a' -as'\<rightarrow>\<^sub>\<surd>* (_Exit_)"
          by(auto intro:vp_split_Cons)
        from IH \<open>targetnode a' -as'\<rightarrow>\<^sub>\<surd>* (_Exit_)\<close> \<open>as = a'#as'\<close>
        obtain xs where "targetnode a' -xs\<rightarrow>\<^sub>\<surd>* (_Exit_)" 
          and "set (sourcenodes xs) \<subseteq> set (sourcenodes as')"
          and "\<forall>a'\<in>set xs. intra_kind (kind a') \<or> (\<exists>Q f p. kind a' = Q\<hookleftarrow>\<^bsub>p\<^esub>f)"
          apply(erule_tac x="as'" in allE) by auto
        from \<open>sourcenode a' = n\<close> \<open>valid_edge a'\<close> \<open>kind a' = Q\<hookleftarrow>\<^bsub>p\<^esub>f\<close>
          \<open>targetnode a' -xs\<rightarrow>\<^sub>\<surd>* (_Exit_)\<close>
        have "n -a'#xs\<rightarrow>\<^sub>\<surd>* (_Exit_)"
          by(fastforce intro:Cons_path simp:vp_def valid_path_def)
        moreover
        from \<open>set (sourcenodes xs) \<subseteq> set (sourcenodes as')\<close> \<open>as = a'#as'\<close>
        have "set (sourcenodes (a'#xs)) \<subseteq> set (sourcenodes as)"
          by(auto simp:sourcenodes_def)
        moreover
        from \<open>\<forall>a'\<in>set xs. intra_kind (kind a') \<or> (\<exists>Q f p. kind a' = Q\<hookleftarrow>\<^bsub>p\<^esub>f)\<close> 
          \<open>kind a' = Q\<hookleftarrow>\<^bsub>p\<^esub>f\<close>
        have "\<forall>a'\<in>set (a'#xs). intra_kind (kind a') \<or> (\<exists>Q f p. kind a' = Q\<hookleftarrow>\<^bsub>p\<^esub>f)"
          by fastforce
        ultimately show ?thesis by blast
      next
        assume "\<exists>as' as'' n'. as = as'@as'' \<and> as' \<noteq> [] \<and> n -as'\<rightarrow>\<^bsub>sl\<^esub>* n'"
        then obtain as' as'' n' where "as = as'@as''" and "as' \<noteq> []"
          and "n -as'\<rightarrow>\<^bsub>sl\<^esub>* n'" by blast
        from \<open>n -as\<rightarrow>\<^sub>\<surd>* (_Exit_)\<close> \<open>as = as'@as''\<close> \<open>as' \<noteq> []\<close>
        have "last(targetnodes as') -as''\<rightarrow>\<^sub>\<surd>* (_Exit_)"
          by(cases as' rule:rev_cases,auto intro:vp_split simp:targetnodes_def)
        from \<open>n -as'\<rightarrow>\<^bsub>sl\<^esub>* n'\<close> \<open>as' \<noteq> []\<close> have "last(targetnodes as') = n'"
          by(fastforce intro:path_targetnode simp:slp_def)
        from \<open>as = as'@as''\<close> \<open>as' \<noteq> []\<close> have "length as'' < length as" by simp
        with IH \<open>last(targetnodes as') -as''\<rightarrow>\<^sub>\<surd>* (_Exit_)\<close>
          \<open>last(targetnodes as') = n'\<close>
        obtain xs where "n' -xs\<rightarrow>\<^sub>\<surd>* (_Exit_)" 
          and "set (sourcenodes xs) \<subseteq> set (sourcenodes as'')"
          and "\<forall>a'\<in>set xs. intra_kind (kind a') \<or> (\<exists>Q f p. kind a' = Q\<hookleftarrow>\<^bsub>p\<^esub>f)"
          apply(erule_tac x="as''" in allE) by auto
        from \<open>n -as'\<rightarrow>\<^bsub>sl\<^esub>* n'\<close> obtain ys where "n -ys\<rightarrow>\<^sub>\<iota>* n'"
          and "set(sourcenodes ys) \<subseteq> set(sourcenodes as')"
          by(erule same_level_path_inner_path)
        from \<open>n -ys\<rightarrow>\<^sub>\<iota>* n'\<close> \<open>n' -xs\<rightarrow>\<^sub>\<surd>* (_Exit_)\<close> have "n -ys@xs\<rightarrow>\<^sub>\<surd>* (_Exit_)"
          by(fastforce intro:slp_vp_Append intra_path_slp)
        moreover
        from \<open>set (sourcenodes xs) \<subseteq> set (sourcenodes as'')\<close>
          \<open>set(sourcenodes ys) \<subseteq> set(sourcenodes as')\<close> \<open>as = as'@as''\<close>
        have "set (sourcenodes (ys@xs)) \<subseteq> set(sourcenodes as)"
          by(auto simp:sourcenodes_def)
        moreover
        from \<open>\<forall>a'\<in>set xs. intra_kind (kind a') \<or> (\<exists>Q f p. kind a' = Q\<hookleftarrow>\<^bsub>p\<^esub>f)\<close>
          \<open>n -ys\<rightarrow>\<^sub>\<iota>* n'\<close>
        have "\<forall>a'\<in>set (ys@xs). intra_kind (kind a') \<or> (\<exists>Q f p. kind a' = Q\<hookleftarrow>\<^bsub>p\<^esub>f)"
          by(fastforce simp:intra_path_def)
        ultimately show ?thesis by blast
      qed
    qed
  qed
qed


lemma valid_Exit_path_intra_path:
  assumes "n -as\<rightarrow>\<^sub>\<surd>* (_Exit_)" 
  obtains as' pex where "n -as'\<rightarrow>\<^sub>\<iota>* pex" and "method_exit pex" 
  and "set(sourcenodes as') \<subseteq> set(sourcenodes as)"
proof(atomize_elim)
  from \<open>n -as\<rightarrow>\<^sub>\<surd>* (_Exit_)\<close>
  obtain as' where "n -as'\<rightarrow>\<^sub>\<surd>* (_Exit_)" 
    and "set(sourcenodes as') \<subseteq> set(sourcenodes as)"
    and all:"\<forall>a' \<in> set as'. intra_kind(kind a') \<or> (\<exists>Q f p. kind a' = Q\<hookleftarrow>\<^bsub>p\<^esub>f)"
    by(erule valid_Exit_path_descending_path)
  show "\<exists>as' pex. n -as'\<rightarrow>\<^sub>\<iota>* pex \<and> method_exit pex \<and> 
                  set(sourcenodes as') \<subseteq> set(sourcenodes as)"
  proof(cases "\<exists>a' \<in> set as'. \<exists>Q f p. kind a' = Q\<hookleftarrow>\<^bsub>p\<^esub>f")
    case True
    then obtain asx ax asx' where [simp]:"as' = asx@ax#asx'" 
      and "\<exists>Q f p. kind ax = Q\<hookleftarrow>\<^bsub>p\<^esub>f" and "\<forall>a' \<in> set asx. \<not> (\<exists>Q f p. kind a' = Q\<hookleftarrow>\<^bsub>p\<^esub>f)"
      by(erule split_list_first_propE)
    with all have "\<forall>a' \<in> set asx. intra_kind(kind a')" by auto
    from \<open>n -as'\<rightarrow>\<^sub>\<surd>* (_Exit_)\<close> have "n -asx\<rightarrow>* sourcenode ax"
      and "valid_edge ax" by(auto elim:path_split simp:vp_def)
    from \<open>n -asx\<rightarrow>* sourcenode ax\<close> \<open>\<forall>a' \<in> set asx. intra_kind(kind a')\<close>
    have "n -asx\<rightarrow>\<^sub>\<iota>* sourcenode ax" by(simp add:intra_path_def)
    moreover
    from \<open>valid_edge ax\<close> \<open>\<exists>Q f p. kind ax = Q\<hookleftarrow>\<^bsub>p\<^esub>f\<close>
    have "method_exit (sourcenode ax)" by(fastforce simp:method_exit_def)
    moreover
    from \<open>set(sourcenodes as') \<subseteq> set(sourcenodes as)\<close>
    have "set(sourcenodes asx) \<subseteq> set(sourcenodes as)" by(simp add:sourcenodes_def)
    ultimately show ?thesis by blast
  next
    case False
    with all \<open>n -as'\<rightarrow>\<^sub>\<surd>* (_Exit_)\<close> have "n -as'\<rightarrow>\<^sub>\<iota>* (_Exit_)" 
      by(fastforce simp:vp_def intra_path_def)
    moreover have "method_exit (_Exit_)" by(simp add:method_exit_def)
    ultimately show ?thesis using \<open>set(sourcenodes as') \<subseteq> set(sourcenodes as)\<close>
      by blast
  qed
qed



end 

end
