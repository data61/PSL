section \<open>Dependent Live Variables\<close>

theory DependentLiveVariables imports DynPDG begin

text \<open>\<open>dependent_live_vars\<close> calculates variables which
  can change\\ the value of the @{term Use} variables of the target node\<close>

context DynPDG begin

inductive_set
  dependent_live_vars :: "'node \<Rightarrow> ('var \<times> 'edge list \<times> 'edge list) set"
  for n' :: "'node"
  where dep_vars_Use: 
  "V \<in> Use n' \<Longrightarrow> (V,[],[]) \<in> dependent_live_vars n'"

  | dep_vars_Cons_cdep:
  "\<lbrakk>V \<in> Use (sourcenode a); sourcenode a -a#as'\<rightarrow>\<^sub>c\<^sub>d n''; n'' -as''\<rightarrow>\<^sub>d* n'\<rbrakk>
  \<Longrightarrow> (V,[],a#as'@as'') \<in> dependent_live_vars n'"

  | dep_vars_Cons_ddep:
  "\<lbrakk>(V,as',as) \<in> dependent_live_vars n'; V' \<in> Use (sourcenode a);
    n' = last(targetnodes (a#as));
    sourcenode a -{V}a#as'\<rightarrow>\<^sub>d\<^sub>d last(targetnodes (a#as'))\<rbrakk>
  \<Longrightarrow> (V',[],a#as) \<in> dependent_live_vars n'"

  | dep_vars_Cons_keep:
  "\<lbrakk>(V,as',as) \<in> dependent_live_vars n'; n' = last(targetnodes (a#as));
     \<not> sourcenode a -{V}a#as'\<rightarrow>\<^sub>d\<^sub>d last(targetnodes (a#as'))\<rbrakk>
  \<Longrightarrow> (V,a#as',a#as) \<in> dependent_live_vars n'"



lemma dependent_live_vars_fst_prefix_snd:
  "(V,as',as) \<in> dependent_live_vars n' \<Longrightarrow> \<exists>as''. as'@as'' = as"
by(induct rule:dependent_live_vars.induct,simp_all)


lemma dependent_live_vars_Exit_empty [dest]:
  "(V,as',as) \<in> dependent_live_vars (_Exit_) \<Longrightarrow> False"
proof(induct rule:dependent_live_vars.induct)
  case (dep_vars_Cons_cdep V a as' n'' as'')
  from \<open>n'' -as''\<rightarrow>\<^sub>d* (_Exit_)\<close> have "n'' = (_Exit_)"
    by(fastforce intro:DynPDG_path_Exit)
  with \<open>sourcenode a -a#as'\<rightarrow>\<^sub>c\<^sub>d n''\<close> have "sourcenode a -a#as'\<rightarrow>\<^sub>d* (_Exit_)"
    by(fastforce intro:DynPDG_path_cdep)
  hence "sourcenode a = (_Exit_)" by(fastforce intro:DynPDG_path_Exit)
  with \<open>V \<in> Use (sourcenode a)\<close> show False by simp(erule Exit_Use_empty)
qed auto


lemma dependent_live_vars_lastnode:
  "\<lbrakk>(V,as',as) \<in> dependent_live_vars n'; as \<noteq> []\<rbrakk> 
  \<Longrightarrow> n' = last(targetnodes as)"
proof(induct rule:dependent_live_vars.induct)
  case (dep_vars_Cons_cdep V a as' n'' as'')
  from \<open>sourcenode a -a#as'\<rightarrow>\<^sub>c\<^sub>d n''\<close> have "sourcenode a -a#as'\<rightarrow>* n''"
    by(rule DynPDG_cdep_edge_CFG_path(1))
  from \<open>n'' -as''\<rightarrow>\<^sub>d* n'\<close> have "n'' -as''\<rightarrow>* n'" by(rule DynPDG_path_CFG_path)
  show ?case
  proof(cases "as'' = []")
    case True
    with \<open>n'' -as''\<rightarrow>* n'\<close> have "n'' = n'" by (auto elim: DynPDG.dependent_live_vars.cases)
    with \<open>sourcenode a -a#as'\<rightarrow>* n''\<close> True
    show ?thesis by(fastforce intro:path_targetnode[THEN sym])
  next
    case False
    with \<open>n'' -as''\<rightarrow>* n'\<close> have "n' = last(targetnodes as'')"
      by(fastforce intro:path_targetnode[THEN sym])
    with False show ?thesis by(fastforce simp:targetnodes_def)
  qed
qed simp_all


lemma dependent_live_vars_Use_cases:
  "\<lbrakk>(V,as',as) \<in> dependent_live_vars n'; n -as\<rightarrow>* n'\<rbrakk>
  \<Longrightarrow> \<exists>nx as''. as = as'@as'' \<and> n -as'\<rightarrow>* nx \<and> nx -as''\<rightarrow>\<^sub>d* n' \<and> V \<in> Use nx \<and> 
               (\<forall>n'' \<in> set (sourcenodes as'). V \<notin> Def n'')"
proof(induct arbitrary:n rule:dependent_live_vars.induct)
  case (dep_vars_Use V)
  from \<open>n -[]\<rightarrow>* n'\<close> have "valid_node n'" by(rule path_valid_node(2))
  hence "n' -[]\<rightarrow>\<^sub>d* n'" by(rule DynPDG_path_Nil)
  with \<open>V \<in> Use n'\<close> \<open>n -[]\<rightarrow>* n'\<close> show ?case 
    by(auto simp:sourcenodes_def)
next
  case (dep_vars_Cons_cdep V a as' n'' as'' n)
  from \<open>n -a#as'@as''\<rightarrow>* n'\<close> have "sourcenode a = n"
    by(auto elim:path.cases)
  from \<open>sourcenode a -a#as'\<rightarrow>\<^sub>c\<^sub>d n''\<close> have "sourcenode a -a#as'\<rightarrow>* n''"
    by(rule DynPDG_cdep_edge_CFG_path(1))
  hence "valid_edge a" by(auto elim:path.cases) 
  hence "sourcenode a -[]\<rightarrow>* sourcenode a" by(fastforce intro:empty_path)
  from \<open>sourcenode a -a#as'\<rightarrow>\<^sub>c\<^sub>d n''\<close> have "sourcenode a -a#as'\<rightarrow>\<^sub>d* n''"
    by(rule DynPDG_path_cdep)
  with \<open>n'' -as''\<rightarrow>\<^sub>d* n'\<close> have "sourcenode a -(a#as')@as''\<rightarrow>\<^sub>d* n'"
    by(rule DynPDG_path_Append)
  with \<open>sourcenode a -[]\<rightarrow>* sourcenode a\<close> \<open>V \<in> Use (sourcenode a)\<close> \<open>sourcenode a = n\<close>
  show ?case by(auto simp:sourcenodes_def)
next
  case(dep_vars_Cons_ddep V as' as V' a n)
  note ddep = \<open>sourcenode a -{V}a#as'\<rightarrow>\<^sub>d\<^sub>d last (targetnodes (a#as'))\<close>
  note IH = \<open>\<And>n. n -as\<rightarrow>* n'
    \<Longrightarrow> \<exists>nx as''. as = as'@as'' \<and> n -as'\<rightarrow>* nx \<and> nx -as''\<rightarrow>\<^sub>d* n' \<and> 
                   V \<in> Use nx \<and> (\<forall>n''\<in>set (sourcenodes as'). V \<notin> Def n'')\<close>
  from \<open>n -a#as\<rightarrow>* n'\<close> have "n -[]@a#as\<rightarrow>* n'" by simp
  hence "n = sourcenode a" and "targetnode a -as\<rightarrow>* n'" and "valid_edge a"
    by(fastforce dest:path_split)+
  hence "n -[]\<rightarrow>* n" 
    by(fastforce intro:empty_path simp:valid_node_def)
  from IH[OF \<open>targetnode a -as\<rightarrow>* n'\<close>]
  have "\<exists>nx as''. as = as'@as'' \<and> targetnode a -as'\<rightarrow>* nx \<and> nx -as''\<rightarrow>\<^sub>d* n' \<and> 
                  V \<in> Use nx \<and> (\<forall>n''\<in>set (sourcenodes as'). V \<notin> Def n'')" .
  then obtain nx'' as'' where "targetnode a -as'\<rightarrow>* nx''"
    and "nx'' -as''\<rightarrow>\<^sub>d* n'" and "as = as'@as''" by blast
  have "last (targetnodes (a#as')) -as''\<rightarrow>\<^sub>d* n'"
  proof(cases as')
    case Nil
    with \<open>targetnode a -as'\<rightarrow>* nx''\<close> have "nx'' = targetnode a"
      by(auto elim:path.cases)
    with \<open>nx'' -as''\<rightarrow>\<^sub>d* n'\<close> Nil show ?thesis by(simp add:targetnodes_def)
  next
    case (Cons ax asx)
    hence "last (targetnodes (a#as')) = last (targetnodes as')"
      by(simp add:targetnodes_def)
    from Cons \<open>targetnode a -as'\<rightarrow>* nx''\<close> have "last (targetnodes as') = nx''"
      by(fastforce intro:path_targetnode)
    with \<open>last (targetnodes (a#as')) = last (targetnodes as')\<close> \<open>nx'' -as''\<rightarrow>\<^sub>d* n'\<close>
    show ?thesis by simp
  qed
  with ddep \<open>as = as'@as''\<close> have "sourcenode a -a#as\<rightarrow>\<^sub>d* n'"
    by(fastforce dest:DynPDG_path_ddep DynPDG_path_Append)
  with \<open>V' \<in> Use (sourcenode a)\<close> \<open>n = sourcenode a\<close> \<open>n -[]\<rightarrow>* n\<close>
  show ?case by(auto simp:sourcenodes_def)
next
  case (dep_vars_Cons_keep V as' as a n)
  note no_dep = \<open>\<not> sourcenode a -{V}a#as'\<rightarrow>\<^sub>d\<^sub>d last (targetnodes (a#as'))\<close>
  note IH = \<open>\<And>n. n -as\<rightarrow>* n'
    \<Longrightarrow> \<exists>nx as''. (as = as'@as'') \<and> (n -as'\<rightarrow>* nx) \<and> (nx -as''\<rightarrow>\<^sub>d* n') \<and> 
                   V \<in> Use nx \<and> (\<forall>n''\<in>set (sourcenodes as'). V \<notin> Def n'')\<close>
  from \<open>n -a#as\<rightarrow>* n'\<close> have "n = sourcenode a" and "valid_edge a"
    and "targetnode a -as\<rightarrow>* n'" by(auto elim:path_split_Cons)
  from IH[OF \<open>targetnode a -as\<rightarrow>* n'\<close>]
  have "\<exists>nx as''. as = as'@as'' \<and> targetnode a -as'\<rightarrow>* nx \<and> nx -as''\<rightarrow>\<^sub>d* n' \<and> 
               V \<in> Use nx \<and> (\<forall>n''\<in>set (sourcenodes as'). V \<notin> Def n'')" .
  then obtain nx'' as'' where "V \<in> Use nx''"
    and "\<forall>n''\<in>set (sourcenodes as'). V \<notin> Def n''" and "targetnode a -as'\<rightarrow>* nx''"
    and "nx'' -as''\<rightarrow>\<^sub>d* n'" and "as = as'@as''" by blast
  from \<open>valid_edge a\<close> \<open>targetnode a -as'\<rightarrow>* nx''\<close> have "sourcenode a -a#as'\<rightarrow>* nx''"
    by(fastforce intro:Cons_path)
  hence "last(targetnodes (a#as')) = nx''" by(fastforce dest:path_targetnode)
  { assume "V \<in> Def (sourcenode a)"
    with \<open>V \<in> Use nx''\<close> \<open>sourcenode a -a#as'\<rightarrow>* nx''\<close>
      \<open>\<forall>n''\<in>set (sourcenodes as'). V \<notin> Def n''\<close> 
    have "(sourcenode a) influences V in nx'' via a#as'"
      by(simp add:dyn_data_dependence_def sourcenodes_def)
    with no_dep \<open>last(targetnodes (a#as')) = nx''\<close>
      \<open>\<forall>n''\<in>set (sourcenodes as'). V \<notin> Def n''\<close> \<open>V \<in> Def (sourcenode a)\<close>
    have False by(fastforce dest:DynPDG_ddep_edge) }
  with \<open>\<forall>n''\<in>set (sourcenodes as'). V \<notin> Def n''\<close> 
  have "\<forall>n''\<in>set (sourcenodes (a#as')). V \<notin> Def n''"
    by(fastforce simp:sourcenodes_def)
  with \<open>V \<in> Use nx''\<close> \<open>sourcenode a -a#as'\<rightarrow>* nx''\<close> \<open>nx'' -as''\<rightarrow>\<^sub>d* n'\<close>
    \<open>as = as'@as''\<close> \<open>n = sourcenode a\<close> show ?case by fastforce
qed


lemma dependent_live_vars_dependent_edge:
  assumes "(V,as',as) \<in> dependent_live_vars n'" 
  and "targetnode a -as\<rightarrow>* n'"
  and "V \<in> Def (sourcenode a)" and "valid_edge a"
  obtains nx as'' where "as = as'@as''" and "sourcenode a -{V}a#as'\<rightarrow>\<^sub>d\<^sub>d nx"
  and "nx -as''\<rightarrow>\<^sub>d* n'"
proof(atomize_elim)
  from \<open>(V,as',as) \<in> dependent_live_vars n'\<close> \<open>targetnode a -as\<rightarrow>* n'\<close>
  have "\<exists>nx as''. as = as'@as'' \<and> targetnode a -as'\<rightarrow>* nx \<and> nx -as''\<rightarrow>\<^sub>d* n' \<and> 
    V \<in> Use nx \<and> (\<forall>n'' \<in> set (sourcenodes as'). V \<notin> Def n'')"
    by(rule dependent_live_vars_Use_cases)
  then obtain nx as'' where "V \<in> Use nx"
    and "\<forall>n''\<in> set(sourcenodes as'). V \<notin> Def n''"
    and "targetnode a -as'\<rightarrow>* nx" and "nx -as''\<rightarrow>\<^sub>d* n'"
    and "as = as'@as''" by blast
  from \<open>targetnode a -as'\<rightarrow>* nx\<close> \<open>valid_edge a\<close> have "sourcenode a -a#as'\<rightarrow>* nx"
    by(fastforce intro:Cons_path)
  with \<open>V \<in> Def (sourcenode a)\<close> \<open>V \<in> Use nx\<close> 
    \<open>\<forall>n''\<in> set(sourcenodes as'). V \<notin> Def n''\<close> 
  have "sourcenode a influences V in nx via a#as'"
    by(auto simp:dyn_data_dependence_def sourcenodes_def)
  hence "sourcenode a -{V}a#as'\<rightarrow>\<^sub>d\<^sub>d nx" by(rule DynPDG_ddep_edge)
  with \<open>nx -as''\<rightarrow>\<^sub>d* n'\<close> \<open>as = as'@as''\<close> 
  show "\<exists>as'' nx. (as = as'@as'') \<and> (sourcenode a -{V}a#as'\<rightarrow>\<^sub>d\<^sub>d nx) \<and> 
    (nx -as''\<rightarrow>\<^sub>d* n')" by fastforce
qed



lemma dependent_live_vars_same_pathsI:
  assumes "V \<in> Use n'"
  shows "\<lbrakk>\<forall>as' a as''. as = as'@a#as'' \<longrightarrow> \<not> sourcenode a -{V}a#as''\<rightarrow>\<^sub>d\<^sub>d n'; 
          as \<noteq> [] \<longrightarrow> n' = last(targetnodes as)\<rbrakk>
  \<Longrightarrow> (V,as,as) \<in> dependent_live_vars n'"
proof(induct as)
  case Nil
  from \<open>V \<in> Use n'\<close> show ?case by(rule dep_vars_Use)
next
  case (Cons ax asx)
  note lastnode = \<open>ax#asx \<noteq> [] \<longrightarrow> n' = last (targetnodes (ax#asx))\<close>
  note IH = \<open>\<lbrakk>\<forall>as' a as''. asx = as'@a#as'' \<longrightarrow>
                           \<not> sourcenode a -{V}a#as''\<rightarrow>\<^sub>d\<^sub>d n';
             asx \<noteq> [] \<longrightarrow> n' = last (targetnodes asx)\<rbrakk>
           \<Longrightarrow> (V, asx, asx) \<in> dependent_live_vars n'\<close>
  from \<open>\<forall>as' a as''. ax#asx = as'@a#as'' \<longrightarrow> \<not> sourcenode a -{V}a#as''\<rightarrow>\<^sub>d\<^sub>d n'\<close>
  have all':"\<forall>as' a as''. asx = as'@a#as'' \<longrightarrow> \<not> sourcenode a -{V}a#as''\<rightarrow>\<^sub>d\<^sub>d n'"
    and "\<not> sourcenode ax -{V}ax#asx\<rightarrow>\<^sub>d\<^sub>d n'"
    by simp_all
  show ?case
  proof(cases "asx = []")
    case True
    from \<open>V \<in> Use n'\<close> have "(V,[],[]) \<in> dependent_live_vars n'" by(rule dep_vars_Use)
    with \<open>\<not> sourcenode ax -{V}ax#asx\<rightarrow>\<^sub>d\<^sub>d n'\<close> True lastnode
    have "(V,[ax],[ax]) \<in> dependent_live_vars n'"
      by(fastforce intro:dep_vars_Cons_keep)
    with True show ?thesis by simp
  next
    case False
    with lastnode have "asx \<noteq> [] \<longrightarrow> n' = last (targetnodes asx)"
      by(simp add:targetnodes_def)
    from IH[OF all' this] have "(V, asx, asx) \<in> dependent_live_vars n'" .
    with \<open>\<not> sourcenode ax -{V}ax#asx\<rightarrow>\<^sub>d\<^sub>d n'\<close> lastnode 
    show ?thesis by(fastforce intro:dep_vars_Cons_keep)
  qed
qed


lemma dependent_live_vars_same_pathsD:
  "\<lbrakk>(V,as,as) \<in> dependent_live_vars n';  as \<noteq> [] \<longrightarrow> n' = last(targetnodes as)\<rbrakk>
  \<Longrightarrow> V \<in> Use n' \<and> (\<forall>as' a as''. as = as'@a#as'' \<longrightarrow>
                       \<not> sourcenode a -{V}a#as''\<rightarrow>\<^sub>d\<^sub>d n')"
proof(induct as)
  case Nil
  have "(V,[],[]) \<in> dependent_live_vars n'" by fact
  thus ?case
    by(fastforce elim:dependent_live_vars.cases simp:targetnodes_def sourcenodes_def)
next
  case (Cons ax asx)
  note IH = \<open>\<lbrakk>(V,asx,asx) \<in> dependent_live_vars n'; 
              asx \<noteq> [] \<longrightarrow> n' = last (targetnodes asx)\<rbrakk>
    \<Longrightarrow> V \<in> Use n' \<and> (\<forall>as' a as''. asx = as'@a#as'' \<longrightarrow>
                          \<not> sourcenode a -{V}a#as''\<rightarrow>\<^sub>d\<^sub>d n')\<close>
  from \<open>(V,ax#asx,ax#asx) \<in> dependent_live_vars n'\<close>
  have "(V,asx,asx) \<in> dependent_live_vars n'"
    and "\<not> sourcenode ax -{V}ax#asx\<rightarrow>\<^sub>d\<^sub>d last(targetnodes (ax#asx))"
    by(auto elim:dependent_live_vars.cases)
  from \<open>ax#asx \<noteq> [] \<longrightarrow> n' = last (targetnodes (ax#asx))\<close>
  have "n' = last (targetnodes (ax#asx))" by simp
  show ?case
  proof(cases "asx = []")
    case True
    with \<open>(V,asx,asx) \<in> dependent_live_vars n'\<close> have "V \<in> Use n'"
      by(fastforce elim:dependent_live_vars.cases)
    from \<open>\<not> sourcenode ax -{V}ax#asx\<rightarrow>\<^sub>d\<^sub>d last(targetnodes (ax#asx))\<close> 
      True \<open>n' = last (targetnodes (ax#asx))\<close>
    have "\<forall>as' a as''. ax#asx = as'@a#as'' \<longrightarrow> \<not> sourcenode a -{V}a#as''\<rightarrow>\<^sub>d\<^sub>d n'"
      by auto(case_tac as',auto)
    with \<open>V \<in> Use n'\<close> show ?thesis by simp
  next
    case False
    with \<open>n' = last (targetnodes (ax#asx))\<close>
    have "asx \<noteq> [] \<longrightarrow> n' = last (targetnodes asx)"
      by(simp add:targetnodes_def)
    from IH[OF \<open>(V,asx,asx) \<in> dependent_live_vars n'\<close> this] 
    have "V \<in> Use n' \<and> (\<forall>as' a as''. asx = as'@a#as'' \<longrightarrow>
                            \<not> sourcenode a -{V}a#as''\<rightarrow>\<^sub>d\<^sub>d n')" .
    with \<open>\<not> sourcenode ax -{V}ax#asx\<rightarrow>\<^sub>d\<^sub>d last(targetnodes (ax#asx))\<close>
      \<open>n' = last (targetnodes (ax#asx))\<close> have "V \<in> Use n'"
      and "\<forall>as' a as''. ax#asx = as'@a#as'' \<longrightarrow>
                            \<not> sourcenode a -{V}a#as''\<rightarrow>\<^sub>d\<^sub>d n'"
      by auto(case_tac as',auto)
    thus ?thesis by simp
  qed
qed


lemma dependent_live_vars_same_paths:
  "as \<noteq> [] \<longrightarrow> n' = last(targetnodes as) \<Longrightarrow>
  (V,as,as) \<in> dependent_live_vars n' = 
  (V \<in> Use n' \<and> (\<forall>as' a as''. as = as'@a#as'' \<longrightarrow>
                       \<not> sourcenode a -{V}a#as''\<rightarrow>\<^sub>d\<^sub>d n'))"
by(fastforce intro!:dependent_live_vars_same_pathsD dependent_live_vars_same_pathsI)


lemma dependent_live_vars_cdep_empty_fst:
assumes "n'' -as\<rightarrow>\<^sub>c\<^sub>d n'" and "V' \<in> Use n''"
  shows "(V',[],as) \<in> dependent_live_vars n'"
proof(cases as)
  case Nil
  with \<open>n'' -as\<rightarrow>\<^sub>c\<^sub>d n'\<close> show ?thesis
    by(fastforce elim:DynPDG_edge.cases dest:dyn_control_dependence_path)
next
  case (Cons ax asx)
  with \<open>n'' -as\<rightarrow>\<^sub>c\<^sub>d n'\<close> have "sourcenode ax = n''"
    by(auto dest:DynPDG_cdep_edge_CFG_path elim:path.cases)
  from \<open>n'' -as\<rightarrow>\<^sub>c\<^sub>d n'\<close> have "valid_node n'"
    by(fastforce intro:path_valid_node(2) DynPDG_cdep_edge_CFG_path(1))
  from Cons \<open>n'' -as\<rightarrow>\<^sub>c\<^sub>d n'\<close> have "last(targetnodes as) = n'"
    by(fastforce intro:path_targetnode dest:DynPDG_cdep_edge_CFG_path)
  with Cons \<open>n'' -as\<rightarrow>\<^sub>c\<^sub>d n'\<close> \<open>V' \<in> Use n''\<close> \<open>sourcenode ax = n''\<close> \<open>valid_node n'\<close>
  have "(V', [], ax#asx@[]) \<in> dependent_live_vars n'"
    by(fastforce intro:dep_vars_Cons_cdep DynPDG_path_Nil)
  with Cons show ?thesis by simp
qed
  

lemma dependent_live_vars_ddep_empty_fst:
  assumes "n'' -{V}as\<rightarrow>\<^sub>d\<^sub>d n'" and "V' \<in> Use n''"
  shows "(V',[],as) \<in> dependent_live_vars n'"
proof(cases as)
  case Nil
  with \<open>n'' -{V}as\<rightarrow>\<^sub>d\<^sub>d n'\<close> show ?thesis
    by(fastforce elim:DynPDG_edge.cases simp:dyn_data_dependence_def)
next
  case (Cons ax asx)
  with \<open>n'' -{V}as\<rightarrow>\<^sub>d\<^sub>d n'\<close> have "sourcenode ax = n''"
    by(auto dest:DynPDG_ddep_edge_CFG_path elim:path.cases)
  from Cons \<open>n'' -{V}as\<rightarrow>\<^sub>d\<^sub>d n'\<close> have "last(targetnodes as) = n'"
    by(fastforce intro:path_targetnode elim:DynPDG_ddep_edge_CFG_path(1))
  from Cons \<open>n'' -{V}as\<rightarrow>\<^sub>d\<^sub>d n'\<close> have all:"\<forall>as' a as''. asx = as'@a#as'' \<longrightarrow>
                             \<not> sourcenode a -{V}a#as''\<rightarrow>\<^sub>d\<^sub>d n'"
    by(fastforce dest:DynPDG_ddep_edge_no_shorter_ddep_edge)
  from \<open>n'' -{V}as\<rightarrow>\<^sub>d\<^sub>d n'\<close> have "V \<in> Use n'" 
    by(auto elim!:DynPDG_edge.cases simp:dyn_data_dependence_def)
  from Cons \<open>n'' -{V}as\<rightarrow>\<^sub>d\<^sub>d n'\<close> have "as \<noteq> [] \<longrightarrow> n' = last(targetnodes as)"
    by(fastforce dest:DynPDG_ddep_edge_CFG_path path_targetnode)
  with Cons have "asx \<noteq> [] \<longrightarrow> n' = last(targetnodes asx)"
    by(fastforce simp:targetnodes_def)
  with all \<open>V \<in> Use n'\<close> have "(V,asx,asx) \<in> dependent_live_vars n'"
    by -(rule dependent_live_vars_same_pathsI)
  with \<open>V' \<in> Use n''\<close> \<open>n'' -{V}as\<rightarrow>\<^sub>d\<^sub>d n'\<close> \<open>last(targetnodes as) = n'\<close>
    Cons \<open>sourcenode ax = n''\<close> show ?thesis
    by(fastforce intro:dep_vars_Cons_ddep)
qed




lemma ddep_dependent_live_vars_keep_notempty:
  assumes "n -{V}a#as\<rightarrow>\<^sub>d\<^sub>d n''" and "as' \<noteq> []"
  and "(V,as'',as') \<in> dependent_live_vars n'"
  shows "(V,as@as'',as@as') \<in> dependent_live_vars n'"
proof -
  from \<open>n -{V}a#as\<rightarrow>\<^sub>d\<^sub>d n''\<close> have "\<forall>n'' \<in> set (sourcenodes as). V \<notin> Def n''"
    by(auto elim:DynPDG_edge.cases simp:dyn_data_dependence_def)
  with \<open>(V,as'',as') \<in> dependent_live_vars n'\<close> show ?thesis
  proof(induct as)
    case Nil thus ?case by simp
  next
    case (Cons ax asx)
    note IH = \<open>\<lbrakk>(V,as'',as') \<in> dependent_live_vars n';
                \<forall>n''\<in>set (sourcenodes asx). V \<notin> Def n''\<rbrakk>
               \<Longrightarrow> (V, asx@as'',asx@as') \<in> dependent_live_vars n'\<close>
    from \<open>\<forall>n''\<in>set (sourcenodes (ax#asx)). V \<notin> Def n''\<close>
    have "\<forall>n''\<in>set (sourcenodes asx). V \<notin> Def n''"
      by(auto simp:sourcenodes_def)
    from IH[OF \<open>(V,as'',as') \<in> dependent_live_vars n'\<close> this]
    have "(V,asx@as'',asx@as') \<in> dependent_live_vars n'" .
    from \<open>as' \<noteq> []\<close> \<open>(V,as'',as') \<in> dependent_live_vars n'\<close>
    have "n' = last(targetnodes as')" 
      by(fastforce intro:dependent_live_vars_lastnode)
    with \<open>as' \<noteq> []\<close> have "n' = last(targetnodes (ax#asx@as'))"
      by(fastforce simp:targetnodes_def)
    have "\<not> sourcenode ax -{V}ax#asx@as''\<rightarrow>\<^sub>d\<^sub>d last(targetnodes (ax#asx@as''))"
    proof
      assume "sourcenode ax -{V}ax#asx@as''\<rightarrow>\<^sub>d\<^sub>d last(targetnodes (ax#asx@as''))"
      hence "sourcenode ax -{V}ax#asx@as''\<rightarrow>\<^sub>d\<^sub>d last(targetnodes (ax#asx@as''))"
        by simp
      with \<open>\<forall>n''\<in>set (sourcenodes (ax#asx)). V \<notin> Def n''\<close>
      show False
        by(fastforce elim:DynPDG_edge.cases 
                    simp:dyn_data_dependence_def sourcenodes_def)
    qed
    with \<open>(V,asx@as'',asx@as') \<in> dependent_live_vars n'\<close> 
      \<open>n' = last(targetnodes (ax#asx@as'))\<close>
    show ?case by(fastforce intro:dep_vars_Cons_keep)
  qed
qed



lemma dependent_live_vars_cdep_dependent_live_vars:
  assumes "n'' -as''\<rightarrow>\<^sub>c\<^sub>d n'" and "(V',as',as) \<in> dependent_live_vars n''"
  shows "(V',as',as@as'') \<in> dependent_live_vars n'"
proof -
  from \<open>n'' -as''\<rightarrow>\<^sub>c\<^sub>d n'\<close> have "as'' \<noteq> []"
    by(fastforce elim:DynPDG_edge.cases dest:dyn_control_dependence_path)
  with \<open>n'' -as''\<rightarrow>\<^sub>c\<^sub>d n'\<close> have "last(targetnodes as'') = n'"
    by(fastforce intro:path_targetnode elim:DynPDG_cdep_edge_CFG_path(1))
  from \<open>(V',as',as) \<in> dependent_live_vars n''\<close> show ?thesis
  proof(induct rule:dependent_live_vars.induct)
    case (dep_vars_Use V')
    from \<open>V' \<in> Use n''\<close> \<open>n'' -as''\<rightarrow>\<^sub>c\<^sub>d n'\<close> \<open>last(targetnodes as'') = n'\<close> show ?case
      by(fastforce intro:dependent_live_vars_cdep_empty_fst simp:targetnodes_def)
  next
    case (dep_vars_Cons_cdep V a as' nx asx)
    from \<open>n'' -as''\<rightarrow>\<^sub>c\<^sub>d n'\<close> have "n'' -as''\<rightarrow>\<^sub>d* n'" by(rule DynPDG_path_cdep)
    with \<open>nx -asx\<rightarrow>\<^sub>d* n''\<close> have "nx -asx@as''\<rightarrow>\<^sub>d* n'"
      by -(rule DynPDG_path_Append)
    with \<open>V \<in> Use (sourcenode a)\<close> \<open>(sourcenode a) -a#as'\<rightarrow>\<^sub>c\<^sub>d nx\<close>
    show ?case by(fastforce intro:dependent_live_vars.dep_vars_Cons_cdep)
  next
    case (dep_vars_Cons_ddep V as' as V' a)
    from \<open>as'' \<noteq> []\<close> \<open>last(targetnodes as'') = n'\<close>
    have "n' = last(targetnodes ((a#as)@as''))"
      by(simp add:targetnodes_def)
    with dep_vars_Cons_ddep
    show ?case by(fastforce intro:dependent_live_vars.dep_vars_Cons_ddep)
  next
    case (dep_vars_Cons_keep V as' as a)
    from \<open>as'' \<noteq> []\<close> \<open>last(targetnodes as'') = n'\<close>
    have "n' = last(targetnodes ((a#as)@as''))"
      by(simp add:targetnodes_def)
    with dep_vars_Cons_keep
    show ?case by(fastforce intro:dependent_live_vars.dep_vars_Cons_keep)
  qed
qed


lemma dependent_live_vars_ddep_dependent_live_vars:
  assumes "n'' -{V}as''\<rightarrow>\<^sub>d\<^sub>d n'" and "(V',as',as) \<in> dependent_live_vars n''"
  shows "(V',as',as@as'') \<in> dependent_live_vars n'"
proof -
  from \<open>n'' -{V}as''\<rightarrow>\<^sub>d\<^sub>d n'\<close> have "as'' \<noteq> []"
    by(rule DynPDG_ddep_edge_CFG_path(2))
  with \<open>n'' -{V}as''\<rightarrow>\<^sub>d\<^sub>d n'\<close> have "last(targetnodes as'') = n'"
    by(fastforce intro:path_targetnode elim:DynPDG_ddep_edge_CFG_path(1))
  from \<open>n'' -{V}as''\<rightarrow>\<^sub>d\<^sub>d n'\<close> have notExit:"n' \<noteq> (_Exit_)" 
    by(fastforce elim:DynPDG_edge.cases simp:dyn_data_dependence_def)
  from \<open>(V',as',as) \<in> dependent_live_vars n''\<close> show ?thesis
  proof(induct rule:dependent_live_vars.induct)
    case (dep_vars_Use V')
    from \<open>V' \<in> Use n''\<close> \<open>n'' -{V}as''\<rightarrow>\<^sub>d\<^sub>d n'\<close> \<open>last(targetnodes as'') = n'\<close> show ?case
      by(fastforce intro:dependent_live_vars_ddep_empty_fst simp:targetnodes_def)
  next
    case (dep_vars_Cons_cdep V' a as' nx asx)
    from \<open>n'' -{V}as''\<rightarrow>\<^sub>d\<^sub>d n'\<close> have "n'' -as''\<rightarrow>\<^sub>d* n'" by(rule DynPDG_path_ddep)
    with \<open>nx -asx\<rightarrow>\<^sub>d* n''\<close> have "nx -asx@as''\<rightarrow>\<^sub>d* n'"
      by -(rule DynPDG_path_Append)
    with \<open>V' \<in> Use (sourcenode a)\<close> \<open>sourcenode a -a#as'\<rightarrow>\<^sub>c\<^sub>d nx\<close> notExit
    show ?case by(fastforce intro:dependent_live_vars.dep_vars_Cons_cdep)
  next
    case (dep_vars_Cons_ddep V as' as V' a)
    from \<open>as'' \<noteq> []\<close> \<open>last(targetnodes as'') = n'\<close>
    have "n' = last(targetnodes ((a#as)@as''))"
      by(simp add:targetnodes_def)
    with dep_vars_Cons_ddep
    show ?case by(fastforce intro:dependent_live_vars.dep_vars_Cons_ddep)
  next
    case (dep_vars_Cons_keep V as' as a)
    from \<open>as'' \<noteq> []\<close> \<open>last(targetnodes as'') = n'\<close>
    have "n' = last(targetnodes ((a#as)@as''))"
      by(simp add:targetnodes_def)
    with dep_vars_Cons_keep
    show ?case by(fastforce intro:dependent_live_vars.dep_vars_Cons_keep)
  qed
qed


lemma dependent_live_vars_dep_dependent_live_vars:
  "\<lbrakk>n'' -as''\<rightarrow>\<^sub>d* n'; (V',as',as) \<in> dependent_live_vars n''\<rbrakk>
  \<Longrightarrow> (V',as',as@as'') \<in> dependent_live_vars n'"
proof(induct rule:DynPDG_path.induct)
  case (DynPDG_path_Nil n) thus ?case by simp
next
  case (DynPDG_path_Append_cdep n asx n'' asx' n')
  note IH = \<open>(V', as', as) \<in> dependent_live_vars n \<Longrightarrow>
             (V', as', as @ asx) \<in> dependent_live_vars n''\<close>
  from IH[OF \<open>(V',as',as) \<in> dependent_live_vars n\<close>]
  have "(V',as',as@asx) \<in> dependent_live_vars n''" .
  with \<open>n'' -asx'\<rightarrow>\<^sub>c\<^sub>d n'\<close> have "(V',as',(as@asx)@asx') \<in> dependent_live_vars n'"
    by(rule dependent_live_vars_cdep_dependent_live_vars)
  thus ?case by simp
next
  case (DynPDG_path_Append_ddep n asx n'' V asx' n')
  note IH = \<open>(V', as', as) \<in> dependent_live_vars n \<Longrightarrow>
             (V', as', as @ asx) \<in> dependent_live_vars n''\<close>
  from IH[OF \<open>(V',as',as) \<in> dependent_live_vars n\<close>]
  have "(V',as',as@asx) \<in> dependent_live_vars n''" .
  with \<open>n'' -{V}asx'\<rightarrow>\<^sub>d\<^sub>d n'\<close> have "(V',as',(as@asx)@asx') \<in> dependent_live_vars n'"
    by(rule dependent_live_vars_ddep_dependent_live_vars)
  thus ?case by simp
qed

end


end
