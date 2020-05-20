section \<open>Instantiate framework with control dependences\<close>

theory CDepInstantiations imports 
  Slice 
  PDG 
  WeakOrderDependence 
begin

subsection\<open>Standard control dependence\<close>

context StandardControlDependencePDG begin

lemma Exit_in_obs_slice_node:"(_Exit_) \<in> obs n' (PDG_BS S) \<Longrightarrow> (_Exit_) \<in> S"
  by(auto elim:obsE PDG_path_CFG_path simp:PDG_BS_def split:if_split_asm)


abbreviation PDG_path' :: "'node \<Rightarrow> 'node \<Rightarrow> bool" ("_ \<longrightarrow>\<^sub>d* _" [51,0] 80)
  where "n \<longrightarrow>\<^sub>d* n' \<equiv> PDG.PDG_path sourcenode targetnode valid_edge Def Use
  standard_control_dependence n n'"

lemma cd_closed:
  "\<lbrakk>n' \<in> PDG_BS S; n controls\<^sub>s n'\<rbrakk> \<Longrightarrow> n \<in> PDG_BS S"
  by(simp add:PDG_BS_def)(blast dest:PDG_cdep_edge PDG_path_Append PDG_path_cdep)


lemma obs_postdominate:
  assumes "n \<in> obs n' (PDG_BS S)" and "n \<noteq> (_Exit_)" shows "n postdominates n'"
proof(rule ccontr)
  assume "\<not> n postdominates n'"
  from \<open>n \<in> obs n' (PDG_BS S)\<close> have "valid_node n" by(fastforce dest:in_obs_valid)
  with \<open>n \<in> obs n' (PDG_BS S)\<close> \<open>n \<noteq> (_Exit_)\<close> have "n postdominates n"
    by(fastforce intro:postdominate_refl)
  from \<open>n \<in> obs n' (PDG_BS S)\<close> obtain as where "n' -as\<rightarrow>* n"
    and "\<forall>n' \<in> set(sourcenodes as). n' \<notin> (PDG_BS S)"
    and "n \<in> (PDG_BS S)" by(erule obsE)
  from \<open>n postdominates n\<close> \<open>\<not> n postdominates n'\<close> \<open>n' -as\<rightarrow>* n\<close>
  obtain as' a as'' where [simp]:"as = as'@a#as''" and "valid_edge a"
    and "\<not> n postdominates (sourcenode a)" and "n postdominates (targetnode a)"
    by -(erule postdominate_path_branch)
  from \<open>\<not> n postdominates (sourcenode a)\<close> \<open>valid_edge a\<close> \<open>valid_node n\<close>
  obtain asx  where "sourcenode a -asx\<rightarrow>* (_Exit_)"
    and "n \<notin> set(sourcenodes asx)" by(auto simp:postdominate_def)
  from \<open>sourcenode a -asx\<rightarrow>* (_Exit_)\<close> \<open>valid_edge a\<close>
  obtain ax asx' where [simp]:"asx = ax#asx'"
    apply - apply(erule path.cases)
    apply(drule_tac s="(_Exit_)" in sym)
    apply simp
    apply(drule Exit_source)
    by simp_all
  with \<open>sourcenode a -asx\<rightarrow>* (_Exit_)\<close> have "sourcenode a -[]@ax#asx'\<rightarrow>* (_Exit_)" 
    by simp
  hence "valid_edge ax" and [simp]:"sourcenode a = sourcenode ax"
    and "targetnode ax -asx'\<rightarrow>* (_Exit_)"
    by(fastforce dest:path_split)+
  with \<open>n \<notin> set(sourcenodes asx)\<close> have "\<not> n postdominates targetnode ax"
    by(fastforce simp:postdominate_def sourcenodes_def)
  from \<open>n \<in> obs n' (PDG_BS S)\<close> \<open>\<forall>n' \<in> set(sourcenodes as). n' \<notin> (PDG_BS S)\<close>
  have "n \<notin> set (sourcenodes (a#as''))"
    by(fastforce elim:obs.cases simp:sourcenodes_def)
  from \<open>n' -as\<rightarrow>* n\<close> have "sourcenode a -a#as''\<rightarrow>* n"
    by(fastforce dest:path_split_second)
  with \<open>n postdominates (targetnode a)\<close> \<open>\<not> n postdominates targetnode ax\<close>
    \<open>valid_edge ax\<close> \<open>n \<notin> set (sourcenodes (a#as''))\<close>
  have "sourcenode a controls\<^sub>s n" by(fastforce simp:standard_control_dependence_def)
  with \<open>n \<in> obs n' (PDG_BS S)\<close> have "sourcenode a \<in> (PDG_BS S)"
    by(fastforce intro:cd_closed PDG_cdep_edge elim:obs.cases)
  with \<open>\<forall>n' \<in> set(sourcenodes as). n' \<notin> (PDG_BS S)\<close> 
  show False by(simp add:sourcenodes_def)
qed


lemma obs_singleton:"(\<exists>m. obs n (PDG_BS S) = {m}) \<or> obs n (PDG_BS S) = {}"
proof(rule ccontr)
  assume "\<not> ((\<exists>m. obs n (PDG_BS S) = {m}) \<or> obs n (PDG_BS S) = {})"
  hence "\<exists>nx nx'. nx \<in> obs n (PDG_BS S) \<and> nx' \<in> obs n (PDG_BS S) \<and>
    nx \<noteq> nx'" by auto
  then obtain nx nx' where "nx \<in> obs n (PDG_BS S)" and "nx' \<in> obs n (PDG_BS S)"
    and "nx \<noteq> nx'" by auto
  from \<open>nx \<in> obs n (PDG_BS S)\<close> obtain as where "n -as\<rightarrow>* nx" 
    and "\<forall>n' \<in> set(sourcenodes as). n' \<notin> (PDG_BS S)" and "nx \<in> (PDG_BS S)" 
    by(erule obsE)
  from \<open>n -as\<rightarrow>* nx\<close> have "valid_node nx" by(fastforce dest:path_valid_node)
  with \<open>nx \<in> (PDG_BS S)\<close> have "obs nx (PDG_BS S) = {nx}" by -(rule n_in_obs)
  with \<open>n -as\<rightarrow>* nx\<close> \<open>nx \<in> obs n (PDG_BS S)\<close> \<open>nx' \<in> obs n (PDG_BS S)\<close> \<open>nx \<noteq> nx'\<close>
  have "as \<noteq> []" by(fastforce elim:path.cases)
  with \<open>n -as\<rightarrow>* nx\<close> \<open>nx \<in> obs n (PDG_BS S)\<close> \<open>nx' \<in> obs n (PDG_BS S)\<close> 
    \<open>nx \<noteq> nx'\<close> \<open>obs nx (PDG_BS S) = {nx}\<close> \<open>\<forall>n' \<in> set(sourcenodes as). n' \<notin> (PDG_BS S)\<close>
  have "\<exists>a as' as''. n -as'\<rightarrow>* sourcenode a \<and> targetnode a -as''\<rightarrow>* nx \<and>
                     valid_edge a \<and> as = as'@a#as'' \<and> 
                     obs (targetnode a) (PDG_BS S) = {nx} \<and> 
                    (\<not> (\<exists>m. obs (sourcenode a) (PDG_BS S) = {m} \<or> 
                       obs (sourcenode a) (PDG_BS S) = {}))"
  proof(induct arbitrary:nx' rule:path.induct)
    case (Cons_path n'' as n' a n)
    note [simp] = \<open>sourcenode a = n\<close>[THEN sym] \<open>targetnode a = n''\<close>[THEN sym]
    note more_than_one = \<open>n' \<in> obs n (PDG_BS S)\<close> \<open>nx' \<in> obs n (PDG_BS S)\<close> \<open>n' \<noteq> nx'\<close>
    note IH = \<open>\<And>nx'. \<lbrakk>n' \<in> obs n'' (PDG_BS S); nx' \<in> obs n'' (PDG_BS S); n' \<noteq> nx'; 
      obs n' (PDG_BS S) = {n'}; \<forall>n'\<in>set (sourcenodes as). n' \<notin> (PDG_BS S); as \<noteq> []\<rbrakk>
      \<Longrightarrow> \<exists>a as' as''. n'' -as'\<rightarrow>* sourcenode a \<and> targetnode a -as''\<rightarrow>* n' \<and>
      valid_edge a \<and> as = as'@a#as'' \<and> obs (targetnode a) (PDG_BS S) = {n'} \<and>
      (\<not> (\<exists>m. obs (sourcenode a) (PDG_BS S) = {m} \<or> 
      obs (sourcenode a) (PDG_BS S) = {}))\<close>
    from \<open>\<forall>n'\<in>set (sourcenodes (a#as)). n' \<notin> (PDG_BS S)\<close>
    have "\<forall>n'\<in>set (sourcenodes as). n' \<notin> (PDG_BS S)" and "sourcenode a \<notin> (PDG_BS S)"
      by(simp_all add:sourcenodes_def)
    show ?case
    proof(cases "as = []")
      case True
      with \<open>n'' -as\<rightarrow>* n'\<close> have [simp]:"n' = n''" by(fastforce elim:path.cases)
      from more_than_one
      have "\<not> (\<exists>m. obs (sourcenode a) (PDG_BS S) = {m} \<or> 
               obs (sourcenode a) (PDG_BS S) = {})"
        by auto
      with \<open>obs n' (PDG_BS S) = {n'}\<close> True \<open>valid_edge a\<close> show ?thesis
        apply(rule_tac x="a" in exI)
        apply(rule_tac x="[]" in exI)
        apply(rule_tac x="[]" in exI)
        by(auto intro!:empty_path)
    next
      case False
      hence "as \<noteq> []" .
      from \<open>n'' -as\<rightarrow>* n'\<close> \<open>\<forall>n'\<in>set (sourcenodes as). n' \<notin> (PDG_BS S)\<close> 
      have "obs n' (PDG_BS S) \<subseteq> obs n'' (PDG_BS S)" by(rule path_obs_subset)
      show ?thesis
      proof(cases "obs n' (PDG_BS S) = obs n'' (PDG_BS S)")
        case True
        with \<open>n'' -as\<rightarrow>* n'\<close> \<open>valid_edge a\<close> \<open>obs n' (PDG_BS S) = {n'}\<close> more_than_one
        show ?thesis
          apply(rule_tac x="a" in exI)
          apply(rule_tac x="[]" in exI)
          apply(rule_tac x="as" in exI)
          by(fastforce intro:empty_path)
      next
        case False
        with \<open>obs n' (PDG_BS S) \<subseteq> obs n'' (PDG_BS S)\<close>
        have "obs n' (PDG_BS S) \<subset> obs n'' (PDG_BS S)" by simp
        with \<open>obs n' (PDG_BS S) = {n'}\<close> obtain ni where "n' \<in> obs n'' (PDG_BS S)"
          and "ni \<in> obs n'' (PDG_BS S)" and "n' \<noteq> ni" by auto
        from IH[OF this \<open>obs n' (PDG_BS S) = {n'}\<close> 
          \<open>\<forall>n'\<in>set (sourcenodes as). n' \<notin> (PDG_BS S)\<close> \<open>as \<noteq> []\<close>] obtain a' as' as''
          where "n'' -as'\<rightarrow>* sourcenode a'" and "targetnode a' -as''\<rightarrow>* n'"
          and "valid_edge a'" and [simp]:"as = as'@a'#as''" 
          and "obs (targetnode a') (PDG_BS S) = {n'}"
          and more_than_one':"\<not> (\<exists>m. obs (sourcenode a') (PDG_BS S) = {m} \<or> 
          obs (sourcenode a') (PDG_BS S) = {})"
          by blast
        from \<open>n'' -as'\<rightarrow>* sourcenode a'\<close> \<open>valid_edge a\<close>
        have "n -a#as'\<rightarrow>* sourcenode a'" by(fastforce intro:path.Cons_path)
        with \<open>targetnode a' -as''\<rightarrow>* n'\<close> \<open>obs (targetnode a') (PDG_BS S) = {n'}\<close>
          more_than_one' \<open>valid_edge a'\<close> show ?thesis
          apply(rule_tac x="a'" in exI)
          apply(rule_tac x="a#as'" in exI)
          apply(rule_tac x="as''" in exI)
          by fastforce
      qed
    qed
  qed simp
  then obtain a as' as'' where "valid_edge a"
    and "obs (targetnode a) (PDG_BS S) = {nx}"
    and more_than_one:"\<not> (\<exists>m. obs (sourcenode a) (PDG_BS S) = {m} \<or> 
                         obs (sourcenode a) (PDG_BS S) = {})"
    by blast
  have "sourcenode a \<notin> (PDG_BS S)"
  proof(rule ccontr)
    assume "\<not> sourcenode a \<notin> PDG_BS S"
    hence "sourcenode a \<in> PDG_BS S" by simp
    with \<open>valid_edge a\<close> have "obs (sourcenode a) (PDG_BS S) = {sourcenode a}"
      by(fastforce intro!:n_in_obs)
    with more_than_one show False by simp
  qed
  with \<open>valid_edge a\<close> 
  have "obs (targetnode a) (PDG_BS S) \<subseteq> obs (sourcenode a) (PDG_BS S)"
    by(rule edge_obs_subset)
  with \<open>obs (targetnode a) (PDG_BS S) = {nx}\<close> 
  have "nx \<in> obs (sourcenode a) (PDG_BS S)" by simp
  with more_than_one obtain m  where "m \<in> obs (sourcenode a) (PDG_BS S)"
    and "nx \<noteq> m" by auto
  from \<open>m \<in> obs (sourcenode a) (PDG_BS S)\<close> 
  have "valid_node m" by(fastforce dest:in_obs_valid)
  from \<open>obs (targetnode a) (PDG_BS S) = {nx}\<close> have "valid_node nx" 
    by(fastforce dest:in_obs_valid)
  show False
  proof(cases "m postdominates (sourcenode a)")
    case True
    with \<open>nx \<in> obs (sourcenode a) (PDG_BS S)\<close> \<open>m \<in> obs (sourcenode a) (PDG_BS S)\<close>
    have "m postdominates nx"
      by(fastforce intro:postdominate_path_targetnode elim:obs.cases)
    with \<open>nx \<noteq> m\<close> have "\<not> nx postdominates m" by(fastforce dest:postdominate_antisym)
    have "(_Exit_) -[]\<rightarrow>* (_Exit_)" by(fastforce intro:empty_path)
    with \<open>m postdominates nx\<close> have "nx \<noteq> (_Exit_)"
      by(fastforce simp:postdominate_def sourcenodes_def)
    have "\<not> nx postdominates (sourcenode a)"
    proof(rule ccontr)
      assume "\<not> \<not> nx postdominates sourcenode a"
      hence "nx postdominates sourcenode a" by simp
      from \<open>m \<in> obs (sourcenode a) (PDG_BS S)\<close> \<open>nx \<in> obs (sourcenode a) (PDG_BS S)\<close>
      obtain asx' where "sourcenode a -asx'\<rightarrow>* m" and "nx \<notin> set(sourcenodes asx')"
        by(fastforce elim:obs.cases)
      with \<open>nx postdominates sourcenode a\<close> have "nx postdominates m"
        by(rule postdominate_path_targetnode)
      with \<open>\<not> nx postdominates m\<close> show False by simp
    qed
    with \<open>nx \<in> obs (sourcenode a) (PDG_BS S)\<close> \<open>valid_node nx\<close> \<open>nx \<noteq> (_Exit_)\<close> 
    show False by(fastforce dest:obs_postdominate)
  next
    case False
    show False
    proof(cases "m = Exit")
      case True
      from \<open>m \<in> obs (sourcenode a) (PDG_BS S)\<close> \<open>nx \<in> obs (sourcenode a) (PDG_BS S)\<close>
      obtain xs where "sourcenode a -xs\<rightarrow>* m" and "nx \<notin> set(sourcenodes xs)"
        by(fastforce elim:obsE)
      obtain x' xs' where [simp]:"xs = x'#xs'"
      proof(cases xs)
        case Nil
        with \<open>sourcenode a -xs\<rightarrow>* m\<close> have [simp]:"sourcenode a = m" by fastforce
        with \<open>m \<in> obs (sourcenode a) (PDG_BS S)\<close> 
        have "m \<in> (PDG_BS S)" by(metis obsE)
        with \<open>valid_node m\<close> have "obs m (PDG_BS S) = {m}"
          by(rule n_in_obs)
        with \<open>nx \<in> obs (sourcenode a) (PDG_BS S)\<close> \<open>nx \<noteq> m\<close> have False
          by fastforce
        thus ?thesis by simp
      qed blast
      from \<open>sourcenode a -xs\<rightarrow>* m\<close> have "sourcenode a = sourcenode x'" 
        and "valid_edge x'" and "targetnode x' -xs'\<rightarrow>* m"
        by(auto elim:path_split_Cons)
      from \<open>targetnode x' -xs'\<rightarrow>* m\<close> \<open>nx \<notin> set(sourcenodes xs)\<close> \<open>valid_edge x'\<close> 
        \<open>valid_node m\<close> True
      have "\<not> nx postdominates (targetnode x')" 
        by(fastforce simp:postdominate_def sourcenodes_def)
      from \<open>nx \<noteq> m\<close> True have "nx \<noteq> (_Exit_)" by simp
      with \<open>obs (targetnode a) (PDG_BS S) = {nx}\<close>
      have "nx postdominates (targetnode a)"
        by(fastforce intro:obs_postdominate)
      from \<open>obs (targetnode a) (PDG_BS S) = {nx}\<close>
      obtain ys where "targetnode a -ys\<rightarrow>* nx" 
        and "\<forall>nx' \<in> set(sourcenodes ys). nx' \<notin> (PDG_BS S)"
        and "nx \<in> (PDG_BS S)" by(fastforce elim:obsE)
      hence "nx \<notin> set(sourcenodes ys)"by fastforce
      have "sourcenode a \<noteq> nx"
      proof
        assume "sourcenode a = nx"
        from \<open>nx \<in> obs (sourcenode a) (PDG_BS S)\<close>
        have "nx \<in> (PDG_BS S)" by -(erule obsE)
        with \<open>valid_node nx\<close> have "obs nx (PDG_BS S) = {nx}" by -(erule n_in_obs)
        with \<open>sourcenode a = nx\<close> \<open>m \<in> obs (sourcenode a) (PDG_BS S)\<close> 
          \<open>nx \<noteq> m\<close> show False by fastforce
      qed
      with \<open>nx \<notin> set(sourcenodes ys)\<close> have "nx \<notin> set(sourcenodes (a#ys))"
        by(fastforce simp:sourcenodes_def)
      from \<open>valid_edge a\<close> \<open>targetnode a -ys\<rightarrow>* nx\<close>
      have "sourcenode a -a#ys\<rightarrow>* nx" by(fastforce intro:Cons_path)
      from \<open>sourcenode a -a#ys\<rightarrow>* nx\<close> \<open>nx \<notin> set(sourcenodes (a#ys))\<close>
        \<open>nx postdominates (targetnode a)\<close> \<open>valid_edge x'\<close>
        \<open>\<not> nx postdominates (targetnode x')\<close> \<open>sourcenode a = sourcenode x'\<close>
      have "(sourcenode a) controls\<^sub>s nx"
        by(fastforce simp:standard_control_dependence_def)
      with \<open>nx \<in> (PDG_BS S)\<close> have "sourcenode a \<in> (PDG_BS S)"
        by(rule cd_closed)
      with \<open>valid_edge a\<close> have "obs (sourcenode a) (PDG_BS S) = {sourcenode a}"
        by(fastforce intro!:n_in_obs)
      with \<open>m \<in> obs (sourcenode a) (PDG_BS S)\<close>
        \<open>nx \<in> obs (sourcenode a) (PDG_BS S)\<close> \<open>nx \<noteq> m\<close>
      show False by simp
    next
      case False
      with \<open>m \<in> obs (sourcenode a) (PDG_BS S)\<close> \<open>valid_node m\<close>
        \<open>\<not> m postdominates sourcenode a\<close> 
      show False by(fastforce dest:obs_postdominate)
    qed
  qed
qed


lemma PDGBackwardSliceCorrect:
  "BackwardSlice sourcenode targetnode kind valid_edge
        (_Entry_) Def Use state_val PDG_BS"
proof(unfold_locales)
  fix n S assume "n \<in> PDG_BS S"
  thus "valid_node n" by(rule PDG_BS_valid_node)
next
  fix n S assume "valid_node n" and "n \<in> S"
  thus "n \<in> PDG_BS S" by(fastforce intro:PDG_path_Nil simp:PDG_BS_def)
next
  fix n' S n V
  assume "n' \<in> PDG_BS S" and "n influences V in n'"
  thus "n \<in> PDG_BS S"
    by(auto dest:PDG.PDG_path_ddep[OF PDG_scd,OF PDG.PDG_ddep_edge[OF PDG_scd]]
            dest:PDG_path_Append simp:PDG_BS_def split:if_split_asm)
next
  fix n S
  have "(\<exists>m. obs n (PDG_BS S) = {m}) \<or> obs n (PDG_BS S) = {}" 
    by(rule obs_singleton)
  thus "finite (obs n (PDG_BS S))" by fastforce
next
  fix n S
  have "(\<exists>m. obs n (PDG_BS S) = {m}) \<or> obs n (PDG_BS S) = {}" 
    by(rule obs_singleton)
  thus "card (obs n (PDG_BS S)) \<le> 1" by fastforce
qed

end


subsection\<open>Weak control dependence\<close>

context WeakControlDependencePDG begin

lemma Exit_in_obs_slice_node:"(_Exit_) \<in> obs n' (PDG_BS S) \<Longrightarrow> (_Exit_) \<in> S"
  by(auto elim:obsE PDG_path_CFG_path simp:PDG_BS_def split:if_split_asm)


lemma cd_closed:
  "\<lbrakk>n' \<in> PDG_BS S; n weakly controls n'\<rbrakk> \<Longrightarrow> n \<in> PDG_BS S"
  by(simp add:PDG_BS_def)(blast dest:PDG_cdep_edge PDG_path_Append PDG_path_cdep)


lemma obs_strong_postdominate:
  assumes "n \<in> obs n' (PDG_BS S)" and "n \<noteq> (_Exit_)" 
  shows "n strongly-postdominates n'"
proof(rule ccontr)
  assume "\<not> n strongly-postdominates n'"
  from \<open>n \<in> obs n' (PDG_BS S)\<close> have "valid_node n" by(fastforce dest:in_obs_valid)
  with \<open>n \<in> obs n' (PDG_BS S)\<close> \<open>n \<noteq> (_Exit_)\<close> have "n strongly-postdominates n"
    by(fastforce intro:strong_postdominate_refl)
  from \<open>n \<in> obs n' (PDG_BS S)\<close> obtain as where "n' -as\<rightarrow>* n"
    and "\<forall>n' \<in> set(sourcenodes as). n' \<notin> (PDG_BS S)"
    and "n \<in> (PDG_BS S)" by(erule obsE)
  from \<open>n strongly-postdominates n\<close> \<open>\<not> n strongly-postdominates n'\<close> \<open>n' -as\<rightarrow>* n\<close>
  obtain as' a as'' where [simp]:"as = as'@a#as''" and "valid_edge a"
    and "\<not> n strongly-postdominates (sourcenode a)" and 
    "n strongly-postdominates (targetnode a)"
    by -(erule strong_postdominate_path_branch)
  from \<open>n \<in> obs n' (PDG_BS S)\<close> \<open>\<forall>n' \<in> set(sourcenodes as). n' \<notin> (PDG_BS S)\<close> 
  have "n \<notin> set (sourcenodes (a#as''))"
    by(fastforce elim:obs.cases simp:sourcenodes_def)
  from \<open>n' -as\<rightarrow>* n\<close> have "sourcenode a -a#as''\<rightarrow>* n"
    by(fastforce dest:path_split_second)
  from \<open>\<not> n strongly-postdominates (sourcenode a)\<close> \<open>valid_edge a\<close> \<open>valid_node n\<close>
  obtain a' where "sourcenode a' = sourcenode a"
    and "valid_edge a'" and "\<not> n strongly-postdominates (targetnode a')"
    by(fastforce elim:not_strong_postdominate_predecessor_successor)
  with \<open>n strongly-postdominates (targetnode a)\<close> \<open>n \<notin> set (sourcenodes (a#as''))\<close>
    \<open>sourcenode a -a#as''\<rightarrow>* n\<close>
  have "sourcenode a weakly controls n"
    by(fastforce simp:weak_control_dependence_def)
  with \<open>n \<in> obs n' (PDG_BS S)\<close> have "sourcenode a \<in> (PDG_BS S)"
    by(fastforce intro:cd_closed PDG_cdep_edge elim:obs.cases)
  with \<open>\<forall>n' \<in> set(sourcenodes as). n' \<notin> (PDG_BS S)\<close>
  show False by(simp add:sourcenodes_def)
qed


lemma obs_singleton:"(\<exists>m. obs n (PDG_BS S) = {m}) \<or> obs n (PDG_BS S) = {}"
proof(rule ccontr)
  assume "\<not> ((\<exists>m. obs n (PDG_BS S) = {m}) \<or> obs n (PDG_BS S) = {})"
  hence "\<exists>nx nx'. nx \<in> obs n (PDG_BS S) \<and> nx' \<in> obs n (PDG_BS S) \<and>
    nx \<noteq> nx'" by auto
  then obtain nx nx' where "nx \<in> obs n (PDG_BS S)" and "nx' \<in> obs n (PDG_BS S)"
    and "nx \<noteq> nx'" by auto
  from \<open>nx \<in> obs n (PDG_BS S)\<close> obtain as where "n -as\<rightarrow>* nx" 
    and "\<forall>n' \<in> set(sourcenodes as). n' \<notin> (PDG_BS S)" and "nx \<in> (PDG_BS S)" 
    by(erule obsE)
  from \<open>n -as\<rightarrow>* nx\<close> have "valid_node nx" by(fastforce dest:path_valid_node)
  with \<open>nx \<in> (PDG_BS S)\<close> have "obs nx (PDG_BS S) = {nx}" by -(rule n_in_obs)
  with \<open>n -as\<rightarrow>* nx\<close> \<open>nx \<in> obs n (PDG_BS S)\<close> \<open>nx' \<in> obs n (PDG_BS S)\<close> \<open>nx \<noteq> nx'\<close>
  have "as \<noteq> []" by(fastforce elim:path.cases)
  with \<open>n -as\<rightarrow>* nx\<close> \<open>nx \<in> obs n (PDG_BS S)\<close> \<open>nx' \<in> obs n (PDG_BS S)\<close> 
    \<open>nx \<noteq> nx'\<close> \<open>obs nx (PDG_BS S) = {nx}\<close> \<open>\<forall>n' \<in> set(sourcenodes as). n' \<notin> (PDG_BS S)\<close>
  have "\<exists>a as' as''. n -as'\<rightarrow>* sourcenode a \<and> targetnode a -as''\<rightarrow>* nx \<and>
                     valid_edge a \<and> as = as'@a#as'' \<and> 
                     obs (targetnode a) (PDG_BS S) = {nx} \<and> 
                    (\<not> (\<exists>m. obs (sourcenode a) (PDG_BS S) = {m} \<or> 
                       obs (sourcenode a) (PDG_BS S) = {}))"
  proof(induct arbitrary:nx' rule:path.induct)
    case (Cons_path n'' as n' a n)
    note [simp] = \<open>sourcenode a = n\<close>[THEN sym] \<open>targetnode a = n''\<close>[THEN sym]
    note more_than_one = \<open>n' \<in> obs n (PDG_BS S)\<close> \<open>nx' \<in> obs n (PDG_BS S)\<close> \<open>n' \<noteq> nx'\<close>
    note IH = \<open>\<And>nx'. \<lbrakk>n' \<in> obs n'' (PDG_BS S); nx' \<in> obs n'' (PDG_BS S); n' \<noteq> nx'; 
      obs n' (PDG_BS S) = {n'}; \<forall>n'\<in>set (sourcenodes as). n' \<notin> (PDG_BS S); as \<noteq> []\<rbrakk>
      \<Longrightarrow> \<exists>a as' as''. n'' -as'\<rightarrow>* sourcenode a \<and> targetnode a -as''\<rightarrow>* n' \<and>
      valid_edge a \<and> as = as'@a#as'' \<and> obs (targetnode a) (PDG_BS S) = {n'} \<and>
      (\<not> (\<exists>m. obs (sourcenode a) (PDG_BS S) = {m} \<or> 
      obs (sourcenode a) (PDG_BS S) = {}))\<close>
    from \<open>\<forall>n'\<in>set (sourcenodes (a#as)). n' \<notin> (PDG_BS S)\<close>
    have "\<forall>n'\<in>set (sourcenodes as). n' \<notin> (PDG_BS S)" and "sourcenode a \<notin> (PDG_BS S)"
      by(simp_all add:sourcenodes_def)
    show ?case
    proof(cases "as = []")
      case True
      with \<open>n'' -as\<rightarrow>* n'\<close> have [simp]:"n' = n''" by(fastforce elim:path.cases)
      from more_than_one
      have "\<not> (\<exists>m. obs (sourcenode a) (PDG_BS S) = {m} \<or> 
               obs (sourcenode a) (PDG_BS S) = {})"
        by auto
      with \<open>obs n' (PDG_BS S) = {n'}\<close> True \<open>valid_edge a\<close> show ?thesis
        apply(rule_tac x="a" in exI)
        apply(rule_tac x="[]" in exI)
        apply(rule_tac x="[]" in exI)
        by(auto intro!:empty_path)
    next
      case False
      hence "as \<noteq> []" .
      from \<open>n'' -as\<rightarrow>* n'\<close> \<open>\<forall>n'\<in>set (sourcenodes as). n' \<notin> (PDG_BS S)\<close> 
      have "obs n' (PDG_BS S) \<subseteq> obs n'' (PDG_BS S)" by(rule path_obs_subset)
      show ?thesis
      proof(cases "obs n' (PDG_BS S) = obs n'' (PDG_BS S)")
        case True
        with \<open>n'' -as\<rightarrow>* n'\<close> \<open>valid_edge a\<close> \<open>obs n' (PDG_BS S) = {n'}\<close> more_than_one
        show ?thesis
          apply(rule_tac x="a" in exI)
          apply(rule_tac x="[]" in exI)
          apply(rule_tac x="as" in exI)
          by(fastforce intro:empty_path)
      next
        case False
        with \<open>obs n' (PDG_BS S) \<subseteq> obs n'' (PDG_BS S)\<close>
        have "obs n' (PDG_BS S) \<subset> obs n'' (PDG_BS S)" by simp
        with \<open>obs n' (PDG_BS S) = {n'}\<close> obtain ni where "n' \<in> obs n'' (PDG_BS S)"
          and "ni \<in> obs n'' (PDG_BS S)" and "n' \<noteq> ni" by auto
        from IH[OF this \<open>obs n' (PDG_BS S) = {n'}\<close> 
          \<open>\<forall>n'\<in>set (sourcenodes as). n' \<notin> (PDG_BS S)\<close> \<open>as \<noteq> []\<close>] obtain a' as' as''
          where "n'' -as'\<rightarrow>* sourcenode a'" and "targetnode a' -as''\<rightarrow>* n'"
          and "valid_edge a'" and [simp]:"as = as'@a'#as''" 
          and "obs (targetnode a') (PDG_BS S) = {n'}"
          and more_than_one':"\<not> (\<exists>m. obs (sourcenode a') (PDG_BS S) = {m} \<or> 
          obs (sourcenode a') (PDG_BS S) = {})"
          by blast
        from \<open>n'' -as'\<rightarrow>* sourcenode a'\<close> \<open>valid_edge a\<close>
        have "n -a#as'\<rightarrow>* sourcenode a'" by(fastforce intro:path.Cons_path)
        with \<open>targetnode a' -as''\<rightarrow>* n'\<close> \<open>obs (targetnode a') (PDG_BS S) = {n'}\<close>
          more_than_one' \<open>valid_edge a'\<close> show ?thesis
          apply(rule_tac x="a'" in exI)
          apply(rule_tac x="a#as'" in exI)
          apply(rule_tac x="as''" in exI)
          by fastforce
      qed
    qed
  qed simp
  then obtain a as' as'' where "valid_edge a"
    and "obs (targetnode a) (PDG_BS S) = {nx}"
    and more_than_one:"\<not> (\<exists>m. obs (sourcenode a) (PDG_BS S) = {m} \<or> 
                         obs (sourcenode a) (PDG_BS S) = {})"
    by blast
  have "sourcenode a \<notin> (PDG_BS S)"
  proof(rule ccontr)
    assume "\<not> sourcenode a \<notin> PDG_BS S"
    hence "sourcenode a \<in> PDG_BS S" by simp
    with \<open>valid_edge a\<close> have "obs (sourcenode a) (PDG_BS S) = {sourcenode a}"
      by(fastforce intro!:n_in_obs)
    with more_than_one show False by simp
  qed
  with \<open>valid_edge a\<close> 
  have "obs (targetnode a) (PDG_BS S) \<subseteq> obs (sourcenode a) (PDG_BS S)"
    by(rule edge_obs_subset)
  with \<open>obs (targetnode a) (PDG_BS S) = {nx}\<close> 
  have "nx \<in> obs (sourcenode a) (PDG_BS S)" by simp
  with more_than_one obtain m  where "m \<in> obs (sourcenode a) (PDG_BS S)"
    and "nx \<noteq> m" by auto
  from \<open>m \<in> obs (sourcenode a) (PDG_BS S)\<close> 
  have "valid_node m" by(fastforce dest:in_obs_valid)
  from \<open>obs (targetnode a) (PDG_BS S) = {nx}\<close> have "valid_node nx" 
    by(fastforce dest:in_obs_valid)
  show False
  proof(cases "m strongly-postdominates (sourcenode a)")
    case True
    with \<open>nx \<in> obs (sourcenode a) (PDG_BS S)\<close> \<open>m \<in> obs (sourcenode a) (PDG_BS S)\<close>
    have "m strongly-postdominates nx"
      by(fastforce intro:strong_postdominate_path_targetnode elim:obs.cases)
    with \<open>nx \<noteq> m\<close> have "\<not> nx strongly-postdominates m" 
      by(fastforce dest:strong_postdominate_antisym)
    have "(_Exit_) -[]\<rightarrow>* (_Exit_)" by(fastforce intro:empty_path)
    with \<open>m strongly-postdominates nx\<close> have "nx \<noteq> (_Exit_)"
      by(fastforce simp:strong_postdominate_def sourcenodes_def postdominate_def)
    have "\<not> nx strongly-postdominates (sourcenode a)"
    proof(rule ccontr)
      assume "\<not> \<not> nx strongly-postdominates sourcenode a"
      hence "nx strongly-postdominates sourcenode a" by simp
      from \<open>m \<in> obs (sourcenode a) (PDG_BS S)\<close> \<open>nx \<in> obs (sourcenode a) (PDG_BS S)\<close>
      obtain asx' where "sourcenode a -asx'\<rightarrow>* m" and "nx \<notin> set(sourcenodes asx')"
        by(fastforce elim:obs.cases)
      with \<open>nx strongly-postdominates sourcenode a\<close> have "nx strongly-postdominates m"
        by(rule strong_postdominate_path_targetnode)
      with \<open>\<not> nx strongly-postdominates m\<close> show False by simp
    qed
    with \<open>nx \<in> obs (sourcenode a) (PDG_BS S)\<close> \<open>valid_node nx\<close> \<open>nx \<noteq> (_Exit_)\<close> 
    show False by(fastforce dest:obs_strong_postdominate)
  next
    case False
    show False
    proof(cases "m = Exit")
      case True
      from \<open>m \<in> obs (sourcenode a) (PDG_BS S)\<close> \<open>nx \<in> obs (sourcenode a) (PDG_BS S)\<close>
      obtain xs where "sourcenode a -xs\<rightarrow>* m" and "nx \<notin> set(sourcenodes xs)"
        by(fastforce elim:obsE)
      obtain x' xs' where [simp]:"xs = x'#xs'"
      proof(cases xs)
        case Nil
        with \<open>sourcenode a -xs\<rightarrow>* m\<close> have [simp]:"sourcenode a = m" by fastforce
        with \<open>m \<in> obs (sourcenode a) (PDG_BS S)\<close> 
        have "m \<in> (PDG_BS S)" by (metis obsE)
        with \<open>valid_node m\<close> have "obs m (PDG_BS S) = {m}"
          by(rule n_in_obs)
        with \<open>nx \<in> obs (sourcenode a) (PDG_BS S)\<close> \<open>nx \<noteq> m\<close> have False
          by fastforce
        thus ?thesis by simp
      qed blast
      from \<open>sourcenode a -xs\<rightarrow>* m\<close> have "sourcenode a = sourcenode x'" 
        and "valid_edge x'" and "targetnode x' -xs'\<rightarrow>* m"
        by(auto elim:path_split_Cons)
      from \<open>targetnode x' -xs'\<rightarrow>* m\<close> \<open>nx \<notin> set(sourcenodes xs)\<close> \<open>valid_edge x'\<close> 
        \<open>valid_node m\<close> True
      have "\<not> nx strongly-postdominates (targetnode x')" 
        by(fastforce simp:strong_postdominate_def postdominate_def sourcenodes_def)
      from \<open>nx \<noteq> m\<close> True have "nx \<noteq> (_Exit_)" by simp
      with \<open>obs (targetnode a) (PDG_BS S) = {nx}\<close>
      have "nx strongly-postdominates (targetnode a)"
        by(fastforce intro:obs_strong_postdominate)
      from \<open>obs (targetnode a) (PDG_BS S) = {nx}\<close>
      obtain ys where "targetnode a -ys\<rightarrow>* nx" 
        and "\<forall>nx' \<in> set(sourcenodes ys). nx' \<notin> (PDG_BS S)"
        and "nx \<in> (PDG_BS S)" by(fastforce elim:obsE)
      hence "nx \<notin> set(sourcenodes ys)"by fastforce
      have "sourcenode a \<noteq> nx"
      proof
        assume "sourcenode a = nx"
        from \<open>nx \<in> obs (sourcenode a) (PDG_BS S)\<close>
        have "nx \<in> (PDG_BS S)" by -(erule obsE)
        with \<open>valid_node nx\<close> have "obs nx (PDG_BS S) = {nx}" by -(erule n_in_obs)
        with \<open>sourcenode a = nx\<close> \<open>m \<in> obs (sourcenode a) (PDG_BS S)\<close> 
          \<open>nx \<noteq> m\<close> show False by fastforce
      qed
      with \<open>nx \<notin> set(sourcenodes ys)\<close> have "nx \<notin> set(sourcenodes (a#ys))"
        by(fastforce simp:sourcenodes_def)
      from \<open>valid_edge a\<close> \<open>targetnode a -ys\<rightarrow>* nx\<close>
      have "sourcenode a -a#ys\<rightarrow>* nx" by(fastforce intro:Cons_path)
      from \<open>sourcenode a -a#ys\<rightarrow>* nx\<close> \<open>nx \<notin> set(sourcenodes (a#ys))\<close>
        \<open>nx strongly-postdominates (targetnode a)\<close> \<open>valid_edge x'\<close>
        \<open>\<not> nx strongly-postdominates (targetnode x')\<close> \<open>sourcenode a = sourcenode x'\<close>
      have "(sourcenode a) weakly controls nx"
        by(fastforce simp:weak_control_dependence_def)
      with \<open>nx \<in> (PDG_BS S)\<close> have "sourcenode a \<in> (PDG_BS S)"
        by(rule cd_closed)
      with \<open>valid_edge a\<close> have "obs (sourcenode a) (PDG_BS S) = {sourcenode a}"
        by(fastforce intro!:n_in_obs)
      with \<open>m \<in> obs (sourcenode a) (PDG_BS S)\<close>
        \<open>nx \<in> obs (sourcenode a) (PDG_BS S)\<close> \<open>nx \<noteq> m\<close>
      show False by simp
    next
      case False
      with \<open>m \<in> obs (sourcenode a) (PDG_BS S)\<close> \<open>valid_node m\<close>
        \<open>\<not> m strongly-postdominates sourcenode a\<close> 
      show False by(fastforce dest:obs_strong_postdominate)
    qed
  qed
qed


lemma WeakPDGBackwardSliceCorrect:
  "BackwardSlice sourcenode targetnode kind valid_edge
        (_Entry_) Def Use state_val PDG_BS"
proof(unfold_locales)
  fix n S assume "n \<in> PDG_BS S"
  thus "valid_node n" by(rule PDG_BS_valid_node)
next
  fix n S assume "valid_node n" and "n \<in> S"
  thus "n \<in> PDG_BS S" by(fastforce intro:PDG_path_Nil simp:PDG_BS_def)
next
  fix n' S n V assume "n' \<in> PDG_BS S" and "n influences V in n'"
  thus "n \<in> PDG_BS S"
    by(auto dest:PDG.PDG_path_ddep[OF PDG_wcd,OF PDG.PDG_ddep_edge[OF PDG_wcd]]
            dest:PDG_path_Append simp:PDG_BS_def split:if_split_asm)
next
  fix n S
  have "(\<exists>m. obs n (PDG_BS S) = {m}) \<or> obs n (PDG_BS S) = {}" 
    by(rule obs_singleton)
  thus "finite (obs n (PDG_BS S))" by fastforce
next
  fix n S
  have "(\<exists>m. obs n (PDG_BS S) = {m}) \<or> obs n (PDG_BS S) = {}" 
    by(rule obs_singleton)
  thus "card (obs n (PDG_BS S)) \<le> 1" by fastforce
qed

end


subsection\<open>Weak order dependence\<close>

context CFG_wf begin

lemma obs_singleton: 
  (*assumes valid:"valid_node n"*)
  shows "(\<exists>m. obs n (wod_backward_slice S) = {m}) \<or>
         obs n (wod_backward_slice S) = {}"
proof(rule ccontr)
  let ?WOD_BS = "wod_backward_slice S"
  assume "\<not> ((\<exists>m. obs n ?WOD_BS = {m}) \<or> obs n ?WOD_BS = {})"
  hence "\<exists>nx nx'. nx \<in> obs n ?WOD_BS \<and> nx' \<in> obs n ?WOD_BS \<and>
    nx \<noteq> nx'" by auto
  then obtain nx nx' where "nx \<in> obs n ?WOD_BS" and "nx' \<in> obs n ?WOD_BS"
    and "nx \<noteq> nx'" by auto
  from \<open>nx \<in> obs n ?WOD_BS\<close> obtain as where "n -as\<rightarrow>* nx" 
    and "\<forall>n' \<in> set(sourcenodes as). n' \<notin> ?WOD_BS" and "nx \<in> ?WOD_BS" 
    by(erule obsE)
  from \<open>n -as\<rightarrow>* nx\<close> have "valid_node nx" by(fastforce dest:path_valid_node)
  with \<open>nx \<in> ?WOD_BS\<close> have "obs nx ?WOD_BS = {nx}" by -(rule n_in_obs)
  with \<open>n -as\<rightarrow>* nx\<close> \<open>nx \<in> obs n ?WOD_BS\<close> \<open>nx' \<in> obs n ?WOD_BS\<close> \<open>nx \<noteq> nx'\<close> 
  have "as \<noteq> []" by(fastforce elim:path.cases)
  with \<open>n -as\<rightarrow>* nx\<close> \<open>nx \<in> obs n ?WOD_BS\<close> \<open>nx' \<in> obs n ?WOD_BS\<close> \<open>nx \<noteq> nx'\<close> 
    \<open>obs nx ?WOD_BS = {nx}\<close> \<open>\<forall>n' \<in> set(sourcenodes as). n' \<notin> ?WOD_BS\<close>
  have "\<exists>a as' as''. n -as'\<rightarrow>* sourcenode a \<and> targetnode a -as''\<rightarrow>* nx \<and>
                     valid_edge a \<and> as = as'@a#as'' \<and> 
                     obs (targetnode a) ?WOD_BS = {nx} \<and> 
                    (\<not> (\<exists>m. obs (sourcenode a) ?WOD_BS = {m} \<or> 
                       obs (sourcenode a) ?WOD_BS = {}))"
  proof(induct arbitrary:nx' rule:path.induct)
    case (Cons_path n'' as n' a n)
    note [simp] = \<open>sourcenode a = n\<close>[THEN sym] \<open>targetnode a = n''\<close>[THEN sym]
    note more_than_one = \<open>n' \<in> obs n (?WOD_BS)\<close> \<open>nx' \<in> obs n (?WOD_BS)\<close> \<open>n' \<noteq> nx'\<close>
    note IH = \<open>\<And>nx'. \<lbrakk>n' \<in> obs n'' (?WOD_BS); nx' \<in> obs n'' (?WOD_BS); n' \<noteq> nx'; 
      obs n' (?WOD_BS) = {n'}; \<forall>n'\<in>set (sourcenodes as). n' \<notin> (?WOD_BS); as \<noteq> []\<rbrakk>
      \<Longrightarrow> \<exists>a as' as''. n'' -as'\<rightarrow>* sourcenode a \<and> targetnode a -as''\<rightarrow>* n' \<and>
      valid_edge a \<and> as = as'@a#as'' \<and> obs (targetnode a) (?WOD_BS) = {n'} \<and>
      (\<not> (\<exists>m. obs (sourcenode a) (?WOD_BS) = {m} \<or> 
      obs (sourcenode a) (?WOD_BS) = {}))\<close>
    from \<open>\<forall>n'\<in>set (sourcenodes (a#as)). n' \<notin> (?WOD_BS)\<close>
    have "\<forall>n'\<in>set (sourcenodes as). n' \<notin> (?WOD_BS)" and "sourcenode a \<notin> (?WOD_BS)"
      by(simp_all add:sourcenodes_def)
    show ?case
    proof(cases "as = []")
      case True
      with \<open>n'' -as\<rightarrow>* n'\<close> have [simp]:"n' = n''" by(fastforce elim:path.cases)
      from more_than_one
      have "\<not> (\<exists>m. obs (sourcenode a) (?WOD_BS) = {m} \<or> 
               obs (sourcenode a) (?WOD_BS) = {})"
        by auto
      with \<open>obs n' (?WOD_BS) = {n'}\<close> True \<open>valid_edge a\<close> show ?thesis
        apply(rule_tac x="a" in exI)
        apply(rule_tac x="[]" in exI)
        apply(rule_tac x="[]" in exI)
        by(auto intro!:empty_path)
    next
      case False
      hence "as \<noteq> []" .
      from \<open>n'' -as\<rightarrow>* n'\<close> \<open>\<forall>n'\<in>set (sourcenodes as). n' \<notin> (?WOD_BS)\<close> 
      have "obs n' (?WOD_BS) \<subseteq> obs n'' (?WOD_BS)" by(rule path_obs_subset)
      show ?thesis
      proof(cases "obs n' (?WOD_BS) = obs n'' (?WOD_BS)")
        case True
        with \<open>n'' -as\<rightarrow>* n'\<close> \<open>valid_edge a\<close> \<open>obs n' (?WOD_BS) = {n'}\<close> more_than_one
        show ?thesis
          apply(rule_tac x="a" in exI)
          apply(rule_tac x="[]" in exI)
          apply(rule_tac x="as" in exI)
          by(fastforce intro:empty_path)
      next
        case False
        with \<open>obs n' (?WOD_BS) \<subseteq> obs n'' (?WOD_BS)\<close>
        have "obs n' (?WOD_BS) \<subset> obs n'' (?WOD_BS)" by simp
        with \<open>obs n' (?WOD_BS) = {n'}\<close> obtain ni where "n' \<in> obs n'' (?WOD_BS)"
          and "ni \<in> obs n'' (?WOD_BS)" and "n' \<noteq> ni" by auto
        from IH[OF this \<open>obs n' (?WOD_BS) = {n'}\<close> 
          \<open>\<forall>n'\<in>set (sourcenodes as). n' \<notin> (?WOD_BS)\<close> \<open>as \<noteq> []\<close>] obtain a' as' as''
          where "n'' -as'\<rightarrow>* sourcenode a'" and "targetnode a' -as''\<rightarrow>* n'"
          and "valid_edge a'" and [simp]:"as = as'@a'#as''" 
          and "obs (targetnode a') (?WOD_BS) = {n'}"
          and more_than_one':"\<not> (\<exists>m. obs (sourcenode a') (?WOD_BS) = {m} \<or> 
          obs (sourcenode a') (?WOD_BS) = {})"
          by blast
        from \<open>n'' -as'\<rightarrow>* sourcenode a'\<close> \<open>valid_edge a\<close>
        have "n -a#as'\<rightarrow>* sourcenode a'" by(fastforce intro:path.Cons_path)
        with \<open>targetnode a' -as''\<rightarrow>* n'\<close> \<open>obs (targetnode a') (?WOD_BS) = {n'}\<close>
          more_than_one' \<open>valid_edge a'\<close> show ?thesis
          apply(rule_tac x="a'" in exI)
          apply(rule_tac x="a#as'" in exI)
          apply(rule_tac x="as''" in exI)
          by fastforce
      qed
    qed
  qed simp
  then obtain a as' as'' where "valid_edge a"
    and "obs (targetnode a) (?WOD_BS) = {nx}"
    and more_than_one:"\<not> (\<exists>m. obs (sourcenode a) (?WOD_BS) = {m} \<or> 
                         obs (sourcenode a) (?WOD_BS) = {})"
    by blast
  have "sourcenode a \<notin> (?WOD_BS)"
  proof(rule ccontr)
    assume "\<not> sourcenode a \<notin> ?WOD_BS"
    hence "sourcenode a \<in> ?WOD_BS" by simp
    with \<open>valid_edge a\<close> have "obs (sourcenode a) (?WOD_BS) = {sourcenode a}"
      by(fastforce intro!:n_in_obs)
    with more_than_one show False by simp
  qed
  with \<open>valid_edge a\<close> 
  have "obs (targetnode a) (?WOD_BS) \<subseteq> obs (sourcenode a) (?WOD_BS)"
    by(rule edge_obs_subset)
  with \<open>obs (targetnode a) (?WOD_BS) = {nx}\<close> 
  have "nx \<in> obs (sourcenode a) (?WOD_BS)" by simp
  with more_than_one obtain m  where "m \<in> obs (sourcenode a) (?WOD_BS)"
    and "nx \<noteq> m" by auto
  with \<open>nx \<in> obs (sourcenode a) (?WOD_BS)\<close> obtain as2 
    where "sourcenode a -as2\<rightarrow>* m" and "nx \<notin> set(sourcenodes as2)" 
    by(fastforce elim:obsE)
  from \<open>nx \<in> obs (sourcenode a) (?WOD_BS)\<close> \<open>m \<in> obs (sourcenode a) (?WOD_BS)\<close> 
  obtain as1 where "sourcenode a -as1\<rightarrow>* nx" and "m \<notin> set(sourcenodes as1)"
    by(fastforce elim:obsE)
  from \<open>obs (targetnode a) (?WOD_BS) = {nx}\<close> obtain asx 
    where "targetnode a -asx\<rightarrow>* nx" by(fastforce elim:obsE)
  have "\<forall>asx'. targetnode a -asx'\<rightarrow>* m \<longrightarrow> nx \<in> set(sourcenodes asx')"
  proof(rule ccontr)
    assume "\<not> (\<forall>asx'. targetnode a -asx'\<rightarrow>* m \<longrightarrow> nx \<in> set (sourcenodes asx'))"
    then obtain asx' where "targetnode a -asx'\<rightarrow>* m" and "nx \<notin> set (sourcenodes asx')"
      by blast
    show False
    proof(cases "\<forall>nx \<in> set(sourcenodes asx'). nx \<notin> ?WOD_BS")
      case True
      with \<open>targetnode a -asx'\<rightarrow>* m\<close> \<open>m \<in> obs (sourcenode a) (?WOD_BS)\<close> 
      have "m \<in> obs (targetnode a) ?WOD_BS" by(fastforce intro:obs_elem elim:obsE)
      with \<open>nx \<noteq> m\<close> \<open>obs (targetnode a) (?WOD_BS) = {nx}\<close> show False by simp
    next
      case False
      hence "\<exists>nx \<in> set(sourcenodes asx'). nx \<in> ?WOD_BS" by blast
      then obtain nx' ns ns' where "sourcenodes asx' = ns@nx'#ns'" and "nx' \<in> ?WOD_BS"
        and "\<forall>nx \<in> set ns. nx \<notin> ?WOD_BS" by(fastforce elim!:split_list_first_propE)
      from \<open>sourcenodes asx' = ns@nx'#ns'\<close> obtain ax ai ai' 
        where [simp]:"asx' = ai@ax#ai'" "ns = sourcenodes ai" "nx' = sourcenode ax"
        by(fastforce elim:map_append_append_maps simp:sourcenodes_def)
      from \<open>targetnode a -asx'\<rightarrow>* m\<close> have "targetnode a -ai\<rightarrow>* sourcenode ax"
        by(fastforce dest:path_split)
      with \<open>nx' \<in> ?WOD_BS\<close> \<open>\<forall>nx \<in> set ns. nx \<notin> ?WOD_BS\<close> 
      have "nx' \<in> obs (targetnode a) ?WOD_BS" by(fastforce intro:obs_elem)
      with \<open>obs (targetnode a) (?WOD_BS) = {nx}\<close> have "nx' = nx" by simp
      with \<open>nx \<notin> set (sourcenodes asx')\<close> show False by(simp add:sourcenodes_def)
    qed
  qed
  with \<open>nx \<noteq> m\<close> \<open>sourcenode a -as1\<rightarrow>* nx\<close> \<open>m \<notin> set(sourcenodes as1)\<close> 
    \<open>sourcenode a -as2\<rightarrow>* m\<close> \<open>nx \<notin> set(sourcenodes as2)\<close> \<open>valid_edge a\<close> 
    \<open>targetnode a -asx\<rightarrow>* nx\<close>
  have "sourcenode a \<longrightarrow>\<^sub>w\<^sub>o\<^sub>d nx,m" by(simp add:wod_def,blast)
  with \<open>nx \<in> obs (sourcenode a) (?WOD_BS)\<close> \<open>m \<in> obs (sourcenode a) (?WOD_BS)\<close> 
  have "sourcenode a \<in> ?WOD_BS" by(fastforce elim:cd_closed elim:obsE)
  with \<open>sourcenode a \<notin> ?WOD_BS\<close> show False by simp
qed


lemma WODBackwardSliceCorrect:
  "BackwardSlice sourcenode targetnode kind valid_edge
        (_Entry_) Def Use state_val wod_backward_slice"
proof(unfold_locales)
  fix n S assume "n \<in> wod_backward_slice S"
  thus "valid_node n" by(rule wod_backward_slice_valid_node)
next
  fix n S assume "valid_node n" and "n \<in> S"
  thus "n \<in> wod_backward_slice S" by(rule refl)
next
  fix n' S n V assume "n' \<in> wod_backward_slice S" "n influences V in n'"
  thus "n \<in> wod_backward_slice S"
    by -(rule dd_closed)
next
  fix n S
  have "(\<exists>m. obs n (wod_backward_slice S) = {m}) \<or> 
    obs n (wod_backward_slice S) = {}" 
    by(rule obs_singleton)
  thus "finite (obs n (wod_backward_slice S))" by fastforce
next
  fix n S 
  have "(\<exists>m. obs n (wod_backward_slice S) = {m}) \<or> obs n (wod_backward_slice S) = {}" 
    by(rule obs_singleton)
  thus "card (obs n (wod_backward_slice S)) \<le> 1" by fastforce
qed

end

end
