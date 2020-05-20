section \<open>Dynamic Standard Control Dependence\<close>

theory DynStandardControlDependence imports Postdomination begin

context Postdomination begin

definition
  dyn_standard_control_dependence :: "'node \<Rightarrow> 'node \<Rightarrow> 'edge list \<Rightarrow> bool"
  ("_ controls\<^sub>s _ via _" [51,0,0])
where dyn_standard_control_dependence_def:"n controls\<^sub>s n' via as \<equiv> 
    (\<exists>a a' as'. (as = a#as') \<and> (n' \<notin> set(sourcenodes as)) \<and> (n -as\<rightarrow>* n') \<and>
                   (n' postdominates (targetnode a)) \<and>
                   (valid_edge a') \<and> (sourcenode a' = n) \<and> 
                   (\<not> n' postdominates (targetnode a')))"


lemma Exit_not_dyn_standard_control_dependent:
  assumes control:"n controls\<^sub>s (_Exit_) via as" shows "False"
proof -
  from control obtain a as' where path:"n -as\<rightarrow>* (_Exit_)" and as:"as = a#as'"
    and pd:"(_Exit_) postdominates (targetnode a)" 
    by(auto simp:dyn_standard_control_dependence_def)
  from path as have "n -[]@a#as'\<rightarrow>* (_Exit_)" by simp
  hence "valid_edge a" by(fastforce dest:path_split)
  with pd show False by -(rule Exit_no_postdominator,auto)
qed


lemma dyn_standard_control_dependence_def_variant:
  "n controls\<^sub>s n' via as = ((n -as\<rightarrow>* n') \<and> (n \<noteq> n') \<and>
    (\<not> n' postdominates n) \<and> (n' \<notin> set(sourcenodes as)) \<and>
  (\<forall>n'' \<in> set(targetnodes as). n' postdominates n''))"
proof
  assume "(n -as\<rightarrow>* n') \<and> (n \<noteq> n') \<and> (\<not> n' postdominates n) \<and> 
    (n' \<notin> set(sourcenodes as)) \<and>
    (\<forall>n''\<in>set (targetnodes as). n' postdominates n'')"
  hence path:"n -as\<rightarrow>* n'" and noteq:"n \<noteq> n'"
    and not_pd:"\<not> n' postdominates n"
    and notin:"n' \<notin> set(sourcenodes as)"
    and all:"\<forall>n''\<in>set (targetnodes as). n' postdominates n''"
    by auto
  have notExit:"n \<noteq> (_Exit_)"
  proof
    assume "n = (_Exit_)"
    with path have "n = n'" by(fastforce dest:path_Exit_source)
    with noteq show False by simp
  qed
  from path have valid:"valid_node n" and valid':"valid_node n'"
    by(auto dest:path_valid_node)
  show "n controls\<^sub>s n' via as"
  proof(cases as)
    case Nil    
    with path valid not_pd notExit have False 
      by(fastforce elim:path.cases dest:postdominate_refl)
    thus ?thesis by simp
  next
    case (Cons ax asx)
    with all have pd:"n' postdominates targetnode ax"
      by(auto simp:targetnodes_def)
    from path Cons have source:"n = sourcenode ax" 
      and path2:"targetnode ax -asx\<rightarrow>* n'"
      by(auto intro:path_split_Cons)
    show ?thesis
    proof(cases "\<exists>as'. n -as'\<rightarrow>* (_Exit_)")
      case True
      with not_pd valid valid' obtain as' where path':"n -as'\<rightarrow>* (_Exit_)"
        and not_isin:"n' \<notin> set (sourcenodes as')"
        by(auto simp:postdominate_def)
      have "as' \<noteq> []"
      proof
        assume "as' = []"
        with path' have "n = (_Exit_)" by(auto elim:path.cases)
        with notExit show False by simp
      qed
      then obtain a' as'' where as':"as' = a'#as''"
        by(cases as',auto elim:path.cases)
      with path' have "n -[]@a'#as''\<rightarrow>* (_Exit_)" by simp
      hence source':"n = sourcenode a'" 
        and valid_edge:"valid_edge a'"
        and path2':"targetnode a' -as''\<rightarrow>* (_Exit_)"
        by(fastforce dest:path_split)+
      from path2' not_isin as' valid'
      have "\<not> n' postdominates (targetnode a')"
        by(auto simp:postdominate_def sourcenodes_def)
      with pd path Cons source source' notin valid_edge show ?thesis
        by(auto simp:dyn_standard_control_dependence_def)
    next
      case False
      with valid valid' have "n' postdominates n"
        by(auto simp:postdominate_def)
      with not_pd have False by simp
      thus ?thesis by simp
    qed
  qed
next
  assume "n controls\<^sub>s n' via as"
  then obtain a nx a' nx' as' where notin:"n' \<notin> set(sourcenodes as)"
    and path:"n -as\<rightarrow>* n'" and as:"as = a#as'" and valid_edge:"valid_edge a'"
    and pd:"n' postdominates (targetnode a)"
    and source':"sourcenode a' = n"
    and not_pd:"\<not> n' postdominates (targetnode a')"
    by(auto simp:dyn_standard_control_dependence_def)
  from path as have source:"sourcenode a = n" by(auto elim:path.cases)
  from path as have notExit:"n \<noteq> (_Exit_)" by(auto elim:path.cases)
  from path have valid:"valid_node n" and valid':"valid_node n'"
    by(auto dest:path_valid_node)
  from notin as source have noteq:"n \<noteq> n'"
    by(fastforce simp:sourcenodes_def)
  from valid_edge have valid_target':"valid_node (targetnode a')"
    by(fastforce simp:valid_node_def)
  { assume pd':"n' postdominates n"
    hence all:"\<forall>as. n -as\<rightarrow>* (_Exit_) \<longrightarrow> n' \<in> set (sourcenodes as)"
      by(auto simp:postdominate_def)
    from not_pd valid' valid_target' obtain as' 
      where "targetnode a' -as'\<rightarrow>* (_Exit_)"
      by(auto simp:postdominate_def)
    with source' valid_edge have path':"n -a'#as'\<rightarrow>* (_Exit_)"
      by(fastforce intro:Cons_path)
    with all have "n' \<in> set (sourcenodes (a'#as'))" by blast
    with source' have "n' = n \<or> n' \<in> set (sourcenodes as')"
      by(fastforce simp:sourcenodes_def)
    hence False
    proof
      assume "n' = n"
      with noteq show ?thesis by simp
    next
      assume isin:"n' \<in> set (sourcenodes as')"
      from path' have path2:"targetnode a' -as'\<rightarrow>* (_Exit_)"
        by(fastforce elim:path_split_Cons)
      thus ?thesis
      proof(cases "as' = []")
        case True
        with path2 have "targetnode a' = (_Exit_)" by(auto elim:path.cases)
        with valid_edge all source' have "n' = n"
          by(fastforce dest:path_edge simp:sourcenodes_def)
        with noteq show ?thesis by simp
      next
        case False
        from path2 not_pd valid' valid_edge obtain as''
          where path'':"targetnode a' -as''\<rightarrow>* (_Exit_)"
          and notin:"n' \<notin> set (sourcenodes as'')"
          by(auto simp:postdominate_def)
        from valid_edge path'' have "sourcenode a' -a'#as''\<rightarrow>* (_Exit_)"
          by(fastforce intro:Cons_path)
        with all source' have "n' \<in> set (sourcenodes ([a']@as''))" by simp
        with source' have "n' = n \<or> n' \<in> set (sourcenodes as'')"
          by(auto simp:sourcenodes_def)
        thus ?thesis
        proof
          assume "n' = n"
          with noteq show ?thesis by simp
        next
          assume "n' \<in> set (sourcenodes as'')"
          with notin show ?thesis by simp
        qed
      qed
    qed }
  hence not_pd':"\<not> n' postdominates n" by blast
  { fix n'' assume "n'' \<in> set (targetnodes as)"
    with as source have "n'' = targetnode a \<or> n'' \<in> set (targetnodes as')" 
      by(auto simp:targetnodes_def)
    hence "n' postdominates n''"
    proof
      assume "n'' = targetnode a"
      with pd show ?thesis by simp
    next
      assume isin:"n'' \<in> set (targetnodes as')"
      hence "\<exists>ni \<in> set (targetnodes as'). ni = n''" by simp
      then obtain ns ns' where targets:"targetnodes as' = ns@n''#ns'"
        and all_noteq:"\<forall>ni \<in> set ns'. ni \<noteq> n''"
        by(fastforce elim!:rightmost_element_property)
      from targets obtain xs ax ys where ys:"ns' = targetnodes ys"
        and as':"as' = xs@ax#ys" and target'':"targetnode ax = n''"
        by(fastforce elim:map_append_append_maps simp:targetnodes_def)
      from all_noteq ys have notin_target:"n'' \<notin> set(targetnodes ys)"
        by auto
      from path as have "n -[]@a#as'\<rightarrow>* n'" by simp
      hence "targetnode a -as'\<rightarrow>* n'" 
        by(fastforce dest:path_split)
      with isin have path':"targetnode a -as'\<rightarrow>* n'"
        by(fastforce split:if_split_asm simp:targetnodes_def)
      with as' target'' have path1:"targetnode a -xs\<rightarrow>* sourcenode ax"
        and valid_edge':"valid_edge ax"
        and path2:"n'' -ys\<rightarrow>* n'"
        by(auto intro:path_split)
      from valid_edge' have "sourcenode ax -[ax]\<rightarrow>* targetnode ax" by(rule path_edge)
      with path1 target'' have path_n'':"targetnode a -xs@[ax]\<rightarrow>* n''"
        by(fastforce intro:path_Append)
      from notin as as' have notin':"n'\<notin> set (sourcenodes (xs@[ax]))"
        by(simp add:sourcenodes_def)
      show ?thesis
      proof(rule ccontr)
        assume "\<not> n' postdominates n''"
        with valid' target'' valid_edge' obtain asx' 
          where Exit_path:"n'' -asx'\<rightarrow>* (_Exit_)"
          and notin'':"n' \<notin> set(sourcenodes asx')" by(auto simp:postdominate_def)
        from path_n'' Exit_path
        have Exit_path':"targetnode a -(xs@[ax])@asx'\<rightarrow>* (_Exit_)"
          by(fastforce intro:path_Append)
        from notin' notin'' have "n' \<notin> set(sourcenodes (xs@ax#asx'))"
          by(simp add:sourcenodes_def)
        with pd Exit_path' show False by(simp add:postdominate_def)
      qed
    qed }
  with path not_pd' notin noteq show "(n -as\<rightarrow>* n') \<and> (n \<noteq> n') \<and>
    (\<not> n' postdominates n) \<and> (n' \<notin> set(sourcenodes as)) \<and>
    (\<forall>n'' \<in> set(targetnodes as). n' postdominates n'')" by blast
qed


lemma which_node_dyn_standard_control_dependence_source:
  assumes path:"(_Entry_) -as@a#as'\<rightarrow>* n"
  and Exit_path:"n -as''\<rightarrow>* (_Exit_)" and source:"sourcenode a = n'" 
  and source':"sourcenode a' = n'"
  and no_source:"n \<notin> set(sourcenodes (a#as'))" and valid_edge':"valid_edge a'"
  and inner_node:"inner_node n" and not_pd:"\<not> n postdominates (targetnode a')"
  and last:"\<forall>ax ax'. ax \<in> set as' \<and> sourcenode ax = sourcenode ax' \<and>
    valid_edge ax' \<longrightarrow> n postdominates targetnode ax'"
  shows "n' controls\<^sub>s n via a#as'"
proof -
  from path source have path_n'n:"n' -a#as'\<rightarrow>* n" by(fastforce dest:path_split_second)
  from path have valid_edge:"valid_edge a" by(fastforce intro:path_split)
  show ?thesis
  proof(cases "n postdominates (targetnode a)")
    case True
    with path_n'n not_pd no_source source source' valid_edge' show ?thesis
      by(auto simp:dyn_standard_control_dependence_def)
  next
    case False
    hence not_pd':"\<not> n postdominates (targetnode a)" .
    show ?thesis
    proof(cases "as' = []")
      case True
      with path_n'n have "targetnode a = n" by(fastforce elim:path.cases)
      with inner_node have "n postdominates (targetnode a)"
        by(cases "n = (_Exit_)",auto intro:postdominate_refl simp:inner_node_def)
      with not_pd path_n'n no_source source source' valid_edge' show ?thesis
        by(fastforce simp:dyn_standard_control_dependence_def)
    next
      case False
      hence notempty':"as' \<noteq> []" .
      with path have path_nxn:"targetnode a -as'\<rightarrow>* n"
        by(fastforce dest:path_split)
      from Exit_path path_nxn have "\<exists>as. targetnode a -as\<rightarrow>* (_Exit_)"
        by(fastforce dest:path_Append)
      with not_pd' inner_node valid_edge obtain asx 
        where path_Exit:"targetnode a -asx\<rightarrow>* (_Exit_)" 
        and notin:"n \<notin> set (sourcenodes asx)"
        by(auto simp:postdominate_def inner_is_valid)
      show ?thesis
      proof(cases "\<exists>asx'. asx = as'@asx'")
        case True
        then obtain asx' where asx:"asx = as'@asx'" by blast
        from path notempty' have "targetnode a -as'\<rightarrow>* n"
          by(fastforce dest:path_split)
        with path_Exit inner_node asx notempty'
        obtain a'' as'' where "asx' = a''#as'' \<and> sourcenode a'' = n"
          apply(cases asx')
           apply(fastforce dest:path_det)
          by(fastforce dest:path_split path_det)
        with asx have "n \<in> set(sourcenodes asx)" by(simp add:sourcenodes_def)
        with notin have False by simp
        thus ?thesis by simp
      next
        case False
        hence all:"\<forall>asx'. asx \<noteq> as'@asx'" by simp
        then obtain j asx' where asx:"asx = (take j as')@asx'"
          and length:"j < length as'"
          and not_more:"\<forall>k > j. \<forall>asx''. asx \<noteq> (take k as')@asx''"
          by(auto elim:path_split_general)
        from asx length have "\<exists>as'1 as'2. asx = as'1@asx' \<and> 
          as' = as'1@as'2 \<and> as'2 \<noteq> [] \<and> as'1 = take j as'"
          by simp(rule_tac x= "drop j as'" in exI,simp)
        then obtain as'1 as'' where asx:"asx = as'1@asx'"
          and take:"as'1 = take j as'"
          and x:"as' = as'1@as''" and x':"as'' \<noteq> []" by blast
        from x x' obtain a1 as'2 where as':"as' = as'1@a1#as'2" and "as'' = a1#as'2"
          by(cases as'') auto
        have notempty_x':"asx' \<noteq> []"
        proof(cases "asx' = []")
          case True
          with asx as' have "as' = asx@a1#as'2" by simp
          with path_n'n have "n' -(a#asx)@a1#as'2\<rightarrow>* n"
            by simp
          hence "n' -a#asx\<rightarrow>* sourcenode a1"
            and valid_edge1:"valid_edge a1" by(fastforce elim:path_split)+
          hence "targetnode a -asx\<rightarrow>* sourcenode a1"
            by(fastforce intro:path_split_Cons)
          with path_Exit have "(_Exit_) = sourcenode a1" by(rule path_det)
          from this[THEN sym] valid_edge1 have False by -(rule Exit_source,simp_all)
          thus ?thesis by simp
        qed simp
        with asx obtain a2 asx'1 
          where asx:"asx = as'1@a2#asx'1"
          and asx':"asx' = a2#asx'1" by(cases asx') auto
        from path_n'n as' have "n' -(a#as'1)@a1#as'2\<rightarrow>* n" by simp
        hence "n' -a#as'1\<rightarrow>* sourcenode a1" and valid_edge1:"valid_edge a1"
          by(fastforce elim:path_split)+
        hence path1:"targetnode a -as'1\<rightarrow>* sourcenode a1"
          by(fastforce intro:path_split_Cons)
        from path_Exit asx
        have "targetnode a -as'1\<rightarrow>* sourcenode a2"
          and valid_edge2:"valid_edge a2"
          and path2:"targetnode a2 -asx'1\<rightarrow>* (_Exit_)"
          by(auto intro:path_split)
        with path1 have eq12:"sourcenode a1 = sourcenode a2"
          by(cases as'1,auto dest:path_det)
        from asx notin have "n \<notin> set (sourcenodes asx'1)"
          by(simp add:sourcenodes_def)
        with path2 have not_pd'2:"\<not> n postdominates targetnode a2"
          by(cases "asx'1 = []",auto simp:postdominate_def)
        from as' have "a1 \<in> set as'" by simp
        with eq12 last valid_edge2 have "n postdominates targetnode a2" by blast
        with not_pd'2 have False by simp
        thus ?thesis by simp
      qed
    qed
  qed
qed


lemma inner_node_dyn_standard_control_dependence_predecessor:
  assumes inner_node:"inner_node n"
  obtains n' as where "n' controls\<^sub>s n via as"
proof(atomize_elim)
  from inner_node obtain as' where pathExit:"n -as'\<rightarrow>* (_Exit_)"
    by(fastforce dest:inner_is_valid Exit_path)
  from inner_node obtain as where pathEntry:"(_Entry_) -as\<rightarrow>* n"
    by(fastforce dest:inner_is_valid Entry_path)
  with inner_node have notEmpty:"as \<noteq> []" 
    by(auto elim:path.cases simp:inner_node_def)
  have "\<exists>a asx. (_Entry_) -a#asx\<rightarrow>* n \<and> n \<notin> set (sourcenodes (a#asx))"
  proof(cases "n \<in> set (sourcenodes as)")
    case True
    hence "\<exists>n'' \<in> set(sourcenodes as). n = n''" by simp
    then obtain ns' ns'' where nodes:"sourcenodes as = ns'@n#ns''"
      and notin:"\<forall>n'' \<in> set ns'. n \<noteq> n''"
      by(fastforce elim!:split_list_first_propE)
    from nodes obtain xs ys a'
      where xs:"sourcenodes xs = ns'" and as:"as = xs@a'#ys"
      and source:"sourcenode a' = n"
      by(fastforce elim:map_append_append_maps simp:sourcenodes_def)
    from pathEntry as have "(_Entry_) -xs@a'#ys\<rightarrow>* n" by simp
    hence path2:"(_Entry_) -xs\<rightarrow>* sourcenode a'"
      by(fastforce dest:path_split)
    show ?thesis
    proof(cases "xs = []")
      case True
      with path2 have "(_Entry_) = sourcenode a'" by(auto elim:path.cases)
      with pathEntry source notEmpty have "(_Entry_) -as\<rightarrow>* (_Entry_) \<and> as \<noteq> []"
        by(auto elim:path.cases)
      hence False by(fastforce dest:path_Entry_target)
      thus ?thesis by simp
    next
      case False
      then obtain n a'' xs' where "xs = a''#xs'" by(cases xs) auto
      with False path2 notin xs source show ?thesis by simp blast
    qed
  next
    case False
    from notEmpty obtain a as' where "as = a#as'" by (cases as) auto
    with False pathEntry show ?thesis by auto
  qed
  then obtain a asx where pathEntry':"(_Entry_) -a#asx\<rightarrow>* n"
    and notin:"n \<notin> set (sourcenodes (a#asx))" by blast
  show "\<exists>n' as. n' controls\<^sub>s n via as"
  proof(cases "\<forall>a' a''. a' \<in> set asx \<and> sourcenode a' = sourcenode a'' \<and> 
      valid_edge a'' \<longrightarrow> n postdominates targetnode a''")
    case True
    from inner_node have not_pd:"\<not> n postdominates (_Exit_)" 
      by(fastforce intro:empty_path simp:postdominate_def sourcenodes_def)
    from pathEntry' have path':"(_Entry_) -[]@a#asx\<rightarrow>* n" by simp
    hence eq:"sourcenode a = (_Entry_)"
      by(fastforce dest:path_split elim:path.cases)
    from Entry_Exit_edge obtain a' where "sourcenode a' = (_Entry_)"
      and "targetnode a' = (_Exit_)" and "valid_edge a'" by auto
    with path' inner_node not_pd True eq notin pathExit
    have "sourcenode a controls\<^sub>s n via a#asx"
      by -(erule which_node_dyn_standard_control_dependence_source,auto)
    thus ?thesis by blast
  next
    case False
    hence "\<exists>a' \<in> set asx. \<exists>a''. sourcenode a' = sourcenode a'' \<and> valid_edge a'' \<and>
      \<not> n postdominates targetnode a''"
      by fastforce
    then obtain ax asx' asx'' where "asx = asx'@ax#asx'' \<and>
      (\<exists>a''. sourcenode ax = sourcenode a'' \<and> valid_edge a'' \<and>
      \<not> n postdominates targetnode a'') \<and>
      (\<forall>z \<in> set asx''. \<not> (\<exists>a''. sourcenode z = sourcenode a'' \<and> valid_edge a'' \<and>
      \<not> n postdominates targetnode a''))"
      by(blast elim!:rightmost_element_property)
    then obtain a'' where as':"asx = asx'@ax#asx''"
      and eq:"sourcenode ax = sourcenode a''"
      and valid_edge:"valid_edge a''"
      and not_pd:"\<not> n postdominates targetnode a''"
      and last:"\<forall>z \<in> set asx''. \<not> (\<exists>a''. sourcenode z = sourcenode a'' \<and> 
        valid_edge a'' \<and> \<not> n postdominates targetnode a'')"
      by blast
    from notin as' have notin':"n \<notin> set (sourcenodes (ax#asx''))"
      by(auto simp:sourcenodes_def)
    from as' pathEntry' have "(_Entry_) -(a#asx')@ax#asx''\<rightarrow>* n" by simp
    with inner_node not_pd notin' eq last pathExit valid_edge
    have "sourcenode ax controls\<^sub>s n via ax#asx''"
      by(fastforce elim!:which_node_dyn_standard_control_dependence_source)
    thus ?thesis by blast
  qed
qed


end

end
