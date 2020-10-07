section \<open>Relations between control dependences\<close>

theory ControlDependenceRelations 
  imports WeakOrderDependence StandardControlDependence 
begin

context StrongPostdomination begin

lemma standard_control_implies_weak_order: 
  assumes "n controls\<^sub>s n'" shows "n \<longrightarrow>\<^sub>w\<^sub>o\<^sub>d n',(_Exit_)"
proof -
  from \<open>n controls\<^sub>s n'\<close> obtain as a a' as' where "as = a#as'"
    and "n' \<notin> set(sourcenodes as)" and "n -as\<rightarrow>* n'"
    and "n' postdominates (targetnode a)"
    and "valid_edge a'" and "sourcenode a' = n"
    and "\<not> n' postdominates (targetnode a')" 
    by(auto simp:standard_control_dependence_def)
  from \<open>n -as\<rightarrow>* n'\<close> \<open>as = a#as'\<close> have "sourcenode a = n" by(auto elim:path.cases)
  from \<open>n -as\<rightarrow>* n'\<close> \<open>as = a#as'\<close> \<open>n' \<notin> set(sourcenodes as)\<close> have "n \<noteq> n'"
    by(induct rule:path.induct,auto simp:sourcenodes_def)
  from \<open>n -as\<rightarrow>* n'\<close> \<open>as = a#as'\<close> have "valid_edge a"
    by(auto elim:path.cases)
  from \<open>n controls\<^sub>s n'\<close> have "n' \<noteq> (_Exit_)"
    by(fastforce dest:Exit_not_standard_control_dependent)
  from \<open>n -as\<rightarrow>* n'\<close> have "(_Exit_) \<notin> set (sourcenodes as)" by fastforce
  from \<open>n -as\<rightarrow>* n'\<close> have "valid_node n" and "valid_node n'"
    by(auto dest:path_valid_node)
  with \<open>\<not> n' postdominates (targetnode a')\<close> \<open>valid_edge a'\<close>
  obtain asx where "targetnode a' -asx\<rightarrow>* (_Exit_)" and "n' \<notin> set(sourcenodes asx)"
    by(auto simp:postdominate_def)
  with \<open>valid_edge a'\<close> \<open>sourcenode a' = n\<close> have "n -a'#asx\<rightarrow>* (_Exit_)"
    by(fastforce intro:Cons_path)
  with \<open>n \<noteq> n'\<close> \<open>sourcenode a' = n\<close> \<open>n' \<notin> set(sourcenodes asx)\<close>
  have "n' \<notin> set(sourcenodes (a'#asx))" by(simp add:sourcenodes_def)
  from \<open>n' postdominates (targetnode a)\<close> 
  obtain asx' where "targetnode a -asx'\<rightarrow>* n'" by(erule postdominate_implies_path)
  from \<open>n' postdominates (targetnode a)\<close>
  have "\<forall>as'. targetnode a -as'\<rightarrow>* (_Exit_) \<longrightarrow> n' \<in> set(sourcenodes as')"
    by(auto simp:postdominate_def)
  with \<open>n' \<noteq> (_Exit_)\<close> \<open>n -as\<rightarrow>* n'\<close> \<open>(_Exit_) \<notin> set (sourcenodes as)\<close>
    \<open>n -a'#asx\<rightarrow>* (_Exit_)\<close> \<open>n' \<notin> set(sourcenodes (a'#asx))\<close>
    \<open>valid_edge a\<close> \<open>sourcenode a = n\<close> \<open>targetnode a -asx'\<rightarrow>* n'\<close>
  show ?thesis by(auto simp:wod_def)
qed

end

end
