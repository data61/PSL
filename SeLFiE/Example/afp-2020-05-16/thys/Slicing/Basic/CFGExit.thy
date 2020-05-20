theory CFGExit imports CFG begin

subsection \<open>Adds an exit node to the abstract CFG\<close>

locale CFGExit = CFG sourcenode targetnode kind valid_edge Entry
  for sourcenode :: "'edge \<Rightarrow> 'node" and targetnode :: "'edge \<Rightarrow> 'node"
  and kind :: "'edge \<Rightarrow> 'state edge_kind" and valid_edge :: "'edge \<Rightarrow> bool"
  and Entry :: "'node" ("'('_Entry'_')") + 
  fixes Exit::"'node"  ("'('_Exit'_')")
  assumes Exit_source [dest]: "\<lbrakk>valid_edge a; sourcenode a = (_Exit_)\<rbrakk> \<Longrightarrow> False"
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

lemma path_Exit_source [dest]:
  assumes "(_Exit_) -as\<rightarrow>* n'" shows "n' = (_Exit_)" and "as = []"
  using \<open>(_Exit_) -as\<rightarrow>* n'\<close>
proof(induct n\<equiv>"(_Exit_)" as n' rule:path.induct)
  case (Cons_path n'' as n' a)
  from \<open>sourcenode a = (_Exit_)\<close> \<open>valid_edge a\<close> have False 
    by -(rule Exit_source,simp_all)
  { case 1 with \<open>False\<close> show ?case ..
  next
    case 2 with \<open>False\<close> show ?case ..
  }
qed simp_all

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


end 

end
