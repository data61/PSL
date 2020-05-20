section \<open>CFG\<close>

theory CFG imports BasicDefs begin

subsection \<open>The abstract CFG\<close>

locale CFG =
  fixes sourcenode :: "'edge \<Rightarrow> 'node"
  fixes targetnode :: "'edge \<Rightarrow> 'node"
  fixes kind :: "'edge \<Rightarrow> 'state edge_kind"
  fixes valid_edge :: "'edge \<Rightarrow> bool"
  fixes Entry::"'node" ("'('_Entry'_')")
  assumes Entry_target [dest]: "\<lbrakk>valid_edge a; targetnode a = (_Entry_)\<rbrakk> \<Longrightarrow> False"
  and edge_det: 
  "\<lbrakk>valid_edge a; valid_edge a'; sourcenode a = sourcenode a'; 
    targetnode a = targetnode a'\<rbrakk> \<Longrightarrow> a = a'"

begin

definition valid_node :: "'node \<Rightarrow> bool"
  where "valid_node n \<equiv> 
  (\<exists>a. valid_edge a \<and> (n = sourcenode a \<or> n = targetnode a))"

lemma [simp]: "valid_edge a \<Longrightarrow> valid_node (sourcenode a)"
  by(fastforce simp:valid_node_def)

lemma [simp]: "valid_edge a \<Longrightarrow> valid_node (targetnode a)"
  by(fastforce simp:valid_node_def)


subsection \<open>CFG paths and lemmas\<close>

inductive path :: "'node \<Rightarrow> 'edge list \<Rightarrow> 'node \<Rightarrow> bool"
  ("_ -_\<rightarrow>* _" [51,0,0] 80)
where 
  empty_path:"valid_node n \<Longrightarrow> n -[]\<rightarrow>* n"

  | Cons_path:
  "\<lbrakk>n'' -as\<rightarrow>* n'; valid_edge a; sourcenode a = n; targetnode a = n''\<rbrakk>
    \<Longrightarrow> n -a#as\<rightarrow>* n'"


lemma path_valid_node:
  assumes "n -as\<rightarrow>* n'" shows "valid_node n" and "valid_node n'"
  using \<open>n -as\<rightarrow>* n'\<close>
  by(induct rule:path.induct,auto)

lemma empty_path_nodes [dest]:"n -[]\<rightarrow>* n' \<Longrightarrow> n = n'"
  by(fastforce elim:path.cases)

lemma path_valid_edges:"n -as\<rightarrow>* n' \<Longrightarrow> \<forall>a \<in> set as. valid_edge a"
by(induct rule:path.induct) auto


lemma path_edge:"valid_edge a \<Longrightarrow> sourcenode a -[a]\<rightarrow>* targetnode a"
  by(fastforce intro:Cons_path empty_path)


lemma path_Entry_target [dest]:
  assumes "n -as\<rightarrow>* (_Entry_)"
  shows "n = (_Entry_)" and "as = []"
using \<open>n -as\<rightarrow>* (_Entry_)\<close>
proof(induct n as n'\<equiv>"(_Entry_)" rule:path.induct)
  case (Cons_path n'' as a n)
  from \<open>targetnode a = n''\<close> \<open>valid_edge a\<close> \<open>n'' = (_Entry_)\<close> have False
    by -(rule Entry_target,simp_all)
  { case 1
    with \<open>False\<close> show ?case ..
  next
    case 2
    with \<open>False\<close> show ?case ..
  }
qed simp_all



lemma path_Append:"\<lbrakk>n -as\<rightarrow>* n''; n'' -as'\<rightarrow>* n'\<rbrakk> 
  \<Longrightarrow> n -as@as'\<rightarrow>* n'"
by(induct rule:path.induct,auto intro:Cons_path)


lemma path_split:
  assumes "n -as@a#as'\<rightarrow>* n'"
  shows "n -as\<rightarrow>* sourcenode a" and "valid_edge a" and "targetnode a -as'\<rightarrow>* n'"
  using \<open>n -as@a#as'\<rightarrow>* n'\<close>
proof(induct as arbitrary:n)
  case Nil case 1
  thus ?case by(fastforce elim:path.cases intro:empty_path)
next
  case Nil case 2
  thus ?case by(fastforce elim:path.cases intro:path_edge)
next
  case Nil case 3
  thus ?case by(fastforce elim:path.cases)
next
  case (Cons ax asx) 
  note IH1 = \<open>\<And>n. n -asx@a#as'\<rightarrow>* n' \<Longrightarrow> n -asx\<rightarrow>* sourcenode a\<close>
  note IH2 = \<open>\<And>n. n -asx@a#as'\<rightarrow>* n' \<Longrightarrow> valid_edge a\<close>
  note IH3 = \<open>\<And>n. n -asx@a#as'\<rightarrow>* n' \<Longrightarrow> targetnode a -as'\<rightarrow>* n'\<close>
  { case 1 
    hence "sourcenode ax = n" and "targetnode ax -asx@a#as'\<rightarrow>* n'" and "valid_edge ax"
      by(auto elim:path.cases)
    from IH1[OF \<open> targetnode ax -asx@a#as'\<rightarrow>* n'\<close>] 
    have "targetnode ax -asx\<rightarrow>* sourcenode a" .
    with \<open>sourcenode ax = n\<close> \<open>valid_edge ax\<close> show ?case by(fastforce intro:Cons_path)
  next
    case 2 hence "targetnode ax -asx@a#as'\<rightarrow>* n'" by(auto elim:path.cases)
    from IH2[OF this] show ?case .
  next
    case 3 hence "targetnode ax -asx@a#as'\<rightarrow>* n'" by(auto elim:path.cases)
    from IH3[OF this] show ?case .
  }
qed


lemma path_split_Cons:
  assumes "n -as\<rightarrow>* n'" and "as \<noteq> []"
  obtains a' as' where "as = a'#as'" and "n = sourcenode a'"
  and "valid_edge a'" and "targetnode a' -as'\<rightarrow>* n'"
proof -
  from \<open>as \<noteq> []\<close> obtain a' as' where "as = a'#as'" by(cases as) auto
  with \<open>n -as\<rightarrow>* n'\<close> have "n -[]@a'#as'\<rightarrow>* n'" by simp
  hence "n -[]\<rightarrow>* sourcenode a'" and "valid_edge a'" and "targetnode a' -as'\<rightarrow>* n'"
    by(rule path_split)+
  from \<open>n -[]\<rightarrow>* sourcenode a'\<close> have "n = sourcenode a'" by fast
  with \<open>as = a'#as'\<close> \<open>valid_edge a'\<close> \<open>targetnode a' -as'\<rightarrow>* n'\<close> that show ?thesis 
    by fastforce
qed


lemma path_split_snoc:
  assumes "n -as\<rightarrow>* n'" and "as \<noteq> []"
  obtains a' as' where "as = as'@[a']" and "n -as'\<rightarrow>* sourcenode a'"
  and "valid_edge a'" and "n' = targetnode a'"
proof -
  from \<open>as \<noteq> []\<close> obtain a' as' where "as = as'@[a']" by(cases as rule:rev_cases) auto
  with \<open>n -as\<rightarrow>* n'\<close> have "n -as'@a'#[]\<rightarrow>* n'" by simp
  hence "n -as'\<rightarrow>* sourcenode a'" and "valid_edge a'" and "targetnode a' -[]\<rightarrow>* n'"
    by(rule path_split)+
  from \<open>targetnode a' -[]\<rightarrow>* n'\<close> have "n' = targetnode a'" by fast
  with \<open>as = as'@[a']\<close> \<open>valid_edge a'\<close> \<open>n -as'\<rightarrow>* sourcenode a'\<close> that show ?thesis 
    by fastforce
qed


lemma path_split_second:
  assumes "n -as@a#as'\<rightarrow>* n'" shows "sourcenode a -a#as'\<rightarrow>* n'"
proof -
  from \<open>n -as@a#as'\<rightarrow>* n'\<close> have "valid_edge a" and "targetnode a -as'\<rightarrow>* n'"
    by(auto intro:path_split)
  thus ?thesis by(fastforce intro:Cons_path)
qed


lemma path_Entry_Cons:
  assumes "(_Entry_) -as\<rightarrow>* n'" and "n' \<noteq> (_Entry_)"
  obtains n a where "sourcenode a = (_Entry_)" and "targetnode a = n"
  and "n -tl as\<rightarrow>* n'" and "valid_edge a" and "a = hd as"
proof -
  from \<open>(_Entry_) -as\<rightarrow>* n'\<close> \<open>n' \<noteq> (_Entry_)\<close> have "as \<noteq> []"
    by(cases as,auto elim:path.cases)
  with \<open>(_Entry_) -as\<rightarrow>* n'\<close> obtain a' as' where "as = a'#as'" 
    and "(_Entry_) = sourcenode a'" and "valid_edge a'" and "targetnode a' -as'\<rightarrow>* n'"
    by(erule path_split_Cons)
  with that show ?thesis by fastforce
qed


lemma path_det:
  "\<lbrakk>n -as\<rightarrow>* n'; n -as\<rightarrow>* n''\<rbrakk> \<Longrightarrow> n' = n''"
proof(induct as arbitrary:n)
  case Nil thus ?case by(auto elim:path.cases)
next
  case (Cons a' as')
  note IH = \<open>\<And>n. \<lbrakk>n -as'\<rightarrow>* n'; n -as'\<rightarrow>* n''\<rbrakk> \<Longrightarrow> n' = n''\<close>
  from \<open>n -a'#as'\<rightarrow>* n'\<close> have "targetnode a' -as'\<rightarrow>* n'" 
    by(fastforce elim:path_split_Cons)
  from \<open>n -a'#as'\<rightarrow>* n''\<close> have "targetnode a' -as'\<rightarrow>* n''" 
    by(fastforce elim:path_split_Cons)
  from IH[OF \<open>targetnode a' -as'\<rightarrow>* n'\<close> this] show ?thesis .
qed


definition
  sourcenodes :: "'edge list \<Rightarrow> 'node list"
  where "sourcenodes xs \<equiv> map sourcenode xs"

definition
  kinds :: "'edge list \<Rightarrow> 'state edge_kind list"
  where "kinds xs \<equiv> map kind xs"

definition
  targetnodes :: "'edge list \<Rightarrow> 'node list"
  where "targetnodes xs \<equiv> map targetnode xs"


lemma path_sourcenode:
  "\<lbrakk>n -as\<rightarrow>* n'; as \<noteq> []\<rbrakk> \<Longrightarrow> hd (sourcenodes as) = n"
by(fastforce elim:path_split_Cons simp:sourcenodes_def)



lemma path_targetnode:
  "\<lbrakk>n -as\<rightarrow>* n'; as \<noteq> []\<rbrakk> \<Longrightarrow> last (targetnodes as) = n'"
by(fastforce elim:path_split_snoc simp:targetnodes_def)



lemma sourcenodes_is_n_Cons_butlast_targetnodes:
  "\<lbrakk>n -as\<rightarrow>* n'; as \<noteq> []\<rbrakk> \<Longrightarrow> 
  sourcenodes as = n#(butlast (targetnodes as))"
proof(induct as arbitrary:n)
  case Nil thus ?case by simp
next
  case (Cons a' as')
  note IH = \<open>\<And>n. \<lbrakk>n -as'\<rightarrow>* n'; as' \<noteq> []\<rbrakk>
            \<Longrightarrow> sourcenodes as' = n#(butlast (targetnodes as'))\<close>
  from \<open>n -a'#as'\<rightarrow>* n'\<close> have "n = sourcenode a'" and "targetnode a' -as'\<rightarrow>* n'"
    by(auto elim:path_split_Cons)
  show ?case
  proof(cases "as' = []")
    case True
    with \<open>targetnode a' -as'\<rightarrow>* n'\<close> have "targetnode a' = n'" by fast
    with True \<open>n = sourcenode a'\<close> show ?thesis
      by(simp add:sourcenodes_def targetnodes_def)
  next
    case False
    from IH[OF \<open>targetnode a' -as'\<rightarrow>* n'\<close> this] 
    have "sourcenodes as' = targetnode a' # butlast (targetnodes as')" .
    with \<open>n = sourcenode a'\<close> False show ?thesis
      by(simp add:sourcenodes_def targetnodes_def)
  qed
qed



lemma targetnodes_is_tl_sourcenodes_App_n':
  "\<lbrakk>n -as\<rightarrow>* n'; as \<noteq> []\<rbrakk> \<Longrightarrow> 
    targetnodes as = (tl (sourcenodes as))@[n']"
proof(induct as arbitrary:n' rule:rev_induct)
  case Nil thus ?case by simp
next
  case (snoc a' as')
  note IH = \<open>\<And>n'. \<lbrakk>n -as'\<rightarrow>* n'; as' \<noteq> []\<rbrakk>
    \<Longrightarrow> targetnodes as' = tl (sourcenodes as') @ [n']\<close>
  from \<open>n -as'@[a']\<rightarrow>* n'\<close> have "n -as'\<rightarrow>* sourcenode a'" and "n' = targetnode a'"
    by(auto elim:path_split_snoc)
  show ?case
  proof(cases "as' = []")
    case True
    with \<open>n -as'\<rightarrow>* sourcenode a'\<close> have "n = sourcenode a'" by fast
    with True \<open>n' = targetnode a'\<close> show ?thesis
      by(simp add:sourcenodes_def targetnodes_def)
  next
    case False
    from IH[OF \<open>n -as'\<rightarrow>* sourcenode a'\<close> this]
    have "targetnodes as' = tl (sourcenodes as')@[sourcenode a']" .
    with \<open>n' = targetnode a'\<close> False show ?thesis
      by(simp add:sourcenodes_def targetnodes_def)
  qed
qed

lemma Entry_sourcenode_hd:
  assumes "n -as\<rightarrow>* n'" and "(_Entry_) \<in> set (sourcenodes as)"
  shows "n = (_Entry_)" and "(_Entry_) \<notin> set (sourcenodes (tl as))"
  using \<open>n -as\<rightarrow>* n'\<close> \<open>(_Entry_) \<in> set (sourcenodes as)\<close>
proof(induct rule:path.induct)
  case (empty_path n) case 1
  thus ?case by(simp add:sourcenodes_def)
next
  case (empty_path n) case 2
  thus ?case by(simp add:sourcenodes_def)
next
  case (Cons_path n'' as n' a n)
  note IH1 = \<open>(_Entry_) \<in> set(sourcenodes as) \<Longrightarrow> n'' = (_Entry_)\<close>
  note IH2 = \<open>(_Entry_) \<in> set(sourcenodes as) \<Longrightarrow> (_Entry_) \<notin> set(sourcenodes(tl as))\<close>
  have "(_Entry_) \<notin> set (sourcenodes(tl(a#as)))"
  proof
    assume "(_Entry_) \<in> set (sourcenodes (tl (a#as)))"
    hence "(_Entry_) \<in> set (sourcenodes as)" by simp
    from IH1[OF this] have "n'' = (_Entry_)" by simp
    with \<open>targetnode a = n''\<close> \<open>valid_edge a\<close> show False by -(erule Entry_target,simp)
  qed
  hence "(_Entry_) \<notin> set (sourcenodes(tl(a#as)))" by fastforce
  { case 1
    with \<open>(_Entry_) \<notin> set (sourcenodes(tl(a#as)))\<close> \<open>sourcenode a = n\<close>
    show ?case by(simp add:sourcenodes_def)
  next
    case 2
    with \<open>(_Entry_) \<notin> set (sourcenodes(tl(a#as)))\<close> \<open>sourcenode a = n\<close>
    show ?case by(simp add:sourcenodes_def)
  }
qed

end

end
