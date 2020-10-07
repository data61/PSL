section \<open>Observable Sets of Nodes\<close>

theory Observable imports "../Basic/CFG" begin

context CFG begin

inductive_set obs :: "'node \<Rightarrow> 'node set \<Rightarrow> 'node set" 
for n::"'node" and S::"'node set"
where obs_elem: 
  "\<lbrakk>n -as\<rightarrow>* n'; \<forall>nx \<in> set(sourcenodes as). nx \<notin> S; n' \<in> S\<rbrakk> \<Longrightarrow> n' \<in> obs n S"


lemma obsE:
  assumes "n' \<in> obs n S"
  obtains as where "n -as\<rightarrow>* n'" and "\<forall>nx \<in> set(sourcenodes as). nx \<notin> S"
  and "n' \<in> S"
proof(atomize_elim)
  from \<open>n' \<in> obs n S\<close> 
  have "\<exists>as. n -as\<rightarrow>* n' \<and> (\<forall>nx \<in> set(sourcenodes as). nx \<notin> S) \<and> n' \<in> S"
    by(auto elim:obs.cases)
  thus "\<exists>as. n -as\<rightarrow>* n' \<and> (\<forall>nx\<in>set (sourcenodes as). nx \<notin> S) \<and> n' \<in> S" by blast
qed


lemma n_in_obs:
  assumes "valid_node n" and "n \<in> S" shows "obs n S = {n}"
proof -
  from \<open>valid_node n\<close> have "n -[]\<rightarrow>* n" by(rule empty_path)
  with \<open>n \<in> S\<close> have "n \<in> obs n S" by(fastforce elim:obs_elem simp:sourcenodes_def)
  { fix n' assume "n' \<in> obs n S"
    have "n' = n"
    proof(rule ccontr)
      assume "n' \<noteq> n"
      from \<open>n' \<in> obs n S\<close> obtain as where "n -as\<rightarrow>* n'"
        and "\<forall>nx \<in> set(sourcenodes as). nx \<notin> S"
        and "n' \<in> S" by(erule obsE)
      from \<open>n -as\<rightarrow>* n'\<close> \<open>\<forall>nx \<in> set(sourcenodes as). nx \<notin> S\<close> \<open>n' \<noteq> n\<close> \<open>n \<in> S\<close>
      show False
      proof(induct rule:path.induct)
        case (Cons_path n'' as n' a n)
        from \<open>\<forall>nx\<in>set (sourcenodes (a#as)). nx \<notin> S\<close> \<open>sourcenode a = n\<close>
        have "n \<notin> S" by(simp add:sourcenodes_def)
        with \<open>n \<in> S\<close> show False by simp
      qed simp
    qed }
  with \<open>n \<in> obs n S\<close> show ?thesis by fastforce
qed


lemma in_obs_valid:
  assumes "n' \<in> obs n S" shows "valid_node n" and "valid_node n'"
  using \<open>n' \<in> obs n S\<close>
  by(auto elim:obsE intro:path_valid_node)


lemma edge_obs_subset:
  assumes"valid_edge a" and "sourcenode a \<notin> S"
  shows "obs (targetnode a) S \<subseteq> obs (sourcenode a) S"
proof
  fix n assume "n \<in> obs (targetnode a) S"
  then obtain as where "targetnode a -as\<rightarrow>* n" 
    and all:"\<forall>nx \<in> set(sourcenodes as). nx \<notin> S" and "n \<in> S" by(erule obsE)
  from \<open>valid_edge a\<close> \<open>targetnode a -as\<rightarrow>* n\<close>
  have "sourcenode a -a#as\<rightarrow>* n" by(fastforce intro:Cons_path)
  moreover
  from all \<open>sourcenode a \<notin> S\<close> have "\<forall>nx \<in> set(sourcenodes (a#as)). nx \<notin> S"
    by(simp add:sourcenodes_def)
  ultimately show "n \<in> obs (sourcenode a) S" using \<open>n \<in> S\<close>
    by(rule obs_elem)
qed


lemma path_obs_subset:
  "\<lbrakk>n -as\<rightarrow>* n'; \<forall>n' \<in> set(sourcenodes as). n' \<notin> S\<rbrakk>
  \<Longrightarrow> obs n' S \<subseteq> obs n S"
proof(induct rule:path.induct)
  case (Cons_path n'' as n' a n)
  note IH = \<open>\<forall>n'\<in>set (sourcenodes as). n' \<notin> S \<Longrightarrow> obs n' S \<subseteq> obs n'' S\<close>
  from \<open>\<forall>n'\<in>set (sourcenodes (a#as)). n' \<notin> S\<close> 
  have all:"\<forall>n'\<in>set (sourcenodes as). n' \<notin> S" and "sourcenode a \<notin> S"
    by(simp_all add:sourcenodes_def)
  from IH[OF all] have "obs n' S \<subseteq> obs n'' S" .
  from \<open>valid_edge a\<close> \<open>targetnode a = n''\<close> \<open>sourcenode a = n\<close> \<open>sourcenode a \<notin> S\<close>
  have "obs n'' S \<subseteq> obs n S" by(fastforce dest:edge_obs_subset)
  with \<open>obs n' S \<subseteq> obs n'' S\<close> show ?case by fastforce
qed simp


lemma path_ex_obs:
  assumes "n -as\<rightarrow>* n'" and "n' \<in> S"
  obtains m where "m \<in> obs n S"
proof(atomize_elim)
  show "\<exists>m. m \<in> obs n S"
  proof(cases "\<forall>nx \<in> set(sourcenodes as). nx \<notin> S")
    case True
    with \<open>n -as\<rightarrow>* n'\<close> \<open>n' \<in> S\<close> have "n' \<in> obs n S" by -(rule obs_elem)
    thus ?thesis by fastforce
  next
    case False
    hence "\<exists>nx \<in> set(sourcenodes as). nx \<in> S" by fastforce
    then obtain nx ns ns' where "sourcenodes as = ns@nx#ns'"
      and "nx \<in> S" and "\<forall>n' \<in> set ns. n' \<notin> S"
      by(fastforce elim!:split_list_first_propE)
    from \<open>sourcenodes as = ns@nx#ns'\<close> obtain as' a as'' 
      where "ns = sourcenodes as'"
      and "as = as'@a#as''" and "sourcenode a = nx"
      by(fastforce elim:map_append_append_maps simp:sourcenodes_def)
    with \<open>n -as\<rightarrow>* n'\<close> have "n -as'\<rightarrow>* nx" by(fastforce dest:path_split)
    with \<open>nx \<in> S\<close> \<open>\<forall>n' \<in> set ns. n' \<notin> S\<close> \<open>ns = sourcenodes as'\<close> have "nx \<in> obs n S"
      by(fastforce intro:obs_elem)
    thus ?thesis by fastforce
  qed
qed

end

end

