section \<open>Return and their corresponding call nodes\<close>

theory ReturnAndCallNodes imports CFG begin

context CFG begin

subsection \<open>Defining \<open>return_node\<close>\<close>

definition return_node :: "'node \<Rightarrow> bool"
  where "return_node n \<equiv> \<exists>a a'. valid_edge a \<and> n = targetnode a \<and> 
    valid_edge a' \<and> a \<in> get_return_edges a'"


lemma return_node_determines_call_node:
  assumes "return_node n"
  shows "\<exists>!n'. \<exists>a a'. valid_edge a \<and> n' = sourcenode a \<and> valid_edge a' \<and> 
    a' \<in> get_return_edges a \<and> n = targetnode a'"
proof(rule ex_ex1I)
  from \<open>return_node n\<close>
  show "\<exists>n' a a'. valid_edge a \<and> n' = sourcenode a \<and> valid_edge a' \<and> 
    a' \<in> get_return_edges a \<and> n = targetnode a'"
    by(simp add:return_node_def) blast
next
  fix n' nx
  assume "\<exists>a a'. valid_edge a \<and> n' = sourcenode a \<and> valid_edge a' \<and> 
    a' \<in> get_return_edges a \<and> n = targetnode a'"
    and "\<exists>a a'. valid_edge a \<and> nx = sourcenode a \<and> valid_edge a' \<and> 
    a' \<in> get_return_edges a \<and> n = targetnode a'"
  then obtain a a' ax ax' where "valid_edge a" and "n' = sourcenode a"
    and "valid_edge a'" and "a' \<in> get_return_edges a"
    and "n = targetnode a'" and "valid_edge ax" and "nx = sourcenode ax" 
   and "valid_edge ax'" and "ax' \<in> get_return_edges ax"
    and "n = targetnode ax'"
    by blast
  from \<open>valid_edge a\<close> \<open>a' \<in> get_return_edges a\<close> have "valid_edge a'"
    by(rule get_return_edges_valid)
  from \<open>valid_edge a\<close> \<open>a' \<in> get_return_edges a\<close> obtain a''
    where intra_edge1:"valid_edge a''" "sourcenode a'' = sourcenode a"
    "targetnode a'' = targetnode a'" "kind a'' = (\<lambda>cf. False)\<^sub>\<surd>"
    by(fastforce dest:call_return_node_edge)
  from \<open>valid_edge ax\<close> \<open>ax' \<in> get_return_edges ax\<close> obtain ax''
    where intra_edge2:"valid_edge ax''" "sourcenode ax'' = sourcenode ax"
    "targetnode ax'' = targetnode ax'" "kind ax'' = (\<lambda>cf. False)\<^sub>\<surd>"
    by(fastforce dest:call_return_node_edge)
  from \<open>valid_edge a\<close> \<open>a' \<in> get_return_edges a\<close> 
  obtain Q r p fs where "kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs"
    by(fastforce dest!:only_call_get_return_edges)
  with \<open>valid_edge a\<close> \<open>a' \<in> get_return_edges a\<close> obtain Q' p f' 
    where "kind a' = Q'\<hookleftarrow>\<^bsub>p\<^esub>f'" by(fastforce dest!:call_return_edges)
  with \<open>valid_edge a'\<close>
  have "\<exists>!a''. valid_edge a'' \<and> targetnode a'' = targetnode a' \<and> intra_kind(kind a'')"
    by(rule return_only_one_intra_edge)
  with intra_edge1 intra_edge2 \<open>n = targetnode a'\<close> \<open>n = targetnode ax'\<close>
  have "a'' = ax''" by(fastforce simp:intra_kind_def)
  with \<open>sourcenode a'' = sourcenode a\<close> \<open>sourcenode ax'' = sourcenode ax\<close>
    \<open>n' = sourcenode a\<close> \<open>nx = sourcenode ax\<close>
  show "n' = nx" by simp
qed


lemma return_node_THE_call_node:
  "\<lbrakk>return_node n; valid_edge a; valid_edge a'; a' \<in> get_return_edges a; 
  n = targetnode a'\<rbrakk>
  \<Longrightarrow> (THE n'. \<exists>a a'. valid_edge a \<and> n' = sourcenode a \<and> valid_edge a' \<and> 
  a' \<in> get_return_edges a \<and> n = targetnode a') = sourcenode a"
  by(fastforce intro!:the1_equality return_node_determines_call_node)


subsection \<open>Defining call nodes belonging to a certain \<open>return_node\<close>\<close>

definition call_of_return_node :: "'node \<Rightarrow> 'node \<Rightarrow> bool"
  where "call_of_return_node n n' \<equiv> \<exists>a a'. return_node n \<and> 
  valid_edge a \<and> n' = sourcenode a \<and> valid_edge a' \<and>
  a' \<in> get_return_edges a \<and> n = targetnode a'"


lemma return_node_call_of_return_node:
  "return_node n \<Longrightarrow> \<exists>!n'. call_of_return_node n n'"
  by -(frule return_node_determines_call_node,unfold call_of_return_node_def,simp)


lemma call_of_return_nodes_det [dest]:
  assumes "call_of_return_node n n'" and "call_of_return_node n n''"
  shows "n' = n''"
proof -
  from \<open>call_of_return_node n n'\<close> have "return_node n" 
    by(simp add:call_of_return_node_def)
  hence "\<exists>!n'. call_of_return_node n n'" by(rule return_node_call_of_return_node)
  with \<open>call_of_return_node n n'\<close> \<open>call_of_return_node n n''\<close>
  show ?thesis by auto
qed



lemma get_return_edges_call_of_return_nodes:
  "\<lbrakk>valid_call_list cs m; valid_return_list rs m;
    \<forall>i < length rs. rs!i \<in> get_return_edges (cs!i); length rs = length cs\<rbrakk>
  \<Longrightarrow> \<forall>i<length cs. call_of_return_node (targetnodes rs!i) (sourcenode (cs!i))"
proof(induct cs arbitrary:m rs)
  case Nil thus ?case by fastforce
next
  case (Cons c' cs')
  note IH = \<open>\<And>m rs. \<lbrakk>valid_call_list cs' m; valid_return_list rs m;
    \<forall>i<length rs. rs ! i \<in> get_return_edges (cs' ! i); length rs = length cs'\<rbrakk>
    \<Longrightarrow> \<forall>i<length cs'. call_of_return_node (targetnodes rs ! i) (sourcenode (cs'!i))\<close>
  from \<open>length rs = length (c' # cs')\<close> obtain r' rs' where "rs = r' # rs'"
    and "length rs' = length cs'" by(cases rs) auto
  with \<open>\<forall>i<length rs. rs ! i \<in> get_return_edges ((c' # cs') ! i)\<close>
  have "\<forall>i<length rs'. rs' ! i \<in> get_return_edges (cs' ! i)"
    and "r' \<in> get_return_edges c'" by auto
  from \<open>valid_call_list (c'#cs') m\<close> have "valid_edge c'"
    by(fastforce simp:valid_call_list_def)
  from this \<open>r' \<in> get_return_edges c'\<close>
  have "get_proc (sourcenode c') = get_proc (targetnode r')"
    by(rule get_proc_get_return_edge)
  from \<open>valid_call_list (c'#cs') m\<close>
  have "valid_call_list cs' (sourcenode c')"
    apply(clarsimp simp:valid_call_list_def)
    apply(hypsubst_thin)
    apply(erule_tac x="c'#cs'" in allE) apply clarsimp
    by(case_tac cs')(auto simp:sourcenodes_def)
  from \<open>valid_return_list rs m\<close> \<open>rs = r' # rs'\<close> 
    \<open>get_proc (sourcenode c') = get_proc (targetnode r')\<close>
  have "valid_return_list rs' (sourcenode c')"
    apply(clarsimp simp:valid_return_list_def)
    apply(erule_tac x="r'#cs'" in allE) apply clarsimp
    by(case_tac cs')(auto simp:targetnodes_def)
  from IH[OF \<open>valid_call_list cs' (sourcenode c')\<close> 
    \<open>valid_return_list rs' (sourcenode c')\<close>
    \<open>\<forall>i<length rs'. rs' ! i \<in> get_return_edges (cs' ! i)\<close> \<open>length rs' = length cs'\<close>]
  have all:"\<forall>i<length cs'.
    call_of_return_node (targetnodes rs' ! i) (sourcenode (cs' ! i))" .
  from \<open>valid_edge c'\<close> \<open>r' \<in> get_return_edges c'\<close> have "valid_edge r'" 
    by(rule get_return_edges_valid)
  from \<open>valid_edge r'\<close> \<open>valid_edge c'\<close> \<open>r' \<in> get_return_edges c'\<close>
  have "return_node (targetnode r')" by(fastforce simp:return_node_def)
  with \<open>valid_edge c'\<close> \<open>r' \<in> get_return_edges c'\<close> \<open>valid_edge r'\<close>
  have "call_of_return_node (targetnode r') (sourcenode c')"
    by(simp add:call_of_return_node_def) blast
  with all \<open>rs = r' # rs'\<close> show ?case
    by auto(case_tac i,auto simp:targetnodes_def)
qed


end

end
