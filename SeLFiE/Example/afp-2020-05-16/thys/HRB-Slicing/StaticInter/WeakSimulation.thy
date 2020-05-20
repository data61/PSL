section \<open>The weak simulation\<close>

theory WeakSimulation imports Slice begin

context SDG begin

lemma call_node_notin_slice_return_node_neither:
  assumes "call_of_return_node n n'" and "n' \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
  shows "n \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
proof -
  from \<open>call_of_return_node n n'\<close> obtain a a' where "return_node n"
    and "valid_edge a" and "n' = sourcenode a"
    and "valid_edge a'" and "a' \<in> get_return_edges a" 
    and "n = targetnode a'" by(fastforce simp:call_of_return_node_def)
  from \<open>valid_edge a\<close> \<open>a' \<in> get_return_edges a\<close> obtain Q p r fs 
    where "kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs" by(fastforce dest!:only_call_get_return_edges)
  with \<open>valid_edge a\<close> \<open>a' \<in> get_return_edges a\<close> obtain Q' f' where "kind a' = Q'\<hookleftarrow>\<^bsub>p\<^esub>f'"
    by(fastforce dest!:call_return_edges)
  from \<open>valid_edge a\<close> \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close> \<open>a' \<in> get_return_edges a\<close>
  have "CFG_node (sourcenode a) s-p\<rightarrow>\<^bsub>sum\<^esub> CFG_node (targetnode a')"
    by(fastforce intro:sum_SDG_call_summary_edge)
  show ?thesis
  proof
    assume "n \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
    with \<open>n = targetnode a'\<close> have "CFG_node (targetnode a') \<in> HRB_slice S"
      by(simp add:SDG_to_CFG_set_def)
    hence "CFG_node (sourcenode a) \<in> HRB_slice S"
    proof(induct "CFG_node (targetnode a')" rule:HRB_slice_cases)
      case (phase1 nx)
      with \<open>CFG_node (sourcenode a) s-p\<rightarrow>\<^bsub>sum\<^esub> CFG_node (targetnode a')\<close>
      show ?case by(fastforce intro:combine_SDG_slices.combSlice_refl sum_slice1 
                              simp:HRB_slice_def)
    next
      case (phase2 nx n' n'' p')
      from \<open>CFG_node (targetnode a') \<in> sum_SDG_slice2 n'\<close> 
        \<open>CFG_node (sourcenode a) s-p\<rightarrow>\<^bsub>sum\<^esub> CFG_node (targetnode a')\<close> \<open>valid_edge a\<close>
      have "CFG_node (sourcenode a) \<in> sum_SDG_slice2 n'"
        by(fastforce intro:sum_slice2)
      with \<open>n' \<in> sum_SDG_slice1 nx\<close> \<open>n'' s-p'\<rightarrow>\<^bsub>ret\<^esub> CFG_node (parent_node n')\<close> \<open>nx \<in> S\<close>
      show ?case by(fastforce intro:combine_SDG_slices.combSlice_Return_parent_node
                              simp:HRB_slice_def)
    qed
    with \<open>n' \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close> \<open>n' = sourcenode a\<close> show False 
      by(simp add:SDG_to_CFG_set_def HRB_slice_def)
  qed
qed


lemma edge_obs_intra_slice_eq:
assumes "valid_edge a" and "intra_kind (kind a)" and "sourcenode a \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
  shows "obs_intra (targetnode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = 
         obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
proof -
  from assms have "obs_intra (targetnode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> \<subseteq>
                   obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
    by(rule edge_obs_intra_subset)
  from \<open>valid_edge a\<close> have "valid_node (sourcenode a)" by simp
  { fix x assume "x \<in> obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
    and "obs_intra (targetnode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {}"
    have "\<exists>as. targetnode a -as\<rightarrow>\<^sub>\<iota>* x"
    proof(cases "method_exit x")
      case True
      from \<open>valid_edge a\<close> have "valid_node (targetnode a)" by simp
      then obtain asx where "targetnode a -asx\<rightarrow>\<^sub>\<surd>* (_Exit_)" 
        by(fastforce dest:Exit_path)
      then obtain as pex where "targetnode a -as\<rightarrow>\<^sub>\<iota>* pex" and "method_exit pex"
        by -(erule valid_Exit_path_intra_path)
      hence "get_proc pex = get_proc (targetnode a)"
        by -(rule intra_path_get_procs[THEN sym])
      also from \<open>valid_edge a\<close> \<open>intra_kind (kind a)\<close> 
      have "\<dots> = get_proc (sourcenode a)"
        by -(rule get_proc_intra[THEN sym])
      also from \<open>x \<in> obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close> True
      have "\<dots> = get_proc x"
        by(fastforce elim:obs_intraE intro:intra_path_get_procs)
      finally have "pex = x" using \<open>method_exit pex\<close> True
        by -(rule method_exit_unique)
      with \<open>targetnode a -as\<rightarrow>\<^sub>\<iota>* pex\<close> show ?thesis by fastforce
    next
      case False
      with \<open>x \<in> obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close>
      have "x postdominates (sourcenode a)" by(rule obs_intra_postdominate)
      with \<open>valid_edge a\<close> \<open>intra_kind (kind a)\<close> \<open>sourcenode a \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close>
        \<open>x \<in> obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close>
      have "x postdominates (targetnode a)"
        by(fastforce elim:postdominate_inner_path_targetnode path_edge obs_intraE 
                    simp:intra_path_def sourcenodes_def)
      thus ?thesis by(fastforce elim:postdominate_implies_inner_path)
    qed
    then obtain as where "targetnode a -as\<rightarrow>\<^sub>\<iota>* x" by blast
    from \<open>x \<in> obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close>
    have "x \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>" by -(erule obs_intraE)
    have "\<exists>x' \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>. \<exists>as'. targetnode a -as'\<rightarrow>\<^sub>\<iota>* x' \<and> 
      (\<forall>a' \<in> set (sourcenodes as'). a' \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>)"
    proof(cases "\<exists>a' \<in> set (sourcenodes as). a' \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>")
      case True
      then obtain zs z zs' where "sourcenodes as = zs@z#zs'"
        and "z \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>" and "\<forall>z' \<in> set zs. z' \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
        by(erule split_list_first_propE)
      then obtain ys y ys'
        where "sourcenodes ys = zs" and "as = ys@y#ys'"
        and "sourcenode y = z"
        by(fastforce elim:map_append_append_maps simp:sourcenodes_def)
      from \<open>targetnode a -as\<rightarrow>\<^sub>\<iota>* x\<close> \<open>as = ys@y#ys'\<close>
      have "targetnode a -ys@y#ys'\<rightarrow>* x" and "\<forall>y' \<in> set ys. intra_kind (kind y')"
        by(simp_all add:intra_path_def)
      from \<open>targetnode a -ys@y#ys'\<rightarrow>* x\<close> have "targetnode a -ys\<rightarrow>* sourcenode y"
        by(rule path_split)
      with \<open>\<forall>y' \<in> set ys. intra_kind (kind y')\<close> \<open>sourcenode y = z\<close>
        \<open>\<forall>z' \<in> set zs. z' \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close> \<open>z \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close>
        \<open>sourcenodes ys = zs\<close>
      show ?thesis by(fastforce simp:intra_path_def)
    next
      case False
      with \<open>targetnode a -as\<rightarrow>\<^sub>\<iota>* x\<close> \<open>x \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close>
      show ?thesis by fastforce
    qed
    hence "\<exists>y. y \<in> obs_intra (targetnode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
      by(fastforce intro:obs_intra_elem)
    with \<open>obs_intra (targetnode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {}\<close> 
    have False by simp }
  with \<open>obs_intra (targetnode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> \<subseteq>
        obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close> \<open>valid_node (sourcenode a)\<close>
  show ?thesis by(cases "obs_intra (targetnode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {}") 
                 (auto dest!:obs_intra_singleton_disj)
qed


lemma intra_edge_obs_slice:
  assumes "ms \<noteq> []" and "ms'' \<in> obs ms' \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>" and "valid_edge a" 
  and "intra_kind (kind a)" 
  and disj:"(\<exists>m \<in> set (tl ms). \<exists>m'. call_of_return_node m m' \<and> 
                               m' \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>) \<or> hd ms \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
  and "hd ms = sourcenode a" and "ms' = targetnode a#tl ms" 
  and "\<forall>n \<in> set (tl ms'). return_node n"
  shows "ms'' \<in> obs ms \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
proof -
  from \<open>ms'' \<in> obs ms' \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close> \<open>\<forall>n \<in> set (tl ms'). return_node n\<close>
  obtain msx m msx' mx m' where "ms' = msx@m#msx'" and "ms'' = mx#msx'"
    and "mx \<in> obs_intra m \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
    and "\<forall>nx \<in> set msx'. \<exists>nx'. call_of_return_node nx nx' \<and> nx' \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
    and imp:"\<forall>xs x xs'. msx = xs@x#xs' \<and> obs_intra x \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> \<noteq> {}
    \<longrightarrow> (\<exists>x'' \<in> set (xs'@[m]). \<exists>mx. call_of_return_node x'' mx \<and> 
                                   mx \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>)"
    by(erule obsE)
  show ?thesis
  proof(cases msx)
    case Nil
    with \<open>\<forall>nx \<in> set msx'. \<exists>nx'. call_of_return_node nx nx' \<and> nx' \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close>
      disj \<open>ms' = msx@m#msx'\<close> \<open>hd ms = sourcenode a\<close> \<open>ms' = targetnode a#tl ms\<close>
    have "sourcenode a \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>" by(cases ms) auto
    from \<open>ms' = msx@m#msx'\<close> \<open>ms' = targetnode a#tl ms\<close> Nil 
    have "m = targetnode a" by simp
    with \<open>valid_edge a\<close> \<open>intra_kind (kind a)\<close> \<open>sourcenode a \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close>
      \<open>mx \<in> obs_intra m \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close>
    have "mx \<in> obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
      by(fastforce dest:edge_obs_intra_subset)
    from \<open>ms' = msx@m#msx'\<close> Nil \<open>ms' = targetnode a # tl ms\<close> 
      \<open>hd ms = sourcenode a\<close> \<open>ms \<noteq> []\<close>
    have "ms = []@sourcenode a#msx'" by(cases ms) auto
    with \<open>ms'' = mx#msx'\<close> \<open>mx \<in> obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close>  
      \<open>\<forall>nx \<in> set msx'. \<exists>nx'. call_of_return_node nx nx' \<and> nx' \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close> Nil
    show ?thesis by(fastforce intro!:obsI)
  next
    case (Cons x xs)
    with \<open>ms' = msx@m#msx'\<close> \<open>ms' = targetnode a # tl ms\<close>
    have "msx = targetnode a#xs" by simp
    from Cons \<open>ms' = msx@m#msx'\<close> \<open>ms' = targetnode a # tl ms\<close> \<open>hd ms = sourcenode a\<close>
    have "ms = (sourcenode a#xs)@m#msx'" by(cases ms) auto
    from disj \<open>ms = (sourcenode a#xs)@m#msx'\<close> 
      \<open>\<forall>nx \<in> set msx'. \<exists>nx'. call_of_return_node nx nx' \<and> nx' \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close>
    have disj2:"(\<exists>m \<in> set (xs@[m]). \<exists>m'. call_of_return_node m m' \<and> 
                            m' \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>) \<or> hd ms \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
      by fastforce
    hence "\<forall>zs z zs'. sourcenode a#xs = zs@z#zs' \<and> obs_intra z \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> \<noteq> {}
      \<longrightarrow> (\<exists>z'' \<in> set (zs'@[m]). \<exists>mx. call_of_return_node z'' mx \<and> 
                                   mx \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>)"
    proof(cases "hd ms \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>")
      case True
      with \<open>hd ms = sourcenode a\<close> have "sourcenode a \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>" by simp
      with \<open>valid_edge a\<close> \<open>intra_kind (kind a)\<close>
      have "obs_intra (targetnode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = 
        obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
        by(rule edge_obs_intra_slice_eq)
      with imp \<open>msx = targetnode a#xs\<close> show ?thesis
        by auto(case_tac zs,fastforce,erule_tac x="targetnode a#list" in allE,fastforce)
    next
      case False
      with \<open>hd ms = sourcenode a\<close> \<open>valid_edge a\<close> 
      have "obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {sourcenode a}"
        by(fastforce intro!:n_in_obs_intra)
      from False disj2 
      have "\<exists>m \<in> set (xs@[m]). \<exists>m'. call_of_return_node m m' \<and> m' \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
        by simp
      with imp \<open>obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {sourcenode a}\<close>
        \<open>msx = targetnode a#xs\<close> show ?thesis
        by auto(case_tac zs,fastforce,erule_tac x="targetnode a#list" in allE,fastforce)
    qed
    with \<open>ms' = msx@m#msx'\<close> \<open>ms' = targetnode a # tl ms\<close> \<open>hd ms = sourcenode a\<close>
      \<open>ms'' = mx#msx'\<close> \<open>mx \<in> obs_intra m \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close> 
      \<open>\<forall>nx \<in> set msx'. \<exists>nx'. call_of_return_node nx nx' \<and> nx' \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close>
      \<open>ms = (sourcenode a#xs)@m#msx'\<close>
    show ?thesis by(simp del:obs.simps)(rule obsI,auto)
  qed
qed



subsection \<open>Silent moves\<close>

inductive silent_move :: 
  "'node SDG_node set \<Rightarrow> ('edge \<Rightarrow> ('var,'val,'ret,'pname) edge_kind) \<Rightarrow> 'node list \<Rightarrow> 
  (('var \<rightharpoonup> 'val) \<times> 'ret) list \<Rightarrow> 'edge \<Rightarrow> 'node list \<Rightarrow> (('var \<rightharpoonup> 'val) \<times> 'ret) list \<Rightarrow> bool"
("_,_ \<turnstile> '(_,_') -_\<rightarrow>\<^sub>\<tau> '(_,_')" [51,50,0,0,50,0,0] 51) 

where silent_move_intra:
  "\<lbrakk>pred (f a) s; transfer (f a) s = s'; valid_edge a; intra_kind(kind a);
    (\<exists>m \<in> set (tl ms). \<exists>m'. call_of_return_node m m' \<and> m' \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>) \<or>
    hd ms \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>; \<forall>m \<in> set (tl ms). return_node m;
    length s' = length s; length ms = length s;
    hd ms = sourcenode a; ms' = (targetnode a)#tl ms\<rbrakk>  
  \<Longrightarrow> S,f \<turnstile> (ms,s) -a\<rightarrow>\<^sub>\<tau> (ms',s')"

  | silent_move_call:
  "\<lbrakk>pred (f a) s; transfer (f a) s = s'; valid_edge a; kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs; 
    valid_edge a'; a' \<in> get_return_edges a;
    (\<exists>m \<in> set (tl ms). \<exists>m'. call_of_return_node m m' \<and> m' \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>) \<or>
    hd ms \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>; \<forall>m \<in> set (tl ms). return_node m;
    length ms = length s; length s' = Suc(length s); 
    hd ms = sourcenode a; ms' = (targetnode a)#(targetnode a')#tl ms\<rbrakk>  
  \<Longrightarrow> S,f \<turnstile> (ms,s) -a\<rightarrow>\<^sub>\<tau> (ms',s')"

  | silent_move_return:
  "\<lbrakk>pred (f a) s; transfer (f a) s = s'; valid_edge a; kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f'; 
    \<exists>m \<in> set (tl ms). \<exists>m'. call_of_return_node m m' \<and> m' \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>;
    \<forall>m \<in> set (tl ms). return_node m; length ms = length s; length s = Suc(length s');
    s' \<noteq> []; hd ms = sourcenode a; hd(tl ms) = targetnode a; ms' = tl ms\<rbrakk>  
  \<Longrightarrow> S,f \<turnstile> (ms,s) -a\<rightarrow>\<^sub>\<tau> (ms',s')"


lemma silent_move_valid_nodes:
  "\<lbrakk>S,f \<turnstile> (ms,s) -a\<rightarrow>\<^sub>\<tau> (ms',s'); \<forall>m \<in> set ms'. valid_node m\<rbrakk>
  \<Longrightarrow> \<forall>m \<in> set ms. valid_node m"
by(induct rule:silent_move.induct)(case_tac ms,auto)+


lemma silent_move_return_node:
  "S,f \<turnstile> (ms,s) -a\<rightarrow>\<^sub>\<tau> (ms',s') \<Longrightarrow> \<forall>m \<in> set (tl ms'). return_node m"
proof(induct rule:silent_move.induct)
  case (silent_move_intra f a s s' ms n\<^sub>c ms')
  thus ?case by simp
next
  case (silent_move_call f a s s' Q r p fs a' ms n\<^sub>c ms')
  from \<open>valid_edge a'\<close> \<open>valid_edge a\<close> \<open>a' \<in> get_return_edges a\<close>
  have "return_node (targetnode a')" by(fastforce simp:return_node_def)
  with \<open>\<forall>m\<in>set (tl ms). return_node m\<close> \<open>ms' = targetnode a # targetnode a' # tl ms\<close>
  show ?case by simp
next
  case (silent_move_return f a s s' Q p f' ms n\<^sub>c ms')
  thus ?case by(cases "tl ms") auto
qed


lemma silent_move_equal_length:
  assumes "S,f \<turnstile> (ms,s) -a\<rightarrow>\<^sub>\<tau> (ms',s')" 
  shows "length ms = length s" and "length ms' = length s'"
proof -
  from \<open>S,f \<turnstile> (ms,s) -a\<rightarrow>\<^sub>\<tau> (ms',s')\<close>
  have "length ms = length s \<and> length ms' = length s'"
  proof(induct rule:silent_move.induct)
    case (silent_move_intra f a s s' ms n\<^sub>c ms')
    from \<open>pred (f a) s\<close> obtain cf cfs where [simp]:"s = cf#cfs" by(cases s) auto
    from \<open>length ms = length s\<close> \<open>ms' = targetnode a # tl ms\<close>
      \<open>length s' = length s\<close> show ?case by simp
  next
    case (silent_move_call f a s s' Q r p fs a' ms n\<^sub>c ms')
    from \<open>pred (f a) s\<close> obtain cf cfs where [simp]:"s = cf#cfs" by(cases s) auto
    from \<open>length ms = length s\<close> \<open>length s' = Suc (length s)\<close> 
      \<open>ms' = targetnode a # targetnode a' # tl ms\<close> show ?case by simp
  next
    case (silent_move_return f a s s' Q p f' ms n\<^sub>c ms')
    from \<open>length ms = length s\<close> \<open>length s = Suc (length s')\<close> \<open>ms' = tl ms\<close> \<open>s' \<noteq> []\<close>
    show ?case by simp
  qed
  thus "length ms = length s" and "length ms' = length s'" by simp_all
qed


lemma silent_move_obs_slice:
  "\<lbrakk>S,kind \<turnstile> (ms,s) -a\<rightarrow>\<^sub>\<tau> (ms',s'); msx \<in> obs ms' \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>; 
    \<forall>n \<in> set (tl ms'). return_node n\<rbrakk>
  \<Longrightarrow> msx \<in> obs ms \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
proof(induct S f\<equiv>"kind" ms s a ms' s' rule:silent_move.induct)
  case (silent_move_intra a s s' ms n\<^sub>c ms')
  from \<open>pred (kind a) s\<close> \<open>length ms = length s\<close> have "ms \<noteq> []"
    by(cases s) auto
  with silent_move_intra show ?case by -(rule intra_edge_obs_slice)
next
  case (silent_move_call a s s' Q r p fs a' ms S ms')
  note disj = \<open>(\<exists>m\<in>set (tl ms). \<exists>m'. call_of_return_node m m' \<and> 
    m' \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>) \<or> hd ms \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close>
  from \<open>valid_edge a'\<close> \<open>valid_edge a\<close> \<open>a' \<in> get_return_edges a\<close>
  have "return_node (targetnode a')" by(fastforce simp:return_node_def)
  with \<open>valid_edge a\<close> \<open>a' \<in> get_return_edges a\<close> \<open>valid_edge a'\<close>
  have "call_of_return_node (targetnode a') (sourcenode a)"
    by(simp add:call_of_return_node_def) blast
  from \<open>pred (kind a) s\<close> \<open>length ms = length s\<close>
  have "ms \<noteq> []" by(cases s) auto
  from disj
  show ?case
  proof
    assume "hd ms \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
    with \<open>hd ms = sourcenode a\<close> have "sourcenode a \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>" by simp
    with \<open>call_of_return_node (targetnode a') (sourcenode a)\<close>
      \<open>ms' = targetnode a # targetnode a' # tl ms\<close>
    have "\<exists>n' \<in> set (tl ms'). \<exists>nx. call_of_return_node n' nx \<and> nx \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
      by fastforce
    with \<open>msx \<in> obs ms' \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close> \<open>ms' = targetnode a # targetnode a' # tl ms\<close>
    have "msx \<in> obs (targetnode a' # tl ms) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>" by simp
    from \<open>valid_edge a\<close> \<open>a' \<in> get_return_edges a\<close>
    obtain a'' where "valid_edge a''" and [simp]:"sourcenode a'' = sourcenode a"
      and [simp]:"targetnode a'' = targetnode a'" and "intra_kind(kind a'')"
      by -(drule call_return_node_edge,auto simp:intra_kind_def)
    from \<open>\<forall>m\<in>set (tl ms'). return_node m\<close> \<open>ms' = targetnode a # targetnode a' # tl ms\<close>
    have "\<forall>m\<in>set (tl ms). return_node m" by simp
    with \<open>ms \<noteq> []\<close> \<open>msx \<in> obs (targetnode a'#tl ms) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close>
      \<open>valid_edge a''\<close> \<open>intra_kind(kind a'')\<close> disj
      \<open>hd ms = sourcenode a\<close>
    show ?case by -(rule intra_edge_obs_slice,fastforce+)
  next
    assume "\<exists>m\<in>set (tl ms).
      \<exists>m'. call_of_return_node m m' \<and> m' \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
    with \<open>ms \<noteq> []\<close> \<open>msx \<in> obs ms' \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close>
      \<open>ms' = targetnode a # targetnode a' # tl ms\<close>
    show ?thesis by(cases ms) auto
  qed
next
  case (silent_move_return a s s' Q p f' ms S ms')
  from \<open>length ms = length s\<close> \<open>length s = Suc (length s')\<close> \<open>s' \<noteq> []\<close>
  have "ms \<noteq> []" and "tl ms \<noteq> []" by(auto simp:length_Suc_conv)
  from \<open>\<exists>m\<in>set (tl ms).
    \<exists>m'. call_of_return_node m m' \<and> m' \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close>
    \<open>tl ms \<noteq> []\<close> \<open>hd (tl ms) = targetnode a\<close>
  have "(\<exists>m'. call_of_return_node (targetnode a) m' \<and> m' \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>) \<or>
    (\<exists>m\<in>set (tl (tl ms)). \<exists>m'. call_of_return_node m m' \<and> m' \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>)"
    by(cases "tl ms") auto
  hence "obs ms \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = obs (tl ms) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
  proof
    assume "\<exists>m'. call_of_return_node (targetnode a) m' \<and> m' \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
    from \<open>tl ms \<noteq> []\<close> have "hd (tl ms) \<in> set (tl ms)" by simp
    with \<open>hd (tl ms) = targetnode a\<close> have "targetnode a \<in> set (tl ms)" by simp
    with \<open>ms \<noteq> []\<close> 
      \<open>\<exists>m'. call_of_return_node (targetnode a) m' \<and> m' \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close>
    have "\<exists>m\<in>set (tl ms). \<exists>m'. call_of_return_node m m' \<and> 
      m' \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>" by(cases ms) auto
    with \<open>ms \<noteq> []\<close> show ?thesis by(cases ms) auto
  next
    assume "\<exists>m\<in>set (tl (tl ms)). \<exists>m'. call_of_return_node m m' \<and> 
      m' \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
    with \<open>ms \<noteq> []\<close> \<open>tl ms \<noteq> []\<close> show ?thesis
      by(cases ms,auto simp:Let_def)(case_tac list,auto)+
  qed
  with \<open>ms' = tl ms\<close> \<open>msx \<in> obs ms' \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close> show ?case by simp
qed



lemma silent_move_empty_obs_slice:
  assumes "S,f \<turnstile> (ms,s) -a\<rightarrow>\<^sub>\<tau> (ms',s')" and "obs ms' \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {}"
  shows "obs ms \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {}"
proof(rule ccontr)
  assume "obs ms \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> \<noteq> {}"
  then obtain xs where "xs \<in> obs ms \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>" by fastforce
  from \<open>S,f \<turnstile> (ms,s) -a\<rightarrow>\<^sub>\<tau> (ms',s')\<close>
  have "\<forall>m \<in> set (tl ms). return_node m"
    by(fastforce elim!:silent_move.cases simp:call_of_return_node_def)
  with \<open>xs \<in> obs ms \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close>
  obtain msx m msx' m' where assms:"ms = msx@m#msx'" "xs = m'#msx'"
    "m' \<in> obs_intra m \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>" 
    "\<forall>mx \<in> set msx'. \<exists>mx'. call_of_return_node mx mx' \<and> mx' \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
    "\<forall>xs x xs'. msx = xs@x#xs' \<and> obs_intra x \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> \<noteq> {}
    \<longrightarrow> (\<exists>x'' \<in> set (xs'@[m]). \<exists>mx. call_of_return_node x'' mx \<and> 
                              mx \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>)"
    by(erule obsE)
  from \<open>S,f \<turnstile> (ms,s) -a\<rightarrow>\<^sub>\<tau> (ms',s')\<close> \<open>obs ms' \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {}\<close> assms
  show False
  proof(induct rule:silent_move.induct)
    case (silent_move_intra f a s s' ms S ms')
    note disj = \<open>(\<exists>m\<in>set (tl ms). \<exists>m'. call_of_return_node m m' \<and> 
      m' \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>) \<or> hd ms \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close>
    note msx = \<open>\<forall>xs x xs'. msx = xs@x#xs' \<and> obs_intra x \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> \<noteq> {} \<longrightarrow> 
      (\<exists>x''\<in>set (xs' @ [m]). \<exists>mx. call_of_return_node x'' mx \<and> mx \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>)\<close>
    note msx' = \<open>\<forall>mx\<in>set msx'. \<exists>mx'. call_of_return_node mx mx' \<and> 
      mx' \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close>
    show False
    proof(cases msx)
      case Nil
      with \<open>ms = msx @ m # msx'\<close> \<open>hd ms = sourcenode a\<close> have [simp]:"m = sourcenode a"
        and "tl ms = msx'" by simp_all
      from Nil \<open>ms' = targetnode a # tl ms\<close> \<open>ms = msx @ m # msx'\<close>
      have "ms' = msx @ targetnode a # msx'" by simp
      from msx' disj \<open>tl ms = msx'\<close> \<open>hd ms = sourcenode a\<close>
      have "sourcenode a \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>" by fastforce
      with \<open>valid_edge a\<close> \<open>intra_kind (kind a)\<close>
      have "obs_intra (targetnode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> =
        obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>" by(rule edge_obs_intra_slice_eq)
      with \<open>m' \<in> obs_intra m \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close>
      have "m' \<in> obs_intra (targetnode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>" by simp
      from msx Nil have "\<forall>xs x xs'. msx = xs@x#xs' \<and>  
        obs_intra x \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> \<noteq> {} \<longrightarrow> 
        (\<exists>x''\<in>set (xs' @ [targetnode a]). \<exists>mx. call_of_return_node x'' mx \<and> 
        mx \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>)" by simp
      with \<open>m' \<in> obs_intra (targetnode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close> msx' 
        \<open>ms' = msx @ targetnode a # msx'\<close>
      have "m'#msx' \<in> obs ms' \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>" by(rule obsI)
      with \<open>obs ms' \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {}\<close> show False by simp
    next
      case (Cons y ys)
      with \<open>ms = msx @ m # msx'\<close> \<open>ms' = targetnode a # tl ms\<close> \<open>hd ms = sourcenode a\<close>
      have "ms' = targetnode a # ys @ m # msx'" and "y = sourcenode a" 
        and "tl ms = ys @ m # msx'" by simp_all
      { fix x assume "x \<in> obs_intra (targetnode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
        have "obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> \<noteq> {}"
        proof(cases "sourcenode a \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>")
          case True
          from \<open>valid_edge a\<close> have "valid_node (sourcenode a)" by simp
          from this True 
          have "obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {sourcenode a}"
            by(rule n_in_obs_intra)
          thus ?thesis by simp
        next
          case False
          from \<open>valid_edge a\<close> \<open>intra_kind (kind a)\<close> False
          have "obs_intra (targetnode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = 
            obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
            by(rule edge_obs_intra_slice_eq)
          with \<open>x \<in> obs_intra (targetnode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close> show ?thesis
            by fastforce
        qed }
      with msx Cons \<open>y = sourcenode a\<close> 
      have "\<forall>xs x xs'. targetnode a # ys = xs@x#xs' \<and> 
        obs_intra x \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> \<noteq> {} \<longrightarrow> (\<exists>x''\<in>set (xs' @ [m]). 
        \<exists>mx. call_of_return_node x'' mx \<and> mx \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>)"
        apply clarsimp apply(case_tac xs) apply auto
        apply(erule_tac x="[]" in allE) apply clarsimp
        apply(erule_tac x="sourcenode a # list" in allE) apply auto
        done
      with \<open>m' \<in> obs_intra m \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close> msx' 
        \<open>ms' = targetnode a # ys @ m # msx'\<close>
      have "m'#msx' \<in> obs ms' \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>" by -(rule obsI,auto)
      with \<open>obs ms' \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {}\<close> show False by simp
    qed
  next
    case (silent_move_call f a s s' Q r p fs a' ms S ms')
    note disj = \<open>(\<exists>m\<in>set (tl ms). \<exists>m'. call_of_return_node m m' \<and> 
      m' \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>) \<or> hd ms \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close>
    note msx = \<open>\<forall>xs x xs'. msx = xs@x#xs' \<and> obs_intra x \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> \<noteq> {} \<longrightarrow> 
      (\<exists>x''\<in>set (xs' @ [m]). \<exists>mx. call_of_return_node x'' mx \<and> mx \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>)\<close>
    note msx' = \<open>\<forall>mx\<in>set msx'. \<exists>mx'. call_of_return_node mx mx' \<and> 
      mx' \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close>
    from \<open>valid_edge a\<close> \<open>a' \<in> get_return_edges a\<close> obtain a'' where "valid_edge a''"
      and "sourcenode a'' = sourcenode a" and "targetnode a'' = targetnode a'"
      and "intra_kind (kind a'')" 
      by(fastforce dest:call_return_node_edge simp:intra_kind_def)
    from \<open>valid_edge a'\<close> \<open>valid_edge a\<close> \<open>a' \<in> get_return_edges a\<close>
    have "call_of_return_node (targetnode a') (sourcenode a)"
      by(fastforce simp:call_of_return_node_def return_node_def)
    show False
    proof(cases msx)
      case Nil
      with \<open>ms = msx @ m # msx'\<close> \<open>hd ms = sourcenode a\<close> have [simp]:"m = sourcenode a"
        and "tl ms = msx'" by simp_all
      from Nil \<open>ms' = targetnode a # targetnode a' # tl ms\<close> \<open>ms = msx @ m # msx'\<close>
      have "ms' = targetnode a # targetnode a' # msx'" by simp
      from msx' disj \<open>tl ms = msx'\<close> \<open>hd ms = sourcenode a\<close>
      have "sourcenode a \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>" by fastforce
      from \<open>valid_edge a''\<close> \<open>intra_kind (kind a'')\<close> \<open>sourcenode a \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close>
        \<open>sourcenode a'' = sourcenode a\<close> \<open>targetnode a'' = targetnode a'\<close>
      have "obs_intra (targetnode a') \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = 
         obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
        by(fastforce dest:edge_obs_intra_slice_eq)
      with \<open>m' \<in> obs_intra m \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close> 
      have "m' \<in> obs_intra (targetnode a') \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>" by simp
      from this msx' have "m'#msx' \<in> obs (targetnode a'#msx') \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
        by(fastforce intro:obsI)
      from \<open>call_of_return_node (targetnode a') (sourcenode a)\<close>
        \<open>sourcenode a \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close>
      have "\<exists>m' \<in> set (targetnode a'#msx').
        \<exists>mx. call_of_return_node m' mx \<and> mx \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
        by fastforce
      with \<open>m'#msx' \<in> obs (targetnode a'#msx') \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close>
      have "m'#msx' \<in> obs (targetnode a#targetnode a'#msx') \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
        by simp
      with \<open>ms' = targetnode a # targetnode a' # msx'\<close> \<open>obs ms' \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {}\<close>
      show False by simp
    next
      case (Cons y ys)
      with \<open>ms = msx @ m # msx'\<close> \<open>ms' = targetnode a # targetnode a' # tl ms\<close> 
        \<open>hd ms = sourcenode a\<close>
      have "ms' = targetnode a # targetnode a' # ys @ m # msx'" 
        and "y = sourcenode a" and "tl ms = ys @ m # msx'" by simp_all
      show False
      proof(cases "obs_intra (targetnode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> \<noteq> {} \<longrightarrow> 
          (\<exists>x''\<in>set (targetnode a' # ys @ [m]).
          \<exists>mx. call_of_return_node x'' mx \<and> mx \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>)")
        case True
        hence imp:"obs_intra (targetnode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> \<noteq> {} \<longrightarrow>
          (\<exists>x''\<in>set (targetnode a' # ys @ [m]).
          \<exists>mx. call_of_return_node x'' mx \<and> mx \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>)" .
        show False
        proof(cases "obs_intra (targetnode a') \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> \<noteq> {} \<longrightarrow> 
            (\<exists>x''\<in>set (ys @ [m]). \<exists>mx. call_of_return_node x'' mx \<and> 
            mx \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>)")
          case True
          with imp msx Cons \<open>y = sourcenode a\<close> 
          have "\<forall>xs x xs'. targetnode a # targetnode a' # ys = xs@x#xs' \<and> 
            obs_intra x \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> \<noteq> {} \<longrightarrow> (\<exists>x''\<in>set (xs' @ [m]). 
            \<exists>mx. call_of_return_node x'' mx \<and> mx \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>)"
            apply clarsimp apply(case_tac xs) apply fastforce
            apply(case_tac list) apply fastforce apply clarsimp
            apply(erule_tac x="sourcenode a # lista" in allE) apply auto
            done
          with \<open>m' \<in> obs_intra m \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close> msx' 
            \<open>ms' = targetnode a # targetnode a' # ys @ m # msx'\<close>
          have "m'#msx' \<in> obs ms' \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>" by -(rule obsI,auto)
          with \<open>obs ms' \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {}\<close> show False by simp
        next
          case False
          hence "obs_intra (targetnode a') \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> \<noteq> {}"
            and all:"\<forall>x''\<in>set (ys @ [m]). \<forall>mx. call_of_return_node x'' mx \<longrightarrow> 
            mx \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
            by fastforce+
          have "obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> \<noteq> {}"
          proof(cases "sourcenode a \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>")
            case True
            from \<open>valid_edge a\<close> have "valid_node (sourcenode a)" by simp
            from this True 
            have "obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {sourcenode a}"
              by(rule n_in_obs_intra)
            thus ?thesis by simp
          next
            case False
            with \<open>sourcenode a'' = sourcenode a\<close>
            have "sourcenode a'' \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>" by simp
            with \<open>valid_edge a''\<close> \<open>intra_kind (kind a'')\<close>
            have "obs_intra (targetnode a'') \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = 
              obs_intra (sourcenode a'') \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
              by(rule edge_obs_intra_slice_eq)
            with \<open>obs_intra (targetnode a') \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> \<noteq> {}\<close> 
              \<open>sourcenode a'' = sourcenode a\<close> \<open>targetnode a'' = targetnode a'\<close>
            show ?thesis by fastforce 
          qed
          with msx Cons \<open>y = sourcenode a\<close> all
          show False by simp blast
        qed
      next
        case False
        hence "obs_intra (targetnode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> \<noteq> {}"
          and all:"\<forall>x''\<in>set (targetnode a' # ys @ [m]). 
          \<forall>mx. call_of_return_node x'' mx \<longrightarrow> mx \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
          by fastforce+
        with Cons \<open>y = sourcenode a\<close> msx 
        have "obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {}" by auto blast
        from \<open>call_of_return_node (targetnode a') (sourcenode a)\<close> all
        have "sourcenode a \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>" by fastforce
        from \<open>valid_edge a\<close> have "valid_node (sourcenode a)" by simp
        from this \<open>sourcenode a \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close> 
        have "obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {sourcenode a}"
          by(rule n_in_obs_intra)
        with \<open>obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {}\<close> show False by simp
      qed
    qed
  next
    case (silent_move_return f a s s' Q p f' ms S ms')
    note msx = \<open>\<forall>xs x xs'. msx = xs@x#xs' \<and> obs_intra x \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> \<noteq> {} \<longrightarrow> 
      (\<exists>x''\<in>set (xs' @ [m]). \<exists>mx. call_of_return_node x'' mx \<and> mx \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>)\<close>
    note msx' = \<open>\<forall>mx\<in>set msx'. \<exists>mx'. call_of_return_node mx mx' \<and> 
      mx' \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close>
    show False
    proof(cases msx)
      case Nil
      with \<open>ms = msx @ m # msx'\<close> \<open>hd ms = sourcenode a\<close> have  "tl ms = msx'" by simp
      with \<open>\<exists>m\<in>set (tl ms). \<exists>m'. call_of_return_node m m' \<and> m' \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close>
        msx'
      show False by fastforce
    next
      case (Cons y ys)
      with \<open>ms = msx @ m # msx'\<close> \<open>hd ms = sourcenode a\<close> \<open>ms' = tl ms\<close>
      have "ms' = ys @ m # msx'" and "y = sourcenode a" by simp_all
      from msx Cons have "\<forall>xs x xs'. ys = xs@x#xs' \<and> 
        obs_intra x \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> \<noteq> {} \<longrightarrow>  (\<exists>x''\<in>set (xs' @ [m]). 
        \<exists>mx. call_of_return_node x'' mx \<and> mx \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>)"
        by auto (erule_tac x="y # xs" in allE,auto)
      with \<open>m' \<in> obs_intra m \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close> msx' \<open>ms' = ys @ m # msx'\<close>
      have "m'#msx' \<in> obs ms' \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>" by(rule obsI)
      with \<open>obs ms' \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {}\<close> show False by simp
    qed
  qed
qed



inductive silent_moves :: 
  "'node SDG_node set \<Rightarrow> ('edge \<Rightarrow> ('var,'val,'ret,'pname) edge_kind) \<Rightarrow> 'node list \<Rightarrow> 
  (('var \<rightharpoonup> 'val) \<times> 'ret) list \<Rightarrow> 'edge list \<Rightarrow> 'node list \<Rightarrow> (('var \<rightharpoonup> 'val) \<times> 'ret) list \<Rightarrow> bool"
("_,_ \<turnstile> '(_,_') =_\<Rightarrow>\<^sub>\<tau> '(_,_')" [51,50,0,0,50,0,0] 51)

  where silent_moves_Nil: "length ms = length s \<Longrightarrow> S,f \<turnstile> (ms,s) =[]\<Rightarrow>\<^sub>\<tau> (ms,s)"

  | silent_moves_Cons:
  "\<lbrakk>S,f \<turnstile> (ms,s) -a\<rightarrow>\<^sub>\<tau> (ms',s'); S,f \<turnstile> (ms',s') =as\<Rightarrow>\<^sub>\<tau> (ms'',s'')\<rbrakk> 
  \<Longrightarrow> S,f \<turnstile> (ms,s) =a#as\<Rightarrow>\<^sub>\<tau> (ms'',s'')"


lemma silent_moves_equal_length:
  assumes "S,f \<turnstile> (ms,s) =as\<Rightarrow>\<^sub>\<tau> (ms',s')" 
  shows "length ms = length s" and "length ms' = length s'"
proof -
  from \<open>S,f \<turnstile> (ms,s) =as\<Rightarrow>\<^sub>\<tau> (ms',s')\<close> 
  have "length ms = length s \<and> length ms' = length s'"
  proof(induct rule:silent_moves.induct)
    case (silent_moves_Cons S f ms s a ms' s' as ms'' s'')
    from \<open>S,f \<turnstile> (ms,s) -a\<rightarrow>\<^sub>\<tau> (ms',s')\<close>
    have "length ms = length s" and "length ms' = length s'" 
      by(rule silent_move_equal_length)+
    with \<open>length ms' = length s' \<and> length ms'' = length s''\<close>
    show ?case by simp
  qed simp
  thus "length ms = length s" "length ms' = length s'" by simp_all
qed


lemma silent_moves_Append:
  "\<lbrakk>S,f \<turnstile> (ms,s) =as\<Rightarrow>\<^sub>\<tau> (ms'',s''); S,f \<turnstile> (ms'',s'') =as'\<Rightarrow>\<^sub>\<tau> (ms',s')\<rbrakk>
  \<Longrightarrow> S,f \<turnstile> (ms,s) =as@as'\<Rightarrow>\<^sub>\<tau> (ms',s')"
by(induct rule:silent_moves.induct)(auto intro:silent_moves.intros)


lemma silent_moves_split:
  assumes "S,f \<turnstile> (ms,s) =as@as'\<Rightarrow>\<^sub>\<tau> (ms',s')"
  obtains ms'' s'' where "S,f \<turnstile> (ms,s) =as\<Rightarrow>\<^sub>\<tau> (ms'',s'')"
  and "S,f \<turnstile> (ms'',s'') =as'\<Rightarrow>\<^sub>\<tau> (ms',s')"
proof(atomize_elim)
  from \<open>S,f \<turnstile> (ms,s) =as@as'\<Rightarrow>\<^sub>\<tau> (ms',s')\<close>
  show "\<exists>ms'' s''. S,f \<turnstile> (ms,s) =as\<Rightarrow>\<^sub>\<tau> (ms'',s'') \<and> S,f \<turnstile> (ms'',s'') =as'\<Rightarrow>\<^sub>\<tau> (ms',s')"
  proof(induct as arbitrary:ms s)
    case Nil
    from \<open>S,f \<turnstile> (ms,s) =[] @ as'\<Rightarrow>\<^sub>\<tau> (ms',s')\<close> have "length ms = length s"
      by(fastforce intro:silent_moves_equal_length)
    hence "S,f \<turnstile> (ms,s) =[]\<Rightarrow>\<^sub>\<tau> (ms,s)" by(rule silent_moves_Nil)
    with \<open>S,f \<turnstile> (ms,s) =[] @ as'\<Rightarrow>\<^sub>\<tau> (ms',s')\<close> show ?case by fastforce
  next
    case (Cons ax asx)
    note IH = \<open>\<And>ms s. S,f \<turnstile> (ms,s) =asx @ as'\<Rightarrow>\<^sub>\<tau> (ms',s') \<Longrightarrow>
      \<exists>ms'' s''. S,f \<turnstile> (ms,s) =asx\<Rightarrow>\<^sub>\<tau> (ms'',s'') \<and> S,f \<turnstile> (ms'',s'') =as'\<Rightarrow>\<^sub>\<tau> (ms',s')\<close>
    from \<open>S,f \<turnstile> (ms,s) =(ax # asx) @ as'\<Rightarrow>\<^sub>\<tau> (ms',s')\<close>
    obtain msx sx where "S,f \<turnstile> (ms,s) -ax\<rightarrow>\<^sub>\<tau> (msx,sx)"
      and "S,f \<turnstile> (msx,sx) =asx @ as'\<Rightarrow>\<^sub>\<tau> (ms',s')"
      by(auto elim:silent_moves.cases)
    from IH[OF this(2)] obtain ms'' s'' where "S,f \<turnstile> (msx,sx) =asx\<Rightarrow>\<^sub>\<tau> (ms'',s'')"
      and "S,f \<turnstile> (ms'',s'') =as'\<Rightarrow>\<^sub>\<tau> (ms',s')" by blast
    from \<open>S,f \<turnstile> (ms,s) -ax\<rightarrow>\<^sub>\<tau> (msx,sx)\<close> \<open>S,f \<turnstile> (msx,sx) =asx\<Rightarrow>\<^sub>\<tau> (ms'',s'')\<close>
    have "S,f \<turnstile> (ms,s) =ax#asx\<Rightarrow>\<^sub>\<tau> (ms'',s'')" by(rule silent_moves_Cons)
    with \<open>S,f \<turnstile> (ms'',s'') =as'\<Rightarrow>\<^sub>\<tau> (ms',s')\<close> show ?case by blast
  qed
qed


lemma valid_nodes_silent_moves:
  "\<lbrakk>S,f\<turnstile> (ms,s) =as'\<Rightarrow>\<^sub>\<tau> (ms',s'); \<forall>m \<in> set ms. valid_node m\<rbrakk>
  \<Longrightarrow> \<forall>m \<in> set ms'. valid_node m"
proof(induct rule:silent_moves.induct)
  case (silent_moves_Cons S f ms s a ms' s' as ms'' s'')
  note IH = \<open>\<forall>m\<in>set ms'. valid_node m \<Longrightarrow> \<forall>m\<in>set ms''. valid_node m\<close>
  from \<open>S,f \<turnstile> (ms,s) -a\<rightarrow>\<^sub>\<tau> (ms',s')\<close> \<open>\<forall>m\<in>set ms. valid_node m\<close>
  have "\<forall>m\<in>set ms'. valid_node m"
    apply - apply(erule silent_move.cases) apply auto
    by(cases ms,auto dest:get_return_edges_valid)+
  from IH[OF this] show ?case .
qed simp


lemma return_nodes_silent_moves:
  "\<lbrakk>S,f \<turnstile> (ms,s) =as'\<Rightarrow>\<^sub>\<tau> (ms',s'); \<forall>m \<in> set (tl ms). return_node m\<rbrakk>
  \<Longrightarrow> \<forall>m \<in> set (tl ms'). return_node m"
by(induct rule:silent_moves.induct,auto dest:silent_move_return_node)


lemma silent_moves_intra_path:
  "\<lbrakk>S,f \<turnstile> (m#ms,s) =as\<Rightarrow>\<^sub>\<tau> (m'#ms',s'); \<forall>a \<in> set as. intra_kind(kind a)\<rbrakk>
  \<Longrightarrow> ms = ms' \<and> get_proc m = get_proc m'"
proof(induct S f "m#ms" s as "m'#ms'" s' arbitrary:m
  rule:silent_moves.induct)
  case (silent_moves_Cons S f sx a msx' sx' as s'')
  thus ?case
  proof(induct _ _ "m # ms" _ _ _ _ rule:silent_move.induct)
    case (silent_move_intra f a s s' n\<^sub>c msx')
    note IH = \<open>\<And>m. \<lbrakk>msx' = m # ms; \<forall>a\<in>set as. intra_kind (kind a)\<rbrakk>
      \<Longrightarrow> ms = ms' \<and> get_proc m = get_proc m'\<close>
    from \<open>msx' = targetnode a # tl (m # ms)\<close>
    have "msx' = targetnode a # ms" by simp
    from \<open>\<forall>a\<in>set (a # as). intra_kind (kind a)\<close> have "\<forall>a\<in>set as. intra_kind (kind a)"
      by simp
    from IH[OF \<open>msx' = targetnode a # ms\<close> this]
    have "ms = ms'" and "get_proc (targetnode a) = get_proc m'" by simp_all
    moreover
    from \<open>valid_edge a\<close> \<open>intra_kind (kind a)\<close>
    have "get_proc (sourcenode a) = get_proc (targetnode a)" by(rule get_proc_intra)
    moreover
    from \<open>hd (m # ms) = sourcenode a\<close> have "m = sourcenode a" by simp
    ultimately show ?case using \<open>ms = ms'\<close> by simp
  qed (auto simp:intra_kind_def)
qed simp


lemma silent_moves_nodestack_notempty: 
  "\<lbrakk>S,f \<turnstile> (ms,s) =as\<Rightarrow>\<^sub>\<tau> (ms',s'); ms \<noteq> []\<rbrakk> \<Longrightarrow> ms' \<noteq> []"
apply(induct S f ms s as ms' s' rule:silent_moves.induct) apply auto
apply(erule silent_move.cases) apply auto
apply(case_tac "tl msa") by auto


lemma silent_moves_obs_slice:
  "\<lbrakk>S,kind \<turnstile> (ms,s) =as\<Rightarrow>\<^sub>\<tau> (ms',s'); mx \<in> obs ms' \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>; 
  \<forall>n \<in> set (tl ms'). return_node n\<rbrakk>
  \<Longrightarrow> mx \<in> obs ms \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> \<and> (\<forall>n \<in> set (tl ms). return_node n)"
proof(induct S f\<equiv>"kind" ms s as ms' s' rule:silent_moves.induct)
  case silent_moves_Nil thus ?case by simp
next
  case (silent_moves_Cons S ms s a ms' s' as ms'' s'')
  note IH = \<open>\<lbrakk>mx \<in> obs ms'' \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>; \<forall>m\<in>set (tl ms''). return_node m\<rbrakk>
    \<Longrightarrow> mx \<in> obs ms' \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> \<and> (\<forall>m\<in>set (tl ms'). return_node m)\<close>
  from IH[OF \<open>mx \<in> obs ms'' \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close> \<open>\<forall>m\<in>set (tl ms''). return_node m\<close>]
  have "mx \<in> obs ms' \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>" and "\<forall>m\<in>set (tl ms'). return_node m"
    by simp_all
  with \<open>S,kind \<turnstile> (ms,s) -a\<rightarrow>\<^sub>\<tau> (ms',s')\<close>
  have "mx \<in> obs ms \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>" by(fastforce intro:silent_move_obs_slice)
  moreover
  from \<open>S,kind \<turnstile> (ms,s) -a\<rightarrow>\<^sub>\<tau> (ms',s')\<close> have "\<forall>m\<in>set (tl ms). return_node m"
    by(fastforce elim:silent_move.cases)
  ultimately show ?case by simp
qed


lemma silent_moves_empty_obs_slice:
  "\<lbrakk>S,f \<turnstile> (ms,s) =as\<Rightarrow>\<^sub>\<tau> (ms',s'); obs ms' \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {}\<rbrakk>
  \<Longrightarrow> obs ms \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {}"
proof(induct rule:silent_moves.induct)
  case silent_moves_Nil thus ?case by simp
next
  case (silent_moves_Cons S f ms s a ms' s' as ms'' s'')
  note IH = \<open>obs ms'' \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {} \<Longrightarrow> obs ms' \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {}\<close>
  from IH[OF \<open>obs ms'' \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {}\<close>]
  have "obs ms' \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {}" by simp
  with \<open>S,f \<turnstile> (ms,s) -a\<rightarrow>\<^sub>\<tau> (ms',s')\<close>
  show ?case by -(rule silent_move_empty_obs_slice,fastforce)
qed


lemma silent_moves_preds_transfers:
  assumes "S,f \<turnstile> (ms,s) =as\<Rightarrow>\<^sub>\<tau> (ms',s')"
  shows "preds (map f as) s" and "transfers (map f as) s = s'"
proof -
  from \<open>S,f \<turnstile> (ms,s) =as\<Rightarrow>\<^sub>\<tau> (ms',s')\<close>
  have "preds (map f as) s \<and> transfers (map f as) s = s'"
  proof(induct rule:silent_moves.induct)
    case silent_moves_Nil thus ?case by simp
  next
    case (silent_moves_Cons S f ms s a ms' s' as ms'' s'')
    from \<open>S,f \<turnstile> (ms,s) -a\<rightarrow>\<^sub>\<tau> (ms',s')\<close>
    have "pred (f a) s" and "transfer (f a) s = s'" by(auto elim:silent_move.cases)
    with \<open>preds (map f as) s' \<and> transfers (map f as) s' = s''\<close>
    show ?case by fastforce
  qed
  thus "preds (map f as) s" and "transfers (map f as) s = s'" by simp_all
qed



lemma silent_moves_intra_path_obs:
  assumes "m' \<in> obs_intra m \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>" and "length s = length (m#msx')"
  and "\<forall>m \<in> set msx'. return_node m"
  obtains as' where "S,slice_kind S \<turnstile> (m#msx',s) =as'\<Rightarrow>\<^sub>\<tau> (m'#msx',s)"
proof(atomize_elim)
  from \<open>m' \<in> obs_intra m \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close>
  obtain as where "m -as\<rightarrow>\<^sub>\<iota>* m'" and "m' \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
    by -(erule obs_intraE)
  from \<open>m -as\<rightarrow>\<^sub>\<iota>* m'\<close> obtain x where "distance m m' x" and "x \<le> length as"
    by(erule every_path_distance)
  from \<open>distance m m' x\<close> \<open>m' \<in> obs_intra m \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close>
    \<open>length s = length (m#msx')\<close> \<open>\<forall>m \<in> set msx'. return_node m\<close>
  show "\<exists>as. S,slice_kind S \<turnstile> (m#msx',s) =as\<Rightarrow>\<^sub>\<tau> (m'#msx',s)"
  proof(induct x arbitrary:m s rule:nat.induct)
    fix m fix s::"(('var \<rightharpoonup> 'val) \<times> 'ret) list"
    assume "distance m m' 0" and "length s = length (m#msx')"
    then obtain as' where "m -as'\<rightarrow>\<^sub>\<iota>* m'" and "length as' = 0"
      by(auto elim:distance.cases)
    hence "m -[]\<rightarrow>\<^sub>\<iota>* m'" by(cases as) auto
    hence [simp]:"m = m'" by(fastforce elim:path.cases simp:intra_path_def)
    with \<open>length s = length (m#msx')\<close>[THEN sym]
    have "S,slice_kind S \<turnstile> (m#msx',s) =[]\<Rightarrow>\<^sub>\<tau> (m#msx',s)" 
      by -(rule silent_moves_Nil)
    thus "\<exists>as. S,slice_kind S \<turnstile> (m#msx',s) =as\<Rightarrow>\<^sub>\<tau> (m'#msx',s)" by simp blast
  next
    fix x m fix s::"(('var \<rightharpoonup> 'val) \<times> 'ret) list"
    assume "distance m m' (Suc x)" and "m' \<in> obs_intra m \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
      and "length s = length (m#msx')" and "\<forall>m \<in> set msx'. return_node m"
      and IH:"\<And>m s. \<lbrakk>distance m m' x; m' \<in> obs_intra m \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>;
                     length s = length (m#msx'); \<forall>m \<in> set msx'. return_node m\<rbrakk>
      \<Longrightarrow> \<exists>as. S,slice_kind S \<turnstile> (m#msx',s) =as\<Rightarrow>\<^sub>\<tau> (m'#msx',s)"
    from \<open>m' \<in> obs_intra m \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close> have "valid_node m"
      by(rule in_obs_intra_valid)
    with \<open>distance m m' (Suc x)\<close> have "m \<noteq> m'"
      by(fastforce elim:distance.cases dest:empty_path simp:intra_path_def)
    have "m \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
    proof
      assume isin:"m \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
      with \<open>valid_node m\<close> have "obs_intra m \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {m}"
        by(fastforce intro!:n_in_obs_intra)
      with \<open>m' \<in> obs_intra m \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close> \<open>m \<noteq> m'\<close> show False by simp
    qed
    from \<open>distance m m' (Suc x)\<close> obtain a where "valid_edge a" and "m = sourcenode a"
      and "intra_kind(kind a)" and "distance (targetnode a) m' x"
      and target:"targetnode a = (SOME mx. \<exists>a'. sourcenode a = sourcenode a' \<and> 
                                               distance (targetnode a') m' x \<and>
                                               valid_edge a' \<and> intra_kind (kind a') \<and> 
                                               targetnode a' = mx)"
      by -(erule distance_successor_distance,simp+)
    from \<open>m' \<in> obs_intra m \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close> 
    have "obs_intra m \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {m'}"
      by(rule obs_intra_singleton_element)
    with \<open>valid_edge a\<close> \<open>m \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close> \<open>m = sourcenode a\<close> \<open>intra_kind(kind a)\<close>
    have disj:"obs_intra (targetnode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {} \<or> 
               obs_intra (targetnode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {m'}"
      by -(drule_tac S="\<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>" in edge_obs_intra_subset,auto)
    from \<open>intra_kind(kind a)\<close> \<open>length s = length (m#msx')\<close> \<open>m \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close> 
      \<open>m = sourcenode a\<close>
    have length:"length (transfer (slice_kind S a) s) = length (targetnode a#msx')"
      by(cases s)
    (auto split:if_split_asm simp add:Let_def slice_kind_def intra_kind_def)
    from \<open>distance (targetnode a) m' x\<close> obtain asx where "targetnode a -asx\<rightarrow>\<^sub>\<iota>* m'" 
      and "length asx = x" and "\<forall>as'. targetnode a -as'\<rightarrow>\<^sub>\<iota>* m' \<longrightarrow> x \<le> length as'"
      by(auto elim:distance.cases)
    from \<open>targetnode a -asx\<rightarrow>\<^sub>\<iota>* m'\<close> \<open>m' \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close>
    obtain mx where "mx \<in> obs_intra (targetnode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>" 
      by(erule path_ex_obs_intra)
    with disj have "m' \<in> obs_intra (targetnode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>" by fastforce
    from IH[OF \<open>distance (targetnode a) m' x\<close> this length 
      \<open>\<forall>m \<in> set msx'. return_node m\<close>]
    obtain asx' where moves:"S,slice_kind S \<turnstile> 
      (targetnode a#msx',transfer (slice_kind S a) s) =asx'\<Rightarrow>\<^sub>\<tau> 
      (m'#msx',transfer (slice_kind S a) s)" by blast
    have "pred (slice_kind S a) s \<and> transfer (slice_kind S a) s = s"
    proof(cases "kind a")
      fix f assume "kind a = \<Up>f"
      with \<open>m \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close> \<open>m = sourcenode a\<close> have "slice_kind S a = \<Up>id"
        by(fastforce intro:slice_kind_Upd)
      with \<open>length s = length (m#msx')\<close> show ?thesis by(cases s) auto
    next
      fix Q assume "kind a = (Q)\<^sub>\<surd>"
      with \<open>m \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close> \<open>m = sourcenode a\<close>
        \<open>m' \<in> obs_intra m \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close> \<open>distance (targetnode a) m' x\<close>
        \<open>distance m m' (Suc x)\<close> target
      have "slice_kind S a = (\<lambda>s. True)\<^sub>\<surd>"
        by(fastforce intro:slice_kind_Pred_obs_nearer_SOME)
      with \<open>length s = length (m#msx')\<close> show ?thesis by(cases s) auto
    next
      fix Q r p fs assume "kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs"
      with \<open>intra_kind(kind a)\<close> have False by(simp add:intra_kind_def)
      thus ?thesis by simp
    next
      fix Q p f assume "kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f"
      with \<open>intra_kind(kind a)\<close> have False by(simp add:intra_kind_def)
      thus ?thesis by simp
    qed
    hence "pred (slice_kind S a) s" and "transfer (slice_kind S a) s = s"
      by simp_all
    with \<open>m \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close> \<open>m = sourcenode a\<close> \<open>valid_edge a\<close>
      \<open>intra_kind(kind a)\<close> \<open>length s = length (m#msx')\<close> \<open>\<forall>m \<in> set msx'. return_node m\<close>
    have "S,slice_kind S \<turnstile> (sourcenode a#msx',s) -a\<rightarrow>\<^sub>\<tau> 
                             (targetnode a#msx',transfer (slice_kind S a) s)"
      by(fastforce intro:silent_move_intra)
    with moves \<open>transfer (slice_kind S a) s = s\<close> \<open>m = sourcenode a\<close>
    have "S,slice_kind S \<turnstile> (m#msx',s) =a#asx'\<Rightarrow>\<^sub>\<tau> (m'#msx',s)"
      by(fastforce intro:silent_moves_Cons)
    thus "\<exists>as. S,slice_kind S \<turnstile> (m#msx',s) =as\<Rightarrow>\<^sub>\<tau> (m'#msx',s)" by blast
  qed
qed


lemma silent_moves_intra_path_no_obs:
  assumes "obs_intra m \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {}" and "method_exit m'"
  and "get_proc m = get_proc m'" and "valid_node m" and "length s = length (m#msx')"
  and "\<forall>m \<in> set msx'. return_node m"
  obtains as where "S,slice_kind S \<turnstile> (m#msx',s) =as\<Rightarrow>\<^sub>\<tau> (m'#msx',s)"
proof(atomize_elim)
  from \<open>method_exit m'\<close> \<open>get_proc m = get_proc m'\<close> \<open>valid_node m\<close>
  obtain as where "m -as\<rightarrow>\<^sub>\<iota>* m'" by(erule intra_path_to_matching_method_exit)
  then obtain x where "distance m m' x" and "x \<le> length as"
    by(erule every_path_distance)
  from \<open>distance m m' x\<close> \<open>m -as\<rightarrow>\<^sub>\<iota>* m'\<close> \<open>obs_intra m \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {}\<close>
    \<open>length s = length (m#msx')\<close> \<open>\<forall>m \<in> set msx'. return_node m\<close>
  show "\<exists>as. S,slice_kind S \<turnstile> (m#msx',s) =as\<Rightarrow>\<^sub>\<tau> (m'#msx',s)"
  proof(induct x arbitrary:m as s rule:nat.induct)
    fix m fix s::"(('var \<rightharpoonup> 'val) \<times> 'ret) list"
    assume "distance m m' 0" and "length s = length (m#msx')"
    then obtain as' where "m -as'\<rightarrow>\<^sub>\<iota>* m'" and "length as' = 0"
      by(auto elim:distance.cases)
    hence "m -[]\<rightarrow>\<^sub>\<iota>* m'" by(cases as) auto
    hence [simp]:"m = m'" by(fastforce elim:path.cases simp:intra_path_def)
    with \<open>length s = length (m#msx')\<close>[THEN sym]
    have "S,slice_kind S \<turnstile> (m#msx',s) =[]\<Rightarrow>\<^sub>\<tau> (m#msx',s)" 
      by(fastforce intro:silent_moves_Nil)
    thus "\<exists>as. S,slice_kind S \<turnstile> (m#msx',s) =as\<Rightarrow>\<^sub>\<tau> (m'#msx',s)" by simp blast
  next
    fix x m as fix s::"(('var \<rightharpoonup> 'val) \<times> 'ret) list"
    assume "distance m m' (Suc x)" and "m -as\<rightarrow>\<^sub>\<iota>* m'"
      and "obs_intra m \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {}"
      and "length s = length (m#msx')" and "\<forall>m \<in> set msx'. return_node m"
      and IH:"\<And>m as s. \<lbrakk>distance m m' x; m -as\<rightarrow>\<^sub>\<iota>* m'; 
      obs_intra m \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {}; length s = length (m#msx'); 
      \<forall>m \<in> set msx'. return_node m\<rbrakk>
      \<Longrightarrow> \<exists>as. S,slice_kind S \<turnstile> (m#msx',s) =as\<Rightarrow>\<^sub>\<tau> (m'#msx',s)"
    from \<open>m -as\<rightarrow>\<^sub>\<iota>* m'\<close> have "valid_node m" 
      by(fastforce intro:path_valid_node simp:intra_path_def)
    from \<open>m -as\<rightarrow>\<^sub>\<iota>* m'\<close> have "get_proc m = get_proc m'" by(rule intra_path_get_procs)
    have "m \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
    proof
      assume "m \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
      with \<open>valid_node m\<close> have "obs_intra m \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {m}"
        by(fastforce intro!:n_in_obs_intra)
      with \<open>obs_intra m \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {}\<close> show False by simp
    qed
    from \<open>distance m m' (Suc x)\<close> obtain a where "valid_edge a" and "m = sourcenode a"
      and "intra_kind(kind a)" and "distance (targetnode a) m' x"
      and target:"targetnode a = (SOME mx. \<exists>a'. sourcenode a = sourcenode a' \<and> 
                                               distance (targetnode a') m' x \<and>
                                               valid_edge a' \<and> intra_kind (kind a') \<and> 
                                               targetnode a' = mx)"
      by -(erule distance_successor_distance,simp+)
    from \<open>intra_kind(kind a)\<close> \<open>length s = length (m#msx')\<close> \<open>m \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close> 
      \<open>m = sourcenode a\<close>
    have length:"length (transfer (slice_kind S a) s) = length (targetnode a#msx')"
      by(cases s)
    (auto split:if_split_asm simp add:Let_def slice_kind_def intra_kind_def)
    from \<open>distance (targetnode a) m' x\<close> obtain asx where "targetnode a -asx\<rightarrow>\<^sub>\<iota>* m'" 
      and "length asx = x" and "\<forall>as'. targetnode a -as'\<rightarrow>\<^sub>\<iota>* m' \<longrightarrow> x \<le> length as'"
      by(auto elim:distance.cases)
    from \<open>valid_edge a\<close> \<open>intra_kind(kind a)\<close> \<open>m \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close> 
      \<open>m = sourcenode a\<close> \<open>obs_intra m \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {}\<close>
    have "obs_intra (targetnode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {}"
      by(fastforce dest:edge_obs_intra_subset)
    from IH[OF \<open>distance (targetnode a) m' x\<close> \<open>targetnode a -asx\<rightarrow>\<^sub>\<iota>* m'\<close> this
      length \<open>\<forall>m \<in> set msx'. return_node m\<close>] obtain as' 
      where moves:"S,slice_kind S \<turnstile> 
      (targetnode a#msx',transfer (slice_kind S a) s) =as'\<Rightarrow>\<^sub>\<tau> 
      (m'#msx',transfer (slice_kind S a) s)" by blast
    have "pred (slice_kind S a) s \<and> transfer (slice_kind S a) s = s"
    proof(cases "kind a")
      fix f assume "kind a = \<Up>f"
      with \<open>m \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close> \<open>m = sourcenode a\<close> have "slice_kind S a = \<Up>id"
        by(fastforce intro:slice_kind_Upd)
      with \<open>length s = length (m#msx')\<close> show ?thesis by(cases s) auto
    next
      fix Q assume "kind a = (Q)\<^sub>\<surd>"
      with \<open>m \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close> \<open>m = sourcenode a\<close>
        \<open>obs_intra m \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {}\<close> \<open>distance (targetnode a) m' x\<close>
        \<open>distance m m' (Suc x)\<close> \<open>method_exit m'\<close> \<open>get_proc m = get_proc m'\<close> target
      have "slice_kind S a = (\<lambda>s. True)\<^sub>\<surd>"
        by(fastforce intro:slice_kind_Pred_empty_obs_nearer_SOME)
     with \<open>length s = length (m#msx')\<close> show ?thesis by(cases s) auto
    next
      fix Q r p fs assume "kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs"
      with \<open>intra_kind(kind a)\<close> have False by(simp add:intra_kind_def)
      thus ?thesis by simp
    next
      fix Q p f assume "kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f"
      with \<open>intra_kind(kind a)\<close> have False by(simp add:intra_kind_def)
      thus ?thesis by simp
    qed
    hence "pred (slice_kind S a) s" and "transfer (slice_kind S a) s = s"
      by simp_all
    with \<open>m \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close> \<open>m = sourcenode a\<close> \<open>valid_edge a\<close>
      \<open>intra_kind(kind a)\<close> \<open>length s = length (m#msx')\<close> \<open>\<forall>m \<in> set msx'. return_node m\<close>
    have "S,slice_kind S \<turnstile> (sourcenode a#msx',s) -a\<rightarrow>\<^sub>\<tau> 
                             (targetnode a#msx',transfer (slice_kind S a) s)"
      by(fastforce intro:silent_move_intra)
    with moves \<open>transfer (slice_kind S a) s = s\<close> \<open>m = sourcenode a\<close>
    have "S,slice_kind S \<turnstile> (m#msx',s) =a#as'\<Rightarrow>\<^sub>\<tau> (m'#msx',s)"
      by(fastforce intro:silent_moves_Cons)
    thus "\<exists>as. S,slice_kind S \<turnstile> (m#msx',s) =as\<Rightarrow>\<^sub>\<tau> (m'#msx',s)" by blast
  qed
qed


lemma silent_moves_vpa_path:
  assumes "S,f \<turnstile> (m#ms,s) =as\<Rightarrow>\<^sub>\<tau> (m'#ms',s')" and "valid_node m"
  and "\<forall>i < length rs. rs!i \<in> get_return_edges (cs!i)" 
  and "ms = targetnodes rs" and "valid_return_list rs m"
  and "length rs = length cs"
  shows "m -as\<rightarrow>* m'" and "valid_path_aux cs as"
proof -
  from assms have "m -as\<rightarrow>* m' \<and> valid_path_aux cs as"
  proof(induct S f "m#ms" s as "m'#ms'" s' arbitrary:m cs ms rs
      rule:silent_moves.induct)
    case (silent_moves_Nil msx sx n\<^sub>c f)
    from \<open>valid_node m'\<close> have "m' -[]\<rightarrow>* m'"
      by (rule empty_path)
    thus ?case by fastforce
  next
    case (silent_moves_Cons S f sx a msx' sx' as s'')
    thus ?case
    proof(induct _ _ "m # ms" _ _ _ _ rule:silent_move.induct)
      case (silent_move_intra f a sx sx' n\<^sub>c msx')
      note IH = \<open>\<And>m cs ms rs. \<lbrakk>msx' = m # ms; valid_node m;
        \<forall>i<length rs. rs ! i \<in> get_return_edges (cs ! i); 
        ms = targetnodes rs; valid_return_list rs m;
        length rs = length cs\<rbrakk>
        \<Longrightarrow> m -as\<rightarrow>* m' \<and> valid_path_aux cs as\<close>
      from \<open>msx' = targetnode a # tl (m # ms)\<close>
      have "msx' = targetnode a # ms" by simp
      from \<open>valid_edge a\<close> \<open>intra_kind (kind a)\<close>
      have "get_proc (sourcenode a) = get_proc (targetnode a)"
        by(rule get_proc_intra)
      with \<open>valid_return_list rs m\<close> \<open>hd (m # ms) = sourcenode a\<close>
      have "valid_return_list rs (targetnode a)"
        apply(clarsimp simp:valid_return_list_def)
        apply(erule_tac x="cs'" in allE) apply clarsimp
        by(case_tac cs') auto
      from \<open>valid_edge a\<close> have "valid_node (targetnode a)" by simp
      from IH[OF \<open>msx' = targetnode a # ms\<close> this 
        \<open>\<forall>i<length rs. rs ! i \<in> get_return_edges (cs ! i)\<close>
        \<open>ms = targetnodes rs\<close> \<open>valid_return_list rs (targetnode a)\<close>
        \<open>length rs = length cs\<close>]
      have "targetnode a -as\<rightarrow>* m'" and "valid_path_aux cs as" by simp_all
      from \<open>valid_edge a\<close> \<open>targetnode a -as\<rightarrow>* m'\<close> 
        \<open>hd (m # ms) = sourcenode a\<close>
      have "m -a#as\<rightarrow>* m'" by(fastforce intro:Cons_path)
      moreover
      from \<open>intra_kind (kind a)\<close> \<open>valid_path_aux cs as\<close>
      have "valid_path_aux cs (a # as)" by(fastforce simp:intra_kind_def)
      ultimately show ?case by simp
    next
      case (silent_move_call f a sx sx' Q r p fs a' n\<^sub>c msx')
      note IH = \<open>\<And>m cs ms rs. \<lbrakk>msx' = m # ms; valid_node m;
        \<forall>i<length rs. rs ! i \<in> get_return_edges (cs ! i); 
        ms = targetnodes rs; valid_return_list rs m;
        length rs = length cs\<rbrakk>
        \<Longrightarrow> m -as\<rightarrow>* m' \<and> valid_path_aux cs as\<close>
      from \<open>valid_edge a\<close> have "valid_node (targetnode a)" by simp
      from \<open>length rs = length cs\<close> 
      have "length (a'#rs) = length (a#cs)" by simp
      from \<open>msx' = targetnode a # targetnode a' # tl (m # ms)\<close>
      have "msx' = targetnode a # targetnode a' # ms" by simp
      from \<open>ms = targetnodes rs\<close> have "targetnode a' # ms = targetnodes (a' # rs)"
        by(simp add:targetnodes_def)
      from \<open>valid_edge a\<close> \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close> have "get_proc (targetnode a) = p"
        by(rule get_proc_call)
      from \<open>valid_edge a\<close> \<open>a' \<in> get_return_edges a\<close> have "valid_edge a'"
        by(rule get_return_edges_valid)
      from \<open>valid_edge a\<close> \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close> \<open>a' \<in> get_return_edges a\<close>
      obtain Q' f' where "kind a' = Q'\<hookleftarrow>\<^bsub>p\<^esub>f'" by(fastforce dest!:call_return_edges)
      from \<open>valid_edge a\<close> \<open>a' \<in> get_return_edges a\<close>
      have "get_proc (sourcenode a) = get_proc (targetnode a')"
        by(rule get_proc_get_return_edge)
      with \<open>valid_return_list rs m\<close> \<open>hd (m # ms) = sourcenode a\<close>
        \<open>get_proc (targetnode a) = p\<close> \<open>valid_edge a'\<close> \<open>kind a' = Q'\<hookleftarrow>\<^bsub>p\<^esub>f'\<close>
      have "valid_return_list (a' # rs) (targetnode a)"
        apply(clarsimp simp:valid_return_list_def)
        apply(case_tac cs') apply auto
        apply(erule_tac x="list" in allE) apply clarsimp
        by(case_tac list)(auto simp:targetnodes_def)
      from \<open>\<forall>i<length rs. rs ! i \<in> get_return_edges (cs ! i)\<close> 
        \<open>a' \<in> get_return_edges a\<close>
      have "\<forall>i<length (a'#rs). (a'#rs) ! i \<in> get_return_edges ((a#cs) ! i)"
        by auto(case_tac i,auto)
      from IH[OF \<open>msx' = targetnode a # targetnode a' # ms\<close> \<open>valid_node (targetnode a)\<close> this 
        \<open>targetnode a' # ms = targetnodes (a' # rs)\<close> 
        \<open>valid_return_list (a' # rs) (targetnode a)\<close> \<open>length (a'#rs) = length (a#cs)\<close>]
      have "targetnode a -as\<rightarrow>* m'" and "valid_path_aux (a # cs) as" by simp_all
      from \<open>valid_edge a\<close> \<open>targetnode a -as\<rightarrow>* m'\<close> 
        \<open>hd (m # ms) = sourcenode a\<close>
      have "m -a#as\<rightarrow>* m'" by(fastforce intro:Cons_path)
      moreover
      from \<open>valid_path_aux (a # cs) as\<close> \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close>
      have "valid_path_aux cs (a # as)" by simp
      ultimately show ?case by simp
    next
      case (silent_move_return f a sx sx' Q p f' n\<^sub>c msx')
      note IH = \<open>\<And>m cs ms rs. \<lbrakk>msx' = m # ms; valid_node m;
        \<forall>i<length rs. rs ! i \<in> get_return_edges (cs ! i); 
        ms = targetnodes rs; valid_return_list rs m;
        length rs = length cs\<rbrakk>
        \<Longrightarrow> m -as\<rightarrow>* m' \<and> valid_path_aux cs as\<close>
      from \<open>valid_edge a\<close> have "valid_node (targetnode a)" by simp
      from \<open>length (m # ms) = length sx\<close> \<open>length sx = Suc (length sx')\<close> 
        \<open>sx' \<noteq> []\<close>
      obtain x xs where "ms = x#xs" by(cases ms) auto
      with \<open>ms = targetnodes rs\<close> obtain r' rs' where "rs = r'#rs'" 
        and "x = targetnode r'" and "xs = targetnodes rs'" 
        by(auto simp:targetnodes_def)
      with \<open>length rs = length cs\<close> obtain c' cs' where "cs = c'#cs'"
        and "length rs' = length cs'"
        by(cases cs) auto
      from \<open>ms = x#xs\<close> \<open>length (m # ms) = length sx\<close> 
        \<open>length sx = Suc (length sx')\<close>
      have "length sx' = Suc (length xs)" by simp
      from \<open>ms = x#xs\<close> \<open>msx' = tl (m # ms)\<close> \<open>hd (tl (m # ms)) = targetnode a\<close>
        \<open>length (m # ms) = length sx\<close> \<open>length sx = Suc (length sx')\<close> \<open>sx' \<noteq> []\<close>
      have "msx' = targetnode a#xs" by simp
      from \<open>\<forall>i<length rs. rs ! i \<in> get_return_edges (cs ! i)\<close> 
        \<open>rs = r'#rs'\<close> \<open>cs = c'#cs'\<close>
      have "r' \<in> get_return_edges c'" by fastforce
      from \<open>ms = x#xs\<close> \<open>hd (tl (m # ms)) = targetnode a\<close>
      have "x = targetnode a" by simp
      with \<open>valid_return_list rs m\<close> \<open>rs = r'#rs'\<close> \<open>x = targetnode r'\<close>
      have "valid_return_list rs' (targetnode a)"
        apply(clarsimp simp:valid_return_list_def)
        apply(erule_tac x="r'#cs'" in allE) apply clarsimp
        by(case_tac cs')(auto simp:targetnodes_def)
      from \<open>\<forall>i<length rs. rs ! i \<in> get_return_edges (cs ! i)\<close> 
        \<open>rs = r'#rs'\<close> \<open>cs = c'#cs'\<close>
      have "\<forall>i<length rs'. rs' ! i \<in> get_return_edges (cs' ! i)"
        and "r' \<in> get_return_edges c'" by auto
      from IH[OF \<open>msx' = targetnode a#xs\<close> \<open>valid_node (targetnode a)\<close> 
        \<open>\<forall>i<length rs'. rs' ! i \<in> get_return_edges (cs' ! i)\<close> \<open>xs = targetnodes rs'\<close>
        \<open>valid_return_list rs' (targetnode a)\<close> \<open>length rs' = length cs'\<close>]
      have "targetnode a -as\<rightarrow>* m'" and "valid_path_aux cs' as" by simp_all
      from \<open>valid_edge a\<close> \<open>targetnode a -as\<rightarrow>* m'\<close> 
        \<open>hd (m # ms) = sourcenode a\<close>
      have "m -a#as\<rightarrow>* m'" by(fastforce intro:Cons_path)
      moreover
      from \<open>ms = x#xs\<close> \<open>hd (tl (m # ms)) = targetnode a\<close>
      have "x = targetnode a" by simp
      from \<open>valid_edge a\<close> \<open>kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f'\<close>
      have "method_exit (sourcenode a)" by(fastforce simp:method_exit_def)
      from \<open>valid_return_list rs m\<close> \<open>hd (m # ms) = sourcenode a\<close> 
        \<open>rs = r'#rs'\<close>
      have "get_proc (sourcenode a) = get_proc (sourcenode r') \<and>
        method_exit (sourcenode r') \<and> valid_edge r'"
        apply(clarsimp simp:valid_return_list_def method_exit_def)
        apply(erule_tac x="[]" in allE) 
        by(auto dest:get_proc_return)
      hence "get_proc (sourcenode a) = get_proc (sourcenode r')"
        and "method_exit (sourcenode r')" and "valid_edge r'" by simp_all
      with \<open>method_exit (sourcenode a)\<close> have "sourcenode r' = sourcenode a"
        by(fastforce intro:method_exit_unique)
      with \<open>valid_edge a\<close> \<open>valid_edge r'\<close> \<open>x = targetnode r'\<close> \<open>x = targetnode a\<close>
      have "r' = a" by(fastforce intro:edge_det)
      with \<open>r' \<in> get_return_edges c'\<close> \<open>valid_path_aux cs' as\<close> \<open>cs = c'#cs'\<close> 
        \<open>kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f'\<close>
      have "valid_path_aux cs (a # as)" by simp
      ultimately show ?case by simp
    qed
  qed
  thus "m -as\<rightarrow>* m'" and "valid_path_aux cs as" by simp_all
qed



subsection \<open>Observable moves\<close>


inductive observable_move ::
  "'node SDG_node set \<Rightarrow> ('edge \<Rightarrow> ('var,'val,'ret,'pname) edge_kind) \<Rightarrow> 'node list \<Rightarrow> 
   (('var \<rightharpoonup> 'val) \<times> 'ret) list \<Rightarrow> 'edge \<Rightarrow> 'node list \<Rightarrow> (('var \<rightharpoonup> 'val) \<times> 'ret) list \<Rightarrow> bool"
("_,_ \<turnstile> '(_,_') -_\<rightarrow> '(_,_')" [51,50,0,0,50,0,0] 51) 
 
  where observable_move_intra:
  "\<lbrakk>pred (f a) s; transfer (f a) s = s'; valid_edge a; intra_kind(kind a); 
    \<forall>m \<in> set (tl ms). \<exists>m'. call_of_return_node m m' \<and> m' \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>;
    hd ms \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>; length s' = length s; length ms = length s;
    hd ms = sourcenode a; ms' = (targetnode a)#tl ms\<rbrakk>  
  \<Longrightarrow> S,f \<turnstile> (ms,s) -a\<rightarrow> (ms',s')"

  | observable_move_call:
  "\<lbrakk>pred (f a) s; transfer (f a) s = s'; valid_edge a; kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs; 
    valid_edge a'; a' \<in> get_return_edges a;
    \<forall>m \<in> set (tl ms). \<exists>m'. call_of_return_node m m' \<and> m' \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>;
    hd ms \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>; length ms = length s; length s' = Suc(length s); 
    hd ms = sourcenode a; ms' = (targetnode a)#(targetnode a')#tl ms\<rbrakk>  
  \<Longrightarrow> S,f \<turnstile> (ms,s) -a\<rightarrow> (ms',s')"

  | observable_move_return:
  "\<lbrakk>pred (f a) s; transfer (f a) s = s'; valid_edge a; kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f'; 
    \<forall>m \<in> set (tl ms). \<exists>m'. call_of_return_node m m' \<and> m' \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>;
    length ms = length s; length s = Suc(length s'); s' \<noteq> [];
    hd ms = sourcenode a; hd(tl ms) = targetnode a; ms' = tl ms\<rbrakk>  
  \<Longrightarrow> S,f \<turnstile> (ms,s) -a\<rightarrow> (ms',s')"



inductive observable_moves :: 
  "'node SDG_node set \<Rightarrow> ('edge \<Rightarrow> ('var,'val,'ret,'pname) edge_kind) \<Rightarrow> 'node list \<Rightarrow> 
   (('var \<rightharpoonup> 'val) \<times> 'ret) list \<Rightarrow> 'edge list \<Rightarrow> 'node list \<Rightarrow> (('var \<rightharpoonup> 'val) \<times> 'ret) list \<Rightarrow> bool"
("_,_ \<turnstile> '(_,_') =_\<Rightarrow> '(_,_')" [51,50,0,0,50,0,0] 51) 

  where observable_moves_snoc:
  "\<lbrakk>S,f \<turnstile> (ms,s) =as\<Rightarrow>\<^sub>\<tau> (ms',s'); S,f \<turnstile> (ms',s') -a\<rightarrow> (ms'',s'')\<rbrakk> 
  \<Longrightarrow> S,f \<turnstile> (ms,s) =as@[a]\<Rightarrow> (ms'',s'')"


lemma observable_move_equal_length:
  assumes "S,f \<turnstile> (ms,s) -a\<rightarrow> (ms',s')" 
  shows "length ms = length s" and "length ms' = length s'"
proof -
  from \<open>S,f \<turnstile> (ms,s) -a\<rightarrow> (ms',s')\<close>
  have "length ms = length s \<and> length ms' = length s'"
  proof(induct rule:observable_move.induct)
    case (observable_move_intra f a s s' ms S ms')
    from \<open>pred (f a) s\<close> obtain cf cfs where [simp]:"s = cf#cfs" by(cases s) auto
    from \<open>length ms = length s\<close> \<open>ms' = targetnode a # tl ms\<close>
      \<open>length s' = length s\<close> show ?case by simp
  next
    case (observable_move_call f a s s' Q r p fs a' ms S ms')
    from \<open>pred (f a) s\<close> obtain cf cfs where [simp]:"s = cf#cfs" by(cases s) auto
    from \<open>length ms = length s\<close> \<open>length s' = Suc (length s)\<close> 
      \<open>ms' = targetnode a # targetnode a' # tl ms\<close> show ?case by simp
  next
    case (observable_move_return f a s s' Q p f' ms S ms')
    from \<open>length ms = length s\<close> \<open>length s = Suc (length s')\<close> \<open>ms' = tl ms\<close> \<open>s' \<noteq> []\<close>
    show ?case by simp
  qed
  thus "length ms = length s" and "length ms' = length s'" by simp_all
qed


lemma observable_moves_equal_length:
  assumes "S,f \<turnstile> (ms,s) =as\<Rightarrow> (ms',s')" 
  shows "length ms = length s" and "length ms' = length s'"
  using \<open>S,f \<turnstile> (ms,s) =as\<Rightarrow> (ms',s')\<close>
proof(induct rule:observable_moves.induct)
  case (observable_moves_snoc S f ms s as ms' s' a ms'' s'')
  from \<open>S,f \<turnstile> (ms',s') -a\<rightarrow> (ms'',s'')\<close>
  have "length ms' = length s'" "length ms'' = length s''"
    by(rule observable_move_equal_length)+
  moreover
  from \<open>S,f \<turnstile> (ms,s) =as\<Rightarrow>\<^sub>\<tau> (ms',s')\<close> 
  have "length ms = length s" and "length ms' = length s'"
    by(rule silent_moves_equal_length)+
  ultimately show "length ms = length s" "length ms'' = length s''" by simp_all
qed


lemma observable_move_notempty:
  "\<lbrakk>S,f \<turnstile> (ms,s) =as\<Rightarrow> (ms',s'); as = []\<rbrakk> \<Longrightarrow> False"
by(induct rule:observable_moves.induct,simp)


lemma silent_move_observable_moves:
  "\<lbrakk>S,f \<turnstile> (ms'',s'') =as\<Rightarrow> (ms',s'); S,f \<turnstile> (ms,s) -a\<rightarrow>\<^sub>\<tau> (ms'',s'')\<rbrakk>
  \<Longrightarrow> S,f \<turnstile> (ms,s) =a#as\<Rightarrow> (ms',s')"
proof(induct rule:observable_moves.induct)
  case (observable_moves_snoc S f msx sx as ms' s' a' ms'' s'')
  from \<open>S,f \<turnstile> (ms,s) -a\<rightarrow>\<^sub>\<tau> (msx,sx)\<close> \<open>S,f \<turnstile> (msx,sx) =as\<Rightarrow>\<^sub>\<tau> (ms',s')\<close>
  have "S,f \<turnstile> (ms,s) =a#as\<Rightarrow>\<^sub>\<tau> (ms',s')" by(fastforce intro:silent_moves_Cons)
  with \<open>S,f \<turnstile> (ms',s') -a'\<rightarrow> (ms'',s'')\<close>
  have "S,f \<turnstile> (ms,s) =(a#as)@[a']\<Rightarrow> (ms'',s'')"
    by(fastforce intro:observable_moves.observable_moves_snoc)
  thus ?case by simp
qed


lemma silent_append_observable_moves:
  "\<lbrakk>S,f \<turnstile> (ms,s) =as\<Rightarrow>\<^sub>\<tau> (ms'',s''); S,f \<turnstile> (ms'',s'') =as'\<Rightarrow> (ms',s')\<rbrakk>
  \<Longrightarrow> S,f \<turnstile> (ms,s) =as@as'\<Rightarrow> (ms',s')"
by(induct rule:silent_moves.induct)(auto elim:silent_move_observable_moves)


lemma observable_moves_preds_transfers:
  assumes "S,f \<turnstile> (ms,s) =as\<Rightarrow> (ms',s')"
  shows "preds (map f as) s" and "transfers (map f as) s = s'"
proof -
  from \<open>S,f \<turnstile> (ms,s) =as\<Rightarrow> (ms',s')\<close>
  have "preds (map f as) s \<and> transfers (map f as) s = s'"
  proof(induct rule:observable_moves.induct)
    case (observable_moves_snoc S f ms s as ms' s' a ms'' s'')
    from \<open>S,f \<turnstile> (ms,s) =as\<Rightarrow>\<^sub>\<tau> (ms',s')\<close> 
    have "preds (map f as) s" and "transfers (map f as) s = s'"
      by(rule silent_moves_preds_transfers)+
    from \<open>S,f \<turnstile> (ms',s') -a\<rightarrow> (ms'',s'')\<close>
    have "pred (f a) s'" and "transfer (f a) s' = s''" 
      by(auto elim:observable_move.cases)
    with \<open>preds (map f as) s\<close> \<open>transfers (map f as) s = s'\<close>
    show ?case by(simp add:preds_split transfers_split)
  qed
  thus "preds (map f as) s" and "transfers (map f as) s = s'" by simp_all
qed


lemma observable_move_vpa_path:
  "\<lbrakk>S,f \<turnstile> (m#ms,s) -a\<rightarrow> (m'#ms',s'); valid_node m; 
    \<forall>i < length rs. rs!i \<in> get_return_edges (cs!i); ms = targetnodes rs;
    valid_return_list rs m; length rs = length cs\<rbrakk> \<Longrightarrow> valid_path_aux cs [a]"
proof(induct S f "m#ms" s a "m'#ms'" s' rule:observable_move.induct)
  case (observable_move_return f a sx sx' Q p f' n\<^sub>c)
  from \<open>length (m # ms) = length sx\<close> \<open>length sx = Suc (length sx')\<close> 
    \<open>sx' \<noteq> []\<close>
  obtain x xs where "ms = x#xs" by(cases ms) auto
  with \<open>ms = targetnodes rs\<close> obtain r' rs' where "rs = r'#rs'" 
    and "x = targetnode r'"     and "xs = targetnodes rs'" 
    by(auto simp:targetnodes_def)
  with \<open>length rs = length cs\<close> obtain c' cs' where "cs = c'#cs'"
    and "length rs' = length cs'"
    by(cases cs) auto
  from \<open>\<forall>i<length rs. rs ! i \<in> get_return_edges (cs ! i)\<close> 
    \<open>rs = r'#rs'\<close> \<open>cs = c'#cs'\<close>
  have "\<forall>i<length rs'. rs' ! i \<in> get_return_edges (cs' ! i)"
    and "r' \<in> get_return_edges c'" by auto
  from \<open>ms = x#xs\<close> \<open>hd (tl (m # ms)) = targetnode a\<close>
  have "x = targetnode a" by simp
  from \<open>valid_edge a\<close> \<open>kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f'\<close>
  have "method_exit (sourcenode a)" by(fastforce simp:method_exit_def)
  from \<open>valid_return_list rs m\<close> \<open>hd (m # ms) = sourcenode a\<close> 
    \<open>rs = r'#rs'\<close>
  have "get_proc (sourcenode a) = get_proc (sourcenode r') \<and>
    method_exit (sourcenode r') \<and> valid_edge r'"
    apply(clarsimp simp:valid_return_list_def method_exit_def)
    apply(erule_tac x="[]" in allE) 
    by(auto dest:get_proc_return)
  hence "get_proc (sourcenode a) = get_proc (sourcenode r')"
    and "method_exit (sourcenode r')" and "valid_edge r'" by simp_all
  with \<open>method_exit (sourcenode a)\<close> have "sourcenode r' = sourcenode a"
    by(fastforce intro:method_exit_unique)
  with \<open>valid_edge a\<close> \<open>valid_edge r'\<close> \<open>x = targetnode r'\<close> \<open>x = targetnode a\<close>
  have "r' = a" by(fastforce intro:edge_det)
  with \<open>r' \<in> get_return_edges c'\<close> \<open>cs = c'#cs'\<close> \<open>kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f'\<close>
  show ?case by simp
qed(auto simp:intra_kind_def)
  


subsection \<open>Relevant variables\<close>

inductive_set relevant_vars ::
  "'node SDG_node set \<Rightarrow> 'node SDG_node \<Rightarrow> 'var set" ("rv _")
for S :: "'node SDG_node set" and n :: "'node SDG_node"

where rvI:
  "\<lbrakk>parent_node n -as\<rightarrow>\<^sub>\<iota>* parent_node n'; n' \<in> HRB_slice S; V \<in> Use\<^bsub>SDG\<^esub> n';
    \<forall>n''. valid_SDG_node n'' \<and> parent_node n'' \<in> set (sourcenodes as) 
          \<longrightarrow> V \<notin> Def\<^bsub>SDG\<^esub> n''\<rbrakk>
  \<Longrightarrow> V \<in> rv S n"


lemma rvE:
  assumes rv:"V \<in> rv S n"
  obtains as n' where "parent_node n -as\<rightarrow>\<^sub>\<iota>* parent_node n'"
  and "n' \<in> HRB_slice S" and "V \<in> Use\<^bsub>SDG\<^esub> n'"
  and "\<forall>n''. valid_SDG_node n'' \<and> parent_node n'' \<in> set (sourcenodes as) 
    \<longrightarrow> V \<notin> Def\<^bsub>SDG\<^esub> n''"
using rv
by(atomize_elim,auto elim!:relevant_vars.cases)


lemma rv_parent_node:
  "parent_node n = parent_node n' \<Longrightarrow> rv (S::'node SDG_node set) n = rv S n'"
by(fastforce elim:rvE intro:rvI)


lemma obs_intra_empty_rv_empty:
  assumes "obs_intra m \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {}" shows "rv S (CFG_node m) = {}"
proof(rule ccontr)
  assume "rv S (CFG_node m) \<noteq> {}"
  then obtain x where "x \<in> rv S (CFG_node m)" by fastforce
  then obtain n' as where "m -as\<rightarrow>\<^sub>\<iota>* parent_node n'" and "n' \<in> HRB_slice S"
    by(fastforce elim:rvE)
  hence "parent_node n' \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
    by(fastforce intro:valid_SDG_node_in_slice_parent_node_in_slice 
                 simp:SDG_to_CFG_set_def)
  with \<open>m -as\<rightarrow>\<^sub>\<iota>* parent_node n'\<close> obtain mx where "mx \<in> obs_intra m \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
    by(erule path_ex_obs_intra)
  with \<open>obs_intra m \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {}\<close> show False by simp
qed


lemma eq_obs_intra_in_rv:
  assumes obs_eq:"obs_intra (parent_node n) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = 
                  obs_intra (parent_node n') \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
  and "x \<in> rv S n" shows "x \<in> rv S n'"
proof -
  from \<open>x \<in> rv S n\<close> obtain as n''
    where "parent_node n -as\<rightarrow>\<^sub>\<iota>* parent_node n''" and "n'' \<in> HRB_slice S" 
    and "x \<in> Use\<^bsub>SDG\<^esub> n''" 
    and "\<forall>n''. valid_SDG_node n'' \<and> parent_node n'' \<in> set (sourcenodes as) 
      \<longrightarrow> x \<notin> Def\<^bsub>SDG\<^esub> n''"
    by(erule rvE)
  from \<open>parent_node n -as\<rightarrow>\<^sub>\<iota>* parent_node n''\<close> have "valid_node (parent_node n'')"
    by(fastforce dest:path_valid_node simp:intra_path_def)
  from \<open>parent_node n -as\<rightarrow>\<^sub>\<iota>* parent_node n''\<close> \<open>n'' \<in> HRB_slice S\<close>
  have "\<exists>nx as' as''. parent_node nx \<in> obs_intra (parent_node n) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> \<and> 
                      parent_node n -as'\<rightarrow>\<^sub>\<iota>* parent_node nx \<and>
                      parent_node nx -as''\<rightarrow>\<^sub>\<iota>* parent_node n'' \<and> as = as'@as''"
  proof(cases "\<forall>nx. parent_node nx \<in> set (sourcenodes as) \<longrightarrow> nx \<notin> HRB_slice S")
    case True
    with \<open>parent_node n -as\<rightarrow>\<^sub>\<iota>* parent_node n''\<close> \<open>n'' \<in> HRB_slice S\<close>
    have "parent_node n'' \<in> obs_intra (parent_node n) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
      by(fastforce intro:obs_intra_elem valid_SDG_node_in_slice_parent_node_in_slice 
                   simp:SDG_to_CFG_set_def)
    with \<open>parent_node n -as\<rightarrow>\<^sub>\<iota>* parent_node n''\<close> \<open>valid_node (parent_node n'')\<close>
    show ?thesis by(fastforce intro:empty_path simp:intra_path_def)
  next
    case False
    hence "\<exists>nx. parent_node nx \<in> set (sourcenodes as) \<and> nx \<in> HRB_slice S" by simp
    hence "\<exists>mx \<in> set (sourcenodes as). \<exists>nx. mx = parent_node nx \<and> nx \<in> HRB_slice S"
      by fastforce
    then obtain mx ms ms' where "sourcenodes as = ms@mx#ms'"
      and "\<exists>nx. mx = parent_node nx \<and> nx \<in> HRB_slice S"
      and all:"\<forall>x \<in> set ms. \<not> (\<exists>nx. x = parent_node nx \<and> nx \<in> HRB_slice S)"
      by(fastforce elim!:split_list_first_propE)
    then obtain nx' where "mx = parent_node nx'" and "nx' \<in> HRB_slice S" by blast
    from \<open>sourcenodes as = ms@mx#ms'\<close>
    obtain as' a' as'' where "ms = sourcenodes as'"
      and [simp]:"as = as'@a'#as''" and "sourcenode a' = mx"
      by(fastforce elim:map_append_append_maps simp:sourcenodes_def)
    from all \<open>ms = sourcenodes as'\<close> 
    have "\<forall>nx\<in>set (sourcenodes as'). nx \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
      by(fastforce simp:SDG_to_CFG_set_def)
    from \<open>parent_node n -as\<rightarrow>\<^sub>\<iota>* parent_node n''\<close> \<open>sourcenode a' = mx\<close>
    have "parent_node n  -as'\<rightarrow>\<^sub>\<iota>* mx" and "valid_edge a'" and "intra_kind(kind a')"
      and "targetnode a' -as''\<rightarrow>\<^sub>\<iota>* parent_node n''"
      by(fastforce dest:path_split simp:intra_path_def)+
    with \<open>sourcenode a' = mx\<close> have "mx -a'#as''\<rightarrow>\<^sub>\<iota>* parent_node n''"
      by(fastforce intro:Cons_path simp:intra_path_def)
    from \<open>parent_node n -as'\<rightarrow>\<^sub>\<iota>* mx\<close> \<open>mx = parent_node nx'\<close> \<open>nx' \<in> HRB_slice S\<close>
      \<open>\<forall>nx\<in>set (sourcenodes as'). nx \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close> \<open>ms = sourcenodes as'\<close>
    have "mx \<in> obs_intra (parent_node n) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
      by(fastforce intro:obs_intra_elem valid_SDG_node_in_slice_parent_node_in_slice
                   simp:SDG_to_CFG_set_def)
    with \<open>parent_node n -as'\<rightarrow>\<^sub>\<iota>* mx\<close> \<open>mx -a'#as''\<rightarrow>\<^sub>\<iota>* parent_node n''\<close>
      \<open>mx = parent_node nx'\<close>
    show ?thesis by simp blast
  qed
  then obtain nx as' as'' 
    where "parent_node nx \<in> obs_intra (parent_node n) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
    and "parent_node n -as'\<rightarrow>\<^sub>\<iota>* parent_node nx" 
    and "parent_node nx -as''\<rightarrow>\<^sub>\<iota>* parent_node n''" and [simp]:"as = as'@as''"
    by blast
  from \<open>parent_node nx \<in> obs_intra (parent_node n) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close> obs_eq
  have "parent_node nx \<in> obs_intra (parent_node n') \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>" by auto
  then obtain asx where "parent_node n' -asx\<rightarrow>\<^sub>\<iota>* parent_node nx" 
    and "\<forall>ni \<in> set(sourcenodes asx). ni \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>" 
    and "parent_node nx \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
    by(erule obs_intraE)
  from \<open>\<forall>n''. valid_SDG_node n'' \<and> parent_node n'' \<in> set (sourcenodes as) 
    \<longrightarrow> x \<notin> Def\<^bsub>SDG\<^esub> n''\<close>
  have "\<forall>ni. valid_SDG_node ni \<and> parent_node ni \<in> set (sourcenodes as'') 
    \<longrightarrow> x \<notin> Def\<^bsub>SDG\<^esub> ni"
    by(auto simp:sourcenodes_def)
  from \<open>\<forall>ni \<in> set(sourcenodes asx). ni \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close>
    \<open>parent_node n' -asx\<rightarrow>\<^sub>\<iota>* parent_node nx\<close>
  have "\<forall>ni. valid_SDG_node ni \<and> parent_node ni \<in> set (sourcenodes asx) 
    \<longrightarrow> x \<notin> Def\<^bsub>SDG\<^esub> ni"
  proof(induct asx arbitrary:n')
    case Nil thus ?case by(simp add:sourcenodes_def)
  next
    case (Cons ax' asx')
    note IH = \<open>\<And>n'. \<lbrakk>\<forall>ni\<in>set (sourcenodes asx'). ni \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>;
      parent_node n' -asx'\<rightarrow>\<^sub>\<iota>* parent_node nx\<rbrakk>
      \<Longrightarrow> \<forall>ni. valid_SDG_node ni \<and> parent_node ni \<in> set (sourcenodes asx') 
              \<longrightarrow> x \<notin> Def\<^bsub>SDG\<^esub> ni\<close>
    from \<open>parent_node n' -ax'#asx'\<rightarrow>\<^sub>\<iota>* parent_node nx\<close>
    have "parent_node n' -[]@ax'#asx'\<rightarrow>* parent_node nx" 
      and "\<forall>a \<in> set (ax'#asx'). intra_kind(kind a)" by(simp_all add:intra_path_def)
    hence "targetnode ax' -asx'\<rightarrow>* parent_node nx" and "valid_edge ax'"
      and "parent_node n' = sourcenode ax'" by(fastforce dest:path_split)+
    with \<open>\<forall>a \<in> set (ax'#asx'). intra_kind(kind a)\<close>
    have path:"parent_node (CFG_node (targetnode ax')) -asx'\<rightarrow>\<^sub>\<iota>* parent_node nx"
      by(simp add:intra_path_def)
    from \<open>\<forall>ni\<in>set (sourcenodes (ax'#asx')). ni \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close>
    have all:"\<forall>ni\<in>set (sourcenodes asx'). ni \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
      and "sourcenode ax' \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
      by(auto simp:sourcenodes_def)
    from IH[OF all path] 
    have "\<forall>ni. valid_SDG_node ni \<and> parent_node ni \<in> set (sourcenodes asx') 
               \<longrightarrow> x \<notin> Def\<^bsub>SDG\<^esub> ni" .
    with \<open>\<forall>ni. valid_SDG_node ni \<and> parent_node ni \<in> set (sourcenodes as'') 
               \<longrightarrow> x \<notin> Def\<^bsub>SDG\<^esub> ni\<close>
    have all:"\<forall>ni. valid_SDG_node ni \<and> parent_node ni \<in> set (sourcenodes (asx'@as'')) 
                   \<longrightarrow> x \<notin> Def\<^bsub>SDG\<^esub> ni"
      by(auto simp:sourcenodes_def)
    from \<open>parent_node n' -ax'#asx'\<rightarrow>\<^sub>\<iota>* parent_node nx\<close> 
      \<open>parent_node nx -as''\<rightarrow>\<^sub>\<iota>* parent_node n''\<close>
    have path:"parent_node n' -ax'#asx'@as''\<rightarrow>\<^sub>\<iota>* parent_node n''"
      by(fastforce intro:path_Append[of _ "ax'#asx'",simplified] simp:intra_path_def)
    have "\<forall>nx'. parent_node nx' = sourcenode ax' \<longrightarrow> x \<notin> Def\<^bsub>SDG\<^esub> nx'"
    proof
      fix nx' 
      show "parent_node nx' = sourcenode ax' \<longrightarrow> x \<notin> Def\<^bsub>SDG\<^esub> nx'"
      proof
        assume "parent_node nx' = sourcenode ax'"
        show "x \<notin> Def\<^bsub>SDG\<^esub> nx'"
        proof
          assume "x \<in> Def\<^bsub>SDG\<^esub> nx'"
          from \<open>parent_node n' = sourcenode ax'\<close> \<open>parent_node nx' = sourcenode ax'\<close>
          have "parent_node nx' = parent_node n'" by simp
          with \<open>x \<in> Def\<^bsub>SDG\<^esub> nx'\<close> \<open>x \<in> Use\<^bsub>SDG\<^esub> n''\<close> all path
          have "nx' influences x in n''" by(fastforce simp:data_dependence_def)
          hence "nx' s-x\<rightarrow>\<^sub>d\<^sub>d n''" by(rule sum_SDG_ddep_edge)
          with \<open>n'' \<in> HRB_slice S\<close> have "nx' \<in> HRB_slice S"
            by(fastforce elim:combine_SDG_slices.cases 
                       intro:combine_SDG_slices.intros ddep_slice1 ddep_slice2 
                        simp:HRB_slice_def)
          hence "CFG_node (parent_node nx') \<in> HRB_slice S"
            by(rule valid_SDG_node_in_slice_parent_node_in_slice)
          with \<open>sourcenode ax' \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close> \<open>parent_node n' = sourcenode ax'\<close>
            \<open>parent_node nx' = sourcenode ax'\<close> show False 
            by(simp add:SDG_to_CFG_set_def)
        qed
      qed
    qed
    with all show ?case by(auto simp add:sourcenodes_def)
  qed
  with \<open>\<forall>ni. valid_SDG_node ni \<and> parent_node ni \<in> set (sourcenodes as'') 
             \<longrightarrow> x \<notin> Def\<^bsub>SDG\<^esub> ni\<close>
  have all:"\<forall>ni. valid_SDG_node ni \<and> parent_node ni \<in> set (sourcenodes (asx@as'')) 
                 \<longrightarrow> x \<notin> Def\<^bsub>SDG\<^esub> ni"
    by(auto simp:sourcenodes_def)
  with \<open>parent_node n' -asx\<rightarrow>\<^sub>\<iota>* parent_node nx\<close> 
    \<open>parent_node nx -as''\<rightarrow>\<^sub>\<iota>* parent_node n''\<close>
  have "parent_node n' -asx@as''\<rightarrow>\<^sub>\<iota>* parent_node n''"
    by(fastforce intro:path_Append simp:intra_path_def)
  from this \<open>n'' \<in> HRB_slice S\<close> \<open>x \<in> Use\<^bsub>SDG\<^esub> n''\<close> all
  show "x \<in> rv S n'" by(rule rvI)
qed


lemma closed_eq_obs_eq_rvs:
  fixes S :: "'node SDG_node set"
  assumes obs_eq:"obs_intra (parent_node n) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = 
  obs_intra (parent_node n') \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
  shows "rv S n = rv S n'"
proof
  show "rv S n \<subseteq> rv S n'"
  proof
    fix x assume "x \<in> rv S n"
    with obs_eq show "x \<in> rv S n'" by(rule eq_obs_intra_in_rv)
  qed
next
  show "rv S n' \<subseteq> rv S n"
  proof
    fix x assume "x \<in> rv S n'"
    with obs_eq[THEN sym] show "x \<in> rv S n" by(rule eq_obs_intra_in_rv)
  qed
qed



lemma closed_eq_obs_eq_rvs':
  fixes S :: "'node SDG_node set"
  assumes obs_eq:"obs_intra m \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = obs_intra m' \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
  shows "rv S (CFG_node m) = rv S (CFG_node m')"
proof
  show "rv S (CFG_node m) \<subseteq> rv S (CFG_node m')"
  proof
    fix x assume "x \<in> rv S (CFG_node m)"
    with obs_eq show "x \<in> rv S (CFG_node m')" 
      by -(rule eq_obs_intra_in_rv,auto)
  qed
next
  show "rv S (CFG_node m') \<subseteq> rv S (CFG_node m)"
  proof
    fix x assume "x \<in> rv S (CFG_node m')"
    with obs_eq[THEN sym] show "x \<in> rv S (CFG_node m)" 
      by -(rule eq_obs_intra_in_rv,auto)
  qed
qed


lemma rv_branching_edges_slice_kinds_False:
  assumes "valid_edge a" and "valid_edge ax" 
  and "sourcenode a = sourcenode ax" and "targetnode a \<noteq> targetnode ax"
  and "intra_kind (kind a)" and "intra_kind (kind ax)"
  and "preds (slice_kinds S (a#as)) s" 
  and "preds (slice_kinds S (ax#asx)) s'"
  and "length s = length s'" and "snd (hd s) = snd (hd s')"
  and "\<forall>V\<in>rv S (CFG_node (sourcenode a)). state_val s V = state_val s' V"
  shows False
proof -
  from \<open>valid_edge a\<close> \<open>valid_edge ax\<close> \<open>sourcenode a = sourcenode ax\<close> 
    \<open>targetnode a \<noteq> targetnode ax\<close> \<open>intra_kind (kind a)\<close> \<open>intra_kind (kind ax)\<close>
  obtain Q Q' where "kind a = (Q)\<^sub>\<surd>" and "kind ax = (Q')\<^sub>\<surd>"
    and "\<forall>s. (Q s \<longrightarrow> \<not> Q' s) \<and> (Q' s \<longrightarrow> \<not> Q s)"
    by(auto dest:deterministic)
  from \<open>valid_edge a\<close> \<open>valid_edge ax\<close> \<open>sourcenode a = sourcenode ax\<close> 
    \<open>targetnode a \<noteq> targetnode ax\<close> \<open>intra_kind (kind a)\<close> \<open>intra_kind (kind ax)\<close>
  obtain P P' where "slice_kind S a = (P)\<^sub>\<surd>" 
    and "slice_kind S ax = (P')\<^sub>\<surd>"
    and "\<forall>s. (P s \<longrightarrow> \<not> P' s) \<and> (P' s \<longrightarrow> \<not> P s)"
    by -(erule slice_deterministic,auto)
  show ?thesis
  proof(cases "sourcenode a \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>")
    case True
    with \<open>intra_kind (kind a)\<close>
    have "slice_kind S a = kind a" by -(rule slice_intra_kind_in_slice)
    with \<open>preds (slice_kinds S (a#as)) s\<close> \<open>kind a = (Q)\<^sub>\<surd>\<close> 
      \<open>slice_kind S a = (P)\<^sub>\<surd>\<close> have "pred (kind a) s"
      by(simp add:slice_kinds_def)
    from True \<open>sourcenode a = sourcenode ax\<close> \<open>intra_kind (kind ax)\<close>
    have "slice_kind S ax = kind ax" 
      by(fastforce intro:slice_intra_kind_in_slice)
    with \<open>preds (slice_kinds S (ax#asx)) s'\<close> \<open>kind ax = (Q')\<^sub>\<surd>\<close>
      \<open>slice_kind S ax = (P')\<^sub>\<surd>\<close> have "pred (kind ax) s'" 
      by(simp add:slice_kinds_def)
    with \<open>kind ax = (Q')\<^sub>\<surd>\<close> have "Q' (fst (hd s'))" by(cases s') auto
    from \<open>valid_edge a\<close> have "sourcenode a -[]\<rightarrow>\<^sub>\<iota>* sourcenode a"
      by(fastforce intro:empty_path simp:intra_path_def)
    with True \<open>valid_edge a\<close>
    have "\<forall>V \<in> Use (sourcenode a). V \<in> rv S (CFG_node (sourcenode a))"
      by(auto intro!:rvI CFG_Use_SDG_Use simp:sourcenodes_def SDG_to_CFG_set_def)
    with \<open>\<forall>V\<in>rv S (CFG_node (sourcenode a)). state_val s V = state_val s' V\<close>
    have "\<forall>V \<in> Use (sourcenode a). state_val s V = state_val s' V" by blast
    with \<open>valid_edge a\<close> \<open>pred (kind a) s\<close> \<open>pred (kind ax) s'\<close> \<open>length s = length s'\<close>
      \<open>snd (hd s) = snd (hd s')\<close>
    have "pred (kind a) s'" by(auto intro:CFG_edge_Uses_pred_equal)
    with \<open>kind a = (Q)\<^sub>\<surd>\<close> have "Q (fst (hd s'))" by(cases s') auto
    with \<open>Q' (fst (hd s'))\<close> \<open>\<forall>s. (Q s \<longrightarrow> \<not> Q' s) \<and> (Q' s \<longrightarrow> \<not> Q s)\<close>
    have False by simp
    thus ?thesis by simp
  next
    case False
    with \<open>kind a = (Q)\<^sub>\<surd>\<close> \<open>slice_kind S a = (P)\<^sub>\<surd>\<close> \<open>valid_edge a\<close>
    have "P = (\<lambda>s. False) \<or> P = (\<lambda>s. True)"
      by(fastforce elim:kind_Predicate_notin_slice_slice_kind_Predicate)
    with \<open>slice_kind S a = (P)\<^sub>\<surd>\<close> 
      \<open>preds (slice_kinds S (a#as)) s\<close>
    have "P = (\<lambda>s. True)" by(cases s)(auto simp:slice_kinds_def)
    from \<open>sourcenode a = sourcenode ax\<close> False
    have "sourcenode ax \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>" by simp
    with \<open>kind ax = (Q')\<^sub>\<surd>\<close> \<open>slice_kind S ax = (P')\<^sub>\<surd>\<close> \<open>valid_edge ax\<close>
    have "P' = (\<lambda>s. False) \<or> P' = (\<lambda>s. True)"
      by(fastforce elim:kind_Predicate_notin_slice_slice_kind_Predicate)
    with \<open>slice_kind S ax = (P')\<^sub>\<surd>\<close> 
      \<open>preds (slice_kinds S (ax#asx)) s'\<close>
    have "P' = (\<lambda>s. True)" by(cases s')(auto simp:slice_kinds_def)
    with \<open>P = (\<lambda>s. True)\<close> \<open>\<forall>s. (P s \<longrightarrow> \<not> P' s) \<and> (P' s \<longrightarrow> \<not> P s)\<close>
    have False by blast
    thus ?thesis by simp
  qed
qed


lemma rv_edge_slice_kinds:
  assumes "valid_edge a" and "intra_kind (kind a)"
  and "\<forall>V\<in>rv S (CFG_node (sourcenode a)). state_val s V = state_val s' V"
  and "preds (slice_kinds S (a#as)) s" and "preds (slice_kinds S (a#asx)) s'"
  shows "\<forall>V\<in>rv S (CFG_node (targetnode a)). 
  state_val (transfer (slice_kind S a) s) V = 
  state_val (transfer (slice_kind S a) s') V"
proof
  fix V assume "V \<in> rv S (CFG_node (targetnode a))"
  from \<open>preds (slice_kinds S (a#as)) s\<close>
  have "s \<noteq> []" by(cases s,auto simp:slice_kinds_def)
  from \<open>preds (slice_kinds S (a#asx)) s'\<close>
  have "s' \<noteq> []" by(cases s',auto simp:slice_kinds_def)
  show "state_val (transfer (slice_kind S a) s) V =
    state_val (transfer (slice_kind S a) s') V"
  proof(cases "V \<in> Def (sourcenode a)")
    case True
    show ?thesis
    proof(cases "sourcenode a \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>")
      case True
      with \<open>intra_kind (kind a)\<close> have "slice_kind S a = kind a"
        by -(rule slice_intra_kind_in_slice)
      with \<open>preds (slice_kinds S (a#as)) s\<close> have "pred (kind a) s"
        by(simp add:slice_kinds_def)
      from \<open>slice_kind S a = kind a\<close> 
        \<open>preds (slice_kinds S (a#asx)) s'\<close>
      have "pred (kind a) s'" by(simp add:slice_kinds_def)
      from \<open>valid_edge a\<close> have "sourcenode a -[]\<rightarrow>\<^sub>\<iota>* sourcenode a"
        by(fastforce intro:empty_path simp:intra_path_def)
      with True \<open>valid_edge a\<close>
      have "\<forall>V \<in> Use (sourcenode a). V \<in> rv S (CFG_node (sourcenode a))"
        by(auto intro!:rvI CFG_Use_SDG_Use simp:sourcenodes_def SDG_to_CFG_set_def)
      with \<open>\<forall>V\<in>rv S (CFG_node (sourcenode a)). state_val s V = state_val s' V\<close>
      have "\<forall>V \<in> Use (sourcenode a). state_val s V = state_val s' V" by blast
      from \<open>valid_edge a\<close> this \<open>pred (kind a) s\<close> \<open>pred (kind a) s'\<close>
        \<open>intra_kind (kind a)\<close>
      have "\<forall>V \<in> Def (sourcenode a). 
        state_val (transfer (kind a) s) V = state_val (transfer (kind a) s') V"
        by -(rule CFG_intra_edge_transfer_uses_only_Use,auto)
      with \<open>V \<in> Def (sourcenode a)\<close> \<open>slice_kind S a = kind a\<close>
      show ?thesis by simp
    next
      case False
      from \<open>V \<in> rv S (CFG_node (targetnode a))\<close> 
      obtain xs nx where "targetnode a -xs\<rightarrow>\<^sub>\<iota>* parent_node nx"
        and "nx \<in> HRB_slice S" and "V \<in> Use\<^bsub>SDG\<^esub> nx"
        and "\<forall>n''. valid_SDG_node n'' \<and> parent_node n'' \<in> set (sourcenodes xs) 
          \<longrightarrow> V \<notin> Def\<^bsub>SDG\<^esub> n''" by(fastforce elim:rvE)
      from \<open>valid_edge a\<close> have "valid_node (sourcenode a)" by simp
      from \<open>valid_edge a\<close> \<open>targetnode a -xs\<rightarrow>\<^sub>\<iota>* parent_node nx\<close> \<open>intra_kind (kind a)\<close>
      have "sourcenode a -a#xs \<rightarrow>\<^sub>\<iota>* parent_node nx"
        by(fastforce intro:path.Cons_path simp:intra_path_def)
      with \<open>V \<in> Def (sourcenode a)\<close> \<open>V \<in> Use\<^bsub>SDG\<^esub> nx\<close> \<open>valid_node (sourcenode a)\<close>
        \<open>\<forall>n''. valid_SDG_node n'' \<and> parent_node n'' \<in> set (sourcenodes xs) 
        \<longrightarrow> V \<notin> Def\<^bsub>SDG\<^esub> n''\<close>
      have "(CFG_node (sourcenode a)) influences V in nx"
        by(fastforce intro:CFG_Def_SDG_Def simp:data_dependence_def)
      hence "(CFG_node (sourcenode a)) s-V\<rightarrow>\<^sub>d\<^sub>d nx" by(rule sum_SDG_ddep_edge)
      from \<open>nx \<in> HRB_slice S\<close> \<open>(CFG_node (sourcenode a)) s-V\<rightarrow>\<^sub>d\<^sub>d nx\<close>
      have "CFG_node (sourcenode a) \<in> HRB_slice S"
      proof(induct rule:HRB_slice_cases)
        case (phase1 n nx')
        with \<open>(CFG_node (sourcenode a)) s-V\<rightarrow>\<^sub>d\<^sub>d nx\<close> show ?case
          by(fastforce intro:intro:ddep_slice1 combine_SDG_slices.combSlice_refl 
                       simp:HRB_slice_def)
      next
        case (phase2 nx' n' n'' p n)
        from \<open>(CFG_node (sourcenode a)) s-V\<rightarrow>\<^sub>d\<^sub>d n\<close> \<open>n \<in> sum_SDG_slice2 n'\<close>
        have "CFG_node (sourcenode a) \<in> sum_SDG_slice2 n'" by(rule ddep_slice2)
        with phase2 show ?thesis
          by(fastforce intro:combine_SDG_slices.combSlice_Return_parent_node 
                       simp:HRB_slice_def)
      qed
      with False have False by(simp add:SDG_to_CFG_set_def)
      thus ?thesis by simp
    qed
  next
    case False
    from \<open>V \<in> rv S (CFG_node (targetnode a))\<close> 
    obtain xs nx where "targetnode a -xs\<rightarrow>\<^sub>\<iota>* parent_node nx"
      and "nx \<in> HRB_slice S" and "V \<in> Use\<^bsub>SDG\<^esub> nx"
      and all:"\<forall>n''. valid_SDG_node n'' \<and> parent_node n'' \<in> set (sourcenodes xs) 
                 \<longrightarrow> V \<notin> Def\<^bsub>SDG\<^esub> n''" by(fastforce elim:rvE)
    from \<open>valid_edge a\<close> have "valid_node (sourcenode a)" by simp
    from \<open>valid_edge a\<close> \<open>targetnode a -xs\<rightarrow>\<^sub>\<iota>* parent_node nx\<close> \<open>intra_kind (kind a)\<close>
    have "sourcenode a -a#xs \<rightarrow>\<^sub>\<iota>* parent_node nx"
      by(fastforce intro:path.Cons_path simp:intra_path_def)
    from False all
    have "\<forall>n''. valid_SDG_node n'' \<and> parent_node n'' \<in> set (sourcenodes (a#xs)) 
                 \<longrightarrow> V \<notin> Def\<^bsub>SDG\<^esub> n''"
      by(fastforce dest:SDG_Def_parent_Def simp:sourcenodes_def)
    with \<open>sourcenode a -a#xs \<rightarrow>\<^sub>\<iota>* parent_node nx\<close> \<open>nx \<in> HRB_slice S\<close>
      \<open>V \<in> Use\<^bsub>SDG\<^esub> nx\<close>
    have "V \<in> rv S (CFG_node (sourcenode a))" by(fastforce intro:rvI)
    from \<open>intra_kind (kind a)\<close> show ?thesis
    proof(cases "kind a")
      case(UpdateEdge f)
      show ?thesis
      proof(cases "sourcenode a \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>")
        case True
        with \<open>intra_kind (kind a)\<close> have "slice_kind S a = kind a"
          by(fastforce intro:slice_intra_kind_in_slice)
        from UpdateEdge \<open>s \<noteq> []\<close> have "pred (kind a) s" by(cases s) auto
        with \<open>valid_edge a\<close> \<open>V \<notin> Def (sourcenode a)\<close> \<open>intra_kind (kind a)\<close>
        have "state_val (transfer (kind a) s) V = state_val s V"
          by(fastforce intro:CFG_intra_edge_no_Def_equal)
        from UpdateEdge \<open>s' \<noteq> []\<close> have "pred (kind a) s'" by(cases s') auto
        with \<open>valid_edge a\<close> \<open>V \<notin> Def (sourcenode a)\<close> \<open>intra_kind (kind a)\<close>
        have "state_val (transfer (kind a) s') V = state_val s' V"
          by(fastforce intro:CFG_intra_edge_no_Def_equal)
        with \<open>\<forall>V\<in>rv S (CFG_node (sourcenode a)). state_val s V = state_val s' V\<close>
          \<open>state_val (transfer (kind a) s) V = state_val s V\<close>
          \<open>V \<in> rv S (CFG_node (sourcenode a))\<close> \<open>slice_kind S a = kind a\<close>
        show ?thesis by fastforce
      next
        case False
        with UpdateEdge have "slice_kind S a = \<Up>id" 
          by -(rule slice_kind_Upd)
        with \<open>\<forall>V\<in>rv S (CFG_node (sourcenode a)). state_val s V = state_val s' V\<close>
          \<open>V \<in> rv S (CFG_node (sourcenode a))\<close> \<open>s \<noteq> []\<close> \<open>s' \<noteq> []\<close>
        show ?thesis by(cases s,auto,cases s',auto)
      qed
    next
      case (PredicateEdge Q)
      show ?thesis
      proof(cases "sourcenode a \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>")
        case True
        with PredicateEdge \<open>intra_kind (kind a)\<close> 
        have "slice_kind S a = (Q)\<^sub>\<surd>"
          by(simp add:slice_intra_kind_in_slice)
        with \<open>\<forall>V\<in>rv S (CFG_node (sourcenode a)). state_val s V = state_val s' V\<close>
          \<open>V \<in> rv S (CFG_node (sourcenode a))\<close> \<open>s \<noteq> []\<close> \<open>s' \<noteq> []\<close>
        show ?thesis by(cases s,auto,cases s',auto)
      next
        case False
        with PredicateEdge \<open>valid_edge a\<close> 
        obtain Q' where "slice_kind S a = (Q')\<^sub>\<surd>" 
          by -(erule kind_Predicate_notin_slice_slice_kind_Predicate)
        with\<open>\<forall>V\<in>rv S (CFG_node (sourcenode a)). state_val s V = state_val s' V\<close>
          \<open>V \<in> rv S (CFG_node (sourcenode a))\<close> \<open>s \<noteq> []\<close> \<open>s' \<noteq> []\<close>
        show ?thesis by(cases s,auto,cases s',auto)
      qed
    qed (auto simp:intra_kind_def)
  qed
qed



subsection \<open>The weak simulation relational set \<open>WS\<close>\<close>

inductive_set WS :: "'node SDG_node set \<Rightarrow> (('node list \<times> (('var \<rightharpoonup> 'val) \<times> 'ret) list) \<times> 
  ('node list \<times> (('var \<rightharpoonup> 'val) \<times> 'ret) list)) set"
for S :: "'node SDG_node set"
  where WSI: "\<lbrakk>\<forall>m \<in> set ms. valid_node m; \<forall>m' \<in> set ms'. valid_node m'; 
  length ms = length s; length ms' = length s'; s \<noteq> []; s' \<noteq> []; ms = msx@mx#tl ms';
  get_proc mx = get_proc (hd ms'); 
  \<forall>m \<in> set (tl ms'). \<exists>m'. call_of_return_node m m' \<and> m' \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>;
  msx \<noteq> [] \<longrightarrow> (\<exists>mx'. call_of_return_node mx mx' \<and> mx' \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>);
  \<forall>i < length ms'. snd (s!(length msx + i)) = snd (s'!i);
  \<forall>m \<in> set (tl ms). return_node m;
  \<forall>i < length ms'. \<forall>V \<in> rv S (CFG_node ((mx#tl ms')!i)). 
    (fst (s!(length msx + i))) V = (fst (s'!i)) V;
  obs ms \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = obs ms' \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<rbrakk>
  \<Longrightarrow> ((ms,s),(ms',s')) \<in> WS S"


lemma WS_silent_move:
  assumes "S,kind \<turnstile> (ms\<^sub>1,s\<^sub>1) -a\<rightarrow>\<^sub>\<tau> (ms\<^sub>1',s\<^sub>1')" and "((ms\<^sub>1,s\<^sub>1),(ms\<^sub>2,s\<^sub>2)) \<in> WS S"
  shows "((ms\<^sub>1',s\<^sub>1'),(ms\<^sub>2,s\<^sub>2)) \<in> WS S"
proof -
  from \<open>((ms\<^sub>1,s\<^sub>1),(ms\<^sub>2,s\<^sub>2)) \<in> WS S\<close> obtain msx mx
    where WSE:"\<forall>m \<in> set ms\<^sub>1. valid_node m" "\<forall>m \<in> set ms\<^sub>2. valid_node m"
    "length ms\<^sub>1 = length s\<^sub>1" "length ms\<^sub>2 = length s\<^sub>2" "s\<^sub>1 \<noteq> []" "s\<^sub>2 \<noteq> []" 
    "ms\<^sub>1 = msx@mx#tl ms\<^sub>2" "get_proc mx = get_proc (hd ms\<^sub>2)"
    "\<forall>m \<in> set (tl ms\<^sub>2). \<exists>m'. call_of_return_node m m' \<and> m' \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
    "msx \<noteq> [] \<longrightarrow> (\<exists>mx'. call_of_return_node mx mx' \<and> mx' \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>)"
    "\<forall>m \<in> set (tl ms\<^sub>1). return_node m"
    "\<forall>i < length ms\<^sub>2. snd (s\<^sub>1!(length msx + i)) = snd (s\<^sub>2!i)"
    "\<forall>i < length ms\<^sub>2. \<forall>V \<in> rv S (CFG_node ((mx#tl ms\<^sub>2)!i)). 
      (fst (s\<^sub>1!(length msx + i))) V = (fst (s\<^sub>2!i)) V"
    "obs ms\<^sub>1 \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = obs ms\<^sub>2 \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
    by(fastforce elim:WS.cases)
  { assume "\<forall>m \<in> set (tl ms\<^sub>1'). return_node m"
    have "obs ms\<^sub>1' \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = obs ms\<^sub>2 \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
    proof(cases "obs ms\<^sub>1' \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {}")
      case True
      with \<open>S,kind \<turnstile> (ms\<^sub>1,s\<^sub>1) -a\<rightarrow>\<^sub>\<tau> (ms\<^sub>1',s\<^sub>1')\<close> have "obs ms\<^sub>1 \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {}" 
        by(rule silent_move_empty_obs_slice)
      with \<open>obs ms\<^sub>1 \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = obs ms\<^sub>2 \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close>
        \<open>obs ms\<^sub>1' \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {}\<close>
      show ?thesis by simp
    next
      case False
      from this \<open>\<forall>m \<in> set (tl ms\<^sub>1'). return_node m\<close>
      obtain ms' where "obs ms\<^sub>1' \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {ms'}"
        by(fastforce dest:obs_singleton_element)
      hence "ms' \<in> obs ms\<^sub>1' \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>" by fastforce
      from \<open>S,kind \<turnstile> (ms\<^sub>1,s\<^sub>1) -a\<rightarrow>\<^sub>\<tau> (ms\<^sub>1',s\<^sub>1')\<close> \<open>ms' \<in> obs ms\<^sub>1' \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close> 
        \<open>\<forall>m \<in> set (tl ms\<^sub>1'). return_node m\<close>
      have "ms' \<in> obs ms\<^sub>1 \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>" by(fastforce intro:silent_move_obs_slice)
      from this \<open>\<forall>m \<in> set (tl ms\<^sub>1). return_node m\<close>
      have "obs ms\<^sub>1 \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {ms'}" by(rule obs_singleton_element)
      with \<open>obs ms\<^sub>1' \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {ms'}\<close> 
        \<open>obs ms\<^sub>1 \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = obs ms\<^sub>2 \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close>
      show ?thesis by simp
    qed }
  with \<open>S,kind \<turnstile> (ms\<^sub>1,s\<^sub>1) -a\<rightarrow>\<^sub>\<tau> (ms\<^sub>1',s\<^sub>1')\<close> WSE
  show ?thesis
  proof(induct S f\<equiv>"kind" ms\<^sub>1 s\<^sub>1 a ms\<^sub>1' s\<^sub>1' rule:silent_move.induct)
    case (silent_move_intra a s\<^sub>1 s\<^sub>1' ms\<^sub>1 S ms\<^sub>1')
    note obs_eq = \<open>\<forall>a\<in>set (tl ms\<^sub>1'). return_node a \<Longrightarrow>
      obs ms\<^sub>1' \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = obs ms\<^sub>2 \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close>
    from \<open>s\<^sub>1 \<noteq> []\<close> \<open>s\<^sub>2 \<noteq> []\<close> obtain cf\<^sub>1 cfs\<^sub>1 cf\<^sub>2 cfs\<^sub>2 where [simp]:"s\<^sub>1 = cf\<^sub>1#cfs\<^sub>1" 
    and [simp]:"s\<^sub>2 = cf\<^sub>2#cfs\<^sub>2" by(cases s\<^sub>1,auto,cases s\<^sub>2,fastforce+)
    from \<open>transfer (kind a) s\<^sub>1 = s\<^sub>1'\<close> \<open>intra_kind (kind a)\<close>
    obtain cf\<^sub>1' where [simp]:"s\<^sub>1' = cf\<^sub>1'#cfs\<^sub>1"
      by(cases cf\<^sub>1,cases "kind a",auto simp:intra_kind_def)
    from \<open>\<forall>m \<in> set ms\<^sub>1. valid_node m\<close> \<open>ms\<^sub>1' = targetnode a # tl ms\<^sub>1\<close> \<open>valid_edge a\<close>
    have "\<forall>m \<in> set ms\<^sub>1'. valid_node m" by(cases ms\<^sub>1) auto
    from \<open>length ms\<^sub>1 = length s\<^sub>1\<close> \<open>length s\<^sub>1' = length s\<^sub>1\<close> 
      \<open>ms\<^sub>1' = targetnode a # tl ms\<^sub>1\<close>
    have "length ms\<^sub>1' = length s\<^sub>1'" by(cases ms\<^sub>1) auto
    from \<open>\<forall>m \<in> set (tl ms\<^sub>1). return_node m\<close> \<open>ms\<^sub>1' = targetnode a # tl ms\<^sub>1\<close>
    have "\<forall>m \<in> set (tl ms\<^sub>1'). return_node m" by simp
    from obs_eq[OF this] have "obs ms\<^sub>1' \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = obs ms\<^sub>2 \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>" .
    from \<open>\<forall>i < length ms\<^sub>2. \<forall>V \<in> rv S (CFG_node ((mx#tl ms\<^sub>2)!i)). 
      (fst (s\<^sub>1!(length msx + i))) V = (fst (s\<^sub>2!i)) V\<close> \<open>length ms\<^sub>2 = length s\<^sub>2\<close>
    have "\<forall>V\<in>rv S (CFG_node mx). (fst (s\<^sub>1 ! length msx)) V = state_val s\<^sub>2 V"
      by(cases ms\<^sub>2) auto
    show ?case
    proof(cases msx)
      case Nil
      with \<open>ms\<^sub>1 = msx@mx#tl ms\<^sub>2\<close> \<open>hd ms\<^sub>1 = sourcenode a\<close> 
      have [simp]:"mx = sourcenode a" and [simp]:"tl ms\<^sub>1 = tl ms\<^sub>2" by simp_all
      from \<open>\<forall>m\<in>set (tl ms\<^sub>2). \<exists>m'. call_of_return_node m m' \<and> m' \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close>
        \<open>(\<exists>m\<in>set (tl ms\<^sub>1). \<exists>m'. call_of_return_node m m' \<and> m' \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>) \<or>
        hd ms\<^sub>1 \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close>
      have "hd ms\<^sub>1 \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>" by fastforce
      with \<open>hd ms\<^sub>1 = sourcenode a\<close> have "sourcenode a \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>" by simp
      from \<open>ms\<^sub>1' = targetnode a # tl ms\<^sub>1\<close> have "ms\<^sub>1' = [] @ targetnode a # tl ms\<^sub>2"
        by simp
      from \<open>valid_edge a\<close> \<open>intra_kind(kind a)\<close> 
      have "get_proc (sourcenode a) = get_proc (targetnode a)" by(rule get_proc_intra)
      with \<open>get_proc mx = get_proc (hd ms\<^sub>2)\<close> 
      have "get_proc (targetnode a) = get_proc (hd ms\<^sub>2)" by simp
      from \<open>transfer (kind a) s\<^sub>1 = s\<^sub>1'\<close> \<open>intra_kind (kind a)\<close>
      have "snd cf\<^sub>1' = snd cf\<^sub>1" by(auto simp:intra_kind_def)
      with \<open>\<forall>i<length ms\<^sub>2. snd (s\<^sub>1 ! (length msx + i)) = snd (s\<^sub>2 ! i)\<close> Nil
      have "\<forall>i<length ms\<^sub>2. snd (s\<^sub>1' ! i) = snd (s\<^sub>2 ! i)"
        by auto(case_tac i,auto)
      have "\<forall>V \<in> rv S (CFG_node (targetnode a)). fst cf\<^sub>1' V = fst cf\<^sub>2 V"
      proof
        fix V assume "V \<in> rv S (CFG_node (targetnode a))"
        from \<open>valid_edge a\<close> \<open>intra_kind (kind a)\<close> \<open>sourcenode a \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close>
        have "obs_intra (targetnode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = 
          obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
          by(rule edge_obs_intra_slice_eq)
        hence "rv S (CFG_node (targetnode a)) = rv S (CFG_node (sourcenode a))" 
          by(rule closed_eq_obs_eq_rvs')
        with \<open>V \<in> rv S (CFG_node (targetnode a))\<close>
        have "V \<in> rv S (CFG_node (sourcenode a))" by simp
        then obtain as n' where "sourcenode a -as\<rightarrow>\<^sub>\<iota>* parent_node n'" 
          and "n' \<in> HRB_slice S" and "V \<in> Use\<^bsub>SDG\<^esub> n'"
          and "\<forall>n''. valid_SDG_node n'' \<and> parent_node n'' \<in> set (sourcenodes as) 
                     \<longrightarrow> V \<notin> Def\<^bsub>SDG\<^esub> n''"
          by(fastforce elim:rvE)
        with \<open>sourcenode a \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close> \<open>valid_edge a\<close>
        have "V \<notin> Def\<^bsub>SDG\<^esub> (CFG_node (sourcenode a))"
          apply(clarsimp simp:intra_path_def)
          apply(erule path.cases)
          by(auto dest:valid_SDG_node_in_slice_parent_node_in_slice 
                  simp:sourcenodes_def SDG_to_CFG_set_def)
        from \<open>valid_edge a\<close> have "valid_node (sourcenode a)" by simp
        with \<open>V \<notin> Def\<^bsub>SDG\<^esub> (CFG_node (sourcenode a))\<close> have "V \<notin> Def (sourcenode a)"
          by(fastforce intro:CFG_Def_SDG_Def valid_SDG_CFG_node)
        with \<open>valid_edge a\<close> \<open>intra_kind (kind a)\<close> \<open>pred (kind a) s\<^sub>1\<close>
        have "state_val (transfer (kind a) s\<^sub>1) V = state_val s\<^sub>1 V"
          by(fastforce intro:CFG_intra_edge_no_Def_equal)
        with \<open>transfer (kind a) s\<^sub>1 = s\<^sub>1'\<close> have "fst cf\<^sub>1' V = fst cf\<^sub>1 V" by simp
        from \<open>V \<in> rv S (CFG_node (sourcenode a))\<close> \<open>msx = []\<close>
          \<open>\<forall>V\<in>rv S (CFG_node mx). (fst (s\<^sub>1 ! length msx)) V = state_val s\<^sub>2 V\<close>
        have "fst cf\<^sub>1 V = fst cf\<^sub>2 V" by simp
        with \<open>fst cf\<^sub>1' V = fst cf\<^sub>1 V\<close> show "fst cf\<^sub>1' V = fst cf\<^sub>2 V" by simp
      qed
      with \<open>\<forall>i<length ms\<^sub>2. \<forall>V\<in>rv S (CFG_node ((mx # tl ms\<^sub>2) ! i)).
        (fst (s\<^sub>1 ! (length msx + i))) V = (fst (s\<^sub>2 ! i)) V\<close> Nil
      have "\<forall>i<length ms\<^sub>2. \<forall>V\<in>rv S (CFG_node ((targetnode a # tl ms\<^sub>2) ! i)).
        (fst (s\<^sub>1' ! (length [] + i))) V = (fst (s\<^sub>2 ! i)) V"
        by auto (case_tac i,auto)
      with \<open>\<forall>m \<in> set ms\<^sub>1'. valid_node m\<close> \<open>\<forall>m \<in> set ms\<^sub>2. valid_node m\<close>
        \<open>length ms\<^sub>1' = length s\<^sub>1'\<close> \<open>length ms\<^sub>2 = length s\<^sub>2\<close>
        \<open>ms\<^sub>1' = [] @ targetnode a # tl ms\<^sub>2\<close> 
        \<open>get_proc (targetnode a) = get_proc (hd ms\<^sub>2)\<close>
        \<open>\<forall>m \<in> set (tl ms\<^sub>2). \<exists>m'. call_of_return_node m m' \<and> m' \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close>
        \<open>\<forall>m \<in> set (tl ms\<^sub>1). return_node m\<close>
        \<open>obs ms\<^sub>1' \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = obs ms\<^sub>2 \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close>
        \<open>\<forall>i<length ms\<^sub>2. snd (s\<^sub>1' ! i) = snd (s\<^sub>2 ! i)\<close>
      show ?thesis by(auto intro!:WSI)
    next
      case (Cons mx' msx')
      with \<open>ms\<^sub>1 = msx@mx#tl ms\<^sub>2\<close> \<open>hd ms\<^sub>1 = sourcenode a\<close>
      have [simp]:"mx' = sourcenode a" and [simp]:"tl ms\<^sub>1 = msx'@mx#tl ms\<^sub>2" 
        by simp_all
     from \<open>ms\<^sub>1' = targetnode a # tl ms\<^sub>1\<close> have "ms\<^sub>1' = ((targetnode a)#msx')@mx#tl ms\<^sub>2"
        by simp
      from \<open>\<forall>V\<in>rv S (CFG_node mx). (fst (s\<^sub>1 ! length msx)) V = state_val s\<^sub>2 V\<close> Cons
      have rv:"\<forall>V\<in>rv S (CFG_node mx).
        (fst (s\<^sub>1' ! length (targetnode a#msx'))) V = state_val s\<^sub>2 V" by fastforce
      from \<open>ms\<^sub>1 = msx@mx#tl ms\<^sub>2\<close> Cons \<open>ms\<^sub>1' = targetnode a # tl ms\<^sub>1\<close>
      have "ms\<^sub>1' = ((targetnode a)#msx')@mx#tl ms\<^sub>2" by simp
      from \<open>\<forall>i<length ms\<^sub>2. snd (s\<^sub>1 ! (length msx + i)) = snd (s\<^sub>2 ! i)\<close> Cons
      have "\<forall>i<length ms\<^sub>2. snd (s\<^sub>1' ! (length msx + i)) = snd (s\<^sub>2 ! i)" by fastforce 
      from \<open>\<forall>V\<in>rv S (CFG_node mx). (fst (s\<^sub>1 ! length msx)) V = state_val s\<^sub>2 V\<close> Cons
      have "\<forall>V\<in>rv S (CFG_node mx). (fst (s\<^sub>1' ! length msx)) V = state_val s\<^sub>2 V"
        by simp
      with \<open>\<forall>i < length ms\<^sub>2. \<forall>V \<in> rv S (CFG_node ((mx#tl ms\<^sub>2)!i)). 
        (fst (s\<^sub>1!(length msx + i))) V = (fst (s\<^sub>2!i)) V\<close> Cons
      have "\<forall>i<length ms\<^sub>2. \<forall>V\<in>rv S (CFG_node ((mx # tl ms\<^sub>2)!i)).
             (fst (s\<^sub>1'!(length (targetnode a # msx') + i))) V = (fst (s\<^sub>2!i)) V"
        by clarsimp
      with \<open>\<forall>m\<in>set ms\<^sub>1'. valid_node m\<close> \<open>\<forall>m\<in>set ms\<^sub>2. valid_node m\<close>
        \<open>length ms\<^sub>1' = length s\<^sub>1'\<close> \<open>length ms\<^sub>2 = length s\<^sub>2\<close> 
        \<open>ms\<^sub>1' = ((targetnode a)#msx')@mx#tl ms\<^sub>2\<close>
        \<open>\<forall>m\<in>set (tl ms\<^sub>2). \<exists>m'. call_of_return_node m m' \<and> m' \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close>
        \<open>\<forall>m \<in> set (tl ms\<^sub>1'). return_node m\<close> \<open>get_proc mx = get_proc (hd ms\<^sub>2)\<close>
        \<open>msx \<noteq> [] \<longrightarrow> (\<exists>mx'. call_of_return_node mx mx' \<and> mx' \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>)\<close>
        \<open>obs ms\<^sub>1' \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = obs ms\<^sub>2 \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close> Cons
        \<open>\<forall>i<length ms\<^sub>2. snd (s\<^sub>1' ! (length msx + i)) = snd (s\<^sub>2 ! i)\<close>
      show ?thesis by -(rule WSI,clarsimp+,fastforce,clarsimp+)
    qed
  next
    case (silent_move_call a s\<^sub>1 s\<^sub>1' Q r p fs a' ms\<^sub>1 S ms\<^sub>1')
    note obs_eq = \<open>\<forall>a\<in>set (tl ms\<^sub>1'). return_node a \<Longrightarrow>
      obs ms\<^sub>1' \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = obs ms\<^sub>2 \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close>
    from \<open>s\<^sub>1 \<noteq> []\<close> \<open>s\<^sub>2 \<noteq> []\<close> obtain cf\<^sub>1 cfs\<^sub>1 cf\<^sub>2 cfs\<^sub>2 where [simp]:"s\<^sub>1 = cf\<^sub>1#cfs\<^sub>1" 
      and [simp]:"s\<^sub>2 = cf\<^sub>2#cfs\<^sub>2" by(cases s\<^sub>1,auto,cases s\<^sub>2,fastforce+)
    from \<open>valid_edge a\<close> \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close> 
    obtain ins outs where "(p,ins,outs) \<in> set procs"
      by(fastforce dest!:callee_in_procs)
    with \<open>transfer (kind a) s\<^sub>1 = s\<^sub>1'\<close> \<open>valid_edge a\<close> \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close>
    have [simp]:"s\<^sub>1' = (Map.empty(ins [:=] params fs (fst cf\<^sub>1)), r) # cf\<^sub>1 # cfs\<^sub>1"
      by simp(unfold formal_in_THE,simp)
    from \<open>length ms\<^sub>1 = length s\<^sub>1\<close> \<open>ms\<^sub>1' = targetnode a # targetnode a' # tl ms\<^sub>1\<close>
    have "length ms\<^sub>1' = length s\<^sub>1'" by simp
    from \<open>valid_edge a\<close> \<open>a' \<in> get_return_edges a\<close> have "valid_edge a'"
      by(rule get_return_edges_valid)
    with \<open>\<forall>m\<in>set ms\<^sub>1. valid_node m\<close> \<open>valid_edge a\<close> 
      \<open>ms\<^sub>1' = targetnode a # targetnode a' # tl ms\<^sub>1\<close>
    have "\<forall>m\<in>set ms\<^sub>1'. valid_node m" by(cases ms\<^sub>1) auto
    from \<open>valid_edge a'\<close> \<open>valid_edge a\<close> \<open>a' \<in> get_return_edges a\<close>
    have "return_node (targetnode a')" by(fastforce simp:return_node_def)
    with \<open>valid_edge a\<close> \<open>a' \<in> get_return_edges a\<close> \<open>valid_edge a'\<close>
    have "call_of_return_node (targetnode a') (sourcenode a)"
      by(simp add:call_of_return_node_def) blast
    from \<open>\<forall>m \<in> set (tl ms\<^sub>1). return_node m\<close> \<open>return_node (targetnode a')\<close>
      \<open>ms\<^sub>1' = targetnode a # targetnode a' # tl ms\<^sub>1\<close>
    have "\<forall>m \<in> set (tl ms\<^sub>1'). return_node m" by simp
    from obs_eq[OF this] have "obs ms\<^sub>1' \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = obs ms\<^sub>2 \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>" .
    from \<open>\<forall>i < length ms\<^sub>2. \<forall>V \<in> rv S (CFG_node ((mx#tl ms\<^sub>2)!i)). 
      (fst (s\<^sub>1!(length msx + i))) V = (fst (s\<^sub>2!i)) V\<close> \<open>length ms\<^sub>2 = length s\<^sub>2\<close>
    have "\<forall>V\<in>rv S (CFG_node mx). (fst (s\<^sub>1 ! length msx)) V = state_val s\<^sub>2 V"
      by(erule_tac x="0" in allE) auto
    show ?case
    proof(cases msx)
      case Nil
      with \<open>ms\<^sub>1 = msx@mx#tl ms\<^sub>2\<close> \<open>hd ms\<^sub>1 = sourcenode a\<close> 
      have [simp]:"mx = sourcenode a" and [simp]:"tl ms\<^sub>1 = tl ms\<^sub>2" by simp_all
      from \<open>\<forall>m\<in>set (tl ms\<^sub>2). \<exists>m'. call_of_return_node m m' \<and> m' \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close>
        \<open>(\<exists>m\<in>set (tl ms\<^sub>1). \<exists>m'. call_of_return_node m m' \<and> m' \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>) \<or>
        hd ms\<^sub>1 \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close>
      have "hd ms\<^sub>1 \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>" by fastforce
      with \<open>hd ms\<^sub>1 = sourcenode a\<close> have "sourcenode a \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>" by simp
      from \<open>valid_edge a\<close> \<open>a' \<in> get_return_edges a\<close>
      obtain a'' where "valid_edge a''" and "sourcenode a'' = sourcenode a"
        and "targetnode a'' = targetnode a'" and "intra_kind(kind a'')"
        by -(drule call_return_node_edge,auto simp:intra_kind_def)
      from \<open>valid_edge a''\<close> \<open>intra_kind(kind a'')\<close>
      have "get_proc (sourcenode a'') = get_proc (targetnode a'')"
        by(rule get_proc_intra)
      with \<open>sourcenode a'' = sourcenode a\<close> \<open>targetnode a'' = targetnode a'\<close>
        \<open>get_proc mx = get_proc (hd ms\<^sub>2)\<close> 
      have "get_proc (targetnode a') = get_proc (hd ms\<^sub>2)" by simp
      from \<open>valid_edge a\<close> \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close> \<open>a' \<in> get_return_edges a\<close>
      have "CFG_node (sourcenode a) s-p\<rightarrow>\<^bsub>sum\<^esub> CFG_node (targetnode a')"
        by(fastforce intro:sum_SDG_call_summary_edge)
      have "targetnode a' \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
      proof
        assume "targetnode a' \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
        hence "CFG_node (targetnode a') \<in> HRB_slice S" by(simp add:SDG_to_CFG_set_def)
        hence "CFG_node (sourcenode a) \<in> HRB_slice S"
        proof(induct "CFG_node (targetnode a')" rule:HRB_slice_cases)
          case (phase1 nx)
          with \<open>CFG_node (sourcenode a) s-p\<rightarrow>\<^bsub>sum\<^esub> CFG_node (targetnode a')\<close>
          show ?case by(fastforce intro:combine_SDG_slices.combSlice_refl sum_slice1
                                  simp:HRB_slice_def)
        next
          case (phase2 nx n' n'' p')
          from \<open>CFG_node (targetnode a') \<in> sum_SDG_slice2 n'\<close> 
            \<open>CFG_node (sourcenode a) s-p\<rightarrow>\<^bsub>sum\<^esub> CFG_node (targetnode a')\<close> \<open>valid_edge a\<close>
          have "CFG_node (sourcenode a) \<in> sum_SDG_slice2 n'"
            by(fastforce intro:sum_slice2)
          with \<open>n' \<in> sum_SDG_slice1 nx\<close> \<open>n'' s-p'\<rightarrow>\<^bsub>ret\<^esub> CFG_node (parent_node n')\<close> 
            \<open>nx \<in> S\<close>
          show ?case
            by(fastforce intro:combine_SDG_slices.combSlice_Return_parent_node 
                         simp:HRB_slice_def)
        qed
        with \<open>sourcenode a \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close> show False
          by(simp add:SDG_to_CFG_set_def HRB_slice_def)
      qed
      from \<open>ms\<^sub>1' = targetnode a # targetnode a' # tl ms\<^sub>1\<close>
      have "ms\<^sub>1' = [targetnode a] @ targetnode a' # tl ms\<^sub>2" by simp
      from \<open>\<forall>i<length ms\<^sub>2. snd (s\<^sub>1 ! (length msx + i)) = snd (s\<^sub>2 ! i)\<close> Nil
      have "\<forall>i<length ms\<^sub>2. snd (s\<^sub>1' ! (length [targetnode a] + i)) = snd (s\<^sub>2 ! i)"
        by fastforce
      have "\<forall>V\<in>rv S (CFG_node (targetnode a')). (fst (s\<^sub>1' ! 1)) V = state_val s\<^sub>2 V"
      proof
        fix V assume "V \<in> rv S (CFG_node (targetnode a'))"
        from \<open>valid_edge a\<close> \<open>a' \<in> get_return_edges a\<close>
        obtain a'' where edge:"valid_edge a''" "sourcenode a'' = sourcenode a"
          "targetnode a'' = targetnode a'" "intra_kind(kind a'')"
          by -(drule call_return_node_edge,auto simp:intra_kind_def)
        from \<open>V \<in> rv S (CFG_node (targetnode a'))\<close>
        obtain as n' where "targetnode a' -as\<rightarrow>\<^sub>\<iota>* parent_node n'"
          and "n' \<in> HRB_slice S" and "V \<in> Use\<^bsub>SDG\<^esub> n'"
          and "\<forall>n''. valid_SDG_node n'' \<and> parent_node n'' \<in> set (sourcenodes as) 
          \<longrightarrow> V \<notin> Def\<^bsub>SDG\<^esub> n''"
          by(fastforce elim:rvE)
        from \<open>targetnode a' -as\<rightarrow>\<^sub>\<iota>* parent_node n'\<close> edge
        have "sourcenode a -a''#as\<rightarrow>\<^sub>\<iota>* parent_node n'"
          by(fastforce intro:Cons_path simp:intra_path_def)
        from \<open>valid_edge a\<close> \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close>
        have "V \<notin> Def (sourcenode a)"
          by(fastforce dest:call_source_Def_empty)
        with \<open>\<forall>n''. valid_SDG_node n'' \<and> parent_node n'' \<in> set (sourcenodes as) 
          \<longrightarrow> V \<notin> Def\<^bsub>SDG\<^esub> n''\<close> \<open>sourcenode a'' = sourcenode a\<close>
        have "\<forall>n''. valid_SDG_node n'' \<and> parent_node n'' \<in> set (sourcenodes (a''#as)) 
          \<longrightarrow> V \<notin> Def\<^bsub>SDG\<^esub> n''"
          by(fastforce dest:SDG_Def_parent_Def simp:sourcenodes_def)
        with \<open>sourcenode a -a''#as\<rightarrow>\<^sub>\<iota>* parent_node n'\<close> \<open>n' \<in> HRB_slice S\<close> 
          \<open>V \<in> Use\<^bsub>SDG\<^esub> n'\<close>
        have "V \<in> rv S (CFG_node (sourcenode a))" by(fastforce intro:rvI)
        from \<open>\<forall>V\<in>rv S (CFG_node mx). (fst (s\<^sub>1 ! length msx)) V = state_val s\<^sub>2 V\<close> Nil
        have "\<forall>V\<in>rv S (CFG_node (sourcenode a)). fst cf\<^sub>1 V = fst cf\<^sub>2 V" by simp
        with \<open>V \<in> rv S (CFG_node (sourcenode a))\<close> have "fst cf\<^sub>1 V = fst cf\<^sub>2 V" by simp
        thus "(fst (s\<^sub>1' ! 1)) V = state_val s\<^sub>2 V" by simp
      qed
      with \<open>\<forall>i < length ms\<^sub>2. \<forall>V \<in> rv S (CFG_node ((mx#tl ms\<^sub>2)!i)). 
        (fst (s\<^sub>1!(length msx + i))) V = (fst (s\<^sub>2!i)) V\<close> Nil
      have "\<forall>i<length ms\<^sub>2. \<forall>V\<in>rv S (CFG_node ((targetnode a' # tl ms\<^sub>2)!i)).
        (fst (s\<^sub>1'!(length [targetnode a] + i))) V = (fst (s\<^sub>2!i)) V"
        by clarsimp(case_tac i,auto)
      with \<open>\<forall>m\<in>set ms\<^sub>1'. valid_node m\<close> \<open>\<forall>m\<in>set ms\<^sub>2. valid_node m\<close>
        \<open>length ms\<^sub>1' = length s\<^sub>1'\<close> \<open>length ms\<^sub>2 = length s\<^sub>2\<close>
        \<open>\<forall>m\<in>set (tl ms\<^sub>2). \<exists>m'. call_of_return_node m m' \<and> m' \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close>
        \<open>ms\<^sub>1' = [targetnode a] @ targetnode a' # tl ms\<^sub>2\<close>
        \<open>targetnode a' \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close> \<open>return_node (targetnode a')\<close>
        \<open>obs ms\<^sub>1' \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = obs ms\<^sub>2 \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close>
        \<open>get_proc (targetnode a') = get_proc (hd ms\<^sub>2)\<close>
        \<open>\<forall>m \<in> set (tl ms\<^sub>1'). return_node m\<close> \<open>sourcenode a \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close>
        \<open>call_of_return_node (targetnode a') (sourcenode a)\<close>
        \<open>\<forall>i<length ms\<^sub>2. snd (s\<^sub>1' ! (length [targetnode a] + i)) = snd (s\<^sub>2 ! i)\<close>
      show ?thesis by(auto intro!:WSI)
    next
      case (Cons mx' msx')
      with \<open>ms\<^sub>1 = msx@mx#tl ms\<^sub>2\<close> \<open>hd ms\<^sub>1 = sourcenode a\<close>
      have [simp]:"mx' = sourcenode a" and [simp]:"tl ms\<^sub>1 = msx'@mx#tl ms\<^sub>2" 
        by simp_all
      from \<open>ms\<^sub>1' = targetnode a # targetnode a' # tl ms\<^sub>1\<close> 
      have "ms\<^sub>1' = (targetnode a # targetnode a' # msx')@mx#tl ms\<^sub>2"
        by simp
      from \<open>\<forall>i<length ms\<^sub>2. snd (s\<^sub>1 ! (length msx + i)) = snd (s\<^sub>2 ! i)\<close> Cons
      have "\<forall>i<length ms\<^sub>2.
        snd (s\<^sub>1' ! (length (targetnode a # targetnode a' # msx') + i)) = snd (s\<^sub>2 ! i)"
        by fastforce
      from \<open>\<forall>V\<in>rv S (CFG_node mx). (fst (s\<^sub>1 ! length msx)) V = state_val s\<^sub>2 V\<close> Cons
      have "\<forall>V\<in>rv S (CFG_node mx). 
        (fst (s\<^sub>1' ! length(targetnode a # targetnode a' # msx'))) V = state_val s\<^sub>2 V" 
        by simp
      with \<open>\<forall>i < length ms\<^sub>2. \<forall>V \<in> rv S (CFG_node ((mx#tl ms\<^sub>2)!i)). 
        (fst (s\<^sub>1!(length msx + i))) V = (fst (s\<^sub>2!i)) V\<close> Cons
      have "\<forall>i<length ms\<^sub>2. \<forall>V\<in>rv S (CFG_node ((mx # tl ms\<^sub>2)!i)).
        (fst (s\<^sub>1'!(length (targetnode a # targetnode a' # msx') + i))) V = 
        (fst (s\<^sub>2!i)) V"
        by clarsimp
      with \<open>\<forall>m\<in>set ms\<^sub>1'. valid_node m\<close> \<open>\<forall>m\<in>set ms\<^sub>2. valid_node m\<close>
        \<open>length ms\<^sub>1' = length s\<^sub>1'\<close> \<open>length ms\<^sub>2 = length s\<^sub>2\<close> 
        \<open>ms\<^sub>1' = (targetnode a # targetnode a' # msx')@mx#tl ms\<^sub>2\<close>
        \<open>return_node (targetnode a')\<close>
        \<open>\<forall>m\<in>set (tl ms\<^sub>2). \<exists>m'. call_of_return_node m m' \<and> m' \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close>
        \<open>msx \<noteq> [] \<longrightarrow> (\<exists>mx'. call_of_return_node mx mx' \<and> mx' \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>)\<close>
        \<open>obs ms\<^sub>1' \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = obs ms\<^sub>2 \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close> Cons
        \<open>get_proc mx = get_proc (hd ms\<^sub>2)\<close> \<open>\<forall>m \<in> set (tl ms\<^sub>1'). return_node m\<close>
        \<open>\<forall>i<length ms\<^sub>2.
        snd (s\<^sub>1' ! (length (targetnode a # targetnode a' # msx') + i)) = snd (s\<^sub>2 ! i)\<close>
      show ?thesis by -(rule WSI,clarsimp+,fastforce,clarsimp+)
    qed
  next
    case (silent_move_return a s\<^sub>1 s\<^sub>1' Q p f' ms\<^sub>1 S ms\<^sub>1')
    note obs_eq = \<open>\<forall>a\<in>set (tl ms\<^sub>1'). return_node a \<Longrightarrow>
      obs ms\<^sub>1' \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = obs ms\<^sub>2 \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close>
    from \<open>transfer (kind a) s\<^sub>1 = s\<^sub>1'\<close> \<open>kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f'\<close> \<open>s\<^sub>1 \<noteq> []\<close> \<open>s\<^sub>1' \<noteq> []\<close>
    obtain cf\<^sub>1 cfx\<^sub>1 cfs\<^sub>1 cf\<^sub>1' where [simp]:"s\<^sub>1 = cf\<^sub>1#cfx\<^sub>1#cfs\<^sub>1"
      and "s\<^sub>1' = (f' (fst cf\<^sub>1) (fst cfx\<^sub>1),snd cfx\<^sub>1)#cfs\<^sub>1"
      by(cases s\<^sub>1,auto,case_tac list,fastforce+)
    from \<open>s\<^sub>2 \<noteq> []\<close> obtain cf\<^sub>2 cfs\<^sub>2 where [simp]:"s\<^sub>2 = cf\<^sub>2#cfs\<^sub>2" by(cases s\<^sub>2) auto
    from \<open>length ms\<^sub>1 = length s\<^sub>1\<close> have "ms\<^sub>1 \<noteq> []" and "tl ms\<^sub>1 \<noteq> []" by(cases ms\<^sub>1,auto)+
    from \<open>valid_edge a\<close> \<open>kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f'\<close>
    obtain a' Q' r' fs' where "valid_edge a'" and "kind a' = Q':r'\<hookrightarrow>\<^bsub>p\<^esub>fs'"
      and "a \<in> get_return_edges a'"
      by -(drule return_needs_call,auto)
    then obtain ins outs where "(p,ins,outs) \<in> set procs"
      by(fastforce dest!:callee_in_procs)
    with \<open>valid_edge a\<close> \<open>kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f'\<close>
    have "f' (fst cf\<^sub>1) (fst cfx\<^sub>1) = 
      (fst cfx\<^sub>1)(ParamDefs (targetnode a) [:=] map (fst cf\<^sub>1) outs)"
      by(rule CFG_return_edge_fun)
    with \<open>s\<^sub>1' = (f' (fst cf\<^sub>1) (fst cfx\<^sub>1),snd cfx\<^sub>1)#cfs\<^sub>1\<close>
    have [simp]:"s\<^sub>1' = ((fst cfx\<^sub>1)
      (ParamDefs (targetnode a) [:=] map (fst cf\<^sub>1) outs),snd cfx\<^sub>1)#cfs\<^sub>1" by simp
    from \<open>\<forall>m\<in>set ms\<^sub>1. valid_node m\<close> \<open>ms\<^sub>1' = tl ms\<^sub>1\<close> have "\<forall>m\<in>set ms\<^sub>1'. valid_node m"
      by(cases ms\<^sub>1) auto
    from \<open>length ms\<^sub>1 = length s\<^sub>1\<close> \<open>ms\<^sub>1' = tl ms\<^sub>1\<close>
    have "length ms\<^sub>1' = length s\<^sub>1'" by simp
    from \<open>\<forall>m\<in>set (tl ms\<^sub>1). return_node m\<close> \<open>ms\<^sub>1' = tl ms\<^sub>1\<close> \<open>ms\<^sub>1 \<noteq> []\<close> \<open>tl ms\<^sub>1 \<noteq> []\<close>
    have "\<forall>m\<in>set (tl ms\<^sub>1'). return_node m" by(cases ms\<^sub>1)(auto,cases ms\<^sub>1',auto)
    from obs_eq[OF this] have "obs ms\<^sub>1' \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = obs ms\<^sub>2 \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>" .
    show ?case
    proof(cases msx)
      case Nil
      with \<open>ms\<^sub>1 = msx@mx#tl ms\<^sub>2\<close> \<open>hd ms\<^sub>1 = sourcenode a\<close> 
      have "mx = sourcenode a" and "tl ms\<^sub>1 = tl ms\<^sub>2" by simp_all
      with \<open>\<exists>m\<in>set (tl ms\<^sub>1). \<exists>m'. call_of_return_node m m' \<and> m' \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close>
        \<open>\<forall>m\<in>set (tl ms\<^sub>2). \<exists>m'. call_of_return_node m m' \<and> m' \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close>
      have False by fastforce
      thus ?thesis by simp
    next
      case (Cons mx' msx')
      with \<open>ms\<^sub>1 = msx@mx#tl ms\<^sub>2\<close> \<open>hd ms\<^sub>1 = sourcenode a\<close>
      have [simp]:"mx' = sourcenode a" and [simp]:"tl ms\<^sub>1 = msx'@mx#tl ms\<^sub>2"
        by simp_all
      from \<open>ms\<^sub>1' = tl ms\<^sub>1\<close> have "ms\<^sub>1' = msx'@mx#tl ms\<^sub>2" by simp
      with \<open>ms\<^sub>1 = msx@mx#tl ms\<^sub>2\<close> \<open>\<forall>m\<in>set (tl ms\<^sub>1). return_node m\<close> Cons
      have "\<forall>m\<in>set (tl ms\<^sub>1'). return_node m"
        by(cases msx') auto
      from \<open>\<forall>i<length ms\<^sub>2. snd (s\<^sub>1 ! (length msx + i)) = snd (s\<^sub>2 ! i)\<close> Cons
      have "\<forall>i<length ms\<^sub>2. snd (s\<^sub>1' ! (length msx' + i)) = snd (s\<^sub>2 ! i)"
        by auto(case_tac i,auto,cases msx',auto)
      from \<open>\<forall>i<length ms\<^sub>2. \<forall>V\<in>rv S (CFG_node ((mx # tl ms\<^sub>2) ! i)).
        (fst (s\<^sub>1 ! (length msx + i))) V = (fst (s\<^sub>2 ! i)) V\<close>
        \<open>length ms\<^sub>2 = length s\<^sub>2\<close> \<open>s\<^sub>2 \<noteq> []\<close>
      have "\<forall>V\<in>rv S (CFG_node mx). (fst (s\<^sub>1 ! length msx)) V = state_val s\<^sub>2 V"
        by fastforce
      have "\<forall>V\<in>rv S (CFG_node mx). (fst (s\<^sub>1' ! length msx')) V = state_val s\<^sub>2 V"
      proof(cases msx')
        case Nil
        with \<open>\<forall>V\<in>rv S (CFG_node mx). (fst (s\<^sub>1 ! length msx)) V = state_val s\<^sub>2 V\<close>
          \<open>msx = mx'#msx'\<close>
        have rv:"\<forall>V\<in>rv S (CFG_node mx). fst cfx\<^sub>1 V = fst cf\<^sub>2 V" by fastforce
        from Nil \<open>tl ms\<^sub>1 = msx'@mx#tl ms\<^sub>2\<close> \<open>hd (tl ms\<^sub>1) = targetnode a\<close>
        have [simp]:"mx = targetnode a" by simp
        from Cons 
          \<open>msx \<noteq> [] \<longrightarrow> (\<exists>mx'. call_of_return_node mx mx' \<and> mx' \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>)\<close>
        obtain mx'' where "call_of_return_node mx mx''" and "mx'' \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
          by blast
        hence "mx \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>" 
          by(rule call_node_notin_slice_return_node_neither)
        have "\<forall>V\<in>rv S (CFG_node mx). 
          (fst cfx\<^sub>1)(ParamDefs (targetnode a) [:=] map (fst cf\<^sub>1) outs) V = fst cf\<^sub>2 V"
        proof
          fix V assume "V\<in>rv S (CFG_node mx)"
          show "(fst cfx\<^sub>1)(ParamDefs (targetnode a) [:=] map (fst cf\<^sub>1) outs) V = 
            fst cf\<^sub>2 V"
          proof(cases "V \<in> set (ParamDefs (targetnode a))")
            case True
            with \<open>valid_edge a\<close> have "V \<in> Def (targetnode a)"
              by(fastforce intro:ParamDefs_in_Def)
            with \<open>valid_edge a\<close> have "V \<in> Def\<^bsub>SDG\<^esub> (CFG_node (targetnode a))"
              by(auto intro!:CFG_Def_SDG_Def)
            from \<open>V\<in>rv S (CFG_node mx)\<close> obtain as n' 
              where "targetnode a -as\<rightarrow>\<^sub>\<iota>* parent_node n'"
              and "n' \<in> HRB_slice S" "V \<in> Use\<^bsub>SDG\<^esub> n'"
              and "\<forall>n''. valid_SDG_node n'' \<and> parent_node n'' \<in> set (sourcenodes as) 
              \<longrightarrow> V \<notin> Def\<^bsub>SDG\<^esub> n''" by(fastforce elim:rvE)
            from \<open>targetnode a -as\<rightarrow>\<^sub>\<iota>* parent_node n'\<close> \<open>n' \<in> HRB_slice S\<close>
              \<open>mx \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close>
            obtain ax asx where "as = ax#asx"
              by(auto simp:intra_path_def)(erule path.cases,
                 auto dest:valid_SDG_node_in_slice_parent_node_in_slice 
                      simp:SDG_to_CFG_set_def)
            with \<open>targetnode a -as\<rightarrow>\<^sub>\<iota>* parent_node n'\<close> 
            have "targetnode a = sourcenode ax" and "valid_edge ax"
              by(auto elim:path.cases simp:intra_path_def)
            with \<open>\<forall>n''. valid_SDG_node n'' \<and> parent_node n'' \<in> set (sourcenodes as) 
              \<longrightarrow> V \<notin> Def\<^bsub>SDG\<^esub> n''\<close> \<open>as = ax#asx\<close> \<open>V \<in> Def\<^bsub>SDG\<^esub> (CFG_node (targetnode a))\<close>
            have False by(fastforce simp:sourcenodes_def)
            thus ?thesis by simp
          next
            case False
            with \<open>V\<in>rv S (CFG_node mx)\<close> rv show ?thesis
              by(fastforce dest:fun_upds_notin[of  _ _ "fst cfx\<^sub>1"])
          qed
        qed
        with Nil \<open>msx = mx'#msx'\<close> show ?thesis by fastforce
      next
        case Cons
        with \<open>\<forall>V\<in>rv S (CFG_node mx). (fst (s\<^sub>1 ! length msx)) V = state_val s\<^sub>2 V\<close>
          \<open>msx = mx'#msx'\<close>
        show ?thesis by fastforce
      qed
      with \<open>\<forall>V\<in>rv S (CFG_node mx). (fst (s\<^sub>1 ! length msx)) V = state_val s\<^sub>2 V\<close> Cons
      have "\<forall>V\<in>rv S (CFG_node mx). (fst (s\<^sub>1' ! length msx')) V = state_val s\<^sub>2 V"
        by(cases msx') auto
      with \<open>\<forall>i < length ms\<^sub>2. \<forall>V \<in> rv S (CFG_node ((mx#tl ms\<^sub>2)!i)). 
        (fst (s\<^sub>1!(length msx + i))) V = (fst (s\<^sub>2!i)) V\<close> Cons
      have "\<forall>i<length ms\<^sub>2. \<forall>V\<in>rv S (CFG_node ((mx # tl ms\<^sub>2) ! i)).
        (fst (s\<^sub>1' ! (length msx' + i))) V = (fst (s\<^sub>2 ! i)) V"
        by clarsimp(case_tac i,auto)
      with \<open>\<forall>m\<in>set ms\<^sub>1'. valid_node m\<close> \<open>\<forall>m\<in>set ms\<^sub>2. valid_node m\<close>
        \<open>length ms\<^sub>1' = length s\<^sub>1'\<close> \<open>length ms\<^sub>2 = length s\<^sub>2\<close> 
        \<open>ms\<^sub>1' = msx'@mx#tl ms\<^sub>2\<close> \<open>get_proc mx = get_proc (hd ms\<^sub>2)\<close>
        \<open>\<forall>m\<in>set (tl ms\<^sub>2). \<exists>m'. call_of_return_node m m' \<and> m' \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close>
        \<open>msx \<noteq> [] \<longrightarrow> (\<exists>mx'. call_of_return_node mx mx' \<and> mx' \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>)\<close>
        \<open>\<forall>m\<in>set (tl ms\<^sub>1'). return_node m\<close> Cons \<open>get_proc mx = get_proc (hd ms\<^sub>2)\<close>
        \<open>\<forall>m\<in>set (tl ms\<^sub>2). \<exists>m'. call_of_return_node m m' \<and> m' \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close>
        \<open>obs ms\<^sub>1' \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = obs ms\<^sub>2 \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close>
        \<open>\<forall>i<length ms\<^sub>2. snd (s\<^sub>1' ! (length msx' + i)) = snd (s\<^sub>2 ! i)\<close>
       show ?thesis by(auto intro!:WSI)
    qed
  qed
qed


lemma WS_silent_moves:
  "\<lbrakk>S,kind \<turnstile> (ms\<^sub>1,s\<^sub>1) =as\<Rightarrow>\<^sub>\<tau> (ms\<^sub>1',s\<^sub>1'); ((ms\<^sub>1,s\<^sub>1),(ms\<^sub>2,s\<^sub>2)) \<in> WS S\<rbrakk>
  \<Longrightarrow> ((ms\<^sub>1',s\<^sub>1'),(ms\<^sub>2,s\<^sub>2)) \<in> WS S"
by(induct S f\<equiv>"kind" ms\<^sub>1 s\<^sub>1 as ms\<^sub>1' s\<^sub>1' rule:silent_moves.induct,
  auto dest:WS_silent_move)


lemma WS_observable_move:
  assumes "((ms\<^sub>1,s\<^sub>1),(ms\<^sub>2,s\<^sub>2)) \<in> WS S"
  and "S,kind \<turnstile> (ms\<^sub>1,s\<^sub>1) -a\<rightarrow> (ms\<^sub>1',s\<^sub>1')" and "s\<^sub>1' \<noteq> []"
  obtains as where "((ms\<^sub>1',s\<^sub>1'),(ms\<^sub>1',transfer (slice_kind S a) s\<^sub>2)) \<in> WS S"
  and "S,slice_kind S \<turnstile> (ms\<^sub>2,s\<^sub>2) =as@[a]\<Rightarrow> (ms\<^sub>1',transfer (slice_kind S a) s\<^sub>2)"
proof(atomize_elim)
  from \<open>((ms\<^sub>1,s\<^sub>1),(ms\<^sub>2,s\<^sub>2)) \<in> WS S\<close> obtain msx mx
    where assms:"\<forall>m \<in> set ms\<^sub>1. valid_node m" "\<forall>m \<in> set ms\<^sub>2. valid_node m"
    "length ms\<^sub>1 = length s\<^sub>1" "length ms\<^sub>2 = length s\<^sub>2" "s\<^sub>1 \<noteq> []" "s\<^sub>2 \<noteq> []" 
    "ms\<^sub>1 = msx@mx#tl ms\<^sub>2" "get_proc mx = get_proc (hd ms\<^sub>2)" 
    "\<forall>m \<in> set (tl ms\<^sub>2). \<exists>m'. call_of_return_node m m' \<and> m' \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
    "msx \<noteq> [] \<longrightarrow> (\<exists>mx'. call_of_return_node mx mx' \<and> mx' \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>)"
    "\<forall>m \<in> set (tl ms\<^sub>1). return_node m"
    "\<forall>i < length ms\<^sub>2. snd (s\<^sub>1!(length msx + i)) = snd (s\<^sub>2!i)"
    "\<forall>i < length ms\<^sub>2. \<forall>V \<in> rv S (CFG_node ((mx#tl ms\<^sub>2)!i)). 
      (fst (s\<^sub>1!(length msx + i))) V = (fst (s\<^sub>2!i)) V"
    "obs ms\<^sub>1 \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = obs ms\<^sub>2 \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
    by(fastforce elim:WS.cases)
  from \<open>S,kind \<turnstile> (ms\<^sub>1,s\<^sub>1) -a\<rightarrow> (ms\<^sub>1',s\<^sub>1')\<close> assms
  show "\<exists>as. ((ms\<^sub>1',s\<^sub>1'),(ms\<^sub>1',transfer (slice_kind S a) s\<^sub>2)) \<in> WS S \<and>
    S,slice_kind S \<turnstile> (ms\<^sub>2,s\<^sub>2) =as @ [a]\<Rightarrow> (ms\<^sub>1',transfer (slice_kind S a) s\<^sub>2)"
  proof(induct S f\<equiv>"kind" ms\<^sub>1 s\<^sub>1 a ms\<^sub>1' s\<^sub>1' rule:observable_move.induct)
    case (observable_move_intra a s\<^sub>1 s\<^sub>1' ms\<^sub>1 S ms\<^sub>1')
    from \<open>s\<^sub>1 \<noteq> []\<close> \<open>s\<^sub>2 \<noteq> []\<close> obtain cf\<^sub>1 cfs\<^sub>1 cf\<^sub>2 cfs\<^sub>2 where [simp]:"s\<^sub>1 = cf\<^sub>1#cfs\<^sub>1" 
      and [simp]:"s\<^sub>2 = cf\<^sub>2#cfs\<^sub>2" by(cases s\<^sub>1,auto,cases s\<^sub>2,fastforce+)
    from \<open>length ms\<^sub>1 = length s\<^sub>1\<close> \<open>s\<^sub>1 \<noteq> []\<close> have [simp]:"ms\<^sub>1 \<noteq> []" by(cases ms\<^sub>1) auto
    from \<open>length ms\<^sub>2 = length s\<^sub>2\<close> \<open>s\<^sub>2 \<noteq> []\<close> have [simp]:"ms\<^sub>2 \<noteq> []" by(cases ms\<^sub>2) auto
    from \<open>\<forall>m \<in> set (tl ms\<^sub>1). \<exists>m'. call_of_return_node m m' \<and> m' \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close>
      \<open>hd ms\<^sub>1 = sourcenode a\<close> \<open>ms\<^sub>1 = msx@mx#tl ms\<^sub>2\<close>
      \<open>msx \<noteq> [] \<longrightarrow> (\<exists>mx'. call_of_return_node mx mx' \<and> mx' \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>)\<close>
    have [simp]:"mx = sourcenode a" "msx = []" and [simp]:"tl ms\<^sub>2 = tl ms\<^sub>1"
      by(cases msx,auto)+
    hence "length ms\<^sub>1 = length ms\<^sub>2" by(cases ms\<^sub>2) auto
    with \<open>length ms\<^sub>1 = length s\<^sub>1\<close> \<open>length ms\<^sub>2 = length s\<^sub>2\<close>
    have "length s\<^sub>1 = length s\<^sub>2" by simp
    from \<open>hd ms\<^sub>1 \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close> \<open>hd ms\<^sub>1 = sourcenode a\<close>
    have "sourcenode a \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>" by simp
    with \<open>valid_edge a\<close>
    have "obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {sourcenode a}"
      by(fastforce intro!:n_in_obs_intra)
    from \<open>\<forall>m \<in> set (tl ms\<^sub>2). \<exists>m'. call_of_return_node m m' \<and> m' \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close>
      \<open>obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {sourcenode a}\<close> 
      \<open>hd ms\<^sub>1 = sourcenode a\<close> 
    have "(hd ms\<^sub>1#tl ms\<^sub>1) \<in> obs ([]@hd ms\<^sub>1#tl ms\<^sub>1) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
      by(cases ms\<^sub>1)(auto intro!:obsI)
    hence "ms\<^sub>1 \<in> obs ms\<^sub>1 \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>" by simp
    with \<open>obs ms\<^sub>1 \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = obs ms\<^sub>2 \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close>
    have "ms\<^sub>1 \<in> obs ms\<^sub>2 \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>" by simp
    from \<open>ms\<^sub>2 \<noteq> []\<close> \<open>length ms\<^sub>2 = length s\<^sub>2\<close> have "length s\<^sub>2 = length (hd ms\<^sub>2#tl ms\<^sub>2)"
      by(fastforce dest!:hd_Cons_tl)
    from \<open>\<forall>m \<in> set (tl ms\<^sub>1). return_node m\<close> have "\<forall>m \<in> set (tl ms\<^sub>2). return_node m"
      by simp
    with \<open>ms\<^sub>1 \<in> obs ms\<^sub>2 \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close>
    have "hd ms\<^sub>1 \<in> obs_intra (hd ms\<^sub>2) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
    proof(rule obsE)
      fix nsx n nsx' n'
      assume "ms\<^sub>2 = nsx @ n # nsx'" and "ms\<^sub>1 = n' # nsx'"
        and "n' \<in> obs_intra n \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
      from \<open>ms\<^sub>2 = nsx @ n # nsx'\<close> \<open>ms\<^sub>1 = n' # nsx'\<close> \<open>tl ms\<^sub>2 = tl ms\<^sub>1\<close>
      have [simp]:"nsx = []" by(cases nsx) auto
      with \<open>ms\<^sub>2 = nsx @ n # nsx'\<close> have [simp]:"n = hd ms\<^sub>2" by simp
      from \<open>ms\<^sub>1 = n' # nsx'\<close> have [simp]:"n' = hd ms\<^sub>1" by simp
      with \<open>n' \<in> obs_intra n \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close> show ?thesis by simp
    qed
    with \<open>length s\<^sub>2 = length (hd ms\<^sub>2#tl ms\<^sub>2)\<close> \<open>\<forall>m \<in> set (tl ms\<^sub>2). return_node m\<close>
    obtain as where "S,slice_kind S \<turnstile> (hd ms\<^sub>2#tl ms\<^sub>2,s\<^sub>2) =as\<Rightarrow>\<^sub>\<tau> (hd ms\<^sub>1#tl ms\<^sub>1,s\<^sub>2)"
      by(fastforce elim:silent_moves_intra_path_obs[of _ _ _ s\<^sub>2 "tl ms\<^sub>2"])
    with \<open>ms\<^sub>2 \<noteq> []\<close> have "S,slice_kind S \<turnstile> (ms\<^sub>2,s\<^sub>2) =as\<Rightarrow>\<^sub>\<tau> (ms\<^sub>1,s\<^sub>2)"
      by(fastforce dest!:hd_Cons_tl)
    from \<open>valid_edge a\<close> have "valid_node (sourcenode a)" by simp
    hence "sourcenode a -[]\<rightarrow>\<^sub>\<iota>* sourcenode a"
      by(fastforce intro:empty_path simp:intra_path_def)
    with \<open>sourcenode a \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close>
    have "\<forall>V. V \<in> Use\<^bsub>SDG\<^esub> (CFG_node (sourcenode a)) 
      \<longrightarrow> V \<in> rv S (CFG_node (sourcenode a))"
      by auto(rule rvI,auto simp:SDG_to_CFG_set_def sourcenodes_def)
    with \<open>valid_node (sourcenode a)\<close>
    have "\<forall>V \<in> Use (sourcenode a). V \<in> rv S (CFG_node (sourcenode a))"
      by(fastforce intro:CFG_Use_SDG_Use)
    from \<open>\<forall>i < length ms\<^sub>2. \<forall>V \<in> rv S (CFG_node ((mx#tl ms\<^sub>2)!i)). 
      (fst (s\<^sub>1!(length msx + i))) V = (fst (s\<^sub>2!i)) V\<close> \<open>length ms\<^sub>2 = length s\<^sub>2\<close>
    have "\<forall>V\<in>rv S (CFG_node mx). (fst (s\<^sub>1 ! length msx)) V = state_val s\<^sub>2 V"
      by(cases ms\<^sub>2) auto
    with \<open>\<forall>V \<in> Use (sourcenode a). V \<in> rv S (CFG_node (sourcenode a))\<close>
    have "\<forall>V \<in> Use (sourcenode a). fst cf\<^sub>1 V = fst cf\<^sub>2 V" by fastforce
    moreover
    from \<open>\<forall>i<length ms\<^sub>2. snd (s\<^sub>1 ! (length msx + i)) = snd (s\<^sub>2 ! i)\<close>
    have "snd (hd s\<^sub>1) = snd (hd s\<^sub>2)" by(erule_tac x="0" in allE) auto
    ultimately have "pred (kind a) s\<^sub>2"
      using \<open>valid_edge a\<close> \<open>pred (kind a) s\<^sub>1\<close> \<open>length s\<^sub>1 = length s\<^sub>2\<close>
      by(fastforce intro:CFG_edge_Uses_pred_equal)
    from \<open>ms\<^sub>1' = targetnode a # tl ms\<^sub>1\<close> \<open>length s\<^sub>1' = length s\<^sub>1\<close> 
      \<open>length ms\<^sub>1 = length s\<^sub>1\<close> have "length ms\<^sub>1' = length s\<^sub>1'" by simp
    from \<open>transfer (kind a) s\<^sub>1 = s\<^sub>1'\<close> \<open>intra_kind (kind a)\<close>
    obtain cf\<^sub>1' where [simp]:"s\<^sub>1' = cf\<^sub>1'#cfs\<^sub>1"
      by(cases cf\<^sub>1,cases "kind a",auto simp:intra_kind_def)
    from \<open>intra_kind (kind a)\<close> \<open>sourcenode a \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close> \<open>pred (kind a) s\<^sub>2\<close>
    have "pred (slice_kind S a) s\<^sub>2" by(simp add:slice_intra_kind_in_slice)
    from \<open>valid_edge a\<close> \<open>length s\<^sub>1 = length s\<^sub>2\<close> \<open>transfer (kind a) s\<^sub>1 = s\<^sub>1'\<close>
    have "length s\<^sub>1' = length (transfer (slice_kind S a) s\<^sub>2)"
      by(fastforce intro:length_transfer_kind_slice_kind)
    with \<open>length s\<^sub>1 = length s\<^sub>2\<close>
    have "length s\<^sub>2 = length (transfer (slice_kind S a) s\<^sub>2)" by simp
    with \<open>pred (slice_kind S a) s\<^sub>2\<close> \<open>valid_edge a\<close> \<open>intra_kind (kind a)\<close>
      \<open>\<forall>m \<in> set (tl ms\<^sub>1). \<exists>m'. call_of_return_node m m' \<and> m' \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close>
      \<open>hd ms\<^sub>1 \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close> \<open>hd ms\<^sub>1 = sourcenode a\<close>
      \<open>length ms\<^sub>1 = length s\<^sub>1\<close> \<open>length s\<^sub>1 = length s\<^sub>2\<close>
      \<open>ms\<^sub>1' = targetnode a # tl ms\<^sub>1\<close> \<open>\<forall>m \<in> set (tl ms\<^sub>2). return_node m\<close>
    have "S,slice_kind S \<turnstile> (ms\<^sub>1,s\<^sub>2) -a\<rightarrow> (ms\<^sub>1',transfer (slice_kind S a) s\<^sub>2)"
      by(auto intro:observable_move.observable_move_intra)
    with \<open>S,slice_kind S \<turnstile> (ms\<^sub>2,s\<^sub>2) =as\<Rightarrow>\<^sub>\<tau> (ms\<^sub>1,s\<^sub>2)\<close> 
    have "S,slice_kind S \<turnstile> (ms\<^sub>2,s\<^sub>2) =as@[a]\<Rightarrow> (ms\<^sub>1',transfer (slice_kind S a) s\<^sub>2)"
      by(rule observable_moves_snoc)
    from \<open>\<forall>m \<in> set ms\<^sub>1. valid_node m\<close> \<open>ms\<^sub>1' = targetnode a # tl ms\<^sub>1\<close> \<open>valid_edge a\<close>
    have "\<forall>m \<in> set ms\<^sub>1'. valid_node m" by(cases ms\<^sub>1) auto
    from \<open>\<forall>m \<in> set (tl ms\<^sub>2). return_node m\<close> \<open>ms\<^sub>1' = targetnode a # tl ms\<^sub>1\<close>
      \<open>ms\<^sub>1' = targetnode a # tl ms\<^sub>1\<close>
    have "\<forall>m \<in> set (tl ms\<^sub>1'). return_node m" by fastforce
    from \<open>ms\<^sub>1' = targetnode a # tl ms\<^sub>1\<close> \<open>tl ms\<^sub>2 = tl ms\<^sub>1\<close>
    have "ms\<^sub>1' = [] @ targetnode a # tl ms\<^sub>2" by simp
    from \<open>intra_kind (kind a)\<close> \<open>sourcenode a \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close>
    have cf2':"\<exists>cf\<^sub>2'. transfer (slice_kind S a) s\<^sub>2 = cf\<^sub>2'#cfs\<^sub>2 \<and> snd cf\<^sub>2' = snd cf\<^sub>2"
      by(cases cf\<^sub>2)(auto dest:slice_intra_kind_in_slice simp:intra_kind_def)
    from \<open>transfer (kind a) s\<^sub>1 = s\<^sub>1'\<close> \<open>intra_kind (kind a)\<close>
    have "snd cf\<^sub>1' = snd cf\<^sub>1" by(auto simp:intra_kind_def)
    with \<open>\<forall>i<length ms\<^sub>2. snd (s\<^sub>1 ! (length msx + i)) = snd (s\<^sub>2 ! i)\<close>
      \<open>snd (hd s\<^sub>1) = snd (hd s\<^sub>2)\<close> \<open>ms\<^sub>1' = [] @ targetnode a # tl ms\<^sub>2\<close>
      cf2' \<open>length ms\<^sub>1 = length ms\<^sub>2\<close>
    have "\<forall>i<length ms\<^sub>1'. snd (s\<^sub>1' ! i) = snd (transfer (slice_kind S a) s\<^sub>2 ! i)"
      by auto(case_tac i,auto)
    have "\<forall>V \<in> rv S (CFG_node (targetnode a)). 
      fst cf\<^sub>1' V = state_val (transfer (slice_kind S a) s\<^sub>2) V" 
    proof
      fix V assume "V \<in> rv S (CFG_node (targetnode a))"
      show "fst cf\<^sub>1' V = state_val (transfer (slice_kind S a) s\<^sub>2) V"
      proof(cases "V \<in> Def (sourcenode a)")
        case True
        from \<open>intra_kind (kind a)\<close> have "(\<exists>f. kind a = \<Up>f) \<or> (\<exists>Q. kind a = (Q)\<^sub>\<surd>)" 
          by(simp add:intra_kind_def)
        thus ?thesis
        proof
          assume "\<exists>f. kind a = \<Up>f"
          then obtain f' where "kind a = \<Up>f'" by blast
          with \<open>transfer (kind a) s\<^sub>1 = s\<^sub>1'\<close>
          have "s\<^sub>1' = (f' (fst cf\<^sub>1),snd cf\<^sub>1) # cfs\<^sub>1" by simp
          from \<open>sourcenode a \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close> \<open>kind a = \<Up>f'\<close>
          have "slice_kind S a = \<Up>f'"
            by(fastforce dest:slice_intra_kind_in_slice simp:intra_kind_def)
          hence "transfer (slice_kind S a) s\<^sub>2 = (f' (fst cf\<^sub>2),snd cf\<^sub>2) # cfs\<^sub>2" by simp
          from \<open>valid_edge a\<close> \<open>\<forall>V \<in> Use (sourcenode a). fst cf\<^sub>1 V = fst cf\<^sub>2 V\<close> 
            \<open>intra_kind (kind a)\<close> \<open>pred (kind a) s\<^sub>1\<close> \<open>pred (kind a) s\<^sub>2\<close>
          have "\<forall>V \<in> Def (sourcenode a). state_val (transfer (kind a) s\<^sub>1) V =
            state_val (transfer (kind a) s\<^sub>2) V"
            by -(erule CFG_intra_edge_transfer_uses_only_Use,auto)
          with \<open>kind a = \<Up>f'\<close> \<open>s\<^sub>1' = (f' (fst cf\<^sub>1),snd cf\<^sub>1) # cfs\<^sub>1\<close> True
            \<open>transfer (slice_kind S a) s\<^sub>2 = (f' (fst cf\<^sub>2),snd cf\<^sub>2) # cfs\<^sub>2\<close>
          show ?thesis by simp
        next
          assume "\<exists>Q. kind a = (Q)\<^sub>\<surd>"
          then obtain Q where "kind a = (Q)\<^sub>\<surd>" by blast
          with \<open>transfer (kind a) s\<^sub>1 = s\<^sub>1'\<close> have "s\<^sub>1' = cf\<^sub>1 # cfs\<^sub>1" by simp
          from \<open>sourcenode a \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close> \<open>kind a = (Q)\<^sub>\<surd>\<close>
          have "slice_kind S a = (Q)\<^sub>\<surd>"
            by(fastforce dest:slice_intra_kind_in_slice simp:intra_kind_def)
          hence "transfer (slice_kind S a) s\<^sub>2 = s\<^sub>2" by simp
          from \<open>valid_edge a\<close> \<open>\<forall>V \<in> Use (sourcenode a). fst cf\<^sub>1 V = fst cf\<^sub>2 V\<close> 
            \<open>intra_kind (kind a)\<close> \<open>pred (kind a) s\<^sub>1\<close> \<open>pred (kind a) s\<^sub>2\<close>
          have "\<forall>V \<in> Def (sourcenode a). state_val (transfer (kind a) s\<^sub>1) V =
                                         state_val (transfer (kind a) s\<^sub>2) V"
            by -(erule CFG_intra_edge_transfer_uses_only_Use,auto simp:intra_kind_def)
          with True \<open>kind a = (Q)\<^sub>\<surd>\<close> \<open>s\<^sub>1' = cf\<^sub>1 # cfs\<^sub>1\<close>
            \<open>transfer (slice_kind S a) s\<^sub>2 = s\<^sub>2\<close> 
          show ?thesis by simp
        qed
      next
        case False
        with \<open>valid_edge a\<close> \<open>intra_kind (kind a)\<close> \<open>pred (kind a) s\<^sub>1\<close>
        have "state_val (transfer (kind a) s\<^sub>1) V = state_val s\<^sub>1 V"
          by(fastforce intro:CFG_intra_edge_no_Def_equal)
        with \<open>transfer (kind a) s\<^sub>1 = s\<^sub>1'\<close> have "fst cf\<^sub>1' V = fst cf\<^sub>1 V" by simp
        from \<open>sourcenode a \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close> \<open>intra_kind (kind a)\<close>
        have "slice_kind S a = kind a" by(fastforce intro:slice_intra_kind_in_slice)
        from False \<open>valid_edge a\<close> \<open>pred (kind a) s\<^sub>2\<close> \<open>intra_kind (kind a)\<close>
        have "state_val (transfer (kind a) s\<^sub>2) V = state_val s\<^sub>2 V"
          by(fastforce intro:CFG_intra_edge_no_Def_equal)
        with \<open>slice_kind S a = kind a\<close>
        have "state_val (transfer (slice_kind S a) s\<^sub>2) V = fst cf\<^sub>2 V" by simp
        from \<open>V \<in> rv S (CFG_node (targetnode a))\<close> obtain as' nx 
          where "targetnode a -as'\<rightarrow>\<^sub>\<iota>* parent_node nx" 
          and "nx \<in> HRB_slice S" and "V \<in> Use\<^bsub>SDG\<^esub> nx"
          and "\<forall>n''. valid_SDG_node n'' \<and> parent_node n'' \<in> set (sourcenodes as') 
                     \<longrightarrow> V \<notin> Def\<^bsub>SDG\<^esub> n''"
          by(fastforce elim:rvE)
        with \<open>\<forall>n''. valid_SDG_node n'' \<and> parent_node n'' \<in> set (sourcenodes as') 
                    \<longrightarrow> V \<notin> Def\<^bsub>SDG\<^esub> n''\<close> False
        have all:"\<forall>n''. valid_SDG_node n'' \<and> 
          parent_node n'' \<in> set (sourcenodes (a#as')) \<longrightarrow> V \<notin> Def\<^bsub>SDG\<^esub> n''"
          by(fastforce dest:SDG_Def_parent_Def simp:sourcenodes_def)
        from  \<open>valid_edge a\<close> \<open>targetnode a -as'\<rightarrow>\<^sub>\<iota>* parent_node nx\<close> 
          \<open>intra_kind (kind a)\<close>
        have "sourcenode a -a#as'\<rightarrow>\<^sub>\<iota>* parent_node nx"
          by(fastforce intro:Cons_path simp:intra_path_def)
        with \<open>nx \<in> HRB_slice S\<close> \<open>V \<in> Use\<^bsub>SDG\<^esub> nx\<close> all
        have "V \<in> rv S (CFG_node (sourcenode a))" by(fastforce intro:rvI)
        with \<open>\<forall>V \<in> rv S (CFG_node mx). (fst (s\<^sub>1!(length msx))) V = state_val s\<^sub>2 V\<close>
          \<open>state_val (transfer (slice_kind S a) s\<^sub>2) V = fst cf\<^sub>2 V\<close>
          \<open>fst cf\<^sub>1' V = fst cf\<^sub>1 V\<close>
        show ?thesis by fastforce
      qed
    qed
    with \<open>\<forall>i < length ms\<^sub>2. \<forall>V \<in> rv S (CFG_node ((mx#tl ms\<^sub>2)!i)). 
      (fst (s\<^sub>1!(length msx + i))) V = (fst (s\<^sub>2!i)) V\<close> cf2' 
      \<open>ms\<^sub>1' = [] @ targetnode a # tl ms\<^sub>2\<close>
      \<open>length ms\<^sub>1 = length s\<^sub>1\<close> \<open>length ms\<^sub>2 = length s\<^sub>2\<close> \<open>length s\<^sub>1 = length s\<^sub>2\<close>
    have "\<forall>i<length ms\<^sub>1'. \<forall>V\<in>rv S (CFG_node ((targetnode a # tl ms\<^sub>1')!i)).
      (fst (s\<^sub>1'!(length [] + i))) V = (fst (transfer (slice_kind S a) s\<^sub>2 ! i)) V"
      by clarsimp(case_tac i,auto)
    with \<open>\<forall>m \<in> set ms\<^sub>2. valid_node m\<close> \<open>\<forall>m \<in> set ms\<^sub>1'. valid_node m\<close> 
      \<open>length ms\<^sub>2 = length s\<^sub>2\<close> \<open>length s\<^sub>1' = length (transfer (slice_kind S a) s\<^sub>2)\<close>
      \<open>length ms\<^sub>1' = length s\<^sub>1'\<close> \<open>\<forall>m \<in> set (tl ms\<^sub>1'). return_node m\<close>
      \<open>ms\<^sub>1' = [] @ targetnode a # tl ms\<^sub>2\<close> \<open>get_proc mx = get_proc (hd ms\<^sub>2)\<close>
      \<open>\<forall>m \<in> set (tl ms\<^sub>1). \<exists>m'. call_of_return_node m m' \<and> m' \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close>
      \<open>\<forall>i<length ms\<^sub>1'. snd (s\<^sub>1' ! i) = snd (transfer (slice_kind S a) s\<^sub>2 ! i)\<close>
    have "((ms\<^sub>1',s\<^sub>1'),(ms\<^sub>1',transfer (slice_kind S a) s\<^sub>2)) \<in> WS S"
      by(fastforce intro!:WSI)
    with \<open>S,slice_kind S \<turnstile> (ms\<^sub>2,s\<^sub>2) =as@[a]\<Rightarrow> (ms\<^sub>1',transfer (slice_kind S a) s\<^sub>2)\<close>
    show ?case by blast
  next
    case (observable_move_call a s\<^sub>1 s\<^sub>1' Q r p fs a' ms\<^sub>1 S ms\<^sub>1')
    from \<open>s\<^sub>1 \<noteq> []\<close> \<open>s\<^sub>2 \<noteq> []\<close> obtain cf\<^sub>1 cfs\<^sub>1 cf\<^sub>2 cfs\<^sub>2 where [simp]:"s\<^sub>1 = cf\<^sub>1#cfs\<^sub>1" 
      and [simp]:"s\<^sub>2 = cf\<^sub>2#cfs\<^sub>2" by(cases s\<^sub>1,auto,cases s\<^sub>2,fastforce+)
    from \<open>length ms\<^sub>1 = length s\<^sub>1\<close> \<open>s\<^sub>1 \<noteq> []\<close> have [simp]:"ms\<^sub>1 \<noteq> []" by(cases ms\<^sub>1) auto
    from \<open>length ms\<^sub>2 = length s\<^sub>2\<close> \<open>s\<^sub>2 \<noteq> []\<close> have [simp]:"ms\<^sub>2 \<noteq> []" by(cases ms\<^sub>2) auto
    from \<open>\<forall>m \<in> set (tl ms\<^sub>1). \<exists>m'. call_of_return_node m m' \<and> m' \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close>
      \<open>hd ms\<^sub>1 = sourcenode a\<close> \<open>ms\<^sub>1 = msx@mx#tl ms\<^sub>2\<close>
      \<open>msx \<noteq> [] \<longrightarrow> (\<exists>mx'. call_of_return_node mx mx' \<and> mx' \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>)\<close>
    have [simp]:"mx = sourcenode a" "msx = []" and [simp]:"tl ms\<^sub>2 = tl ms\<^sub>1"
      by(cases msx,auto)+
    hence "length ms\<^sub>1 = length ms\<^sub>2" by(cases ms\<^sub>2) auto
    with \<open>length ms\<^sub>1 = length s\<^sub>1\<close> \<open>length ms\<^sub>2 = length s\<^sub>2\<close>
    have "length s\<^sub>1 = length s\<^sub>2" by simp
    from \<open>hd ms\<^sub>1 \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close> \<open>hd ms\<^sub>1 = sourcenode a\<close>
    have "sourcenode a \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>" by simp
    with \<open>valid_edge a\<close> 
    have "obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {sourcenode a}"
      by(fastforce intro!:n_in_obs_intra)
    from \<open>\<forall>m \<in> set (tl ms\<^sub>2). \<exists>m'. call_of_return_node m m' \<and> m' \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close>
      \<open>obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {sourcenode a}\<close> 
      \<open>hd ms\<^sub>1 = sourcenode a\<close> 
    have "(hd ms\<^sub>1#tl ms\<^sub>1) \<in> obs ([]@hd ms\<^sub>1#tl ms\<^sub>1) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
      by(cases ms\<^sub>1)(auto intro!:obsI)
    hence "ms\<^sub>1 \<in> obs ms\<^sub>1 \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>" by simp
    with \<open>obs ms\<^sub>1 \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = obs ms\<^sub>2 \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close>
    have "ms\<^sub>1 \<in> obs ms\<^sub>2 \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>" by simp
    from \<open>ms\<^sub>2 \<noteq> []\<close> \<open>length ms\<^sub>2 = length s\<^sub>2\<close> have "length s\<^sub>2 = length (hd ms\<^sub>2#tl ms\<^sub>2)"
      by(fastforce dest!:hd_Cons_tl)
    from \<open>\<forall>m \<in> set (tl ms\<^sub>1). return_node m\<close> have "\<forall>m \<in> set (tl ms\<^sub>2). return_node m"
      by simp
    with \<open>ms\<^sub>1 \<in> obs ms\<^sub>2 \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close>
    have "hd ms\<^sub>1 \<in> obs_intra (hd ms\<^sub>2) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
    proof(rule obsE)
      fix nsx n nsx' n'
      assume "ms\<^sub>2 = nsx @ n # nsx'" and "ms\<^sub>1 = n' # nsx'"
        and "n' \<in> obs_intra n \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
      from \<open>ms\<^sub>2 = nsx @ n # nsx'\<close> \<open>ms\<^sub>1 = n' # nsx'\<close> \<open>tl ms\<^sub>2 = tl ms\<^sub>1\<close>
      have [simp]:"nsx = []" by(cases nsx) auto
      with \<open>ms\<^sub>2 = nsx @ n # nsx'\<close> have [simp]:"n = hd ms\<^sub>2" by simp
      from \<open>ms\<^sub>1 = n' # nsx'\<close> have [simp]:"n' = hd ms\<^sub>1" by simp
      with \<open>n' \<in> obs_intra n \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close> show ?thesis by simp
    qed
    with \<open>length s\<^sub>2 = length (hd ms\<^sub>2#tl ms\<^sub>2)\<close> \<open>\<forall>m \<in> set (tl ms\<^sub>2). return_node m\<close>
    obtain as where "S,slice_kind S \<turnstile> (hd ms\<^sub>2#tl ms\<^sub>2,s\<^sub>2) =as\<Rightarrow>\<^sub>\<tau> (hd ms\<^sub>1#tl ms\<^sub>1,s\<^sub>2)"
      by(fastforce elim:silent_moves_intra_path_obs[of _ _ _ s\<^sub>2 "tl ms\<^sub>2"])
    with \<open>ms\<^sub>2 \<noteq> []\<close> have "S,slice_kind S \<turnstile> (ms\<^sub>2,s\<^sub>2) =as\<Rightarrow>\<^sub>\<tau> (ms\<^sub>1,s\<^sub>2)"
      by(fastforce dest!:hd_Cons_tl)
    from \<open>valid_edge a\<close> have "valid_node (sourcenode a)" by simp
    hence "sourcenode a -[]\<rightarrow>\<^sub>\<iota>* sourcenode a"
      by(fastforce intro:empty_path simp:intra_path_def)
    with \<open>sourcenode a \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close>
    have "\<forall>V. V \<in> Use\<^bsub>SDG\<^esub> (CFG_node (sourcenode a)) 
      \<longrightarrow> V \<in> rv S (CFG_node (sourcenode a))"
      by auto(rule rvI,auto simp:SDG_to_CFG_set_def sourcenodes_def)
    with \<open>valid_node (sourcenode a)\<close>
    have "\<forall>V \<in> Use (sourcenode a). V \<in> rv S (CFG_node (sourcenode a))"
      by(fastforce intro:CFG_Use_SDG_Use)
    from \<open>\<forall>i < length ms\<^sub>2. \<forall>V \<in> rv S (CFG_node ((mx#tl ms\<^sub>2)!i)). 
      (fst (s\<^sub>1!(length msx + i))) V = (fst (s\<^sub>2!i)) V\<close> \<open>length ms\<^sub>2 = length s\<^sub>2\<close>
    have "\<forall>V\<in>rv S (CFG_node mx). (fst (s\<^sub>1 ! length msx)) V = state_val s\<^sub>2 V"
      by(cases ms\<^sub>2) auto
    with \<open>\<forall>V \<in> Use (sourcenode a). V \<in> rv S (CFG_node (sourcenode a))\<close>
    have "\<forall>V \<in> Use (sourcenode a). fst cf\<^sub>1 V = fst cf\<^sub>2 V" by fastforce
    moreover
    from \<open>\<forall>i<length ms\<^sub>2. snd (s\<^sub>1 ! (length msx + i)) = snd (s\<^sub>2 ! i)\<close>
    have "snd (hd s\<^sub>1) = snd (hd s\<^sub>2)" by(erule_tac x="0" in allE) auto
    ultimately have "pred (kind a) s\<^sub>2"
      using \<open>valid_edge a\<close> \<open>pred (kind a) s\<^sub>1\<close> \<open>length s\<^sub>1 = length s\<^sub>2\<close>
      by(fastforce intro:CFG_edge_Uses_pred_equal)
    from \<open>ms\<^sub>1' = (targetnode a)#(targetnode a')#tl ms\<^sub>1\<close> \<open>length s\<^sub>1' = Suc(length s\<^sub>1)\<close> 
      \<open>length ms\<^sub>1 = length s\<^sub>1\<close> have "length ms\<^sub>1' = length s\<^sub>1'" by simp
    from \<open>valid_edge a\<close> \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close> obtain ins outs 
      where "(p,ins,outs) \<in> set procs" by(fastforce dest!:callee_in_procs)
    with \<open>valid_edge a\<close> \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close> 
    have "(THE ins. \<exists>outs. (p,ins,outs) \<in> set procs) = ins"
      by(rule formal_in_THE)
    with \<open>transfer (kind a) s\<^sub>1 = s\<^sub>1'\<close> \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close>
    have [simp]:"s\<^sub>1' = (Map.empty(ins [:=] params fs (fst cf\<^sub>1)),r)#cf\<^sub>1#cfs\<^sub>1" by simp
    from \<open>valid_edge a'\<close> \<open>a' \<in> get_return_edges a\<close> \<open>valid_edge a\<close>
    have "return_node (targetnode a')" by(fastforce simp:return_node_def)
    with \<open>valid_edge a\<close> \<open>valid_edge a'\<close> \<open>a' \<in> get_return_edges a\<close>
    have "call_of_return_node (targetnode a') (sourcenode a)"
      by(simp add:call_of_return_node_def) blast
    from \<open>sourcenode a \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close> \<open>pred (kind a) s\<^sub>2\<close> \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close>
    have "pred (slice_kind S a) s\<^sub>2" by(fastforce dest:slice_kind_Call_in_slice)
    from \<open>valid_edge a\<close> \<open>length s\<^sub>1 = length s\<^sub>2\<close> \<open>transfer (kind a) s\<^sub>1 = s\<^sub>1'\<close>
    have "length s\<^sub>1' = length (transfer (slice_kind S a) s\<^sub>2)"
      by(fastforce intro:length_transfer_kind_slice_kind)
    with \<open>pred (slice_kind S a) s\<^sub>2\<close> \<open>valid_edge a\<close> \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close>
      \<open>\<forall>m \<in> set (tl ms\<^sub>1). \<exists>m'. call_of_return_node m m' \<and> m' \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close>
      \<open>hd ms\<^sub>1 \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close> \<open>hd ms\<^sub>1 = sourcenode a\<close>
      \<open>length ms\<^sub>1 = length s\<^sub>1\<close> \<open>length s\<^sub>1 = length s\<^sub>2\<close> \<open>valid_edge a'\<close>
      \<open>ms\<^sub>1' = (targetnode a)#(targetnode a')#tl ms\<^sub>1\<close> \<open>a' \<in> get_return_edges a\<close>
      \<open>\<forall>m \<in> set (tl ms\<^sub>2). return_node m\<close>
    have "S,slice_kind S \<turnstile> (ms\<^sub>1,s\<^sub>2) -a\<rightarrow> (ms\<^sub>1',transfer (slice_kind S a) s\<^sub>2)"
      by(auto intro:observable_move.observable_move_call)
    with \<open>S,slice_kind S \<turnstile> (ms\<^sub>2,s\<^sub>2) =as\<Rightarrow>\<^sub>\<tau> (ms\<^sub>1,s\<^sub>2)\<close> 
    have "S,slice_kind S \<turnstile> (ms\<^sub>2,s\<^sub>2) =as@[a]\<Rightarrow> (ms\<^sub>1',transfer (slice_kind S a) s\<^sub>2)"
      by(rule observable_moves_snoc)
    from \<open>\<forall>m \<in> set ms\<^sub>1. valid_node m\<close> \<open>ms\<^sub>1' = (targetnode a)#(targetnode a')#tl ms\<^sub>1\<close>
      \<open>valid_edge a\<close> \<open>valid_edge a'\<close>
    have "\<forall>m \<in> set ms\<^sub>1'. valid_node m" by(cases ms\<^sub>1) auto
    from \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close> \<open>sourcenode a \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close>
    have cf2':"\<exists>cf\<^sub>2'. transfer (slice_kind S a) s\<^sub>2 = cf\<^sub>2'#s\<^sub>2 \<and> snd cf\<^sub>2' = r"
      by(auto dest:slice_kind_Call_in_slice)
    with \<open>\<forall>i<length ms\<^sub>2. snd (s\<^sub>1 ! (length msx + i)) = snd (s\<^sub>2 ! i)\<close> 
      \<open>length ms\<^sub>1' = length s\<^sub>1'\<close> \<open>msx = []\<close> \<open>length ms\<^sub>1 = length ms\<^sub>2\<close>
      \<open>length ms\<^sub>1 = length s\<^sub>1\<close>
    have "\<forall>i<length ms\<^sub>1'. snd (s\<^sub>1' ! i) = snd (transfer (slice_kind S a) s\<^sub>2 ! i)"
      by auto(case_tac i,auto)
    have "\<forall>V \<in> rv S (CFG_node (targetnode a')). 
      V \<in> rv S (CFG_node (sourcenode a))"
    proof
      fix V assume "V \<in> rv S (CFG_node (targetnode a'))"
      then obtain as n' where "targetnode a' -as\<rightarrow>\<^sub>\<iota>* parent_node n'"
        and "n' \<in> HRB_slice S" and "V \<in> Use\<^bsub>SDG\<^esub> n'"
        and "\<forall>n''. valid_SDG_node n'' \<and> parent_node n'' \<in> set (sourcenodes as) 
        \<longrightarrow> V \<notin> Def\<^bsub>SDG\<^esub> n''" by(fastforce elim:rvE)
      from \<open>valid_edge a\<close> \<open>a' \<in> get_return_edges a\<close>
      obtain a'' where "valid_edge a''" and "sourcenode a'' = sourcenode a"
        and "targetnode a'' = targetnode a'" and "intra_kind(kind a'')"
        by -(drule call_return_node_edge,auto simp:intra_kind_def)
      with \<open>targetnode a' -as\<rightarrow>\<^sub>\<iota>* parent_node n'\<close> 
      have "sourcenode a -a''#as\<rightarrow>\<^sub>\<iota>* parent_node n'"
        by(fastforce intro:Cons_path simp:intra_path_def)
      from \<open>sourcenode a'' = sourcenode a\<close> \<open>valid_edge a\<close> \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close>
      have "\<forall>n''. valid_SDG_node n'' \<and> parent_node n'' = sourcenode a''
        \<longrightarrow> V \<notin> Def\<^bsub>SDG\<^esub> n''"
        by(fastforce dest:SDG_Def_parent_Def call_source_Def_empty)
      with \<open>\<forall>n''. valid_SDG_node n'' \<and> parent_node n'' \<in> set (sourcenodes as) 
        \<longrightarrow> V \<notin> Def\<^bsub>SDG\<^esub> n''\<close>
      have "\<forall>n''. valid_SDG_node n'' \<and> parent_node n'' \<in> set (sourcenodes (a''#as)) 
        \<longrightarrow> V \<notin> Def\<^bsub>SDG\<^esub> n''" by(fastforce simp:sourcenodes_def)
      with \<open>sourcenode a -a''#as\<rightarrow>\<^sub>\<iota>* parent_node n'\<close> \<open>n' \<in> HRB_slice S\<close>
        \<open>V \<in> Use\<^bsub>SDG\<^esub> n'\<close>
      show "V \<in> rv S (CFG_node (sourcenode a))" by(fastforce intro:rvI)
    qed
    have "\<forall>V \<in> rv S (CFG_node (targetnode a)). 
      (Map.empty(ins [:=] params fs (fst cf\<^sub>1))) V = 
      state_val (transfer (slice_kind S a) s\<^sub>2) V"
    proof
      fix V assume "V \<in> rv S (CFG_node (targetnode a))"
      from \<open>sourcenode a \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close> \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close>
        \<open>(THE ins. \<exists>outs. (p,ins,outs) \<in> set procs) = ins\<close>
      have eq:"fst (hd (transfer (slice_kind S a) s\<^sub>2)) = 
        Map.empty(ins [:=] params (cspp (targetnode a) (HRB_slice S) fs) (fst cf\<^sub>2))"
        by(auto dest:slice_kind_Call_in_slice)
      show "(Map.empty(ins [:=] params fs (fst cf\<^sub>1))) V = 
        state_val (transfer (slice_kind S a) s\<^sub>2) V"
      proof(cases "V \<in> set ins")
        case True
        then obtain i where "V = ins!i" and "i < length ins"
          by(auto simp:in_set_conv_nth)
        from \<open>valid_edge a\<close> \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close> \<open>(p,ins,outs) \<in> set procs\<close>
          \<open>i < length ins\<close>
        have "valid_SDG_node (Formal_in (targetnode a,i))" by fastforce
        from \<open>valid_edge a\<close> \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close> have "get_proc(targetnode a) = p"
          by(rule get_proc_call)
        with \<open>valid_SDG_node (Formal_in (targetnode a,i))\<close> 
          \<open>(p,ins,outs) \<in> set procs\<close> \<open>V = ins!i\<close>
        have "V \<in> Def\<^bsub>SDG\<^esub> (Formal_in (targetnode a,i))"
          by(fastforce intro:Formal_in_SDG_Def)
        from \<open>V \<in> rv S (CFG_node (targetnode a))\<close> obtain as' nx 
          where "targetnode a -as'\<rightarrow>\<^sub>\<iota>* parent_node nx" 
          and "nx \<in> HRB_slice S" and "V \<in> Use\<^bsub>SDG\<^esub> nx"
          and "\<forall>n''. valid_SDG_node n'' \<and> 
          parent_node n'' \<in> set (sourcenodes as') \<longrightarrow> V \<notin> Def\<^bsub>SDG\<^esub> n''"
          by(fastforce elim:rvE)
        with \<open>valid_SDG_node (Formal_in (targetnode a,i))\<close>
          \<open>V \<in> Def\<^bsub>SDG\<^esub> (Formal_in (targetnode a,i))\<close>
        have "targetnode a = parent_node nx" 
          apply(auto simp:intra_path_def sourcenodes_def)
          apply(erule path.cases) apply fastforce
          apply(erule_tac x="Formal_in (targetnode a,i)" in allE) by fastforce
        with \<open>V \<in> Use\<^bsub>SDG\<^esub> nx\<close> have "V \<in> Use (targetnode a)"
          by(fastforce intro:SDG_Use_parent_Use)
        with \<open>valid_edge a\<close> have "V \<in> Use\<^bsub>SDG\<^esub> (CFG_node (targetnode a))"
          by(auto intro!:CFG_Use_SDG_Use)
        from \<open>targetnode a = parent_node nx\<close>[THEN sym] \<open>valid_edge a\<close>
        have "parent_node (Formal_in (targetnode a,i)) -[]\<rightarrow>\<^sub>\<iota>* parent_node nx"
          by(fastforce intro:empty_path simp:intra_path_def)
        with \<open>V \<in> Def\<^bsub>SDG\<^esub> (Formal_in (targetnode a,i))\<close> 
          \<open>V \<in> Use\<^bsub>SDG\<^esub> (CFG_node (targetnode a))\<close> \<open>targetnode a = parent_node nx\<close>
        have "Formal_in (targetnode a,i) influences V in (CFG_node (targetnode a))"
          by(fastforce simp:data_dependence_def sourcenodes_def)
        hence ddep:"Formal_in (targetnode a,i) s-V\<rightarrow>\<^sub>d\<^sub>d (CFG_node (targetnode a))"
          by(rule sum_SDG_ddep_edge)
        from \<open>targetnode a = parent_node nx\<close> \<open>nx \<in> HRB_slice S\<close>
        have "CFG_node (targetnode a) \<in> HRB_slice S"
          by(fastforce dest:valid_SDG_node_in_slice_parent_node_in_slice)
        hence "Formal_in (targetnode a,i) \<in> HRB_slice S"
        proof(induct "CFG_node (targetnode a)" rule:HRB_slice_cases)
          case (phase1 nx)
          with ddep show ?case
            by(fastforce intro:ddep_slice1 combine_SDG_slices.combSlice_refl 
                         simp:HRB_slice_def)
        next
          case (phase2 nx n' n'' p)
          from \<open>CFG_node (targetnode a) \<in> sum_SDG_slice2 n'\<close> ddep
          have "Formal_in (targetnode a,i) \<in> sum_SDG_slice2 n'"
            by(fastforce intro:ddep_slice2)
          with \<open>n'' s-p\<rightarrow>\<^bsub>ret\<^esub> CFG_node (parent_node n')\<close> \<open>n' \<in> sum_SDG_slice1 nx\<close> 
            \<open>nx \<in> S\<close>
          show ?case by(fastforce intro:combine_SDG_slices.combSlice_Return_parent_node                                  simp:HRB_slice_def)
        qed
        from \<open>sourcenode a \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close> \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close>
        have slice_kind:"slice_kind S a = 
          Q:r\<hookrightarrow>\<^bsub>p\<^esub>(cspp (targetnode a) (HRB_slice S) fs)"
          by(rule slice_kind_Call_in_slice)
        from \<open>valid_edge a\<close> \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close> \<open>(p,ins,outs) \<in> set procs\<close>
        have "length fs = length ins" by(rule CFG_call_edge_length)
        from \<open>Formal_in (targetnode a,i) \<in> HRB_slice S\<close>
          \<open>length fs = length ins\<close> \<open>i < length ins\<close>
        have cspp:"(cspp (targetnode a) (HRB_slice S) fs)!i = fs!i"
          by(fastforce intro:csppa_Formal_in_in_slice simp:cspp_def)
        from \<open>i < length ins\<close> \<open>length fs = length ins\<close>
        have "(params (cspp (targetnode a) (HRB_slice S) fs) (fst cf\<^sub>2))!i = 
          ((cspp (targetnode a) (HRB_slice S) fs)!i) (fst cf\<^sub>2)"
          by(fastforce intro:params_nth)
        with cspp 
        have eq:"(params (cspp (targetnode a) (HRB_slice S) fs) (fst cf\<^sub>2))!i =
          (fs!i) (fst cf\<^sub>2)" by simp
        from \<open>valid_edge a\<close> \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close> \<open>(p,ins,outs) \<in> set procs\<close>
        have "(THE ins. \<exists>outs. (p,ins,outs) \<in> set procs) = ins"
          by(rule formal_in_THE)
        with slice_kind
        have "fst (hd (transfer (slice_kind S a) s\<^sub>2)) = 
          Map.empty(ins [:=] params (cspp (targetnode a) (HRB_slice S) fs) (fst cf\<^sub>2))"
          by simp
        moreover
        from \<open>(p,ins,outs) \<in> set procs\<close> have "distinct ins" 
          by(rule distinct_formal_ins)
        ultimately have "state_val (transfer (slice_kind S a) s\<^sub>2) V = 
          (params (cspp (targetnode a) (HRB_slice S) fs) (fst cf\<^sub>2))!i"
          using \<open>V = ins!i\<close> \<open>i < length ins\<close> \<open>length fs = length ins\<close>
          by(fastforce intro:fun_upds_nth)
        with eq 
        have 2:"state_val (transfer (slice_kind S a) s\<^sub>2) V = (fs!i) (fst cf\<^sub>2)"
          by simp
        from \<open>V = ins!i\<close> \<open>i < length ins\<close> \<open>length fs = length ins\<close>
          \<open>distinct ins\<close>
        have "Map.empty(ins [:=] params fs (fst cf\<^sub>1)) V = (params fs (fst cf\<^sub>1))!i"
          by(fastforce intro:fun_upds_nth)
        with \<open>i < length ins\<close> \<open>length fs = length ins\<close>
        have 1:"Map.empty(ins [:=] params fs (fst cf\<^sub>1)) V = (fs!i) (fst cf\<^sub>1)"
          by(fastforce intro:params_nth)
        from \<open>\<forall>i < length ms\<^sub>2. \<forall>V \<in> rv S (CFG_node ((mx#tl ms\<^sub>2)!i)). 
          (fst (s\<^sub>1!(length msx + i))) V = (fst (s\<^sub>2!i)) V\<close>
        have rv:"\<forall>V\<in>rv S (CFG_node (sourcenode a)). fst cf\<^sub>1 V = fst cf\<^sub>2 V"
          by(erule_tac x="0" in allE) auto
        from \<open>valid_edge a\<close> \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close> \<open>(p,ins,outs) \<in> set procs\<close> 
          \<open>i < length ins\<close> have "\<forall>V\<in>(ParamUses (sourcenode a)!i). 
          V \<in> Use\<^bsub>SDG\<^esub> (Actual_in (sourcenode a,i))"
          by(fastforce intro:Actual_in_SDG_Use)
        with \<open>valid_edge a\<close> have "\<forall>V\<in>(ParamUses (sourcenode a)!i). 
          V \<in> Use\<^bsub>SDG\<^esub> (CFG_node (sourcenode a))"
          by(auto intro!:CFG_Use_SDG_Use dest:SDG_Use_parent_Use)
        moreover
        from \<open>valid_edge a\<close> have "parent_node (CFG_node (sourcenode a)) -[]\<rightarrow>\<^sub>\<iota>* 
          parent_node (CFG_node (sourcenode a))"
          by(fastforce intro:empty_path simp:intra_path_def)
        ultimately 
        have "\<forall>V\<in>(ParamUses (sourcenode a)!i). V \<in> rv S (CFG_node (sourcenode a))"
          using \<open>sourcenode a \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close> \<open>valid_edge a\<close>
          by(fastforce intro:rvI simp:SDG_to_CFG_set_def sourcenodes_def)
        with rv have "\<forall>V \<in> (ParamUses (sourcenode a))!i. fst cf\<^sub>1 V = fst cf\<^sub>2 V"
          by fastforce
        with \<open>valid_edge a\<close> \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close> \<open>i < length ins\<close>
          \<open>(p,ins,outs) \<in> set procs\<close> \<open>pred (kind a) s\<^sub>1\<close> \<open>pred (kind a) s\<^sub>2\<close>
        have "(params fs (fst cf\<^sub>1))!i = (params fs (fst cf\<^sub>2))!i"
          by(fastforce dest!:CFG_call_edge_params)
        moreover
        from \<open>i < length ins\<close> \<open>length fs = length ins\<close>
        have "(params fs (fst cf\<^sub>1))!i = (fs!i) (fst cf\<^sub>1)" 
          and "(params fs (fst cf\<^sub>2))!i = (fs!i) (fst cf\<^sub>2)"
          by(auto intro:params_nth)
        ultimately show ?thesis using 1 2 by simp
      next
        case False
        with eq show ?thesis by(fastforce simp:fun_upds_notin)
      qed
    qed
    with \<open>\<forall>i < length ms\<^sub>2. \<forall>V \<in> rv S (CFG_node ((mx#tl ms\<^sub>2)!i)). 
      (fst (s\<^sub>1!(length msx + i))) V = (fst (s\<^sub>2!i)) V\<close> cf2' \<open>tl ms\<^sub>2 = tl ms\<^sub>1\<close>
      \<open>length ms\<^sub>2 = length s\<^sub>2\<close> \<open>length ms\<^sub>1 = length s\<^sub>1\<close> \<open>length s\<^sub>1 = length s\<^sub>2\<close>
      \<open>ms\<^sub>1' = (targetnode a)#(targetnode a')#tl ms\<^sub>1\<close>
      \<open>\<forall>V \<in> rv S (CFG_node (targetnode a')). V \<in> rv S (CFG_node (sourcenode a))\<close>
    have "\<forall>i<length ms\<^sub>1'. \<forall>V\<in>rv S (CFG_node ((targetnode a # tl ms\<^sub>1')!i)).
      (fst (s\<^sub>1'!(length [] + i))) V = (fst (transfer (slice_kind S a) s\<^sub>2!i)) V"
      apply clarsimp apply(case_tac i) apply auto
      apply(erule_tac x="nat" in allE)
      apply(case_tac nat) apply auto done
    with \<open>\<forall>m \<in> set ms\<^sub>2. valid_node m\<close> \<open>\<forall>m \<in> set ms\<^sub>1'. valid_node m\<close> 
      \<open>length ms\<^sub>2 = length s\<^sub>2\<close> \<open>length s\<^sub>1' = length (transfer (slice_kind S a) s\<^sub>2)\<close>
      \<open>length ms\<^sub>1' = length s\<^sub>1'\<close> \<open>ms\<^sub>1' = (targetnode a)#(targetnode a')#tl ms\<^sub>1\<close>
      \<open>get_proc mx = get_proc (hd ms\<^sub>2)\<close> \<open>sourcenode a \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close>
      \<open>\<forall>m \<in> set (tl ms\<^sub>1). \<exists>m'. call_of_return_node m m' \<and> m' \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close>
      \<open>return_node (targetnode a')\<close> \<open>\<forall>m \<in> set (tl ms\<^sub>1). return_node m\<close>
      \<open>call_of_return_node (targetnode a') (sourcenode a)\<close>
      \<open>\<forall>i<length ms\<^sub>1'. snd (s\<^sub>1' ! i) = snd (transfer (slice_kind S a) s\<^sub>2 ! i)\<close>
    have "((ms\<^sub>1',s\<^sub>1'),(ms\<^sub>1',transfer (slice_kind S a) s\<^sub>2)) \<in> WS S"
      by(fastforce intro!:WSI)
    with \<open>S,slice_kind S \<turnstile> (ms\<^sub>2,s\<^sub>2) =as@[a]\<Rightarrow> (ms\<^sub>1',transfer (slice_kind S a) s\<^sub>2)\<close>
    show ?case by blast
  next
    case (observable_move_return a s\<^sub>1 s\<^sub>1' Q p f' ms\<^sub>1 S ms\<^sub>1')
    from \<open>s\<^sub>1 \<noteq> []\<close> \<open>s\<^sub>2 \<noteq> []\<close> obtain cf\<^sub>1 cfs\<^sub>1 cf\<^sub>2 cfs\<^sub>2 where [simp]:"s\<^sub>1 = cf\<^sub>1#cfs\<^sub>1" 
      and [simp]:"s\<^sub>2 = cf\<^sub>2#cfs\<^sub>2" by(cases s\<^sub>1,auto,cases s\<^sub>2,fastforce+)
    from \<open>length ms\<^sub>1 = length s\<^sub>1\<close> \<open>s\<^sub>1 \<noteq> []\<close> have [simp]:"ms\<^sub>1 \<noteq> []" by(cases ms\<^sub>1) auto
    from \<open>length ms\<^sub>2 = length s\<^sub>2\<close> \<open>s\<^sub>2 \<noteq> []\<close> have [simp]:"ms\<^sub>2 \<noteq> []" by(cases ms\<^sub>2) auto
    from \<open>\<forall>m \<in> set (tl ms\<^sub>1). \<exists>m'. call_of_return_node m m' \<and> m' \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close>
      \<open>hd ms\<^sub>1 = sourcenode a\<close> \<open>ms\<^sub>1 = msx@mx#tl ms\<^sub>2\<close>
      \<open>msx \<noteq> [] \<longrightarrow> (\<exists>mx'. call_of_return_node mx mx' \<and> mx' \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>)\<close>
    have [simp]:"mx = sourcenode a" "msx = []" and [simp]:"tl ms\<^sub>2 = tl ms\<^sub>1"
      by(cases msx,auto)+
    hence "length ms\<^sub>1 = length ms\<^sub>2" by(cases ms\<^sub>2) auto
    with \<open>length ms\<^sub>1 = length s\<^sub>1\<close> \<open>length ms\<^sub>2 = length s\<^sub>2\<close>
    have "length s\<^sub>1 = length s\<^sub>2" by simp
    have "\<exists>as. S,slice_kind S \<turnstile> (ms\<^sub>2,s\<^sub>2) =as\<Rightarrow>\<^sub>\<tau> (ms\<^sub>1,s\<^sub>2)"
    proof(cases "obs_intra (hd ms\<^sub>2) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {}")
      case True
      from \<open>valid_edge a\<close> \<open>hd ms\<^sub>1 = sourcenode a\<close> \<open>kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f'\<close>
      have "method_exit (hd ms\<^sub>1)" by(fastforce simp:method_exit_def)
      from \<open>\<forall>m\<in>set ms\<^sub>2. valid_node m\<close> have "valid_node (hd ms\<^sub>2)" by(cases ms\<^sub>2) auto
      then obtain asx where "hd ms\<^sub>2 -asx\<rightarrow>\<^sub>\<surd>* (_Exit_)" by(fastforce dest!:Exit_path)
      then obtain as pex where "hd ms\<^sub>2 -as\<rightarrow>\<^sub>\<iota>* pex" and "method_exit pex"
        by(fastforce elim:valid_Exit_path_intra_path)
      from \<open>hd ms\<^sub>2 -as\<rightarrow>\<^sub>\<iota>* pex\<close> have "get_proc (hd ms\<^sub>2) = get_proc pex"
        by(rule intra_path_get_procs)
      with \<open>get_proc mx = get_proc (hd ms\<^sub>2)\<close>
      have "get_proc mx = get_proc pex" by simp
      with \<open>method_exit (hd ms\<^sub>1)\<close> \<open> hd ms\<^sub>1 = sourcenode a\<close> \<open>method_exit pex\<close>
      have [simp]:"pex = hd ms\<^sub>1" by(fastforce intro:method_exit_unique)
      from \<open>obs_intra (hd ms\<^sub>2) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {}\<close> \<open>method_exit pex\<close>
        \<open>get_proc (hd ms\<^sub>2) = get_proc pex\<close> \<open>valid_node (hd ms\<^sub>2)\<close>
        \<open>length ms\<^sub>2 = length s\<^sub>2\<close> \<open>\<forall>m\<in>set (tl ms\<^sub>1). return_node m\<close> \<open>ms\<^sub>2 \<noteq> []\<close>
      obtain as' 
        where "S,slice_kind S \<turnstile> (hd ms\<^sub>2#tl ms\<^sub>2,s\<^sub>2) =as'\<Rightarrow>\<^sub>\<tau> (hd ms\<^sub>1#tl ms\<^sub>1,s\<^sub>2)"
        by(fastforce elim!:silent_moves_intra_path_no_obs[of _ _ _ s\<^sub>2 "tl ms\<^sub>2"]
                     dest:hd_Cons_tl)
      with \<open>ms\<^sub>2 \<noteq> []\<close> have "S,slice_kind S \<turnstile> (ms\<^sub>2,s\<^sub>2) =as'\<Rightarrow>\<^sub>\<tau> (ms\<^sub>1,s\<^sub>2)"
        by(fastforce dest!:hd_Cons_tl)
      thus ?thesis by blast
    next
      case False
      then obtain x where "x \<in> obs_intra (hd ms\<^sub>2) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>" by fastforce
      hence "obs_intra (hd ms\<^sub>2) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {x}"
        by(rule obs_intra_singleton_element)
      with \<open>\<forall>m \<in> set (tl ms\<^sub>2). \<exists>m'. call_of_return_node m m' \<and> m' \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close>
      have "x#tl ms\<^sub>1 \<in> obs ([]@hd ms\<^sub>2#tl ms\<^sub>2) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
        by(fastforce intro:obsI)
      with \<open>ms\<^sub>2 \<noteq> []\<close> have "x#tl ms\<^sub>1 \<in> obs ms\<^sub>2 \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
        by(fastforce dest:hd_Cons_tl simp del:obs.simps)
      with \<open>obs ms\<^sub>1 \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = obs ms\<^sub>2 \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close>
      have "x#tl ms\<^sub>1 \<in> obs ms\<^sub>1 \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>" by simp
      from this \<open>\<forall>m\<in>set (tl ms\<^sub>1). return_node m\<close>
      have "x \<in> obs_intra (hd ms\<^sub>1) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
      proof(rule obsE)
        fix nsx n nsx' n'
        assume "ms\<^sub>1 = nsx @ n # nsx'" and "x # tl ms\<^sub>1 = n' # nsx'"
          and "n' \<in> obs_intra n \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
        from \<open>ms\<^sub>1 = nsx @ n # nsx'\<close> \<open>x # tl ms\<^sub>1 = n' # nsx'\<close> \<open>tl ms\<^sub>2 = tl ms\<^sub>1\<close>
        have [simp]:"nsx = []" by(cases nsx) auto
        with \<open>ms\<^sub>1 = nsx @ n # nsx'\<close> have [simp]:"n = hd ms\<^sub>1" by simp
        from \<open>x # tl ms\<^sub>1 = n' # nsx'\<close> have [simp]:"n' = x" by simp
        with \<open>n' \<in> obs_intra n \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close> show ?thesis by simp
      qed
      { fix m as assume "hd ms\<^sub>1 -as\<rightarrow>\<^sub>\<iota>* m"
        hence "hd ms\<^sub>1 -as\<rightarrow>* m" and "\<forall>a \<in> set as. intra_kind (kind a)"
          by(simp_all add:intra_path_def)
        hence "m = hd ms\<^sub>1"
        proof(induct "hd ms\<^sub>1" as m rule:path.induct)
          case (Cons_path m'' as' m' a')
          from \<open>\<forall>a\<in>set (a' # as'). intra_kind (kind a)\<close>
          have "intra_kind (kind a')" by simp
          with \<open>valid_edge a\<close> \<open>kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f'\<close> \<open>valid_edge a'\<close> 
            \<open>sourcenode a' = hd ms\<^sub>1\<close> \<open>hd ms\<^sub>1 = sourcenode a\<close>
          have False by(fastforce dest:return_edges_only simp:intra_kind_def)
          thus ?case by simp
        qed simp }
      with \<open>x \<in> obs_intra (hd ms\<^sub>1) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close>
      have "x = hd ms\<^sub>1" by(fastforce elim:obs_intraE)
      with \<open>x \<in> obs_intra (hd ms\<^sub>2) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close> \<open>length ms\<^sub>2 = length s\<^sub>2\<close> 
        \<open>\<forall>m\<in>set (tl ms\<^sub>1). return_node m\<close> \<open>ms\<^sub>2 \<noteq> []\<close>
      obtain as where "S,slice_kind S \<turnstile> (hd ms\<^sub>2#tl ms\<^sub>2,s\<^sub>2) =as\<Rightarrow>\<^sub>\<tau> (hd ms\<^sub>1#tl ms\<^sub>1,s\<^sub>2)"
        by(fastforce elim!:silent_moves_intra_path_obs[of _ _ _ s\<^sub>2 "tl ms\<^sub>2"] 
                     dest:hd_Cons_tl)
      with \<open>ms\<^sub>2 \<noteq> []\<close> have "S,slice_kind S \<turnstile> (ms\<^sub>2,s\<^sub>2) =as\<Rightarrow>\<^sub>\<tau> (ms\<^sub>1,s\<^sub>2)"
        by(fastforce dest!:hd_Cons_tl)
      thus ?thesis by blast
    qed
    then obtain as where "S,slice_kind S \<turnstile> (ms\<^sub>2,s\<^sub>2) =as\<Rightarrow>\<^sub>\<tau> (ms\<^sub>1,s\<^sub>2)" by blast
    from \<open>ms\<^sub>1' = tl ms\<^sub>1\<close> \<open>length s\<^sub>1 = Suc(length s\<^sub>1')\<close> 
      \<open>length ms\<^sub>1 = length s\<^sub>1\<close> have "length ms\<^sub>1' = length s\<^sub>1'" by simp
    from \<open>valid_edge a\<close> \<open>kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f'\<close> obtain a'' Q' r' fs' where "valid_edge a''"
      and "kind a'' = Q':r'\<hookrightarrow>\<^bsub>p\<^esub>fs'" and "a \<in> get_return_edges a''"
      by -(drule return_needs_call,auto)
    then obtain ins outs where "(p,ins,outs) \<in> set procs"
      by(fastforce dest!:callee_in_procs)
    from \<open>length s\<^sub>1 = Suc(length s\<^sub>1')\<close> \<open>s\<^sub>1' \<noteq> []\<close>
    obtain cfx cfsx where [simp]:"cfs\<^sub>1 = cfx#cfsx" by(cases cfs\<^sub>1) auto
    with \<open>length s\<^sub>1 = length s\<^sub>2\<close> obtain cfx' cfsx' where [simp]:"cfs\<^sub>2 = cfx'#cfsx'"
      by(cases cfs\<^sub>2) auto
    from \<open>length ms\<^sub>1 = length s\<^sub>1\<close> have "tl ms\<^sub>1 = []@hd(tl ms\<^sub>1)#tl(tl ms\<^sub>1)"
      by(auto simp:length_Suc_conv)
    from \<open>kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f'\<close> \<open>transfer (kind a) s\<^sub>1 = s\<^sub>1'\<close>
    have "s\<^sub>1' = (f' (fst cf\<^sub>1) (fst cfx),snd cfx)#cfsx" by simp
    from \<open>valid_edge a\<close> \<open>kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f'\<close> \<open>(p,ins,outs) \<in> set procs\<close>
    have "f' (fst cf\<^sub>1) (fst cfx) = 
      (fst cfx)(ParamDefs (targetnode a) [:=] map (fst cf\<^sub>1) outs)"
      by(rule CFG_return_edge_fun)
    with \<open>s\<^sub>1' = (f' (fst cf\<^sub>1) (fst cfx),snd cfx)#cfsx\<close>
    have [simp]:"s\<^sub>1' = 
      ((fst cfx)(ParamDefs (targetnode a) [:=] map (fst cf\<^sub>1) outs),snd cfx)#cfsx"
      by simp
    have "pred (slice_kind S a) s\<^sub>2"
    proof(cases "sourcenode a \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>")
      case True
      from \<open>valid_edge a\<close> have "valid_node (sourcenode a)" by simp
      hence "sourcenode a -[]\<rightarrow>\<^sub>\<iota>* sourcenode a"
        by(fastforce intro:empty_path simp:intra_path_def)
      with \<open>sourcenode a \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close>
      have "\<forall>V. V \<in> Use\<^bsub>SDG\<^esub> (CFG_node (sourcenode a)) 
        \<longrightarrow> V \<in> rv S (CFG_node (sourcenode a))"
        by auto(rule rvI,auto simp:SDG_to_CFG_set_def sourcenodes_def)
      with \<open>valid_node (sourcenode a)\<close>
      have "\<forall>V \<in> Use (sourcenode a). V \<in> rv S (CFG_node (sourcenode a))"
        by(fastforce intro:CFG_Use_SDG_Use)
      from \<open>\<forall>i < length ms\<^sub>2. \<forall>V \<in> rv S (CFG_node ((mx#tl ms\<^sub>2)!i)). 
        (fst (s\<^sub>1!(length msx + i))) V = (fst (s\<^sub>2!i)) V\<close> \<open>length ms\<^sub>2 = length s\<^sub>2\<close>
      have "\<forall>V\<in>rv S (CFG_node mx). (fst (s\<^sub>1 ! length msx)) V = state_val s\<^sub>2 V"
        by(cases ms\<^sub>2) auto
      with \<open>\<forall>V \<in> Use (sourcenode a). V \<in> rv S (CFG_node (sourcenode a))\<close>
      have "\<forall>V \<in> Use (sourcenode a). fst cf\<^sub>1 V = fst cf\<^sub>2 V" by fastforce
      moreover
      from \<open>\<forall>i<length ms\<^sub>2. snd (s\<^sub>1 ! (length msx + i)) = snd (s\<^sub>2 ! i)\<close>
      have "snd (hd s\<^sub>1) = snd (hd s\<^sub>2)" by(erule_tac x="0" in allE) auto
      ultimately have "pred (kind a) s\<^sub>2"
        using \<open>valid_edge a\<close> \<open>pred (kind a) s\<^sub>1\<close> \<open>length s\<^sub>1 = length s\<^sub>2\<close>
        by(fastforce intro:CFG_edge_Uses_pred_equal)
      with \<open>valid_edge a\<close> \<open>kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f'\<close> \<open>(p,ins,outs) \<in> set procs\<close> 
        \<open>sourcenode a \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close>
      show ?thesis by(fastforce dest:slice_kind_Return_in_slice)
    next
      case False
      with \<open>kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f'\<close> have "slice_kind S a = (\<lambda>cf. True)\<hookleftarrow>\<^bsub>p\<^esub>(\<lambda>cf cf'. cf')"
        by -(rule slice_kind_Return)
      thus ?thesis by simp
    qed
    from \<open>valid_edge a\<close> \<open>length s\<^sub>1 = length s\<^sub>2\<close> \<open>transfer (kind a) s\<^sub>1 = s\<^sub>1'\<close>
    have "length s\<^sub>1' = length (transfer (slice_kind S a) s\<^sub>2)"
      by(fastforce intro:length_transfer_kind_slice_kind)
    with \<open>pred (slice_kind S a) s\<^sub>2\<close> \<open>valid_edge a\<close> \<open>kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f'\<close>
      \<open>\<forall>m \<in> set (tl ms\<^sub>1). \<exists>m'. call_of_return_node m m' \<and> m' \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close>
      \<open>hd ms\<^sub>1 = sourcenode a\<close>
      \<open>length ms\<^sub>1 = length s\<^sub>1\<close> \<open>length s\<^sub>1 = length s\<^sub>2\<close>
      \<open>ms\<^sub>1' = tl ms\<^sub>1\<close> \<open>hd(tl ms\<^sub>1) = targetnode a\<close> \<open>\<forall>m \<in> set (tl ms\<^sub>1). return_node m\<close>
    have "S,slice_kind S \<turnstile> (ms\<^sub>1,s\<^sub>2) -a\<rightarrow> (ms\<^sub>1',transfer (slice_kind S a) s\<^sub>2)"
      by(fastforce intro!:observable_move.observable_move_return)
    with \<open>S,slice_kind S \<turnstile> (ms\<^sub>2,s\<^sub>2) =as\<Rightarrow>\<^sub>\<tau> (ms\<^sub>1,s\<^sub>2)\<close>
    have "S,slice_kind S \<turnstile> (ms\<^sub>2,s\<^sub>2) =as@[a]\<Rightarrow> (ms\<^sub>1',transfer (slice_kind S a) s\<^sub>2)"
      by(rule observable_moves_snoc)
    from \<open>\<forall>m \<in> set ms\<^sub>1. valid_node m\<close> \<open>ms\<^sub>1' = tl ms\<^sub>1\<close>
    have "\<forall>m \<in> set ms\<^sub>1'. valid_node m" by(cases ms\<^sub>1) auto
    from \<open>length ms\<^sub>1' = length s\<^sub>1'\<close> have "ms\<^sub>1' = []@hd ms\<^sub>1'#tl ms\<^sub>1'"
      by(cases ms\<^sub>1') auto
    from \<open>\<forall>i<length ms\<^sub>2. snd (s\<^sub>1 ! (length msx + i)) = snd (s\<^sub>2 ! i)\<close>
      \<open>length ms\<^sub>1 = length ms\<^sub>2\<close> \<open>length ms\<^sub>1 = length s\<^sub>1\<close>
    have "snd cfx = snd cfx'" by(erule_tac x="1" in allE) auto
    from \<open>valid_edge a\<close> \<open>kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f'\<close> \<open>(p,ins,outs) \<in> set procs\<close>
    have cf2':"\<exists>cf\<^sub>2'. transfer (slice_kind S a) s\<^sub>2 = cf\<^sub>2'#cfsx' \<and> snd cf\<^sub>2' = snd cfx'"
      by(cases cfx',cases "sourcenode a \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>",
         auto dest:slice_kind_Return slice_kind_Return_in_slice)
    with \<open>\<forall>i<length ms\<^sub>2. snd (s\<^sub>1 ! (length msx + i)) = snd (s\<^sub>2 ! i)\<close> 
      \<open>length ms\<^sub>1' = length s\<^sub>1'\<close> \<open>msx = []\<close> \<open>length ms\<^sub>1 = length ms\<^sub>2\<close>
      \<open>length ms\<^sub>1 = length s\<^sub>1\<close> \<open>snd cfx = snd cfx'\<close>
    have "\<forall>i<length ms\<^sub>1'. snd (s\<^sub>1' ! i) = snd (transfer (slice_kind S a) s\<^sub>2 ! i)"
      apply auto apply(case_tac i) apply auto
      by(erule_tac x="Suc(Suc nat)" in allE) auto
    from \<open>\<forall>m \<in> set (tl ms\<^sub>1). \<exists>m'. call_of_return_node m m' \<and> m' \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close>
    have "\<forall>m \<in> set (tl (tl ms\<^sub>1)). 
      \<exists>m'. call_of_return_node m m' \<and> m' \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
      by(cases "tl ms\<^sub>1") auto
    from \<open>\<forall>m \<in> set (tl ms\<^sub>1). return_node m\<close>
    have "\<forall>m \<in> set (tl (tl ms\<^sub>1)). return_node m" by(cases "tl ms\<^sub>1") auto
    have "\<forall>V\<in>rv S (CFG_node (hd (tl ms\<^sub>1))).
      (fst cfx)(ParamDefs (targetnode a) [:=] map (fst cf\<^sub>1) outs) V = 
      state_val (transfer (slice_kind S a) s\<^sub>2) V"
    proof
      fix V assume "V\<in>rv S (CFG_node (hd (tl ms\<^sub>1)))"
      with \<open>hd(tl ms\<^sub>1) = targetnode a\<close> have "V\<in>rv S (CFG_node (targetnode a))"
        by simp
      show "(fst cfx)(ParamDefs (targetnode a) [:=] map (fst cf\<^sub>1) outs) V = 
        state_val (transfer (slice_kind S a) s\<^sub>2) V"
      proof(cases "V \<in> set (ParamDefs (targetnode a))")
        case True
        then obtain i where "V = (ParamDefs (targetnode a))!i" 
          and "i < length(ParamDefs (targetnode a))"
          by(auto simp:in_set_conv_nth)
        moreover
        from \<open>valid_edge a\<close> \<open>kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f'\<close> \<open>(p,ins,outs) \<in> set procs\<close>
        have length:"length(ParamDefs (targetnode a)) = length outs"
          by(fastforce intro:ParamDefs_return_target_length)
        from \<open>valid_edge a\<close> \<open>kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f'\<close> \<open>(p,ins,outs) \<in> set procs\<close>
          \<open>i < length(ParamDefs (targetnode a))\<close> 
          \<open>length(ParamDefs (targetnode a)) = length outs\<close>
        have "valid_SDG_node (Actual_out(targetnode a,i))" by fastforce
        with \<open>V = (ParamDefs (targetnode a))!i\<close>
        have "V \<in> Def\<^bsub>SDG\<^esub> (Actual_out(targetnode a,i))"
          by(fastforce intro:Actual_out_SDG_Def)
        from \<open>V \<in> rv S (CFG_node (targetnode a))\<close> obtain as' nx 
          where "targetnode a -as'\<rightarrow>\<^sub>\<iota>* parent_node nx" 
          and "nx \<in> HRB_slice S" and "V \<in> Use\<^bsub>SDG\<^esub> nx"
          and "\<forall>n''. valid_SDG_node n'' \<and> 
                         parent_node n'' \<in> set (sourcenodes as') \<longrightarrow> V \<notin> Def\<^bsub>SDG\<^esub> n''"
          by(fastforce elim:rvE)
        with \<open>valid_SDG_node (Actual_out(targetnode a,i))\<close>
          \<open>V \<in> Def\<^bsub>SDG\<^esub> (Actual_out(targetnode a,i))\<close>
        have "targetnode a = parent_node nx" 
          apply(auto simp:intra_path_def sourcenodes_def)
          apply(erule path.cases) apply fastforce
          apply(erule_tac x="(Actual_out(targetnode a,i))" in allE) by fastforce
        with \<open>V \<in> Use\<^bsub>SDG\<^esub> nx\<close> have "V \<in> Use (targetnode a)"
          by(fastforce intro:SDG_Use_parent_Use)
        with \<open>valid_edge a\<close> have "V \<in> Use\<^bsub>SDG\<^esub> (CFG_node (targetnode a))"
          by(auto intro!:CFG_Use_SDG_Use)
        from \<open>targetnode a = parent_node nx\<close>[THEN sym] \<open>valid_edge a\<close>
        have "parent_node (Actual_out(targetnode a,i)) -[]\<rightarrow>\<^sub>\<iota>* parent_node nx"
          by(fastforce intro:empty_path simp:intra_path_def)
        with \<open>V \<in> Def\<^bsub>SDG\<^esub> (Actual_out(targetnode a,i))\<close> 
          \<open>V \<in> Use\<^bsub>SDG\<^esub> (CFG_node (targetnode a))\<close> \<open>targetnode a = parent_node nx\<close>
        have "Actual_out(targetnode a,i) influences V in (CFG_node (targetnode a))"
          by(fastforce simp:data_dependence_def sourcenodes_def)
        hence ddep:"Actual_out(targetnode a,i) s-V\<rightarrow>\<^sub>d\<^sub>d (CFG_node (targetnode a))"
          by(rule sum_SDG_ddep_edge)
        from \<open>targetnode a = parent_node nx\<close> \<open>nx \<in> HRB_slice S\<close>
        have "CFG_node (targetnode a) \<in> HRB_slice S"
          by(fastforce dest:valid_SDG_node_in_slice_parent_node_in_slice)
        hence "Actual_out(targetnode a,i) \<in> HRB_slice S"
        proof(induct "CFG_node (targetnode a)" rule:HRB_slice_cases)
          case (phase1 nx')
          with ddep show ?case
            by(fastforce intro: ddep_slice1 combine_SDG_slices.combSlice_refl
                         simp:HRB_slice_def)
        next
          case (phase2 nx' n' n'' p)
          from \<open>CFG_node (targetnode a) \<in> sum_SDG_slice2 n'\<close> ddep
          have "Actual_out(targetnode a,i) \<in> sum_SDG_slice2 n'"
            by(fastforce intro:ddep_slice2)
          with \<open>n'' s-p\<rightarrow>\<^bsub>ret\<^esub> CFG_node (parent_node n')\<close> \<open>n' \<in> sum_SDG_slice1 nx'\<close>
            \<open>nx' \<in> S\<close>
          show ?case by(fastforce intro:combine_SDG_slices.combSlice_Return_parent_node
                                  simp:HRB_slice_def)
        qed
        from \<open>valid_edge a\<close> \<open>kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f'\<close> \<open>valid_edge a''\<close>
          \<open>kind a'' = Q':r'\<hookrightarrow>\<^bsub>p\<^esub>fs'\<close> \<open>a \<in> get_return_edges a''\<close>
          \<open>CFG_node (targetnode a) \<in> HRB_slice S\<close>
        have "CFG_node (sourcenode a) \<in> HRB_slice S"
          by(rule call_return_nodes_in_slice)
        hence "sourcenode a \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>" by(simp add:SDG_to_CFG_set_def)
        from \<open>sourcenode a \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close> \<open>valid_edge a\<close> \<open>kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f'\<close>
          \<open>(p,ins,outs) \<in> set procs\<close>
        have slice_kind:"slice_kind S a = 
          Q\<hookleftarrow>\<^bsub>p\<^esub>(\<lambda>cf cf'. rspp (targetnode a) (HRB_slice S) outs cf' cf)"
          by(rule slice_kind_Return_in_slice)
        from \<open>Actual_out(targetnode a,i) \<in> HRB_slice S\<close>
          \<open>i < length(ParamDefs (targetnode a))\<close> \<open>valid_edge a\<close>
          \<open>V = (ParamDefs (targetnode a))!i\<close> length
        have 2:"rspp (targetnode a) (HRB_slice S) outs (fst cfx') (fst cf\<^sub>2) V = 
          (fst cf\<^sub>2)(outs!i)"
          by(fastforce intro:rspp_Actual_out_in_slice)
        from \<open>i < length(ParamDefs (targetnode a))\<close> length \<open>valid_edge a\<close>
        have "(fst cfx)(ParamDefs (targetnode a) [:=] map (fst cf\<^sub>1) outs) 
          ((ParamDefs (targetnode a))!i) = (map (fst cf\<^sub>1) outs)!i"
          by(fastforce intro:fun_upds_nth distinct_ParamDefs)
        with \<open>V = (ParamDefs (targetnode a))!i\<close> 
          \<open>i < length(ParamDefs (targetnode a))\<close> length
        have 1:"(fst cfx)(ParamDefs (targetnode a) [:=] map (fst cf\<^sub>1) outs) V = 
          (fst cf\<^sub>1)(outs!i)" 
          by simp
        from \<open>valid_edge a\<close> \<open>kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f'\<close> \<open>(p,ins,outs) \<in> set procs\<close> 
          \<open>i < length(ParamDefs (targetnode a))\<close> length
        have po:"Formal_out(sourcenode a,i) s-p:outs!i\<rightarrow>\<^bsub>out\<^esub> Actual_out(targetnode a,i)"
          by(fastforce intro:sum_SDG_param_out_edge)
        from \<open>valid_edge a\<close> \<open>kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f'\<close>
        have "CFG_node (sourcenode a) s-p\<rightarrow>\<^bsub>ret\<^esub> CFG_node (targetnode a)"
          by(fastforce intro:sum_SDG_return_edge)
        from \<open>Actual_out(targetnode a,i) \<in> HRB_slice S\<close>
        have "Formal_out(sourcenode a,i) \<in> HRB_slice S"
        proof(induct "Actual_out(targetnode a,i)" rule:HRB_slice_cases)
          case (phase1 nx')
          let ?AO = "Actual_out(targetnode a,i)"
          from \<open>valid_SDG_node ?AO\<close> have "?AO \<in> sum_SDG_slice2 ?AO"
            by(rule refl_slice2)
          with po have "Formal_out(sourcenode a,i) \<in> sum_SDG_slice2 ?AO"
            by(rule param_out_slice2)
          with \<open>CFG_node (sourcenode a) s-p\<rightarrow>\<^bsub>ret\<^esub> CFG_node (targetnode a)\<close>
            \<open>Actual_out (targetnode a, i) \<in> sum_SDG_slice1 nx'\<close> \<open>nx' \<in> S\<close>
          show ?case
            by(fastforce intro:combSlice_Return_parent_node simp:HRB_slice_def)
        next
          case (phase2 nx' n' n'' p)
          from \<open>Actual_out (targetnode a, i) \<in> sum_SDG_slice2 n'\<close> po
          have "Formal_out(sourcenode a,i) \<in> sum_SDG_slice2 n'"
            by(fastforce intro:param_out_slice2)
          with \<open>n' \<in> sum_SDG_slice1 nx'\<close> \<open>n'' s-p\<rightarrow>\<^bsub>ret\<^esub> CFG_node (parent_node n')\<close> 
            \<open>nx' \<in> S\<close>
          show ?case by(fastforce intro:combine_SDG_slices.combSlice_Return_parent_node
                                  simp:HRB_slice_def)
        qed
        with \<open>valid_edge a\<close> \<open>kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f'\<close> \<open>(p,ins,outs) \<in> set procs\<close> 
          \<open>i < length(ParamDefs (targetnode a))\<close> length
        have "outs!i \<in> Use\<^bsub>SDG\<^esub> Formal_out(sourcenode a,i)"
          by(fastforce intro!:Formal_out_SDG_Use get_proc_return)
        with \<open>valid_edge a\<close> have "outs!i \<in> Use\<^bsub>SDG\<^esub> (CFG_node (sourcenode a))"
          by(auto intro!:CFG_Use_SDG_Use dest:SDG_Use_parent_Use)
        moreover
        from \<open>valid_edge a\<close> have "parent_node (CFG_node (sourcenode a)) -[]\<rightarrow>\<^sub>\<iota>* 
          parent_node (CFG_node (sourcenode a))"
          by(fastforce intro:empty_path simp:intra_path_def)
        ultimately have "outs!i \<in> rv S (CFG_node (sourcenode a))"
          using \<open>sourcenode a \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close> \<open>valid_edge a\<close>
          by(fastforce intro:rvI simp:SDG_to_CFG_set_def sourcenodes_def)
        with \<open>\<forall>i < length ms\<^sub>2. \<forall>V \<in> rv S (CFG_node ((mx#tl ms\<^sub>2)!i)). 
          (fst (s\<^sub>1!(length msx + i))) V = (fst (s\<^sub>2!i)) V\<close>
        have "(fst cf\<^sub>1)(outs!i) = (fst cf\<^sub>2)(outs!i)"
          by auto(erule_tac x="0" in allE,auto)
        with 1 2 slice_kind show ?thesis by simp
      next
        case False
        with \<open>transfer (kind a) s\<^sub>1 = s\<^sub>1'\<close>
        have "(fst cfx)(ParamDefs (targetnode a) [:=] map (fst cf\<^sub>1) outs) =
          (fst (hd cfs\<^sub>1))(ParamDefs (targetnode a) [:=] map (fst cf\<^sub>1) outs)"
          by(cases cfs\<^sub>1,auto intro:CFG_return_edge_fun)
        show ?thesis
        proof(cases "sourcenode a \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>")
          case True
          from \<open>sourcenode a \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close> \<open>valid_edge a\<close> \<open>kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f'\<close>
            \<open>(p,ins,outs) \<in> set procs\<close>
          have "slice_kind S a = 
            Q\<hookleftarrow>\<^bsub>p\<^esub>(\<lambda>cf cf'. rspp (targetnode a) (HRB_slice S) outs cf' cf)"
            by(rule slice_kind_Return_in_slice)
          with \<open>length s\<^sub>1' = length (transfer (slice_kind S a) s\<^sub>2)\<close> 
            \<open>length s\<^sub>1 = length s\<^sub>2\<close>
          have "state_val (transfer (slice_kind S a) s\<^sub>2) V = 
            rspp (targetnode a) (HRB_slice S) outs (fst cfx') (fst cf\<^sub>2) V"
            by simp
          with \<open>V \<notin> set (ParamDefs (targetnode a))\<close>
          have "state_val (transfer (slice_kind S a) s\<^sub>2) V = state_val cfs\<^sub>2 V"
            by(fastforce simp:rspp_def map_merge_def)
          with \<open>\<forall>i < length ms\<^sub>2. \<forall>V \<in> rv S (CFG_node ((mx#tl ms\<^sub>2)!i)). 
            (fst (s\<^sub>1!(length msx + i))) V = (fst (s\<^sub>2!i)) V\<close>
            \<open>hd(tl ms\<^sub>1) = targetnode a\<close>
            \<open>length ms\<^sub>1 = length s\<^sub>1\<close> \<open>length s\<^sub>1 = length s\<^sub>2\<close>[THEN sym] False
            \<open>tl ms\<^sub>2 = tl ms\<^sub>1\<close> \<open>length ms\<^sub>2 = length s\<^sub>2\<close>
            \<open>V\<in>rv S (CFG_node (targetnode a))\<close>
          show ?thesis by(fastforce simp:length_Suc_conv fun_upds_notin)
        next
          case False
          from \<open>sourcenode a \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close> \<open>kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f'\<close>
          have "slice_kind S a = (\<lambda>cf. True)\<hookleftarrow>\<^bsub>p\<^esub>(\<lambda>cf cf'. cf')"
            by(rule slice_kind_Return)
          from \<open>length ms\<^sub>2 = length s\<^sub>2\<close> have "1 < length ms\<^sub>2" by simp
          with \<open>\<forall>i < length ms\<^sub>2. \<forall>V \<in> rv S (CFG_node ((mx#tl ms\<^sub>2)!i)). 
            (fst (s\<^sub>1!(length msx + i))) V = (fst (s\<^sub>2!i)) V\<close>
            \<open>V\<in>rv S (CFG_node (hd (tl ms\<^sub>1)))\<close>
            \<open>ms\<^sub>1' = tl ms\<^sub>1\<close> \<open>ms\<^sub>1' = []@hd ms\<^sub>1'#tl ms\<^sub>1'\<close>
          have "fst cfx V = fst cfx' V" apply auto
            apply(erule_tac x="1" in allE)
            by(cases "tl ms\<^sub>1") auto
          with \<open>\<forall>i < length ms\<^sub>2. \<forall>V \<in> rv S (CFG_node ((mx#tl ms\<^sub>2)!i)). 
            (fst (s\<^sub>1!(length msx + i))) V = (fst (s\<^sub>2!i)) V\<close> 
            \<open>hd(tl ms\<^sub>1) = targetnode a\<close>
            \<open>length ms\<^sub>1 = length s\<^sub>1\<close> \<open>length s\<^sub>1 = length s\<^sub>2\<close>[THEN sym] False
            \<open>tl ms\<^sub>2 = tl ms\<^sub>1\<close> \<open>length ms\<^sub>2 = length s\<^sub>2\<close>
            \<open>V\<in>rv S (CFG_node (targetnode a))\<close>
            \<open>V \<notin> set (ParamDefs (targetnode a))\<close>
            \<open>slice_kind S a = (\<lambda>cf. True)\<hookleftarrow>\<^bsub>p\<^esub>(\<lambda>cf cf'. cf')\<close>
          show ?thesis by(auto simp:fun_upds_notin)
        qed
      qed
    qed
    with \<open>hd(tl ms\<^sub>1) = targetnode a\<close> \<open>tl ms\<^sub>2 = tl ms\<^sub>1\<close> \<open>ms\<^sub>1' = tl ms\<^sub>1\<close>
      \<open>\<forall>i < length ms\<^sub>2. \<forall>V \<in> rv S (CFG_node ((mx#tl ms\<^sub>2)!i)). 
        (fst (s\<^sub>1!(length msx + i))) V = (fst (s\<^sub>2!i)) V\<close> \<open>length ms\<^sub>1' = length s\<^sub>1'\<close>
      \<open>length ms\<^sub>1 = length s\<^sub>1\<close> \<open>length ms\<^sub>2 = length s\<^sub>2\<close> \<open>length s\<^sub>1 = length s\<^sub>2\<close> cf2'
    have "\<forall>i<length ms\<^sub>1'. \<forall>V\<in>rv S (CFG_node ((hd (tl ms\<^sub>1) # tl ms\<^sub>1')!i)).
      (fst (s\<^sub>1'!(length [] + i))) V = (fst (transfer (slice_kind S a) s\<^sub>2!i)) V"
      apply(case_tac "tl ms\<^sub>1") apply auto 
      apply(cases ms\<^sub>2) apply auto
      apply(case_tac i) apply auto
      by(erule_tac x="Suc(Suc nat)" in allE,auto)
    with \<open>\<forall>m \<in> set ms\<^sub>2. valid_node m\<close> \<open>\<forall>m \<in> set ms\<^sub>1'. valid_node m\<close> 
      \<open>length ms\<^sub>2 = length s\<^sub>2\<close> \<open>length s\<^sub>1' = length (transfer (slice_kind S a) s\<^sub>2)\<close>
      \<open>length ms\<^sub>1' = length s\<^sub>1'\<close> \<open>ms\<^sub>1' = tl ms\<^sub>1\<close> \<open>ms\<^sub>1' = []@hd ms\<^sub>1'#tl ms\<^sub>1'\<close>
      \<open>tl ms\<^sub>1 = []@hd(tl ms\<^sub>1)#tl(tl ms\<^sub>1)\<close>
      \<open>get_proc mx = get_proc (hd ms\<^sub>2)\<close>
      \<open>\<forall>m \<in> set (tl (tl ms\<^sub>1)). \<exists>m'. call_of_return_node m m' \<and> m' \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close>
      \<open>\<forall>m \<in> set (tl (tl ms\<^sub>1)). return_node m\<close>
      \<open>\<forall>i<length ms\<^sub>1'. snd (s\<^sub>1' ! i) = snd (transfer (slice_kind S a) s\<^sub>2 ! i)\<close>
    have "((ms\<^sub>1',s\<^sub>1'),(ms\<^sub>1',transfer (slice_kind S a) s\<^sub>2)) \<in> WS S"
      by(auto intro!:WSI)
    with \<open>S,slice_kind S \<turnstile> (ms\<^sub>2,s\<^sub>2) =as@[a]\<Rightarrow> (ms\<^sub>1',transfer (slice_kind S a) s\<^sub>2)\<close>
    show ?case by blast
  qed
qed



subsection \<open>The weak simulation\<close>

definition is_weak_sim :: 
  "(('node list \<times> (('var \<rightharpoonup> 'val) \<times> 'ret) list) \<times> 
  ('node list \<times> (('var \<rightharpoonup> 'val) \<times> 'ret) list)) set \<Rightarrow> 'node SDG_node set \<Rightarrow> bool"
  where "is_weak_sim R S \<equiv> 
  \<forall>ms\<^sub>1 s\<^sub>1 ms\<^sub>2 s\<^sub>2 ms\<^sub>1' s\<^sub>1' as. 
    ((ms\<^sub>1,s\<^sub>1),(ms\<^sub>2,s\<^sub>2)) \<in> R \<and> S,kind \<turnstile> (ms\<^sub>1,s\<^sub>1) =as\<Rightarrow> (ms\<^sub>1',s\<^sub>1') \<and> s\<^sub>1' \<noteq> []
    \<longrightarrow> (\<exists>ms\<^sub>2' s\<^sub>2' as'. ((ms\<^sub>1',s\<^sub>1'),(ms\<^sub>2',s\<^sub>2')) \<in> R \<and> 
                        S,slice_kind S \<turnstile> (ms\<^sub>2,s\<^sub>2) =as'\<Rightarrow> (ms\<^sub>2',s\<^sub>2'))"


lemma WS_weak_sim:
  assumes "((ms\<^sub>1,s\<^sub>1),(ms\<^sub>2,s\<^sub>2)) \<in> WS S" 
  and "S,kind \<turnstile> (ms\<^sub>1,s\<^sub>1) =as\<Rightarrow> (ms\<^sub>1',s\<^sub>1')" and "s\<^sub>1' \<noteq> []"
  obtains as' where "((ms\<^sub>1',s\<^sub>1'),(ms\<^sub>1',transfer (slice_kind S (last as)) s\<^sub>2)) \<in> WS S"
  and "S,slice_kind S \<turnstile> (ms\<^sub>2,s\<^sub>2) =as'@[last as]\<Rightarrow> 
                          (ms\<^sub>1',transfer (slice_kind S (last as)) s\<^sub>2)"
proof(atomize_elim)
  from \<open>S,kind \<turnstile> (ms\<^sub>1,s\<^sub>1) =as\<Rightarrow> (ms\<^sub>1',s\<^sub>1')\<close> obtain ms' s' as' a'
    where "S,kind \<turnstile> (ms\<^sub>1,s\<^sub>1) =as'\<Rightarrow>\<^sub>\<tau> (ms',s')"
    and "S,kind \<turnstile> (ms',s') -a'\<rightarrow> (ms\<^sub>1',s\<^sub>1')" and "as = as'@[a']"
    by(fastforce elim:observable_moves.cases)
  from \<open>S,kind \<turnstile> (ms',s') -a'\<rightarrow> (ms\<^sub>1',s\<^sub>1')\<close>
  have "\<forall>m \<in> set (tl ms'). \<exists>m'. call_of_return_node m m' \<and> m' \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
    and "\<forall>n \<in> set (tl ms'). return_node n" and "ms' \<noteq> []"
    by(auto elim:observable_move.cases simp:call_of_return_node_def)
  from \<open>S,kind \<turnstile> (ms\<^sub>1,s\<^sub>1) =as'\<Rightarrow>\<^sub>\<tau> (ms',s')\<close> \<open>((ms\<^sub>1,s\<^sub>1),(ms\<^sub>2,s\<^sub>2)) \<in> WS S\<close>
  have "((ms',s'),(ms\<^sub>2,s\<^sub>2)) \<in> WS S" by(rule WS_silent_moves)
  with \<open>S,kind \<turnstile> (ms',s') -a'\<rightarrow> (ms\<^sub>1',s\<^sub>1')\<close> \<open>s\<^sub>1' \<noteq> []\<close>
  obtain as'' where "((ms\<^sub>1',s\<^sub>1'),(ms\<^sub>1',transfer (slice_kind S a') s\<^sub>2)) \<in> WS S"
    and "S,slice_kind S \<turnstile> (ms\<^sub>2,s\<^sub>2) =as''@[a']\<Rightarrow> 
    (ms\<^sub>1',transfer (slice_kind S a') s\<^sub>2)"
    by(fastforce elim:WS_observable_move)
  with \<open>((ms\<^sub>1',s\<^sub>1'),(ms\<^sub>1',transfer (slice_kind S a') s\<^sub>2)) \<in> WS S\<close> \<open>as = as'@[a']\<close>
  show "\<exists>as'. ((ms\<^sub>1',s\<^sub>1'),(ms\<^sub>1',transfer (slice_kind S (last as)) s\<^sub>2)) \<in> WS S \<and>
    S,slice_kind S \<turnstile> (ms\<^sub>2,s\<^sub>2) =as'@[last as]\<Rightarrow> 
    (ms\<^sub>1',transfer (slice_kind S (last as)) s\<^sub>2)"
    by fastforce
qed



text \<open>The following lemma states the correctness of static intraprocedural slicing:\\
  the simulation \<open>WS S\<close> is a desired weak simulation\<close>

theorem WS_is_weak_sim:"is_weak_sim (WS S) S"
by(fastforce elim:WS_weak_sim simp:is_weak_sim_def)

end

end

