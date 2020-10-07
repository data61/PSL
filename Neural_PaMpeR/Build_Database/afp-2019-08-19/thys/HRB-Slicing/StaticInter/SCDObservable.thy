section \<open>Observable sets w.r.t.\ standard control dependence\<close>

theory SCDObservable imports Observable HRBSlice begin

context SDG begin

lemma matched_bracket_assms_variant:
  assumes "n\<^sub>1 -p\<rightarrow>\<^bsub>call\<^esub> n\<^sub>2 \<or> n\<^sub>1 -p:V'\<rightarrow>\<^bsub>in\<^esub> n\<^sub>2" and "matched n\<^sub>2 ns' n\<^sub>3" 
  and "n\<^sub>3 -p\<rightarrow>\<^bsub>ret\<^esub> n\<^sub>4 \<or> n\<^sub>3 -p:V\<rightarrow>\<^bsub>out\<^esub> n\<^sub>4"
  and "call_of_return_node (parent_node n\<^sub>4) (parent_node n\<^sub>1)"
  obtains a a' where "valid_edge a" and "a' \<in> get_return_edges a"
  and "sourcenode a = parent_node n\<^sub>1" and "targetnode a = parent_node n\<^sub>2"
  and "sourcenode a' = parent_node n\<^sub>3" and "targetnode a' = parent_node n\<^sub>4"
proof(atomize_elim)
  from \<open>n\<^sub>1 -p\<rightarrow>\<^bsub>call\<^esub> n\<^sub>2 \<or> n\<^sub>1 -p:V'\<rightarrow>\<^bsub>in\<^esub> n\<^sub>2\<close> obtain a Q r fs where "valid_edge a" 
    and "kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs" and "parent_node n\<^sub>1 = sourcenode a"
    and "parent_node n\<^sub>2 = targetnode a"
    by(fastforce elim:SDG_edge.cases)
  from \<open>n\<^sub>3 -p\<rightarrow>\<^bsub>ret\<^esub> n\<^sub>4 \<or> n\<^sub>3 -p:V\<rightarrow>\<^bsub>out\<^esub> n\<^sub>4\<close> obtain a' Q' f'
    where "valid_edge a'" and "kind a' = Q'\<hookleftarrow>\<^bsub>p\<^esub>f'"
    and "parent_node n\<^sub>3 = sourcenode a'" and "parent_node n\<^sub>4 = targetnode a'"
    by(fastforce elim:SDG_edge.cases)
  from \<open>valid_edge a'\<close> \<open>kind a' = Q'\<hookleftarrow>\<^bsub>p\<^esub>f'\<close>
  obtain ax where "valid_edge ax" and "\<exists>Q r fs. kind ax = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs"
    and "a' \<in> get_return_edges ax"
    by -(drule return_needs_call,fastforce+)
  from \<open>valid_edge a\<close> \<open>valid_edge ax\<close> \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close> \<open>\<exists>Q r fs. kind ax = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close>
  have "targetnode a = targetnode ax" by(fastforce dest:same_proc_call_unique_target)
  from \<open>valid_edge a'\<close> \<open>a' \<in> get_return_edges ax\<close> \<open>valid_edge ax\<close>
  have "call_of_return_node (targetnode a') (sourcenode ax)"
    by(fastforce simp:return_node_def call_of_return_node_def)
  with \<open>call_of_return_node (parent_node n\<^sub>4) (parent_node n\<^sub>1)\<close> 
    \<open>parent_node n\<^sub>4 = targetnode a'\<close>
  have "sourcenode ax = parent_node n\<^sub>1" by fastforce
  with \<open>valid_edge ax\<close> \<open>a' \<in> get_return_edges ax\<close> \<open>targetnode a = targetnode ax\<close>
    \<open>parent_node n\<^sub>2 = targetnode a\<close> \<open>parent_node n\<^sub>3 = sourcenode a'\<close> 
    \<open>parent_node n\<^sub>4 = targetnode a'\<close>
  show "\<exists>a a'. valid_edge a \<and> a' \<in> get_return_edges a \<and>
    sourcenode a = parent_node n\<^sub>1 \<and> targetnode a = parent_node n\<^sub>2 \<and>
    sourcenode a' = parent_node n\<^sub>3 \<and> targetnode a' = parent_node n\<^sub>4"
    by fastforce
qed

subsection \<open>Observable set of standard control dependence is at most a singleton\<close>

definition SDG_to_CFG_set :: "'node SDG_node set \<Rightarrow> 'node set" ("\<lfloor>_\<rfloor>\<^bsub>CFG\<^esub>")
  where "\<lfloor>S\<rfloor>\<^bsub>CFG\<^esub> \<equiv> {m. CFG_node m \<in> S}"


lemma [intro]:"\<forall>n \<in> S. valid_SDG_node n \<Longrightarrow> \<forall>n \<in> \<lfloor>S\<rfloor>\<^bsub>CFG\<^esub>. valid_node n"
  by(fastforce simp:SDG_to_CFG_set_def)


lemma Exit_HRB_Slice:
  assumes "n \<in> \<lfloor>HRB_slice {CFG_node (_Exit_)}\<rfloor>\<^bsub>CFG\<^esub>" shows "n = (_Exit_)"
proof -
  from \<open>n \<in> \<lfloor>HRB_slice {CFG_node (_Exit_)}\<rfloor>\<^bsub>CFG\<^esub>\<close> 
  have "CFG_node n \<in> HRB_slice {CFG_node (_Exit_)}"
    by(simp add:SDG_to_CFG_set_def)
  thus ?thesis
  proof(induct "CFG_node n" rule:HRB_slice_cases)
    case (phase1 nx)
    from \<open>nx \<in> {CFG_node (_Exit_)}\<close> have "nx = CFG_node (_Exit_)" by simp
    with \<open>CFG_node n \<in> sum_SDG_slice1 nx\<close>
    have "CFG_node n = CFG_node (_Exit_) \<or> 
      (\<exists>n Vopt popt b. sum_SDG_edge n Vopt popt b (CFG_node (_Exit_)))"
      by(induct rule:sum_SDG_slice1.induct) auto
    then show ?thesis by(fastforce dest:Exit_no_sum_SDG_edge_target)
  next
    case (phase2 nx n' n'' p)
    from \<open>nx \<in> {CFG_node (_Exit_)}\<close> have "nx = CFG_node (_Exit_)" by simp
    with \<open>n' \<in> sum_SDG_slice1 nx\<close>
    have "n' = CFG_node (_Exit_) \<or> 
      (\<exists>n Vopt popt b. sum_SDG_edge n Vopt popt b (CFG_node (_Exit_)))"
      by(induct rule:sum_SDG_slice1.induct) auto
    hence "n' = CFG_node (_Exit_)" by(fastforce dest:Exit_no_sum_SDG_edge_target)
    with \<open>CFG_node n \<in> sum_SDG_slice2 n'\<close>
    have "CFG_node n = CFG_node (_Exit_) \<or> 
      (\<exists>n Vopt popt b. sum_SDG_edge n Vopt popt b (CFG_node (_Exit_)))"
      by(induct rule:sum_SDG_slice2.induct) auto
    then show ?thesis by(fastforce dest:Exit_no_sum_SDG_edge_target)
  qed
qed


lemma Exit_in_obs_intra_slice_node:
  assumes "(_Exit_) \<in> obs_intra n' \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
  shows "CFG_node (_Exit_) \<in> S"
proof -
  let ?S' = "\<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
  from \<open>(_Exit_) \<in> obs_intra n' ?S'\<close> obtain as where "n' -as\<rightarrow>\<^sub>\<iota>* (_Exit_)"
    and "\<forall>nx \<in> set(sourcenodes as). nx \<notin> ?S'" and "(_Exit_) \<in> ?S'"
    by(erule obs_intraE)
  from \<open>(_Exit_) \<in> ?S'\<close> 
  have "CFG_node (_Exit_) \<in> HRB_slice S" by(simp add:SDG_to_CFG_set_def)
  thus ?thesis
  proof(induct "CFG_node (_Exit_)" rule:HRB_slice_cases)
    case (phase1 nx)
    thus ?case
      by(induct "CFG_node (_Exit_)" rule:sum_SDG_slice1.induct,
        auto dest:Exit_no_sum_SDG_edge_source)
  next
    case (phase2 nx n' n'' p)
    from \<open>CFG_node (_Exit_) \<in> sum_SDG_slice2 n'\<close> \<open>n' \<in> sum_SDG_slice1 nx\<close> \<open>nx \<in> S\<close>
    show ?case
      apply(induct n\<equiv>"CFG_node (_Exit_)" rule:sum_SDG_slice2.induct)
      apply(auto dest:Exit_no_sum_SDG_edge_source)
      apply(hypsubst_thin)
      apply(induct n\<equiv>"CFG_node (_Exit_)" rule:sum_SDG_slice1.induct)
      apply(auto dest:Exit_no_sum_SDG_edge_source)
      done
  qed
qed


lemma obs_intra_postdominate:
  assumes "n \<in> obs_intra n' \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>" and "\<not> method_exit n"
  shows "n postdominates n'"
proof(rule ccontr)
  assume "\<not> n postdominates n'"
  from \<open>n \<in> obs_intra n' \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close> have "valid_node n" 
    by(fastforce dest:in_obs_intra_valid)
  with \<open>n \<in> obs_intra n' \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close> \<open>\<not> method_exit n\<close> have "n postdominates n"
    by(fastforce intro:postdominate_refl)
  from \<open>n \<in> obs_intra n' \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close> obtain as where "n' -as\<rightarrow>\<^sub>\<iota>* n"
    and all_notinS:"\<forall>n' \<in> set(sourcenodes as). n' \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
    and "n \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>" by(erule obs_intraE)
  from \<open>n postdominates n\<close> \<open>\<not> n postdominates n'\<close> \<open>n' -as\<rightarrow>\<^sub>\<iota>* n\<close>
  obtain as' a as'' where [simp]:"as = as'@a#as''"
    and "valid_edge a" and "\<not> n postdominates (sourcenode a)"
    and "n postdominates (targetnode a)"  and "intra_kind (kind a)"
    by(fastforce elim!:postdominate_path_branch simp:intra_path_def)
  from \<open>n' -as\<rightarrow>\<^sub>\<iota>* n\<close> have "sourcenode a -a#as''\<rightarrow>\<^sub>\<iota>* n"
    by(fastforce elim:path_split intro:Cons_path simp:intra_path_def)
  with \<open>\<not> n postdominates (sourcenode a)\<close> \<open>valid_edge a\<close> \<open>valid_node n\<close> 
  obtain asx pex where "sourcenode a -asx\<rightarrow>\<^sub>\<iota>* pex" and "method_exit pex" 
    and "n \<notin> set(sourcenodes asx)" by(fastforce simp:postdominate_def)
  have "asx \<noteq> []"
  proof
    assume "asx = []"
    with \<open>sourcenode a -asx\<rightarrow>\<^sub>\<iota>* pex\<close> have "sourcenode a = pex" 
      by(fastforce simp:intra_path_def)
    from \<open>method_exit pex\<close> show False
    proof(rule method_exit_cases)
      assume "pex = (_Exit_)"
      with \<open>sourcenode a = pex\<close> have "sourcenode a = (_Exit_)" by simp
      with \<open>valid_edge a\<close> show False by(rule Exit_source)
    next
      fix a' Q f p
      assume "pex = sourcenode a'" and "valid_edge a'" and "kind a' = Q\<hookleftarrow>\<^bsub>p\<^esub>f"
      from \<open>valid_edge a'\<close> \<open>kind a' = Q\<hookleftarrow>\<^bsub>p\<^esub>f\<close> \<open>valid_edge a\<close> \<open>intra_kind (kind a)\<close>
        \<open>sourcenode a = pex\<close> \<open>pex = sourcenode a'\<close>
      show False by(fastforce dest:return_edges_only simp:intra_kind_def)
    qed
  qed
  then obtain ax asx' where [simp]:"asx = ax#asx'" by(cases asx) auto
  with \<open>sourcenode a -asx\<rightarrow>\<^sub>\<iota>* pex\<close> have "sourcenode a -ax#asx'\<rightarrow>* pex"
    by(simp add:intra_path_def)
  hence "valid_edge ax" and [simp]:"sourcenode a = sourcenode ax"
    and "targetnode ax -asx'\<rightarrow>* pex" by(auto elim:path_split_Cons)
  with \<open>sourcenode a -asx\<rightarrow>\<^sub>\<iota>* pex\<close> have "targetnode ax -asx'\<rightarrow>\<^sub>\<iota>* pex"
    by(simp add:intra_path_def)
  with \<open>valid_edge ax\<close> \<open>n \<notin> set(sourcenodes asx)\<close> \<open>method_exit pex\<close>
  have "\<not> n postdominates targetnode ax"
    by(fastforce simp:postdominate_def sourcenodes_def)
  from \<open>n \<in> obs_intra n' \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close> all_notinS 
  have "n \<notin> set (sourcenodes (a#as''))"
    by(fastforce elim:obs_intra.cases simp:sourcenodes_def)
  from \<open>sourcenode a -asx\<rightarrow>\<^sub>\<iota>* pex\<close> have "intra_kind (kind ax)"
    by(simp add:intra_path_def)
  with \<open>sourcenode a -a#as''\<rightarrow>\<^sub>\<iota>* n\<close> \<open>n postdominates (targetnode a)\<close> 
    \<open>\<not> n postdominates targetnode ax\<close> \<open>valid_edge ax\<close> 
    \<open>n \<notin> set (sourcenodes (a#as''))\<close> \<open>intra_kind (kind a)\<close>
  have "(sourcenode a) controls n"
    by(fastforce simp:control_dependence_def)
  hence "CFG_node (sourcenode a) s\<longrightarrow>\<^bsub>cd\<^esub> CFG_node n"
    by(fastforce intro:sum_SDG_cdep_edge)
  with \<open>n \<in> obs_intra n' \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close> have "sourcenode a \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
    by(auto elim!:obs_intraE combine_SDG_slices.cases 
            intro:combine_SDG_slices.intros sum_SDG_slice1.intros 
                  sum_SDG_slice2.intros simp:HRB_slice_def SDG_to_CFG_set_def)
  with all_notinS show False by(simp add:sourcenodes_def)
qed



lemma obs_intra_singleton_disj: 
  assumes "valid_node n"
  shows "(\<exists>m. obs_intra n \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {m}) \<or> 
         obs_intra n \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {}"
proof(rule ccontr)
  assume "\<not> ((\<exists>m. obs_intra n \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {m}) \<or> 
             obs_intra n \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {})"
  hence "\<exists>nx nx'. nx \<in> obs_intra n \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> \<and> 
    nx' \<in> obs_intra n \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> \<and> nx \<noteq> nx'" by auto
  then obtain nx nx' where "nx \<in> obs_intra n \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>" 
    and "nx' \<in> obs_intra n \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>" and "nx \<noteq> nx'" by auto
  from \<open>nx \<in> obs_intra n \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close> obtain as where "n -as\<rightarrow>\<^sub>\<iota>* nx" 
    and all:"\<forall>n' \<in> set(sourcenodes as). n' \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>" 
    and "nx \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>" 
    by(erule obs_intraE)
  from \<open>n -as\<rightarrow>\<^sub>\<iota>* nx\<close> have "n -as\<rightarrow>* nx" and "\<forall>a \<in> set as. intra_kind (kind a)"
    by(simp_all add:intra_path_def)
  hence "valid_node nx" by(fastforce dest:path_valid_node)
  with \<open>nx \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close> have "obs_intra nx \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {nx}" 
    by -(rule n_in_obs_intra)
  with \<open>n -as\<rightarrow>* nx\<close> \<open>nx \<in> obs_intra n \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close> 
    \<open>nx' \<in> obs_intra n \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close> \<open>nx \<noteq> nx'\<close> have "as \<noteq> []" 
    by(fastforce elim:path.cases simp:intra_path_def)
  with \<open>n -as\<rightarrow>* nx\<close> \<open>nx \<in> obs_intra n \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close> 
    \<open>nx' \<in> obs_intra n \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close> \<open>nx \<noteq> nx'\<close> 
    \<open>obs_intra nx \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {nx}\<close> \<open>\<forall>a \<in> set as. intra_kind (kind a)\<close> all
  have "\<exists>a as' as''. n -as'\<rightarrow>\<^sub>\<iota>* sourcenode a \<and> targetnode a -as''\<rightarrow>\<^sub>\<iota>* nx \<and>
                     valid_edge a \<and> as = as'@a#as'' \<and> intra_kind (kind a) \<and>
                     obs_intra (targetnode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {nx} \<and> 
                    (\<not> (\<exists>m. obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {m} \<or> 
                       obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {}))"
  proof(induct arbitrary:nx' rule:path.induct)
    case (Cons_path n'' as n' a n)
    note IH = \<open>\<And>nx'. \<lbrakk>n' \<in> obs_intra n'' \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>; 
                       nx' \<in> obs_intra n'' \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>; n' \<noteq> nx'; 
                       obs_intra n' \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {n'};
                       \<forall>a\<in>set as. intra_kind (kind a);
                       \<forall>n'\<in>set (sourcenodes as). n' \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>; as \<noteq> []\<rbrakk>
      \<Longrightarrow> \<exists>a as' as''. n'' -as'\<rightarrow>\<^sub>\<iota>* sourcenode a \<and> targetnode a -as''\<rightarrow>\<^sub>\<iota>* n' \<and>
        valid_edge a \<and> as = as'@a#as'' \<and> intra_kind (kind a) \<and>
        obs_intra (targetnode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {n'} \<and>
        (\<not> (\<exists>m. obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {m} \<or> 
           obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {}))\<close>
    note more_than_one = \<open>n' \<in> obs_intra n \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close>
      \<open>nx' \<in> obs_intra n \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close> \<open>n' \<noteq> nx'\<close>
    from \<open>\<forall>a\<in>set (a#as). intra_kind (kind a)\<close>
    have "\<forall>a\<in>set as. intra_kind (kind a)" and "intra_kind (kind a)" by simp_all
    from \<open>\<forall>n'\<in>set (sourcenodes (a#as)). n' \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close>
    have all:"\<forall>n'\<in>set (sourcenodes as). n' \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
      by(simp add:sourcenodes_def)
    show ?case
    proof(cases "as = []")
      case True
      with \<open>n'' -as\<rightarrow>* n'\<close> have [simp]:"n'' = n'" by(fastforce elim:path.cases)
      from more_than_one \<open>sourcenode a = n\<close>
      have "\<not> (\<exists>m. obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {m} \<or> 
               obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {})"
        by auto
      with \<open>targetnode a = n''\<close> \<open>obs_intra n' \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {n'}\<close>
        \<open>sourcenode a = n\<close> True \<open>valid_edge a\<close> \<open>intra_kind (kind a)\<close> 
      show ?thesis
        apply(rule_tac x="a" in exI)
        apply(rule_tac x="[]" in exI)
        apply(rule_tac x="[]" in exI)
        by(auto intro:empty_path simp:intra_path_def)
    next
      case False
      from \<open>n'' -as\<rightarrow>* n'\<close> \<open>\<forall>a\<in>set (a # as). intra_kind (kind a)\<close>
      have "n'' -as\<rightarrow>\<^sub>\<iota>* n'" by(simp add:intra_path_def)
      with all 
      have subset:"obs_intra n' \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> \<subseteq> obs_intra n'' \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
        by -(rule path_obs_intra_subset)
      thus ?thesis
      proof(cases "obs_intra n' \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = obs_intra n'' \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>")
        case True
        with \<open>n'' -as\<rightarrow>\<^sub>\<iota>* n'\<close> \<open>valid_edge a\<close> \<open>sourcenode a = n\<close> \<open>targetnode a = n''\<close>
          \<open>obs_intra n' \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {n'}\<close> \<open>intra_kind (kind a)\<close> more_than_one
        show ?thesis
          apply(rule_tac x="a" in exI)
          apply(rule_tac x="[]" in exI)
          apply(rule_tac x="as" in exI)
          by(fastforce intro:empty_path simp:intra_path_def)
      next
        case False
        with subset
        have "obs_intra n' \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> \<subset> obs_intra n'' \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>" by simp
        with \<open>obs_intra n' \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {n'}\<close> 
        obtain ni where "n' \<in> obs_intra n'' \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
          and "ni \<in> obs_intra n'' \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>" and "n' \<noteq> ni" by auto
        from IH[OF this \<open>obs_intra n' \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {n'}\<close> 
          \<open>\<forall>a\<in>set as. intra_kind (kind a)\<close> all \<open>as \<noteq> []\<close>] obtain a' as' as''
          where "n'' -as'\<rightarrow>\<^sub>\<iota>* sourcenode a'" 
          and hyps:"targetnode a' -as''\<rightarrow>\<^sub>\<iota>* n'" "valid_edge a'" "as = as'@a'#as''" 
            "intra_kind (kind a')" "obs_intra (targetnode a') \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {n'}"
            "\<not> (\<exists>m. obs_intra (sourcenode a') \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {m} \<or> 
                                obs_intra (sourcenode a') \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {})"
          by blast
        from \<open>n'' -as'\<rightarrow>\<^sub>\<iota>* sourcenode a'\<close> \<open>valid_edge a\<close> \<open>sourcenode a = n\<close> 
          \<open>targetnode a = n''\<close> \<open>intra_kind (kind a)\<close> \<open>intra_kind (kind a')\<close>
        have "n -a#as'\<rightarrow>\<^sub>\<iota>* sourcenode a'"
          by(fastforce intro:path.Cons_path simp:intra_path_def)
        with hyps show ?thesis
          apply(rule_tac x="a'" in exI)
          apply(rule_tac x="a#as'" in exI)
          apply(rule_tac x="as''" in exI)
          by fastforce
      qed
    qed
  qed simp
  then obtain a as' as'' where "valid_edge a" and "intra_kind (kind a)"
    and "obs_intra (targetnode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {nx}"
    and more_than_one:"\<not> (\<exists>m. obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {m} \<or> 
                         obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {})"
    by blast
  have "sourcenode a \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
  proof(rule ccontr)
    assume "\<not> sourcenode a \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
    hence "sourcenode a \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>" by simp
    with \<open>valid_edge a\<close>
    have "obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {sourcenode a}"
      by(fastforce intro!:n_in_obs_intra)
    with more_than_one show False by simp
  qed
  with \<open>valid_edge a\<close> \<open>intra_kind (kind a)\<close>
  have "obs_intra (targetnode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> \<subseteq> 
        obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
    by(rule edge_obs_intra_subset)
  with \<open>obs_intra (targetnode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {nx}\<close> 
  have "nx \<in> obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>" by simp
  with more_than_one obtain m 
    where "m \<in> obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>" and "nx \<noteq> m" by auto
  from \<open>m \<in> obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close> have "valid_node m" 
    by(fastforce dest:in_obs_intra_valid)
  from \<open>obs_intra (targetnode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {nx}\<close> have "valid_node nx"
    by(fastforce dest:in_obs_intra_valid)
  show False
  proof(cases "m postdominates (sourcenode a)")
    case True
    with \<open>nx \<in> obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close>
      \<open>m \<in> obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close>
    have "m postdominates nx"
      by(fastforce intro:postdominate_inner_path_targetnode elim:obs_intraE)
    with \<open>nx \<noteq> m\<close> have "\<not> nx postdominates m" by(fastforce dest:postdominate_antisym)
    with \<open>valid_node nx\<close> \<open>valid_node m\<close> obtain asx pex where "m -asx\<rightarrow>\<^sub>\<iota>* pex"
      and "method_exit pex" and "nx \<notin> set(sourcenodes asx)"
      by(fastforce simp:postdominate_def)
    have "\<not> nx postdominates (sourcenode a)"
    proof
      assume "nx postdominates sourcenode a"
      from \<open>nx \<in> obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close>
        \<open>m \<in> obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close>
      obtain asx' where "sourcenode a -asx'\<rightarrow>\<^sub>\<iota>* m" and "nx \<notin> set(sourcenodes asx')"
        by(fastforce elim:obs_intraE)
      with \<open>m -asx\<rightarrow>\<^sub>\<iota>* pex\<close> have "sourcenode a -asx'@asx\<rightarrow>\<^sub>\<iota>* pex"
        by(fastforce intro:path_Append simp:intra_path_def)
      with \<open>nx \<notin> set(sourcenodes asx)\<close> \<open>nx \<notin> set(sourcenodes asx')\<close> 
        \<open>nx postdominates sourcenode a\<close> \<open>method_exit pex\<close> show False
        by(fastforce simp:sourcenodes_def postdominate_def)
    qed
    show False
    proof(cases "method_exit nx")
      case True
      from \<open>m postdominates nx\<close> obtain xs where "nx -xs\<rightarrow>\<^sub>\<iota>* m"
        by -(erule postdominate_implies_inner_path)
      with True have "nx = m"
        by(fastforce dest!:method_exit_inner_path simp:intra_path_def)
      with \<open>nx \<noteq> m\<close> show False by simp
    next
      case False
      with \<open>nx \<in> obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close>
      have "nx postdominates sourcenode a" by(rule obs_intra_postdominate)
      with \<open>\<not> nx postdominates (sourcenode a)\<close> show False by simp
    qed
  next
    case False
    show False
    proof(cases "method_exit m")
      case True
      from \<open>m \<in> obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close>
        \<open>nx \<in> obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close>
      obtain xs where "sourcenode a -xs\<rightarrow>\<^sub>\<iota>* m" and "nx \<notin> set(sourcenodes xs)"
        by(fastforce elim:obs_intraE)
      obtain x' xs' where [simp]:"xs = x'#xs'"
      proof(cases xs)
        case Nil
        with \<open>sourcenode a -xs\<rightarrow>\<^sub>\<iota>* m\<close> have [simp]:"sourcenode a = m"
          by(fastforce simp:intra_path_def)
        with \<open>m \<in> obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close> 
        have "m \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>" by(metis obs_intraE)
        with \<open>valid_node m\<close> have "obs_intra m \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {m}"
          by(rule n_in_obs_intra)
        with \<open>nx \<in> obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close> \<open>nx \<noteq> m\<close> have False
          by fastforce
        thus ?thesis by simp
      qed blast
      from \<open>sourcenode a -xs\<rightarrow>\<^sub>\<iota>* m\<close> have "sourcenode a = sourcenode x'" 
        and "valid_edge x'" and "targetnode x' -xs'\<rightarrow>\<^sub>\<iota>* m"
        and "intra_kind (kind x')"
        by(auto elim:path_split_Cons simp:intra_path_def)
      from \<open>targetnode x' -xs'\<rightarrow>\<^sub>\<iota>* m\<close> \<open>nx \<notin> set(sourcenodes xs)\<close> \<open>valid_edge x'\<close> 
        \<open>valid_node m\<close> True
      have "\<not> nx postdominates (targetnode x')" 
        by(fastforce simp:postdominate_def sourcenodes_def)
      show False
      proof(cases "method_exit nx")
        case True
        from \<open>m \<in> obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close>
          \<open>nx \<in> obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close>
        have "get_proc m = get_proc nx"
          by(fastforce elim:obs_intraE dest:intra_path_get_procs)
        with \<open>method_exit m\<close> \<open>method_exit nx\<close> have "m = nx"
          by(rule method_exit_unique)
        with \<open>nx \<noteq> m\<close> show False by simp
      next 
        case False
        with \<open>obs_intra (targetnode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {nx}\<close>
        have "nx postdominates (targetnode a)"
          by(fastforce intro:obs_intra_postdominate)
        from \<open>obs_intra (targetnode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {nx}\<close>
        obtain ys where "targetnode a -ys\<rightarrow>\<^sub>\<iota>* nx" 
          and "\<forall>nx' \<in> set(sourcenodes ys). nx' \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
          and "nx \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>" by(fastforce elim:obs_intraE)
        hence "nx \<notin> set(sourcenodes ys)"by fastforce
        have "sourcenode a \<noteq> nx"
        proof
          assume "sourcenode a = nx"
          from \<open>nx \<in> obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close>
          have "nx \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>" by -(erule obs_intraE)
          with \<open>valid_node nx\<close>
          have "obs_intra nx \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {nx}" by -(erule n_in_obs_intra)
          with \<open>sourcenode a = nx\<close> \<open>m \<in> obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close> 
            \<open>nx \<noteq> m\<close> show False by fastforce
        qed
        with \<open>nx \<notin> set(sourcenodes ys)\<close> have "nx \<notin> set(sourcenodes (a#ys))"
          by(fastforce simp:sourcenodes_def)
        from \<open>valid_edge a\<close> \<open>targetnode a -ys\<rightarrow>\<^sub>\<iota>* nx\<close> \<open>intra_kind (kind a)\<close>
        have "sourcenode a -a#ys\<rightarrow>\<^sub>\<iota>* nx"
          by(fastforce intro:Cons_path simp:intra_path_def)
        from \<open>sourcenode a -a#ys\<rightarrow>\<^sub>\<iota>* nx\<close> \<open>nx \<notin> set(sourcenodes (a#ys))\<close>
          \<open>intra_kind (kind a)\<close> \<open>nx postdominates (targetnode a)\<close>
          \<open>valid_edge x'\<close> \<open>intra_kind (kind x')\<close> \<open>\<not> nx postdominates (targetnode x')\<close>
          \<open>sourcenode a = sourcenode x'\<close>
        have "(sourcenode a) controls nx"
          by(fastforce simp:control_dependence_def)
        hence "CFG_node (sourcenode a) \<longrightarrow>\<^bsub>cd\<^esub> CFG_node nx" 
          by(fastforce intro:SDG_cdep_edge)
        with \<open>nx \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close> have "sourcenode a \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
          by(fastforce elim!:combine_SDG_slices.cases
                       dest:SDG_edge_sum_SDG_edge cdep_slice1 cdep_slice2 
                      intro:combine_SDG_slices.intros
                       simp:HRB_slice_def SDG_to_CFG_set_def)
        with \<open>valid_edge a\<close> 
        have "obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {sourcenode a}"
          by(fastforce intro!:n_in_obs_intra)
        with \<open>m \<in> obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close>
          \<open>nx \<in> obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close> \<open>nx \<noteq> m\<close>
        show False by simp
      qed
    next
      case False
      with \<open>m \<in> obs_intra (sourcenode a) \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close>
      have "m postdominates (sourcenode a)" by(rule obs_intra_postdominate)
      with \<open>\<not> m postdominates (sourcenode a)\<close> show False by simp
    qed
  qed
qed



lemma obs_intra_finite:"valid_node n \<Longrightarrow> finite (obs_intra n \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>)"
by(fastforce dest:obs_intra_singleton_disj[of _ S])

lemma obs_intra_singleton:"valid_node n \<Longrightarrow> card (obs_intra n \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>) \<le> 1"
by(fastforce dest:obs_intra_singleton_disj[of _ S])


lemma obs_intra_singleton_element:
  "m \<in> obs_intra n \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> \<Longrightarrow> obs_intra n \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {m}"
apply -
apply(frule in_obs_intra_valid)
apply(drule obs_intra_singleton_disj) apply auto
done


lemma obs_intra_the_element: 
  "m \<in> obs_intra n \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> \<Longrightarrow> (THE m. m \<in> obs_intra n \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>) = m"
by(fastforce dest:obs_intra_singleton_element)


lemma obs_singleton_element:
  assumes "ms \<in> obs ns \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>" and "\<forall>n \<in> set (tl ns). return_node n"
  shows "obs ns \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {ms}"
proof -
  from \<open>ms \<in> obs ns \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close> \<open>\<forall>n \<in> set (tl ns). return_node n\<close>
  obtain nsx n nsx' n' where "ns = nsx@n#nsx'" and "ms = n'#nsx'"
    and split:"n' \<in> obs_intra n \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
    "\<forall>nx \<in> set nsx'. \<exists>nx'. call_of_return_node nx nx' \<and> nx' \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
    "\<forall>xs x xs'. nsx = xs@x#xs' \<and> obs_intra x \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> \<noteq> {}
    \<longrightarrow> (\<exists>x'' \<in> set (xs'@[n]). \<exists>nx. call_of_return_node x'' nx \<and> 
                                   nx \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>)"
    by(erule obsE)
  from \<open>n' \<in> obs_intra n \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close>
  have "obs_intra n \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {n'}"
    by(fastforce intro!:obs_intra_singleton_element)
  { fix xs assume "xs \<noteq> ms" and "xs \<in> obs ns \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
    from \<open>xs \<in> obs ns \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close> \<open>\<forall>n \<in> set (tl ns). return_node n\<close>
    obtain zs z zs' z' where "ns = zs@z#zs'" and "xs = z'#zs'"
      and "z' \<in> obs_intra z \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
      and "\<forall>z' \<in> set zs'. \<exists>nx'. call_of_return_node z' nx' \<and> nx' \<in> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"
      and "\<forall>xs x xs'. zs = xs@x#xs' \<and> obs_intra x \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> \<noteq> {}
      \<longrightarrow> (\<exists>x'' \<in> set (xs'@[z]). \<exists>nx. call_of_return_node x'' nx \<and> 
                                     nx \<notin> \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>)"
      by(erule obsE)
    with \<open>ns = nsx@n#nsx'\<close> split
    have "nsx = zs \<and> n = z \<and> nsx' = zs'"
      by -(rule obs_split_det[of _ _ _ _ _ _ "\<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>"],fastforce+)
    with \<open>obs_intra n \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {n'}\<close> \<open>z' \<in> obs_intra z \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close>
    have "z' = n'" by simp
    with \<open>xs \<noteq> ms\<close> \<open>ms = n'#nsx'\<close> \<open>xs = z'#zs'\<close> \<open>nsx = zs \<and> n = z \<and> nsx' = zs'\<close>
    have False by simp }
  with \<open>ms \<in> obs ns \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>\<close> show ?thesis by fastforce
qed


lemma obs_finite:"\<forall>n \<in> set (tl ns). return_node n 
  \<Longrightarrow> finite (obs ns \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>)"
by(cases "obs ns \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {}",auto dest:obs_singleton_element[of _ _ S])

lemma obs_singleton:"\<forall>n \<in> set (tl ns). return_node n 
  \<Longrightarrow> card (obs ns \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>) \<le> 1"
by(cases "obs ns \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {}",auto dest:obs_singleton_element[of _ _ S])

lemma obs_the_element: 
  "\<lbrakk>ms \<in> obs ns \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>; \<forall>n \<in> set (tl ns). return_node n\<rbrakk> 
  \<Longrightarrow> (THE ms. ms \<in> obs ns \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub>) = ms"
by(cases "obs ns \<lfloor>HRB_slice S\<rfloor>\<^bsub>CFG\<^esub> = {}",auto dest:obs_singleton_element[of _ _ S])
  

end

end
