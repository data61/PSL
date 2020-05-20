section \<open>CFG\<close>

theory CFG imports BasicDefs begin

subsection \<open>The abstract CFG\<close>

subsubsection \<open>Locale fixes and assumptions\<close>

locale CFG =
  fixes sourcenode :: "'edge \<Rightarrow> 'node"
  fixes targetnode :: "'edge \<Rightarrow> 'node"
  fixes kind :: "'edge \<Rightarrow> ('var,'val,'ret,'pname) edge_kind"
  fixes valid_edge :: "'edge \<Rightarrow> bool"
  fixes Entry::"'node" ("'('_Entry'_')")
  fixes get_proc::"'node \<Rightarrow> 'pname"
  fixes get_return_edges::"'edge \<Rightarrow> 'edge set"
  fixes procs::"('pname \<times> 'var list \<times> 'var list) list"
  fixes Main::"'pname"
  assumes Entry_target [dest]: "\<lbrakk>valid_edge a; targetnode a = (_Entry_)\<rbrakk> \<Longrightarrow> False"
  and get_proc_Entry:"get_proc (_Entry_) = Main"
  and Entry_no_call_source:
    "\<lbrakk>valid_edge a; kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs; sourcenode a = (_Entry_)\<rbrakk> \<Longrightarrow> False"
  and edge_det: 
    "\<lbrakk>valid_edge a; valid_edge a'; sourcenode a = sourcenode a'; 
      targetnode a = targetnode a'\<rbrakk> \<Longrightarrow> a = a'" 
  and Main_no_call_target:"\<lbrakk>valid_edge a; kind a = Q:r\<hookrightarrow>\<^bsub>Main\<^esub>f\<rbrakk> \<Longrightarrow> False" 
  and Main_no_return_source:"\<lbrakk>valid_edge a; kind a = Q'\<hookleftarrow>\<^bsub>Main\<^esub>f'\<rbrakk> \<Longrightarrow> False" 
  and callee_in_procs: 
    "\<lbrakk>valid_edge a; kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<rbrakk> \<Longrightarrow> \<exists>ins outs. (p,ins,outs) \<in> set procs" 
  and get_proc_intra:"\<lbrakk>valid_edge a; intra_kind(kind a)\<rbrakk>
    \<Longrightarrow> get_proc (sourcenode a) = get_proc (targetnode a)" 
  and get_proc_call:
    "\<lbrakk>valid_edge a; kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<rbrakk> \<Longrightarrow> get_proc (targetnode a) = p"
  and get_proc_return:
    "\<lbrakk>valid_edge a; kind a = Q'\<hookleftarrow>\<^bsub>p\<^esub>f'\<rbrakk> \<Longrightarrow> get_proc (sourcenode a) = p"
  and call_edges_only:"\<lbrakk>valid_edge a; kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<rbrakk> 
    \<Longrightarrow> \<forall>a'. valid_edge a' \<and> targetnode a' = targetnode a \<longrightarrow> 
            (\<exists>Qx rx fsx. kind a' = Qx:rx\<hookrightarrow>\<^bsub>p\<^esub>fsx)"
  and return_edges_only:"\<lbrakk>valid_edge a; kind a = Q'\<hookleftarrow>\<^bsub>p\<^esub>f'\<rbrakk> 
    \<Longrightarrow> \<forall>a'. valid_edge a' \<and> sourcenode a' = sourcenode a \<longrightarrow> 
            (\<exists>Qx fx. kind a' = Qx\<hookleftarrow>\<^bsub>p\<^esub>fx)" 
  and get_return_edge_call:
    "\<lbrakk>valid_edge a; kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<rbrakk> \<Longrightarrow> get_return_edges a \<noteq> {}" 
  and get_return_edges_valid:
    "\<lbrakk>valid_edge a; a' \<in> get_return_edges a\<rbrakk> \<Longrightarrow> valid_edge a'" 
  and only_call_get_return_edges:
    "\<lbrakk>valid_edge a; a' \<in> get_return_edges a\<rbrakk> \<Longrightarrow> \<exists>Q r p fs. kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs" 
  and call_return_edges:
    "\<lbrakk>valid_edge a; kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs; a' \<in> get_return_edges a\<rbrakk> 
    \<Longrightarrow> \<exists>Q' f'. kind a' = Q'\<hookleftarrow>\<^bsub>p\<^esub>f'" 
  and return_needs_call: "\<lbrakk>valid_edge a; kind a = Q'\<hookleftarrow>\<^bsub>p\<^esub>f'\<rbrakk>
    \<Longrightarrow> \<exists>!a'. valid_edge a' \<and> (\<exists>Q r fs. kind a' = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs) \<and> a \<in> get_return_edges a'"
  and intra_proc_additional_edge: 
    "\<lbrakk>valid_edge a; a' \<in> get_return_edges a\<rbrakk>
    \<Longrightarrow> \<exists>a''. valid_edge a'' \<and> sourcenode a'' = targetnode a \<and> 
              targetnode a'' = sourcenode a' \<and> kind a'' = (\<lambda>cf. False)\<^sub>\<surd>"
  and call_return_node_edge: 
  "\<lbrakk>valid_edge a; a' \<in> get_return_edges a\<rbrakk>
    \<Longrightarrow> \<exists>a''. valid_edge a'' \<and> sourcenode a'' = sourcenode a \<and> 
             targetnode a'' = targetnode a' \<and> kind a'' = (\<lambda>cf. False)\<^sub>\<surd>"
  and call_only_one_intra_edge:
    "\<lbrakk>valid_edge a; kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<rbrakk> 
    \<Longrightarrow> \<exists>!a'. valid_edge a' \<and> sourcenode a' = sourcenode a \<and> intra_kind(kind a')"
 and return_only_one_intra_edge:
    "\<lbrakk>valid_edge a; kind a = Q'\<hookleftarrow>\<^bsub>p\<^esub>f'\<rbrakk> 
    \<Longrightarrow> \<exists>!a'. valid_edge a' \<and> targetnode a' = targetnode a \<and> intra_kind(kind a')"
  and same_proc_call_unique_target:
    "\<lbrakk>valid_edge a; valid_edge a'; kind a = Q\<^sub>1:r\<^sub>1\<hookrightarrow>\<^bsub>p\<^esub>fs\<^sub>1;  kind a' = Q\<^sub>2:r\<^sub>2\<hookrightarrow>\<^bsub>p\<^esub>fs\<^sub>2\<rbrakk>
    \<Longrightarrow> targetnode a = targetnode a'"
  and unique_callers:"distinct_fst procs" 
  and distinct_formal_ins:"(p,ins,outs) \<in> set procs \<Longrightarrow> distinct ins"
  and distinct_formal_outs:"(p,ins,outs) \<in> set procs \<Longrightarrow> distinct outs"

begin


lemma get_proc_get_return_edge:
  assumes "valid_edge a" and "a' \<in> get_return_edges a"
  shows "get_proc (sourcenode a) = get_proc (targetnode a')"
proof -
  from assms obtain ax where "valid_edge ax" and "sourcenode a = sourcenode ax"
    and "targetnode a' = targetnode ax" and "intra_kind(kind ax)"
    by(auto dest:call_return_node_edge simp:intra_kind_def)
  thus ?thesis by(fastforce intro:get_proc_intra)
qed


lemma call_intra_edge_False:
  assumes "valid_edge a" and "kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs" and "valid_edge a'" 
  and "sourcenode a = sourcenode a'" and "intra_kind(kind a')"
  shows "kind a' = (\<lambda>cf. False)\<^sub>\<surd>"
proof -
  from \<open>valid_edge a\<close> \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close> obtain ax where "ax \<in> get_return_edges a"
    by(fastforce dest:get_return_edge_call)
  with \<open>valid_edge a\<close> obtain a'' where "valid_edge a''" 
    and "sourcenode a'' = sourcenode a" and "kind a'' = (\<lambda>cf. False)\<^sub>\<surd>"
    by(fastforce dest:call_return_node_edge)
  from \<open>kind a'' = (\<lambda>cf. False)\<^sub>\<surd>\<close> have "intra_kind(kind a'')" 
    by(simp add:intra_kind_def)
  with assms \<open>valid_edge a''\<close> \<open>sourcenode a'' = sourcenode a\<close> 
    \<open>kind a'' = (\<lambda>cf. False)\<^sub>\<surd>\<close>
  show ?thesis by(fastforce dest:call_only_one_intra_edge)
qed


lemma formal_in_THE: 
  "\<lbrakk>valid_edge a; kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs; (p,ins,outs) \<in> set procs\<rbrakk>
  \<Longrightarrow> (THE ins. \<exists>outs. (p,ins,outs) \<in> set procs) = ins"
by(fastforce dest:distinct_fst_isin_same_fst intro:unique_callers)

lemma formal_out_THE: 
  "\<lbrakk>valid_edge a; kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f; (p,ins,outs) \<in> set procs\<rbrakk>
  \<Longrightarrow> (THE outs. \<exists>ins. (p,ins,outs) \<in> set procs) = outs"
by(fastforce dest:distinct_fst_isin_same_fst intro:unique_callers)


subsubsection \<open>Transfer and predicate functions\<close>

fun params :: "(('var \<rightharpoonup> 'val) \<rightharpoonup> 'val) list \<Rightarrow> ('var \<rightharpoonup> 'val) \<Rightarrow> 'val option list"
where "params [] cf = []"
  | "params (f#fs) cf = (f cf)#params fs cf"


lemma params_nth: 
  "i < length fs \<Longrightarrow> (params fs cf)!i = (fs!i) cf"
by(induct fs arbitrary:i,auto,case_tac i,auto)


lemma [simp]:"length (params fs cf) = length fs"
  by(induct fs) auto


fun transfer :: "('var,'val,'ret,'pname) edge_kind \<Rightarrow> (('var \<rightharpoonup> 'val) \<times> 'ret) list \<Rightarrow> 
  (('var \<rightharpoonup> 'val) \<times> 'ret) list"
where "transfer (\<Up>f) (cf#cfs)    = (f (fst cf),snd cf)#cfs"
  | "transfer (Q)\<^sub>\<surd> (cf#cfs)      = (cf#cfs)"
  | "transfer (Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs) (cf#cfs) = 
       (let ins = THE ins. \<exists>outs. (p,ins,outs) \<in> set procs in
                            (Map.empty(ins [:=] params fs (fst cf)),r)#cf#cfs)"
  | "transfer (Q\<hookleftarrow>\<^bsub>p\<^esub>f )(cf#cfs)    = (case cfs of [] \<Rightarrow> []
                                 | cf'#cfs' \<Rightarrow> (f (fst cf) (fst cf'),snd cf')#cfs')"
  | "transfer et [] = []"

fun transfers :: "('var,'val,'ret,'pname) edge_kind list \<Rightarrow> (('var \<rightharpoonup> 'val) \<times> 'ret) list \<Rightarrow>
                  (('var \<rightharpoonup> 'val) \<times> 'ret) list"
where "transfers [] s   = s"
  | "transfers (et#ets) s = transfers ets (transfer et s)"


fun pred :: "('var,'val,'ret,'pname) edge_kind \<Rightarrow> (('var \<rightharpoonup> 'val) \<times> 'ret) list \<Rightarrow> bool"
where "pred (\<Up>f) (cf#cfs) = True"
  | "pred (Q)\<^sub>\<surd> (cf#cfs)   = Q (fst cf)"
  | "pred (Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs) (cf#cfs) = Q (fst cf,r)"
  | "pred (Q\<hookleftarrow>\<^bsub>p\<^esub>f) (cf#cfs) = (Q cf \<and> cfs \<noteq> [])"
  | "pred et [] = False"

fun preds :: "('var,'val,'ret,'pname) edge_kind list \<Rightarrow> (('var \<rightharpoonup> 'val) \<times> 'ret) list \<Rightarrow> bool"
where "preds [] s   = True"
  | "preds (et#ets) s = (pred et s \<and> preds ets (transfer et s))"


lemma transfers_split:
  "(transfers (ets@ets') s) = (transfers ets' (transfers ets s))"
by(induct ets arbitrary:s) auto

lemma preds_split:
  "(preds (ets@ets') s) = (preds ets s \<and> preds ets' (transfers ets s))"
by(induct ets arbitrary:s) auto


abbreviation state_val :: "(('var \<rightharpoonup> 'val) \<times> 'ret) list \<Rightarrow> 'var \<rightharpoonup> 'val"
  where "state_val s V \<equiv> (fst (hd s)) V"


subsubsection \<open>\<open>valid_node\<close>\<close>

definition valid_node :: "'node \<Rightarrow> bool"
  where "valid_node n \<equiv> 
  (\<exists>a. valid_edge a \<and> (n = sourcenode a \<or> n = targetnode a))"

lemma [simp]: "valid_edge a \<Longrightarrow> valid_node (sourcenode a)"
  by(fastforce simp:valid_node_def)

lemma [simp]: "valid_edge a \<Longrightarrow> valid_node (targetnode a)"
  by(fastforce simp:valid_node_def)



subsection \<open>CFG paths\<close>

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
proof(atomize_elim)
  from \<open>as \<noteq> []\<close> obtain a' as' where "as = a'#as'" by(cases as) auto
  with \<open>n -as\<rightarrow>* n'\<close> have "n -[]@a'#as'\<rightarrow>* n'" by simp
  hence "n -[]\<rightarrow>* sourcenode a'" and "valid_edge a'" and "targetnode a' -as'\<rightarrow>* n'"
    by(rule path_split)+
  from \<open>n -[]\<rightarrow>* sourcenode a'\<close> have "n = sourcenode a'" by fast
  with \<open>as = a'#as'\<close> \<open>valid_edge a'\<close> \<open>targetnode a' -as'\<rightarrow>* n'\<close>
  show "\<exists>a' as'. as = a'#as' \<and> n = sourcenode a' \<and> valid_edge a' \<and> 
                 targetnode a' -as'\<rightarrow>* n'"
    by fastforce
qed


lemma path_split_snoc:
  assumes "n -as\<rightarrow>* n'" and "as \<noteq> []"
  obtains a' as' where "as = as'@[a']" and "n -as'\<rightarrow>* sourcenode a'"
  and "valid_edge a'" and "n' = targetnode a'"
proof(atomize_elim)
  from \<open>as \<noteq> []\<close> obtain a' as' where "as = as'@[a']" by(cases as rule:rev_cases) auto
  with \<open>n -as\<rightarrow>* n'\<close> have "n -as'@a'#[]\<rightarrow>* n'" by simp
  hence "n -as'\<rightarrow>* sourcenode a'" and "valid_edge a'" and "targetnode a' -[]\<rightarrow>* n'"
    by(rule path_split)+
  from \<open>targetnode a' -[]\<rightarrow>* n'\<close> have "n' = targetnode a'" by fast
  with \<open>as = as'@[a']\<close> \<open>valid_edge a'\<close> \<open>n -as'\<rightarrow>* sourcenode a'\<close>
  show "\<exists>as' a'. as = as'@[a'] \<and> n -as'\<rightarrow>* sourcenode a' \<and> valid_edge a' \<and> 
                 n' = targetnode a'"
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
proof(atomize_elim)
  from \<open>(_Entry_) -as\<rightarrow>* n'\<close> \<open>n' \<noteq> (_Entry_)\<close> have "as \<noteq> []"
    by(cases as,auto elim:path.cases)
  with \<open>(_Entry_) -as\<rightarrow>* n'\<close> obtain a' as' where "as = a'#as'" 
    and "(_Entry_) = sourcenode a'" and "valid_edge a'" and "targetnode a' -as'\<rightarrow>* n'"
    by(erule path_split_Cons)
  thus "\<exists>a n. sourcenode a = (_Entry_) \<and> targetnode a = n \<and> n -tl as\<rightarrow>* n' \<and> 
              valid_edge a \<and> a = hd as"
  by fastforce
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
  kinds :: "'edge list \<Rightarrow> ('var,'val,'ret,'pname) edge_kind list"
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


subsubsection \<open>Intraprocedural paths\<close>

definition intra_path :: "'node \<Rightarrow> 'edge list \<Rightarrow> 'node \<Rightarrow> bool" 
  ("_ -_\<rightarrow>\<^sub>\<iota>* _" [51,0,0] 80)
where "n -as\<rightarrow>\<^sub>\<iota>* n' \<equiv> n -as\<rightarrow>* n' \<and> (\<forall>a \<in> set as. intra_kind(kind a))"

lemma intra_path_get_procs:
  assumes "n -as\<rightarrow>\<^sub>\<iota>* n'" shows "get_proc n = get_proc n'"
proof -
  from \<open>n -as\<rightarrow>\<^sub>\<iota>* n'\<close> have "n -as\<rightarrow>* n'" and "\<forall>a \<in> set as. intra_kind(kind a)"
    by(simp_all add:intra_path_def)
  thus ?thesis
  proof(induct as arbitrary:n)
    case Nil thus ?case by fastforce
  next
    case (Cons a' as')
    note IH = \<open>\<And>n. \<lbrakk>n -as'\<rightarrow>* n'; \<forall>a\<in>set as'. intra_kind (kind a)\<rbrakk>
      \<Longrightarrow> get_proc n = get_proc n'\<close>
    from \<open>\<forall>a\<in>set (a'#as'). intra_kind (kind a)\<close>
    have "intra_kind(kind a')" and "\<forall>a\<in>set as'. intra_kind (kind a)" by simp_all
    from \<open>n -a'#as'\<rightarrow>* n'\<close> have "sourcenode a' = n" and "valid_edge a'"
      and "targetnode a' -as'\<rightarrow>* n'" by(auto elim:path.cases)
    from IH[OF \<open>targetnode a' -as'\<rightarrow>* n'\<close> \<open>\<forall>a\<in>set as'. intra_kind (kind a)\<close>]
    have "get_proc (targetnode a') = get_proc n'" .
    from \<open>valid_edge a'\<close> \<open>intra_kind(kind a')\<close> 
    have "get_proc (sourcenode a') = get_proc (targetnode a')"
      by(rule get_proc_intra)
    with \<open>sourcenode a' = n\<close> \<open>get_proc (targetnode a') = get_proc n'\<close>
    show ?case by simp
  qed
qed


lemma intra_path_Append:
  "\<lbrakk>n -as\<rightarrow>\<^sub>\<iota>* n''; n'' -as'\<rightarrow>\<^sub>\<iota>* n'\<rbrakk> \<Longrightarrow> n -as@as'\<rightarrow>\<^sub>\<iota>* n'"
by(fastforce intro:path_Append simp:intra_path_def)


lemma get_proc_get_return_edges: 
  assumes "valid_edge a" and "a' \<in> get_return_edges a"
  shows "get_proc(targetnode a) = get_proc(sourcenode a')"
proof -
  from \<open>valid_edge a\<close> \<open>a' \<in> get_return_edges a\<close>
  obtain a'' where "valid_edge a''" and "sourcenode a'' = targetnode a"
    and "targetnode a'' = sourcenode a'" and "kind a'' = (\<lambda>cf. False)\<^sub>\<surd>"
    by(fastforce dest:intra_proc_additional_edge)
  from \<open>valid_edge a''\<close> \<open>kind a'' = (\<lambda>cf. False)\<^sub>\<surd>\<close>
  have "get_proc(sourcenode a'') = get_proc(targetnode a'')"
    by(fastforce intro:get_proc_intra simp:intra_kind_def)
  with \<open>sourcenode a'' = targetnode a\<close> \<open>targetnode a'' = sourcenode a'\<close>
  show ?thesis by simp
qed


subsubsection \<open>Valid paths\<close>

declare conj_cong[fundef_cong]

fun valid_path_aux :: "'edge list \<Rightarrow> 'edge list \<Rightarrow> bool"
  where "valid_path_aux cs [] \<longleftrightarrow> True"
  | "valid_path_aux cs (a#as) \<longleftrightarrow> 
       (case (kind a) of Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs \<Rightarrow> valid_path_aux (a#cs) as
                       | Q\<hookleftarrow>\<^bsub>p\<^esub>f \<Rightarrow> case cs of [] \<Rightarrow> valid_path_aux [] as
                                     | c'#cs' \<Rightarrow> a \<in> get_return_edges c' \<and>
                                                 valid_path_aux cs' as
                       |    _ \<Rightarrow> valid_path_aux cs as)"


lemma vpa_induct [consumes 1,case_names vpa_empty vpa_intra vpa_Call vpa_ReturnEmpty
  vpa_ReturnCons]:
  assumes major: "valid_path_aux xs ys"
  and rules: "\<And>cs. P cs []"
    "\<And>cs a as. \<lbrakk>intra_kind(kind a); valid_path_aux cs as; P cs as\<rbrakk> \<Longrightarrow> P cs (a#as)"
    "\<And>cs a as Q r p fs. \<lbrakk>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs; valid_path_aux (a#cs) as; P (a#cs) as\<rbrakk> 
      \<Longrightarrow> P cs (a#as)"
    "\<And>cs a as Q p f. \<lbrakk>kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f; cs = []; valid_path_aux [] as; P [] as\<rbrakk> 
      \<Longrightarrow> P cs (a#as)"
    "\<And>cs a as Q p f c' cs' . \<lbrakk>kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f; cs = c'#cs'; valid_path_aux cs' as;
                              a \<in> get_return_edges c'; P cs' as\<rbrakk>
     \<Longrightarrow> P cs (a#as)"
  shows "P xs ys"
using major
apply(induct ys arbitrary: xs)
by(auto intro:rules split:edge_kind.split_asm list.split_asm simp:intra_kind_def)


lemma valid_path_aux_intra_path:
  "\<forall>a \<in> set as. intra_kind(kind a) \<Longrightarrow> valid_path_aux cs as"
by(induct as,auto simp:intra_kind_def)


lemma valid_path_aux_callstack_prefix:
  "valid_path_aux (cs@cs') as \<Longrightarrow> valid_path_aux cs as"
proof(induct "cs@cs'" as arbitrary:cs cs' rule:vpa_induct)
  case vpa_empty thus ?case by simp
next
  case (vpa_intra a as)
  hence "valid_path_aux cs as" by simp
  with \<open>intra_kind (kind a)\<close> show ?case by(cases "kind a",auto simp:intra_kind_def)
next
  case (vpa_Call a as Q r p fs cs'' cs')
  note IH = \<open>\<And>xs ys. a#cs''@cs' = xs@ys \<Longrightarrow> valid_path_aux xs as\<close>
  have "a#cs''@cs' = (a#cs'')@cs'" by simp
  from IH[OF this] have "valid_path_aux (a#cs'') as" .
  with \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close> show ?case by simp
next
  case (vpa_ReturnEmpty a as Q p f cs'' cs')
  hence "valid_path_aux cs'' as" by simp
  with \<open>kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f\<close> \<open>cs''@cs' = []\<close> show ?case by simp
next
  case (vpa_ReturnCons a as Q p f c' cs' csx csx')
  note IH = \<open>\<And>xs ys. cs' = xs@ys \<Longrightarrow> valid_path_aux xs as\<close>
  from \<open>csx@csx' = c'#cs'\<close> 
  have "csx = [] \<and> csx' = c'#cs' \<or> (\<exists>zs. csx = c'#zs \<and> zs@csx' = cs')"
    by(simp add:append_eq_Cons_conv)
  thus ?case
  proof
    assume "csx = [] \<and> csx' = c'#cs'"
    hence "csx = []" and "csx' = c'#cs'" by simp_all
    from \<open>csx' = c'#cs'\<close> have "cs' = []@tl csx'" by simp
    from IH[OF this] have "valid_path_aux [] as" .
    with \<open>csx = []\<close> \<open>kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f\<close> show ?thesis by simp
  next
    assume "\<exists>zs. csx = c'#zs \<and> zs@csx' = cs'"
    then obtain zs where "csx = c'#zs" and "cs' = zs@csx'" by auto
    from IH[OF \<open>cs' = zs@csx'\<close>] have "valid_path_aux zs as" .
    with \<open>csx = c'#zs\<close> \<open>kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f\<close> \<open>a \<in> get_return_edges c'\<close> 
    show ?thesis by simp
  qed
qed


fun upd_cs :: "'edge list \<Rightarrow> 'edge list \<Rightarrow> 'edge list"
  where "upd_cs cs [] = cs"
  | "upd_cs cs (a#as) =
       (case (kind a) of Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs \<Rightarrow> upd_cs (a#cs) as
                       | Q\<hookleftarrow>\<^bsub>p\<^esub>f \<Rightarrow> case cs of [] \<Rightarrow> upd_cs cs as
                                      | c'#cs' \<Rightarrow> upd_cs cs' as
                       |    _ \<Rightarrow> upd_cs cs as)"


lemma upd_cs_empty [dest]:
  "upd_cs cs [] = [] \<Longrightarrow> cs = []"
by(cases cs) auto


lemma upd_cs_intra_path:
  "\<forall>a \<in> set as. intra_kind(kind a) \<Longrightarrow> upd_cs cs as = cs"
by(induct as,auto simp:intra_kind_def)


lemma upd_cs_Append:
  "\<lbrakk>upd_cs cs as = cs'; upd_cs cs' as' = cs''\<rbrakk> \<Longrightarrow> upd_cs cs (as@as') = cs''"
by(induct as arbitrary:cs,auto split:edge_kind.split list.split)


lemma upd_cs_empty_split:
  assumes "upd_cs cs as = []" and "cs \<noteq> []" and "as \<noteq> []"
  obtains xs ys where "as = xs@ys" and "xs \<noteq> []" and "upd_cs cs xs = []"
  and "\<forall>xs' ys'. xs = xs'@ys' \<and> ys' \<noteq> [] \<longrightarrow> upd_cs cs xs' \<noteq> []"
  and "upd_cs [] ys = []"
proof(atomize_elim)
  from \<open>upd_cs cs as = []\<close> \<open>cs \<noteq> []\<close> \<open>as \<noteq> []\<close>
  show "\<exists>xs ys. as = xs@ys \<and> xs \<noteq> [] \<and> upd_cs cs xs = [] \<and> 
             (\<forall>xs' ys'. xs = xs'@ys' \<and> ys' \<noteq> [] \<longrightarrow> upd_cs cs xs' \<noteq> []) \<and> 
             upd_cs [] ys = []"
  proof(induct as arbitrary:cs)
    case Nil thus ?case by simp
  next
    case (Cons a' as')
    note IH = \<open>\<And>cs. \<lbrakk>upd_cs cs as' = []; cs \<noteq> []; as' \<noteq> []\<rbrakk>
      \<Longrightarrow> \<exists>xs ys. as' = xs@ys \<and> xs \<noteq> [] \<and> upd_cs cs xs = [] \<and>
                 (\<forall>xs' ys'. xs = xs'@ys' \<and> ys' \<noteq> [] \<longrightarrow> upd_cs cs xs' \<noteq> []) \<and> 
                 upd_cs [] ys = []\<close>
    show ?case
    proof(cases "kind a'" rule:edge_kind_cases)
      case Intra
      with \<open>upd_cs cs (a'#as') = []\<close> have "upd_cs cs as' = []"
        by(fastforce simp:intra_kind_def)
      with \<open>cs \<noteq> []\<close> have "as' \<noteq> []" by fastforce
      from IH[OF \<open>upd_cs cs as' = []\<close> \<open>cs \<noteq> []\<close> this] obtain xs ys where "as' = xs@ys"
        and "xs \<noteq> []" and "upd_cs cs xs = []" and "upd_cs [] ys = []"
        and "\<forall>xs' ys'. xs = xs'@ys' \<and> ys' \<noteq> [] \<longrightarrow> upd_cs cs xs' \<noteq> []" by blast
      from \<open>upd_cs cs xs = []\<close> Intra have "upd_cs cs (a'#xs) = []"
        by(fastforce simp:intra_kind_def)
      from \<open>\<forall>xs' ys'. xs = xs'@ys' \<and> ys' \<noteq> [] \<longrightarrow> upd_cs cs xs' \<noteq> []\<close> \<open>xs \<noteq> []\<close> Intra
      have "\<forall>xs' ys'. a'#xs = xs'@ys' \<and> ys' \<noteq> [] \<longrightarrow> upd_cs cs xs' \<noteq> []"
        apply auto
        apply(case_tac xs') apply(auto simp:intra_kind_def)
        by(erule_tac x="[]" in allE,fastforce)+
      with \<open>as' = xs@ys\<close> \<open>upd_cs cs (a'#xs) = []\<close> \<open>upd_cs [] ys = []\<close>
      show ?thesis apply(rule_tac x="a'#xs" in exI) by fastforce
    next
      case (Call Q p f)
      with \<open>upd_cs cs (a'#as') = []\<close> have "upd_cs (a'#cs) as' = []" by simp
      with \<open>cs \<noteq> []\<close> have "as' \<noteq> []" by fastforce
      from IH[OF \<open>upd_cs (a'#cs) as' = []\<close> _ this] obtain xs ys where "as' = xs@ys"
        and "xs \<noteq> []" and "upd_cs (a'#cs) xs = []" and "upd_cs [] ys = []"
        and "\<forall>xs' ys'. xs = xs'@ys' \<and> ys' \<noteq> [] \<longrightarrow> upd_cs (a'#cs) xs' \<noteq> []" by blast
      from \<open>upd_cs (a'#cs) xs = []\<close> Call have "upd_cs cs (a'#xs) = []" by simp
      from \<open>\<forall>xs' ys'. xs = xs'@ys' \<and> ys' \<noteq> [] \<longrightarrow> upd_cs (a'#cs) xs' \<noteq> []\<close> 
        \<open>xs \<noteq> []\<close> \<open>cs \<noteq> []\<close> Call
      have "\<forall>xs' ys'. a'#xs = xs'@ys' \<and> ys' \<noteq> [] \<longrightarrow> upd_cs cs xs' \<noteq> []"
        by auto(case_tac xs',auto)
      with \<open>as' = xs@ys\<close> \<open>upd_cs cs (a'#xs) = []\<close> \<open>upd_cs [] ys = []\<close>
      show ?thesis apply(rule_tac x="a'#xs" in exI) by fastforce
    next
      case (Return Q p f)
      with \<open>upd_cs cs (a'#as') = []\<close> \<open>cs \<noteq> []\<close> obtain c' cs' where "cs = c'#cs'"
        and "upd_cs cs' as' = []" by(cases cs) auto
      show ?thesis
      proof(cases "cs' = []")
        case True
        with \<open>cs = c'#cs'\<close> \<open>upd_cs cs' as' = []\<close> Return show ?thesis
          apply(rule_tac x="[a']" in exI) apply clarsimp
          by(case_tac xs') auto
      next
        case False
        with \<open>upd_cs cs' as' = []\<close> have "as' \<noteq> []" by fastforce
        from IH[OF \<open>upd_cs cs' as' = []\<close> False this] obtain xs ys where "as' = xs@ys"
          and "xs \<noteq> []" and "upd_cs cs' xs = []" and "upd_cs [] ys = []"
          and "\<forall>xs' ys'. xs = xs'@ys' \<and> ys' \<noteq> [] \<longrightarrow> upd_cs cs' xs' \<noteq> []" by blast
        from \<open>upd_cs cs' xs = []\<close> \<open>cs = c'#cs'\<close> Return have "upd_cs cs (a'#xs) = []"
          by simp
        from \<open>\<forall>xs' ys'. xs = xs'@ys' \<and> ys' \<noteq> [] \<longrightarrow> upd_cs cs' xs' \<noteq> []\<close>
          \<open>xs \<noteq> []\<close> \<open>cs = c'#cs'\<close> Return
        have "\<forall>xs' ys'. a'#xs = xs'@ys' \<and> ys' \<noteq> [] \<longrightarrow> upd_cs cs xs' \<noteq> []"
          by auto(case_tac xs',auto)
        with \<open>as' = xs@ys\<close> \<open>upd_cs cs (a'#xs) = []\<close> \<open>upd_cs [] ys = []\<close>
        show ?thesis apply(rule_tac x="a'#xs" in exI) by fastforce
      qed
    qed
  qed
qed


lemma upd_cs_snoc_Return_Cons:
  assumes "kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f"
  shows "upd_cs cs as = c'#cs' \<Longrightarrow> upd_cs cs (as@[a]) = cs'"
proof(induct as arbitrary:cs)
  case Nil
  with \<open>kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f\<close> have "upd_cs cs [a] = cs'" by simp
 thus ?case by simp
next
  case (Cons a' as')
  note IH = \<open>\<And>cs. upd_cs cs as' = c'#cs' \<Longrightarrow> upd_cs cs (as'@[a]) = cs'\<close>
  show ?case
  proof(cases "kind a'" rule:edge_kind_cases)
    case Intra
    with \<open>upd_cs cs (a'#as') = c'#cs'\<close>
    have "upd_cs cs as' = c'#cs'" by(fastforce simp:intra_kind_def)
    from IH[OF this] have "upd_cs cs (as'@[a]) = cs'" .
    with Intra show ?thesis by(fastforce simp:intra_kind_def)
  next
    case Call
    with \<open>upd_cs cs (a'#as') = c'#cs'\<close>
    have "upd_cs (a'#cs) as' = c'#cs'" by simp
    from IH[OF this] have "upd_cs (a'#cs) (as'@[a]) = cs'" .
    with Call show ?thesis by simp
  next
    case Return
    show ?thesis
    proof(cases cs)
      case Nil
      with \<open>upd_cs cs (a'#as') = c'#cs'\<close> Return
      have "upd_cs cs as' = c'#cs'" by simp
      from IH[OF this] have "upd_cs cs (as'@[a]) = cs'" .
      with Nil Return show ?thesis by simp
    next
      case (Cons cx csx)
      with \<open>upd_cs cs (a'#as') = c'#cs'\<close> Return
      have "upd_cs csx as' = c'#cs'" by simp
      from IH[OF this] have "upd_cs csx (as'@[a]) = cs'" .
      with Cons Return show ?thesis by simp
    qed
  qed
qed


lemma upd_cs_snoc_Call:
  assumes "kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs"
  shows "upd_cs cs (as@[a]) = a#(upd_cs cs as)"
proof(induct as arbitrary:cs)
  case Nil
  with \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close> show ?case by simp
next
  case (Cons a' as')
  note IH = \<open>\<And>cs. upd_cs cs (as'@[a]) = a#upd_cs cs as'\<close>
  show ?case
  proof(cases "kind a'" rule:edge_kind_cases)
    case Intra 
    with IH[of cs] show ?thesis by(fastforce simp:intra_kind_def)
  next
    case Call
    with IH[of "a'#cs"] show ?thesis by simp
  next
    case Return
    show ?thesis
    proof(cases cs)
      case Nil
      with IH[of "[]"] Return show ?thesis by simp
    next
      case (Cons cx csx)
      with IH[of csx] Return show ?thesis by simp
    qed
  qed
qed





lemma valid_path_aux_split:
  assumes "valid_path_aux cs (as@as')"
  shows "valid_path_aux cs as" and "valid_path_aux (upd_cs cs as) as'"
  using \<open>valid_path_aux cs (as@as')\<close>
proof(induct cs "as@as'" arbitrary:as as' rule:vpa_induct)
  case (vpa_intra cs a as as'')
  note IH1 = \<open>\<And>xs ys. as = xs@ys \<Longrightarrow> valid_path_aux cs xs\<close>
  note IH2 = \<open>\<And>xs ys. as = xs@ys \<Longrightarrow> valid_path_aux (upd_cs cs xs) ys\<close>
  { case 1
    from vpa_intra
    have "as'' = [] \<and> a#as = as' \<or> (\<exists>xs. a#xs = as'' \<and> as = xs@as')"
      by(simp add:Cons_eq_append_conv)
    thus ?case
    proof
      assume "as'' = [] \<and> a#as = as'"
      thus ?thesis by simp
    next
      assume "\<exists>xs. a#xs = as'' \<and> as = xs@as'"
      then obtain xs where "a#xs = as''" and "as = xs@as'" by auto
      from IH1[OF \<open>as = xs@as'\<close>] have "valid_path_aux cs xs" .
      with \<open>a#xs = as''\<close> \<open>intra_kind (kind a)\<close>
      show ?thesis by(fastforce simp:intra_kind_def)
    qed
  next
    case 2
    from vpa_intra
    have "as'' = [] \<and> a#as = as' \<or> (\<exists>xs. a#xs = as'' \<and> as = xs@as')"
      by(simp add:Cons_eq_append_conv)
    thus ?case
    proof
      assume "as'' = [] \<and> a#as = as'"
      hence "as = []@tl as'" by(cases as') auto
      from IH2[OF this] have "valid_path_aux (upd_cs cs []) (tl as')" by simp
      with \<open>as'' = [] \<and> a#as = as'\<close> \<open>intra_kind (kind a)\<close>
      show ?thesis by(fastforce simp:intra_kind_def)
    next
      assume "\<exists>xs. a#xs = as'' \<and> as = xs@as'"
      then obtain xs where "a#xs = as''" and "as = xs@as'" by auto
      from IH2[OF \<open>as = xs@as'\<close>] have "valid_path_aux (upd_cs cs xs) as'" .
      from \<open>a#xs = as''\<close> \<open>intra_kind (kind a)\<close> 
      have "upd_cs cs xs = upd_cs cs as''" by(fastforce simp:intra_kind_def)
      with \<open>valid_path_aux (upd_cs cs xs) as'\<close>
      show ?thesis by simp
    qed
  }
next
  case (vpa_Call cs a as Q r p fs as'')
  note IH1 = \<open>\<And>xs ys. as = xs@ys \<Longrightarrow> valid_path_aux (a#cs) xs\<close>
  note IH2 = \<open>\<And>xs ys. as = xs@ys \<Longrightarrow>   valid_path_aux (upd_cs (a#cs) xs) ys\<close>
  { case 1
    from vpa_Call
    have "as'' = [] \<and> a#as = as' \<or> (\<exists>xs. a#xs = as'' \<and> as = xs@as')"
      by(simp add:Cons_eq_append_conv)
    thus ?case
    proof
      assume "as'' = [] \<and> a#as = as'"
      thus ?thesis by simp
    next
      assume "\<exists>xs. a#xs = as'' \<and> as = xs@as'"
      then obtain xs where "a#xs = as''" and "as = xs@as'" by auto
      from IH1[OF \<open>as = xs@as'\<close>] have "valid_path_aux (a#cs) xs" .
      with \<open>a#xs = as''\<close>[THEN sym] \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close>
      show ?thesis by simp
    qed
  next
    case 2
    from vpa_Call
    have "as'' = [] \<and> a#as = as' \<or> (\<exists>xs. a#xs = as'' \<and> as = xs@as')"
      by(simp add:Cons_eq_append_conv)
    thus ?case
    proof
      assume "as'' = [] \<and> a#as = as'"
      hence "as = []@tl as'" by(cases as') auto
      from IH2[OF this] have "valid_path_aux (upd_cs (a#cs) []) (tl as')" .
      with \<open>as'' = [] \<and> a#as = as'\<close> \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close>
      show ?thesis by clarsimp
    next
      assume "\<exists>xs. a#xs = as'' \<and> as = xs@as'"
      then obtain xs where "a#xs = as''" and "as = xs@as'" by auto
      from IH2[OF \<open>as = xs@as'\<close>] have "valid_path_aux (upd_cs (a # cs) xs) as'" .
      with \<open>a#xs = as''\<close>[THEN sym]  \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close>
      show ?thesis by simp
    qed
  }
next
  case (vpa_ReturnEmpty cs a as Q p f as'')
  note IH1 = \<open>\<And>xs ys. as = xs@ys \<Longrightarrow> valid_path_aux [] xs\<close>
  note IH2 = \<open>\<And>xs ys. as = xs@ys \<Longrightarrow> valid_path_aux (upd_cs [] xs) ys\<close>
  { case 1
    from vpa_ReturnEmpty
    have "as'' = [] \<and> a#as = as' \<or> (\<exists>xs. a#xs = as'' \<and> as = xs@as')"
      by(simp add:Cons_eq_append_conv)
    thus ?case
    proof
      assume "as'' = [] \<and> a#as = as'"
      thus ?thesis by simp
    next
      assume "\<exists>xs. a#xs = as'' \<and> as = xs@as'"
      then obtain xs where "a#xs = as''" and "as = xs@as'" by auto
      from IH1[OF \<open>as = xs@as'\<close>] have "valid_path_aux [] xs" .
      with \<open>a#xs = as''\<close>[THEN sym] \<open>kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f\<close> \<open>cs = []\<close>
      show ?thesis by simp
    qed
  next
    case 2
    from vpa_ReturnEmpty
    have "as'' = [] \<and> a#as = as' \<or> (\<exists>xs. a#xs = as'' \<and> as = xs@as')"
      by(simp add:Cons_eq_append_conv)
    thus ?case
    proof
      assume "as'' = [] \<and> a#as = as'"
      hence "as = []@tl as'" by(cases as') auto
      from IH2[OF this] have "valid_path_aux [] (tl as')" by simp
      with \<open>as'' = [] \<and> a#as = as'\<close> \<open>kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f\<close> \<open>cs = []\<close>
      show ?thesis by fastforce
    next
      assume "\<exists>xs. a#xs = as'' \<and> as = xs@as'"
      then obtain xs where "a#xs = as''" and "as = xs@as'" by auto
      from IH2[OF \<open>as = xs@as'\<close>] have "valid_path_aux (upd_cs [] xs) as'" .
      from \<open>a#xs = as''\<close>[THEN sym] \<open>kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f\<close> \<open>cs = []\<close>
      have "upd_cs [] xs = upd_cs cs as''" by simp
      with \<open>valid_path_aux (upd_cs [] xs) as'\<close> show ?thesis by simp
    qed
  }
next
  case (vpa_ReturnCons cs a as Q p f c' cs' as'')
  note IH1 = \<open>\<And>xs ys. as = xs@ys \<Longrightarrow> valid_path_aux cs' xs\<close>
  note IH2 = \<open>\<And>xs ys. as = xs@ys \<Longrightarrow> valid_path_aux (upd_cs cs' xs) ys\<close>
  { case 1
    from vpa_ReturnCons
    have "as'' = [] \<and> a#as = as' \<or> (\<exists>xs. a#xs = as'' \<and> as = xs@as')"
      by(simp add:Cons_eq_append_conv)
    thus ?case
    proof
      assume "as'' = [] \<and> a#as = as'"
      thus ?thesis by simp
    next
       assume "\<exists>xs. a#xs = as'' \<and> as = xs@as'"
       then obtain xs where "a#xs = as''" and "as = xs@as'" by auto
       from IH1[OF \<open>as = xs@as'\<close>] have "valid_path_aux cs' xs" .
       with \<open>a#xs = as''\<close>[THEN sym] \<open>kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f\<close> \<open>cs = c'#cs'\<close>
         \<open>a \<in> get_return_edges c'\<close>
       show ?thesis by simp
     qed
   next
     case 2
     from vpa_ReturnCons
     have "as'' = [] \<and> a#as = as' \<or> (\<exists>xs. a#xs = as'' \<and> as = xs@as')"
      by(simp add:Cons_eq_append_conv)
    thus ?case
    proof
      assume "as'' = [] \<and> a#as = as'"
      hence "as = []@tl as'" by(cases as') auto
      from IH2[OF this] have "valid_path_aux (upd_cs cs' []) (tl as')" .
       with \<open>as'' = [] \<and> a#as = as'\<close> \<open>kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f\<close> \<open>cs = c'#cs'\<close>
         \<open>a \<in> get_return_edges c'\<close>
       show ?thesis by fastforce
    next
      assume "\<exists>xs. a#xs = as'' \<and> as = xs@as'"
      then obtain xs where "a#xs = as''" and "as = xs@as'" by auto
      from IH2[OF \<open>as = xs@as'\<close>] have "valid_path_aux (upd_cs cs' xs) as'" .
      from \<open>a#xs = as''\<close>[THEN sym] \<open>kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f\<close> \<open>cs = c'#cs'\<close>
      have "upd_cs cs' xs = upd_cs cs as''" by simp
      with \<open>valid_path_aux (upd_cs cs' xs) as'\<close> show ?thesis by simp
    qed
  }
qed simp_all


lemma valid_path_aux_Append:
  "\<lbrakk>valid_path_aux cs as; valid_path_aux (upd_cs cs as) as'\<rbrakk>
  \<Longrightarrow> valid_path_aux cs (as@as')"
by(induct rule:vpa_induct,auto simp:intra_kind_def)


lemma vpa_snoc_Call:
  assumes "kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs"
  shows "valid_path_aux cs as \<Longrightarrow> valid_path_aux cs (as@[a])"
proof(induct rule:vpa_induct)
  case (vpa_empty cs)
  from \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close> have "valid_path_aux cs [a]" by simp
  thus ?case by simp
next
  case (vpa_intra cs a' as')
  from \<open>valid_path_aux cs (as'@[a])\<close> \<open>intra_kind (kind a')\<close>
  have "valid_path_aux cs (a'#(as'@[a]))"
    by(fastforce simp:intra_kind_def)
  thus ?case by simp
next
  case (vpa_Call cs a' as' Q' r' p' fs')
  from \<open>valid_path_aux (a'#cs) (as'@[a])\<close> \<open>kind a' = Q':r'\<hookrightarrow>\<^bsub>p'\<^esub>fs'\<close>
  have "valid_path_aux cs (a'#(as'@[a]))" by simp
  thus ?case by simp
next
  case (vpa_ReturnEmpty cs a' as' Q' p' f')
  from \<open>valid_path_aux [] (as'@[a])\<close> \<open>kind a' = Q'\<hookleftarrow>\<^bsub>p'\<^esub>f'\<close> \<open>cs = []\<close>
  have "valid_path_aux cs (a'#(as'@[a]))" by simp
  thus ?case by simp
next
  case (vpa_ReturnCons cs a' as' Q' p' f' c' cs')
  from \<open>valid_path_aux cs' (as'@[a])\<close> \<open>kind a' = Q'\<hookleftarrow>\<^bsub>p'\<^esub>f'\<close> \<open>cs = c'#cs'\<close>
    \<open>a' \<in> get_return_edges c'\<close>
  have "valid_path_aux cs (a'#(as'@[a]))" by simp
  thus ?case by simp
qed



definition valid_path :: "'edge list \<Rightarrow> bool"
  where "valid_path as \<equiv> valid_path_aux [] as"


lemma valid_path_aux_valid_path:
  "valid_path_aux cs as \<Longrightarrow> valid_path as"
by(fastforce intro:valid_path_aux_callstack_prefix simp:valid_path_def)

lemma valid_path_split:
  assumes "valid_path (as@as')" shows "valid_path as" and "valid_path as'"
  using \<open>valid_path (as@as')\<close>
  apply(auto simp:valid_path_def)
   apply(erule valid_path_aux_split)
  apply(drule valid_path_aux_split(2))
  by(fastforce intro:valid_path_aux_callstack_prefix)



definition valid_path' :: "'node \<Rightarrow> 'edge list \<Rightarrow> 'node \<Rightarrow> bool"
  ("_ -_\<rightarrow>\<^sub>\<surd>* _" [51,0,0] 80)
where vp_def:"n -as\<rightarrow>\<^sub>\<surd>* n' \<equiv> n -as\<rightarrow>* n' \<and> valid_path as"


lemma intra_path_vp:
  assumes "n -as\<rightarrow>\<^sub>\<iota>* n'" shows "n -as\<rightarrow>\<^sub>\<surd>* n'"
proof -
  from \<open>n -as\<rightarrow>\<^sub>\<iota>* n'\<close> have "n -as\<rightarrow>* n'" and "\<forall>a \<in> set as. intra_kind(kind a)"
    by(simp_all add:intra_path_def)
  from \<open>\<forall>a \<in> set as. intra_kind(kind a)\<close> have "valid_path_aux [] as"
    by(rule valid_path_aux_intra_path)
  thus ?thesis using \<open>n -as\<rightarrow>* n'\<close> by(simp add:vp_def valid_path_def)
qed


lemma vp_split_Cons:
  assumes "n -as\<rightarrow>\<^sub>\<surd>* n'" and "as \<noteq> []"
  obtains a' as' where "as = a'#as'" and "n = sourcenode a'"
  and "valid_edge a'" and "targetnode a' -as'\<rightarrow>\<^sub>\<surd>* n'"
proof(atomize_elim)
  from \<open>n -as\<rightarrow>\<^sub>\<surd>* n'\<close> \<open>as \<noteq> []\<close> obtain a' as' where "as = a'#as'"
    and "n = sourcenode a'" and "valid_edge a'" and "targetnode a' -as'\<rightarrow>* n'"
    by(fastforce elim:path_split_Cons simp:vp_def)
  from \<open>n -as\<rightarrow>\<^sub>\<surd>* n'\<close> have "valid_path as" by(simp add:vp_def)
  from \<open>as = a'#as'\<close> have "as = [a']@as'" by simp
  with \<open>valid_path as\<close> have "valid_path ([a']@as')" by simp
  hence "valid_path as'" by(rule valid_path_split)
  with \<open>targetnode a' -as'\<rightarrow>* n'\<close> have "targetnode a' -as'\<rightarrow>\<^sub>\<surd>* n'" by(simp add:vp_def)
  with \<open>as = a'#as'\<close> \<open>n = sourcenode a'\<close> \<open>valid_edge a'\<close>
  show "\<exists>a' as'. as = a'#as' \<and> n = sourcenode a' \<and> valid_edge a' \<and> 
                 targetnode a' -as'\<rightarrow>\<^sub>\<surd>* n'" by blast
qed

lemma vp_split_snoc:
  assumes "n -as\<rightarrow>\<^sub>\<surd>* n'" and "as \<noteq> []"
  obtains a' as' where "as = as'@[a']" and "n -as'\<rightarrow>\<^sub>\<surd>* sourcenode a'"
  and "valid_edge a'" and "n' = targetnode a'"
proof(atomize_elim)
  from \<open>n -as\<rightarrow>\<^sub>\<surd>* n'\<close> \<open>as \<noteq> []\<close> obtain a' as' where "as = as'@[a']"
    and "n -as'\<rightarrow>* sourcenode a'" and "valid_edge a'" and "n' = targetnode a'"
    by(clarsimp simp:vp_def)(erule path_split_snoc,auto)
  from \<open>n -as\<rightarrow>\<^sub>\<surd>* n'\<close> \<open>as = as'@[a']\<close> have "valid_path (as'@[a'])" by(simp add:vp_def)
  hence "valid_path as'" by(rule valid_path_split)
  with \<open>n -as'\<rightarrow>* sourcenode a'\<close> have "n -as'\<rightarrow>\<^sub>\<surd>* sourcenode a'" by(simp add:vp_def)
  with \<open>as = as'@[a']\<close> \<open>valid_edge a'\<close> \<open>n' = targetnode a'\<close>
  show "\<exists>as' a'. as = as'@[a'] \<and> n -as'\<rightarrow>\<^sub>\<surd>* sourcenode a' \<and> valid_edge a' \<and> 
                 n' = targetnode a'"
  by blast
qed

lemma vp_split:
  assumes "n -as@a#as'\<rightarrow>\<^sub>\<surd>* n'"
  shows "n -as\<rightarrow>\<^sub>\<surd>* sourcenode a" and "valid_edge a" and "targetnode a -as'\<rightarrow>\<^sub>\<surd>* n'"
proof -
  from \<open>n -as@a#as'\<rightarrow>\<^sub>\<surd>* n'\<close> have "n -as\<rightarrow>* sourcenode a" and "valid_edge a" 
    and "targetnode a -as'\<rightarrow>* n'"
    by(auto intro:path_split simp:vp_def)
  from \<open>n -as@a#as'\<rightarrow>\<^sub>\<surd>* n'\<close> have "valid_path (as@a#as')" by(simp add:vp_def)
  hence "valid_path as" and "valid_path (a#as')" by(auto intro:valid_path_split)
  from \<open>valid_path (a#as')\<close> have "valid_path ([a]@as')" by simp
  hence "valid_path as'"  by(rule valid_path_split)
  with \<open>n -as\<rightarrow>* sourcenode a\<close> \<open>valid_path as\<close> \<open>valid_edge a\<close> \<open>targetnode a -as'\<rightarrow>* n'\<close>
  show "n -as\<rightarrow>\<^sub>\<surd>* sourcenode a" "valid_edge a" "targetnode a -as'\<rightarrow>\<^sub>\<surd>* n'"
    by(auto simp:vp_def)
qed

lemma vp_split_second:
  assumes "n -as@a#as'\<rightarrow>\<^sub>\<surd>* n'" shows "sourcenode a -a#as'\<rightarrow>\<^sub>\<surd>* n'"
proof -
  from \<open>n -as@a#as'\<rightarrow>\<^sub>\<surd>* n'\<close> have "sourcenode a -a#as'\<rightarrow>* n'"
    by(fastforce elim:path_split_second simp:vp_def)
  from \<open>n -as@a#as'\<rightarrow>\<^sub>\<surd>* n'\<close> have "valid_path (as@a#as')" by(simp add:vp_def)
  hence "valid_path (a#as')" by(rule valid_path_split)
  with \<open>sourcenode a -a#as'\<rightarrow>* n'\<close> show ?thesis by(simp add:vp_def)
qed




function valid_path_rev_aux :: "'edge list \<Rightarrow> 'edge list \<Rightarrow> bool"
  where "valid_path_rev_aux cs [] \<longleftrightarrow> True"
  | "valid_path_rev_aux cs (as@[a]) \<longleftrightarrow> 
       (case (kind a) of Q\<hookleftarrow>\<^bsub>p\<^esub>f \<Rightarrow> valid_path_rev_aux (a#cs) as
                       | Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs \<Rightarrow> case cs of [] \<Rightarrow> valid_path_rev_aux [] as
                                     | c'#cs' \<Rightarrow> c' \<in> get_return_edges a \<and>
                                                 valid_path_rev_aux cs' as
                       |    _ \<Rightarrow> valid_path_rev_aux cs as)"
by auto(case_tac b rule:rev_cases,auto)
termination by lexicographic_order



lemma vpra_induct [consumes 1,case_names vpra_empty vpra_intra vpra_Return 
  vpra_CallEmpty vpra_CallCons]:
  assumes major: "valid_path_rev_aux xs ys"
  and rules: "\<And>cs. P cs []"
    "\<And>cs a as. \<lbrakk>intra_kind(kind a); valid_path_rev_aux cs as; P cs as\<rbrakk> 
      \<Longrightarrow> P cs (as@[a])"
    "\<And>cs a as Q p f. \<lbrakk>kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f; valid_path_rev_aux (a#cs) as; P (a#cs) as\<rbrakk> 
      \<Longrightarrow> P cs (as@[a])"
    "\<And>cs a as Q r p fs. \<lbrakk>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs; cs = []; valid_path_rev_aux [] as; 
         P [] as\<rbrakk> \<Longrightarrow> P cs (as@[a])"
    "\<And>cs a as Q r p fs c' cs'. \<lbrakk>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs; cs = c'#cs'; 
         valid_path_rev_aux cs' as; c' \<in> get_return_edges a; P cs' as\<rbrakk>
     \<Longrightarrow> P cs (as@[a])"
  shows "P xs ys"
using major
apply(induct ys arbitrary:xs rule:rev_induct)
by(auto intro:rules split:edge_kind.split_asm list.split_asm simp:intra_kind_def)


lemma vpra_callstack_prefix:
  "valid_path_rev_aux (cs@cs') as \<Longrightarrow> valid_path_rev_aux cs as"
proof(induct "cs@cs'" as arbitrary:cs cs' rule:vpra_induct)
  case vpra_empty thus ?case by simp
next
  case (vpra_intra a as)
  hence "valid_path_rev_aux cs as" by simp
  with \<open>intra_kind (kind a)\<close> show ?case by(fastforce simp:intra_kind_def)
next
  case (vpra_Return a as Q p f)
  note IH = \<open>\<And>ds ds'. a#cs@cs' = ds@ds' \<Longrightarrow> valid_path_rev_aux ds as\<close>
  have "a#cs@cs' = (a#cs)@cs'" by simp
  from IH[OF this] have "valid_path_rev_aux (a#cs) as" .
  with \<open>kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f\<close> show ?case by simp
next
  case (vpra_CallEmpty a as Q r p fs)
  hence "valid_path_rev_aux cs as" by simp
  with \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close> \<open>cs@cs' = []\<close> show ?case by simp
next
  case (vpra_CallCons a as Q r p fs c' csx)
  note IH = \<open>\<And>cs cs'. csx = cs@cs' \<Longrightarrow> valid_path_rev_aux cs as\<close>
  from \<open>cs@cs' = c'#csx\<close>
  have "(cs = [] \<and> cs' = c'#csx) \<or> (\<exists>zs. cs = c'#zs \<and> zs@cs' = csx)"
    by(simp add:append_eq_Cons_conv)
  thus ?case
  proof
    assume "cs = [] \<and> cs' = c'#csx"
    hence "cs = []" and "cs' = c'#csx" by simp_all
    from \<open>cs' = c'#csx\<close> have "csx = []@tl cs'" by simp
    from IH[OF this] have "valid_path_rev_aux [] as" .
    with \<open>cs = []\<close> \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close> show ?thesis by simp
  next
    assume "\<exists>zs. cs = c'#zs \<and> zs@cs' = csx"
    then obtain zs where "cs = c'#zs" and "csx = zs@cs'" by auto
    from IH[OF \<open>csx = zs@cs'\<close>] have "valid_path_rev_aux zs as" .
    with \<open>cs = c'#zs\<close> \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close> \<open>c' \<in> get_return_edges a\<close> show ?thesis by simp
  qed
qed



function upd_rev_cs :: "'edge list \<Rightarrow> 'edge list \<Rightarrow> 'edge list"
  where "upd_rev_cs cs [] = cs"
  | "upd_rev_cs cs (as@[a]) =
       (case (kind a) of Q\<hookleftarrow>\<^bsub>p\<^esub>f \<Rightarrow> upd_rev_cs (a#cs) as
                       | Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs \<Rightarrow> case cs of [] \<Rightarrow> upd_rev_cs cs as
                                      | c'#cs' \<Rightarrow> upd_rev_cs cs' as
                       |    _ \<Rightarrow> upd_rev_cs cs as)"
by auto(case_tac b rule:rev_cases,auto)
termination by lexicographic_order


lemma upd_rev_cs_empty [dest]:
  "upd_rev_cs cs [] = [] \<Longrightarrow> cs = []"
by(cases cs) auto


lemma valid_path_rev_aux_split:
  assumes "valid_path_rev_aux cs (as@as')"
  shows "valid_path_rev_aux cs as'" and "valid_path_rev_aux (upd_rev_cs cs as') as"
  using \<open>valid_path_rev_aux cs (as@as')\<close>
proof(induct cs "as@as'" arbitrary:as as' rule:vpra_induct)
  case (vpra_intra cs a as as'')
  note IH1 = \<open>\<And>xs ys. as = xs@ys \<Longrightarrow> valid_path_rev_aux cs ys\<close>
  note IH2 = \<open>\<And>xs ys. as = xs@ys \<Longrightarrow> valid_path_rev_aux (upd_rev_cs cs ys) xs\<close>
  { case 1
    from vpra_intra
    have "as' = [] \<and> as@[a] = as'' \<or> (\<exists>xs. as = as''@xs \<and> xs@[a] = as')"
      by(cases as' rule:rev_cases) auto
    thus ?case
    proof
      assume "as' = [] \<and> as@[a] = as''"
      thus ?thesis by simp
    next
      assume "\<exists>xs. as = as''@xs \<and> xs@[a] = as'"
      then obtain xs where "as = as''@xs" and "xs@[a] = as'" by auto
      from IH1[OF \<open>as = as''@xs\<close>] have "valid_path_rev_aux cs xs" .
      with \<open>xs@[a] = as'\<close> \<open>intra_kind (kind a)\<close>
      show ?thesis by(fastforce simp:intra_kind_def)
    qed
  next
    case 2
    from vpra_intra
    have "as' = [] \<and> as@[a] = as'' \<or> (\<exists>xs. as = as''@xs \<and> xs@[a] = as')"
      by(cases as' rule:rev_cases) auto
    thus ?case
    proof
      assume "as' = [] \<and> as@[a] = as''"
      hence "as = butlast as''@[]" by(cases as) auto
      from IH2[OF this] have "valid_path_rev_aux (upd_rev_cs cs []) (butlast as'')" .
      with \<open>as' = [] \<and> as@[a] = as''\<close> \<open>intra_kind (kind a)\<close>
      show ?thesis by(fastforce simp:intra_kind_def)
    next
      assume "\<exists>xs. as = as''@xs \<and> xs@[a] = as'"
      then obtain xs where "as = as''@xs" and "xs@[a] = as'" by auto
      from IH2[OF \<open>as = as''@xs\<close>] have "valid_path_rev_aux (upd_rev_cs cs xs) as''" .
      from \<open>xs@[a] = as'\<close> \<open>intra_kind (kind a)\<close> 
      have "upd_rev_cs cs xs = upd_rev_cs cs as'" by(fastforce simp:intra_kind_def)
      with \<open>valid_path_rev_aux (upd_rev_cs cs xs) as''\<close>
      show ?thesis by simp
    qed
  }
next
  case (vpra_Return cs a as Q p f as'')
  note IH1 = \<open>\<And>xs ys. as = xs@ys \<Longrightarrow> valid_path_rev_aux (a#cs) ys\<close>
  note IH2 = \<open>\<And>xs ys. as = xs@ys \<Longrightarrow> valid_path_rev_aux (upd_rev_cs (a#cs) ys) xs\<close>
  { case 1
    from vpra_Return
    have "as' = [] \<and> as@[a] = as'' \<or> (\<exists>xs. as = as''@xs \<and> xs@[a] = as')"
      by(cases as' rule:rev_cases) auto
    thus ?case
    proof
      assume "as' = [] \<and> as@[a] = as''"
      thus ?thesis by simp
    next
      assume "\<exists>xs. as = as''@xs \<and> xs@[a] = as'"
      then obtain xs where "as = as''@xs" and "xs@[a] = as'" by auto
      from IH1[OF \<open>as = as''@xs\<close>] have "valid_path_rev_aux (a#cs) xs" .
      with \<open>xs@[a] = as'\<close> \<open>kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f\<close>
      show ?thesis by fastforce
    qed
  next
    case 2
    from vpra_Return
    have "as' = [] \<and> as@[a] = as'' \<or> (\<exists>xs. as = as''@xs \<and> xs@[a] = as')"
      by(cases as' rule:rev_cases) auto
    thus ?case
    proof
      assume "as' = [] \<and> as@[a] = as''"
      hence "as = butlast as''@[]" by(cases as) auto
      from IH2[OF this] 
      have "valid_path_rev_aux (upd_rev_cs (a#cs) []) (butlast as'')" .
      with \<open>as' = [] \<and> as@[a] = as''\<close> \<open>kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f\<close>
      show ?thesis by fastforce
    next
      assume "\<exists>xs. as = as''@xs \<and> xs@[a] = as'"
      then obtain xs where "as = as''@xs" and "xs@[a] = as'" by auto
      from IH2[OF \<open>as = as''@xs\<close>] 
      have "valid_path_rev_aux (upd_rev_cs (a#cs) xs) as''" .
      from \<open>xs@[a] = as'\<close> \<open>kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f\<close>
      have "upd_rev_cs (a#cs) xs = upd_rev_cs cs as'" by fastforce
      with \<open>valid_path_rev_aux (upd_rev_cs (a#cs) xs) as''\<close>
      show ?thesis by simp
    qed
  }
next
  case (vpra_CallEmpty cs a as Q r p fs as'')
  note IH1 = \<open>\<And>xs ys. as = xs@ys \<Longrightarrow> valid_path_rev_aux [] ys\<close>
  note IH2 = \<open>\<And>xs ys. as = xs@ys \<Longrightarrow> valid_path_rev_aux (upd_rev_cs [] ys) xs\<close>
  { case 1
    from vpra_CallEmpty
    have "as' = [] \<and> as@[a] = as'' \<or> (\<exists>xs. as = as''@xs \<and> xs@[a] = as')"
      by(cases as' rule:rev_cases) auto
    thus ?case
    proof
      assume "as' = [] \<and> as@[a] = as''"
      thus ?thesis by simp
    next
      assume "\<exists>xs. as = as''@xs \<and> xs@[a] = as'"
      then obtain xs where "as = as''@xs" and "xs@[a] = as'" by auto
      from IH1[OF \<open>as = as''@xs\<close>] have "valid_path_rev_aux [] xs" .
      with \<open>xs@[a] = as'\<close> \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close> \<open>cs = []\<close>
      show ?thesis by fastforce
    qed
  next
    case 2
    from vpra_CallEmpty
    have "as' = [] \<and> as@[a] = as'' \<or> (\<exists>xs. as = as''@xs \<and> xs@[a] = as')"
      by(cases as' rule:rev_cases) auto
    thus ?case
    proof
      assume "as' = [] \<and> as@[a] = as''"
      hence "as = butlast as''@[]" by(cases as) auto
      from IH2[OF this] 
      have "valid_path_rev_aux (upd_rev_cs [] []) (butlast as'')" .
      with \<open>as' = [] \<and> as@[a] = as''\<close> \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close> \<open>cs = []\<close>
      show ?thesis by fastforce
    next
      assume "\<exists>xs. as = as''@xs \<and> xs@[a] = as'"
      then obtain xs where "as = as''@xs" and "xs@[a] = as'" by auto
      from IH2[OF \<open>as = as''@xs\<close>] 
      have "valid_path_rev_aux (upd_rev_cs [] xs) as''" .
      with \<open>xs@[a] = as'\<close> \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close> \<open>cs = []\<close> 
      show ?thesis by fastforce
    qed
  }
next
  case (vpra_CallCons cs a as Q r p fs c' cs' as'')
  note IH1 = \<open>\<And>xs ys. as = xs@ys \<Longrightarrow> valid_path_rev_aux cs' ys\<close>
  note IH2 = \<open>\<And>xs ys. as = xs@ys \<Longrightarrow> valid_path_rev_aux (upd_rev_cs cs' ys) xs\<close>
  { case 1
    from vpra_CallCons
    have "as' = [] \<and> as@[a] = as'' \<or> (\<exists>xs. as = as''@xs \<and> xs@[a] = as')"
      by(cases as' rule:rev_cases) auto
    thus ?case
    proof
      assume "as' = [] \<and> as@[a] = as''"
      thus ?thesis by simp
    next
      assume "\<exists>xs. as = as''@xs \<and> xs@[a] = as'"
      then obtain xs where "as = as''@xs" and "xs@[a] = as'" by auto
      from IH1[OF \<open>as = as''@xs\<close>] have "valid_path_rev_aux cs' xs" .
      with \<open>xs@[a] = as'\<close> \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close> \<open>cs = c' # cs'\<close> \<open>c' \<in> get_return_edges a\<close>
      show ?thesis by fastforce
    qed
  next
    case 2
    from vpra_CallCons
    have "as' = [] \<and> as@[a] = as'' \<or> (\<exists>xs. as = as''@xs \<and> xs@[a] = as')"
      by(cases as' rule:rev_cases) auto
    thus ?case
    proof
      assume "as' = [] \<and> as@[a] = as''"
      hence "as = butlast as''@[]" by(cases as) auto
      from IH2[OF this] 
      have "valid_path_rev_aux (upd_rev_cs cs' []) (butlast as'')" .
      with \<open>as' = [] \<and> as@[a] = as''\<close> \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close> \<open>cs = c' # cs'\<close>
        \<open>c' \<in> get_return_edges a\<close> show ?thesis by fastforce
    next
      assume "\<exists>xs. as = as''@xs \<and> xs@[a] = as'"
      then obtain xs where "as = as''@xs" and "xs@[a] = as'" by auto
      from IH2[OF \<open>as = as''@xs\<close>] 
      have "valid_path_rev_aux (upd_rev_cs cs' xs) as''" .
      with \<open>xs@[a] = as'\<close> \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close> \<open>cs = c' # cs'\<close>
        \<open>c' \<in> get_return_edges a\<close>
      show ?thesis by fastforce
    qed
  }
qed simp_all


lemma valid_path_rev_aux_Append:
  "\<lbrakk>valid_path_rev_aux cs as'; valid_path_rev_aux (upd_rev_cs cs as') as\<rbrakk>
  \<Longrightarrow> valid_path_rev_aux cs (as@as')"
by(induct rule:vpra_induct,
   auto simp:intra_kind_def simp del:append_assoc simp:append_assoc[THEN sym])


lemma vpra_Cons_intra:
  assumes "intra_kind(kind a)"
  shows "valid_path_rev_aux cs as \<Longrightarrow> valid_path_rev_aux cs (a#as)"
proof(induct rule:vpra_induct)
  case (vpra_empty cs)
  have "valid_path_rev_aux cs []" by simp
  with \<open>intra_kind(kind a)\<close> have "valid_path_rev_aux cs ([]@[a])"
    by(simp only:valid_path_rev_aux.simps intra_kind_def,fastforce)
  thus ?case by simp
qed(simp only:append_Cons[THEN sym] valid_path_rev_aux.simps intra_kind_def,fastforce)+


lemma vpra_Cons_Return:
  assumes "kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f"
  shows "valid_path_rev_aux cs as \<Longrightarrow> valid_path_rev_aux cs (a#as)"
proof(induct rule:vpra_induct)
  case (vpra_empty cs)
  from \<open>kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f\<close> have "valid_path_rev_aux cs ([]@[a])"
    by(simp only:valid_path_rev_aux.simps,clarsimp)
  thus ?case by simp
next
  case (vpra_intra cs a' as')
  from \<open>valid_path_rev_aux cs (a#as')\<close> \<open>intra_kind (kind a')\<close>
  have "valid_path_rev_aux cs ((a#as')@[a'])"
    by(simp only:valid_path_rev_aux.simps,fastforce simp:intra_kind_def)
  thus ?case by simp
next
  case (vpra_Return cs a' as' Q' p' f')
  from \<open>valid_path_rev_aux (a'#cs) (a#as')\<close> \<open>kind a' = Q'\<hookleftarrow>\<^bsub>p'\<^esub>f'\<close>
  have "valid_path_rev_aux cs ((a#as')@[a'])"
    by(simp only:valid_path_rev_aux.simps,clarsimp)
  thus ?case by simp
next
  case (vpra_CallEmpty cs a' as' Q' r' p' fs')
  from \<open>valid_path_rev_aux [] (a#as')\<close> \<open>kind a' = Q':r'\<hookrightarrow>\<^bsub>p'\<^esub>fs'\<close> \<open>cs = []\<close>
  have "valid_path_rev_aux cs ((a#as')@[a'])"
    by(simp only:valid_path_rev_aux.simps,clarsimp)
  thus ?case by simp
next
  case (vpra_CallCons cs a' as' Q' r' p' fs' c' cs')
  from \<open>valid_path_rev_aux cs' (a#as')\<close> \<open>kind a' = Q':r'\<hookrightarrow>\<^bsub>p'\<^esub>fs'\<close> \<open>cs = c'#cs'\<close>
    \<open>c' \<in> get_return_edges a'\<close>
  have "valid_path_rev_aux cs ((a#as')@[a'])"
    by(simp only:valid_path_rev_aux.simps,clarsimp)
  thus ?case by simp
qed


(*<*)
lemmas append_Cons_rev = append_Cons[THEN sym]
declare append_Cons [simp del] append_Cons_rev [simp]
(*>*)

lemma upd_rev_cs_Cons_intra:
  assumes "intra_kind(kind a)" shows "upd_rev_cs cs (a#as) = upd_rev_cs cs as"
proof(induct as arbitrary:cs rule:rev_induct)
  case Nil
  from \<open>intra_kind (kind a)\<close>
  have "upd_rev_cs cs ([]@[a]) = upd_rev_cs cs []"
    by(simp only:upd_rev_cs.simps,auto simp:intra_kind_def)
  thus ?case by simp
next
  case (snoc a' as')
  note IH = \<open>\<And>cs. upd_rev_cs cs (a#as') = upd_rev_cs cs as'\<close>
  show ?case
  proof(cases "kind a'" rule:edge_kind_cases)
    case Intra
    from IH have "upd_rev_cs cs (a#as') = upd_rev_cs cs as'" .
    with Intra have "upd_rev_cs cs ((a#as')@[a']) = upd_rev_cs cs (as'@[a'])"
      by(fastforce simp:intra_kind_def)
    thus ?thesis by simp
  next
    case Return
    from IH have "upd_rev_cs (a'#cs) (a#as') = upd_rev_cs (a'#cs) as'" .
    with Return have "upd_rev_cs cs ((a#as')@[a']) = upd_rev_cs cs (as'@[a'])"
      by(auto simp:intra_kind_def)
    thus ?thesis by simp
  next
    case Call
    show ?thesis
    proof(cases cs)
      case Nil
      from IH have "upd_rev_cs [] (a#as') = upd_rev_cs [] as'" .
      with Call Nil have "upd_rev_cs cs ((a#as')@[a']) = upd_rev_cs cs (as'@[a'])"
        by(auto simp:intra_kind_def)
      thus ?thesis by simp
    next
      case (Cons c' cs')
      from IH have "upd_rev_cs cs' (a#as') = upd_rev_cs cs' as'" .
      with Call Cons have "upd_rev_cs cs ((a#as')@[a']) = upd_rev_cs cs (as'@[a'])"
        by(auto simp:intra_kind_def)
      thus ?thesis by simp
    qed
  qed
qed



lemma upd_rev_cs_Cons_Return:
  assumes "kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f" shows "upd_rev_cs cs (a#as) = a#(upd_rev_cs cs as)"
proof(induct as arbitrary:cs rule:rev_induct)
  case Nil
  with \<open>kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f\<close> have "upd_rev_cs cs ([]@[a]) = a#(upd_rev_cs cs [])"
    by(simp only:upd_rev_cs.simps) clarsimp
  thus ?case by simp
next
  case (snoc a' as')
  note IH = \<open>\<And>cs. upd_rev_cs cs (a#as') = a#upd_rev_cs cs as'\<close>
  show ?case
  proof(cases "kind a'" rule:edge_kind_cases)
    case Intra
    from IH have "upd_rev_cs cs (a#as') = a#(upd_rev_cs cs as')" .
    with Intra have "upd_rev_cs cs ((a#as')@[a']) = a#(upd_rev_cs cs (as'@[a']))"
      by(fastforce simp:intra_kind_def)
    thus ?thesis by simp
  next
    case Return
    from IH have "upd_rev_cs (a'#cs) (a#as') = a#(upd_rev_cs (a'#cs) as')" .
    with Return have "upd_rev_cs cs ((a#as')@[a']) = a#(upd_rev_cs cs (as'@[a']))"
      by(auto simp:intra_kind_def)
    thus ?thesis by simp
  next
    case Call
    show ?thesis
    proof(cases cs)
      case Nil
      from IH have "upd_rev_cs [] (a#as') = a#(upd_rev_cs [] as')" .
      with Call Nil have "upd_rev_cs cs ((a#as')@[a']) = a#(upd_rev_cs cs (as'@[a']))"
        by(auto simp:intra_kind_def)
      thus ?thesis by simp
    next
      case (Cons c' cs')
      from IH have "upd_rev_cs cs' (a#as') = a#(upd_rev_cs cs' as')" .
      with Call Cons 
      have "upd_rev_cs cs ((a#as')@[a']) = a#(upd_rev_cs cs (as'@[a']))"
        by(auto simp:intra_kind_def)
      thus ?thesis by simp
    qed
  qed
qed


lemma upd_rev_cs_Cons_Call_Cons:
  assumes "kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs"
  shows "upd_rev_cs cs as = c'#cs' \<Longrightarrow> upd_rev_cs cs (a#as) = cs'"
proof(induct as arbitrary:cs rule:rev_induct)
  case Nil
  with \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close> have "upd_rev_cs cs ([]@[a]) = cs'"
    by(simp only:upd_rev_cs.simps) clarsimp
 thus ?case by simp
next
  case (snoc a' as')
  note IH = \<open>\<And>cs. upd_rev_cs cs as' = c'#cs' \<Longrightarrow> upd_rev_cs cs (a#as') = cs'\<close>
  show ?case
  proof(cases "kind a'" rule:edge_kind_cases)
    case Intra
    with \<open>upd_rev_cs cs (as'@[a']) = c'#cs'\<close>
    have "upd_rev_cs cs as' = c'#cs'" by(fastforce simp:intra_kind_def)
    from IH[OF this] have "upd_rev_cs cs (a#as') = cs'" .
    with Intra show ?thesis by(fastforce simp:intra_kind_def)
  next
    case Return
    with \<open>upd_rev_cs cs (as'@[a']) = c'#cs'\<close>
    have "upd_rev_cs (a'#cs) as' = c'#cs'" by simp
    from IH[OF this] have "upd_rev_cs (a'#cs) (a#as') = cs'" .
    with Return show ?thesis by simp
  next
    case Call
    show ?thesis
    proof(cases cs)
      case Nil
      with \<open>upd_rev_cs cs (as'@[a']) = c'#cs'\<close> Call
      have "upd_rev_cs cs as' = c'#cs'" by simp
      from IH[OF this] have "upd_rev_cs cs (a#as') = cs'" .
      with Nil Call show ?thesis by simp
    next
      case (Cons cx csx)
      with \<open>upd_rev_cs cs (as'@[a']) = c'#cs'\<close> Call
      have "upd_rev_cs csx as' = c'#cs'" by simp
      from IH[OF this] have "upd_rev_cs csx (a#as') = cs'" .
      with Cons Call show ?thesis by simp
    qed
  qed
qed


lemma upd_rev_cs_Cons_Call_Cons_Empty:
  assumes "kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs"
  shows "upd_rev_cs cs as = [] \<Longrightarrow> upd_rev_cs cs (a#as) = []"
proof(induct as arbitrary:cs rule:rev_induct)
  case Nil
  with \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close> have "upd_rev_cs cs ([]@[a]) = []"
    by(simp only:upd_rev_cs.simps) clarsimp
 thus ?case by simp
next
  case (snoc a' as')
  note IH = \<open>\<And>cs. upd_rev_cs cs as' = [] \<Longrightarrow> upd_rev_cs cs (a#as') = []\<close>
  show ?case
  proof(cases "kind a'" rule:edge_kind_cases)
    case Intra
    with \<open>upd_rev_cs cs (as'@[a']) = []\<close>
    have "upd_rev_cs cs as' = []" by(fastforce simp:intra_kind_def)
    from IH[OF this] have "upd_rev_cs cs (a#as') = []" .
    with Intra show ?thesis by(fastforce simp:intra_kind_def)
  next
    case Return
    with \<open>upd_rev_cs cs (as'@[a']) = []\<close>
    have "upd_rev_cs (a'#cs) as' = []" by simp
    from IH[OF this] have "upd_rev_cs (a'#cs) (a#as') = []" .
    with Return show ?thesis by simp
  next
    case Call
    show ?thesis
    proof(cases cs)
      case Nil
      with \<open>upd_rev_cs cs (as'@[a']) = []\<close> Call
      have "upd_rev_cs cs as' = []" by simp
      from IH[OF this] have "upd_rev_cs cs (a#as') = []" .
      with Nil Call show ?thesis by simp
    next
      case (Cons cx csx)
      with \<open>upd_rev_cs cs (as'@[a']) = []\<close> Call
      have "upd_rev_cs csx as' = []" by simp
      from IH[OF this] have "upd_rev_cs csx (a#as') = []" .
      with Cons Call show ?thesis by simp
    qed
  qed
qed

(*<*)declare append_Cons [simp] append_Cons_rev [simp del](*>*)


definition valid_call_list :: "'edge list \<Rightarrow> 'node \<Rightarrow> bool"
  where "valid_call_list cs n \<equiv>
  \<forall>cs' c cs''. cs = cs'@c#cs'' \<longrightarrow> (valid_edge c \<and> (\<exists>Q r p fs. (kind c = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs) \<and> 
                    p = get_proc (case cs' of [] \<Rightarrow> n | _ \<Rightarrow> last (sourcenodes cs'))))"

definition valid_return_list :: "'edge list \<Rightarrow> 'node \<Rightarrow> bool"
  where "valid_return_list cs n \<equiv>
  \<forall>cs' c cs''. cs = cs'@c#cs'' \<longrightarrow> (valid_edge c \<and> (\<exists>Q p f. (kind c = Q\<hookleftarrow>\<^bsub>p\<^esub>f) \<and> 
                    p = get_proc (case cs' of [] \<Rightarrow> n | _ \<Rightarrow> last (targetnodes cs'))))"


lemma valid_call_list_valid_edges: 
  assumes "valid_call_list cs n" shows "\<forall>c \<in> set cs. valid_edge c"
proof -
  from \<open>valid_call_list cs n\<close> 
  have "\<forall>cs' c cs''. cs = cs'@c#cs'' \<longrightarrow> valid_edge c"
    by(simp add:valid_call_list_def)
  thus ?thesis
  proof(induct cs)
    case Nil thus ?case by simp
  next
    case (Cons cx csx)
    note IH = \<open>\<forall>cs' c cs''. csx = cs'@c#cs'' \<longrightarrow> valid_edge c \<Longrightarrow>
                            \<forall>a\<in>set csx. valid_edge a\<close>
    from \<open>\<forall>cs' c cs''. cx#csx = cs'@c#cs'' \<longrightarrow> valid_edge c\<close>
    have "valid_edge cx" by blast
    from \<open>\<forall>cs' c cs''. cx#csx = cs'@c#cs'' \<longrightarrow> valid_edge c\<close>
    have "\<forall>cs' c cs''. csx = cs'@c#cs'' \<longrightarrow> valid_edge c"
      by auto(erule_tac x="cx#cs'" in allE,auto)
    from IH[OF this] \<open>valid_edge cx\<close> show ?case by simp
  qed
qed


lemma valid_return_list_valid_edges: 
  assumes "valid_return_list rs n" shows "\<forall>r \<in> set rs. valid_edge r"
proof -
  from \<open>valid_return_list rs n\<close> 
  have "\<forall>rs' r rs''. rs = rs'@r#rs'' \<longrightarrow> valid_edge r"
    by(simp add:valid_return_list_def)
  thus ?thesis
  proof(induct rs)
    case Nil thus ?case by simp
  next
    case (Cons rx rsx)
    note IH = \<open>\<forall>rs' r rs''. rsx = rs'@r#rs'' \<longrightarrow> valid_edge r \<Longrightarrow>
                            \<forall>a\<in>set rsx. valid_edge a\<close>
    from \<open>\<forall>rs' r rs''. rx#rsx = rs'@r#rs'' \<longrightarrow> valid_edge r\<close>
    have "valid_edge rx" by blast
    from \<open>\<forall>rs' r rs''. rx#rsx = rs'@r#rs'' \<longrightarrow> valid_edge r\<close>
    have "\<forall>rs' r rs''. rsx = rs'@r#rs'' \<longrightarrow> valid_edge r"
      by auto(erule_tac x="rx#rs'" in allE,auto)
    from IH[OF this] \<open>valid_edge rx\<close> show ?case by simp
  qed
qed


lemma vpra_empty_valid_call_list_rev:
  "valid_call_list cs n \<Longrightarrow> valid_path_rev_aux [] (rev cs)"
proof(induct cs arbitrary:n)
  case Nil thus ?case by simp
next
  case (Cons c' cs')
  note IH = \<open>\<And>n. valid_call_list cs' n \<Longrightarrow> valid_path_rev_aux [] (rev cs')\<close>
  from \<open>valid_call_list (c'#cs') n\<close> have "valid_call_list cs' (sourcenode c')"
    apply(clarsimp simp:valid_call_list_def)
    apply hypsubst_thin
    apply(erule_tac x="c'#cs'" in allE)
    apply clarsimp
    by(case_tac cs',auto simp:sourcenodes_def)
  from IH[OF this] have "valid_path_rev_aux [] (rev cs')" .
  moreover
  from \<open>valid_call_list (c'#cs') n\<close> obtain Q r p fs where "kind c' = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs"
    apply(clarsimp simp:valid_call_list_def)
    by(erule_tac x="[]" in allE) fastforce
  ultimately show ?case by simp
qed


lemma vpa_upd_cs_cases:
  "\<lbrakk>valid_path_aux cs as; valid_call_list cs n; n -as\<rightarrow>* n'\<rbrakk>
  \<Longrightarrow> case (upd_cs cs as) of [] \<Rightarrow> (\<forall>c \<in> set cs. \<exists>a \<in> set as. a \<in> get_return_edges c)
                      | cx#csx \<Rightarrow> valid_call_list (cx#csx) n'"
proof(induct arbitrary:n rule:vpa_induct)
  case (vpa_empty cs)
  from \<open>n -[]\<rightarrow>* n'\<close> have "n = n'" by fastforce
  with \<open>valid_call_list cs n\<close> show ?case by(cases cs) auto
next
  case (vpa_intra cs a' as')
  note IH = \<open>\<And>n. \<lbrakk>valid_call_list cs n; n -as'\<rightarrow>* n'\<rbrakk>
    \<Longrightarrow> case (upd_cs cs as') of [] \<Rightarrow> \<forall>c\<in>set cs. \<exists>a\<in>set as'. a \<in> get_return_edges c
                         | cx#csx \<Rightarrow> valid_call_list (cx # csx) n'\<close>
  from \<open>intra_kind (kind a')\<close> have "upd_cs cs (a'#as') = upd_cs cs as'"
    by(fastforce simp:intra_kind_def)
  from \<open>n -a'#as'\<rightarrow>* n'\<close> have [simp]:"n = sourcenode a'" and "valid_edge a'"
    and "targetnode a' -as'\<rightarrow>* n'" by(auto elim:path_split_Cons)
  from \<open>valid_edge a'\<close> \<open>intra_kind (kind a')\<close>
  have "get_proc (sourcenode a') = get_proc (targetnode a')" by(rule get_proc_intra)
  with \<open>valid_call_list cs n\<close> have "valid_call_list cs (targetnode a')"
    apply(clarsimp simp:valid_call_list_def)
    apply(erule_tac x="cs'" in allE) apply clarsimp
    by(case_tac cs') auto
  from IH[OF this \<open>targetnode a' -as'\<rightarrow>* n'\<close>] \<open>upd_cs cs (a'#as') = upd_cs cs as'\<close>
  show ?case by(cases "upd_cs cs as'") auto
next
  case (vpa_Call cs a' as' Q r p fs)
  note IH = \<open>\<And>n. \<lbrakk>valid_call_list (a'#cs) n; n -as'\<rightarrow>* n'\<rbrakk>
    \<Longrightarrow> case (upd_cs (a'#cs) as') 
             of [] \<Rightarrow> \<forall>c\<in>set (a'#cs). \<exists>a\<in>set as'. a \<in> get_return_edges c
          | cx#csx \<Rightarrow> valid_call_list (cx # csx) n'\<close>
  from \<open>kind a' = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close> have "upd_cs (a'#cs) as' = upd_cs cs (a'#as')"
    by simp
  from \<open>n -a'#as'\<rightarrow>* n'\<close> have [simp]:"n = sourcenode a'" and "valid_edge a'"
    and "targetnode a' -as'\<rightarrow>* n'" by(auto elim:path_split_Cons)
  from \<open>valid_edge a'\<close> \<open>kind a' = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close>
  have "get_proc (targetnode a') = p" by(rule get_proc_call)
  with \<open>valid_edge a'\<close> \<open>kind a' = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close> \<open>valid_call_list cs n\<close>
  have "valid_call_list (a'#cs) (targetnode a')"
    apply(clarsimp simp:valid_call_list_def)
    apply(case_tac cs') apply auto
    apply(erule_tac x="list" in allE) apply clarsimp
    by(case_tac list,auto simp:sourcenodes_def)
  from IH[OF this \<open>targetnode a' -as'\<rightarrow>* n'\<close>] 
    \<open>upd_cs (a'#cs) as' = upd_cs cs (a'#as')\<close>
  have "case upd_cs cs (a'#as') 
         of [] \<Rightarrow> \<forall>c\<in>set (a' # cs). \<exists>a\<in>set as'. a \<in> get_return_edges c
    | cx # csx \<Rightarrow> valid_call_list (cx # csx) n'" by simp
  thus ?case by(cases "upd_cs cs (a'#as')") simp+
next
  case (vpa_ReturnEmpty cs a' as' Q p f)
  note IH = \<open>\<And>n. \<lbrakk>valid_call_list [] n; n -as'\<rightarrow>* n'\<rbrakk>
    \<Longrightarrow> case (upd_cs [] as') 
             of [] \<Rightarrow> \<forall>c\<in>set []. \<exists>a\<in>set as'. a \<in> get_return_edges c
          | cx#csx \<Rightarrow> valid_call_list (cx # csx) n'\<close>
  from \<open>kind a' = Q\<hookleftarrow>\<^bsub>p\<^esub>f\<close> \<open>cs = []\<close> have "upd_cs [] as' = upd_cs cs (a'#as')"
    by simp
  from \<open>n -a'#as'\<rightarrow>* n'\<close> have [simp]:"n = sourcenode a'" and "valid_edge a'"
    and "targetnode a' -as'\<rightarrow>* n'" by(auto elim:path_split_Cons)
  have "valid_call_list [] (targetnode a')" by(simp add:valid_call_list_def)
  from IH[OF this \<open>targetnode a' -as'\<rightarrow>* n'\<close>]
    \<open>upd_cs [] as' = upd_cs cs (a'#as')\<close>
  have "case (upd_cs cs (a'#as')) 
         of [] \<Rightarrow> \<forall>c\<in>set []. \<exists>a\<in>set as'. a \<in> get_return_edges c
    | cx#csx \<Rightarrow> valid_call_list (cx#csx) n'" by simp
  with \<open>cs = []\<close> show ?case by(cases "upd_cs cs (a'#as')") simp+
next
  case (vpa_ReturnCons cs a' as' Q p f c' cs')
  note IH = \<open>\<And>n. \<lbrakk>valid_call_list cs' n; n -as'\<rightarrow>* n'\<rbrakk>
    \<Longrightarrow> case (upd_cs cs' as') 
             of [] \<Rightarrow> \<forall>c\<in>set cs'. \<exists>a\<in>set as'. a \<in> get_return_edges c
          | cx#csx \<Rightarrow> valid_call_list (cx # csx) n'\<close>
  from \<open>kind a' = Q\<hookleftarrow>\<^bsub>p\<^esub>f\<close> \<open>cs = c'#cs'\<close> \<open>a' \<in> get_return_edges c'\<close> 
  have "upd_cs cs' as' = upd_cs cs (a'#as')" by simp
  from \<open>n -a'#as'\<rightarrow>* n'\<close> have [simp]:"n = sourcenode a'" and "valid_edge a'"
    and "targetnode a' -as'\<rightarrow>* n'" by(auto elim:path_split_Cons)
  from \<open>valid_call_list cs n\<close> \<open>cs = c'#cs'\<close> have "valid_edge c'"
    apply(clarsimp simp:valid_call_list_def)
    by(erule_tac x="[]" in allE,auto)
  with \<open>a' \<in> get_return_edges c'\<close> obtain ax where "valid_edge ax"
    and sources:"sourcenode ax = sourcenode c'" 
    and targets:"targetnode ax = targetnode a'" and "kind ax = (\<lambda>cf. False)\<^sub>\<surd>"
    by(fastforce dest:call_return_node_edge)
  from \<open>valid_edge ax\<close> sources[THEN sym] targets[THEN sym] \<open>kind ax = (\<lambda>cf. False)\<^sub>\<surd>\<close>
  have "get_proc (sourcenode c') = get_proc (targetnode a')"
    by(fastforce intro:get_proc_intra simp:intra_kind_def)
  with \<open>valid_call_list cs n\<close> \<open>cs = c'#cs'\<close>
  have "valid_call_list cs' (targetnode a')"
    apply(clarsimp simp:valid_call_list_def)
    apply(hypsubst_thin)
    apply(erule_tac x="c'#cs'" in allE)
    by(case_tac cs',auto simp:sourcenodes_def)
  from IH[OF this \<open>targetnode a' -as'\<rightarrow>* n'\<close>] 
    \<open>upd_cs cs' as' = upd_cs cs (a'#as')\<close>
  have "case (upd_cs cs (a'#as')) 
         of [] \<Rightarrow> \<forall>c\<in>set cs'. \<exists>a\<in>set as'. a \<in> get_return_edges c
    | cx#csx \<Rightarrow> valid_call_list (cx#csx) n'" by simp
  with \<open>cs = c' # cs'\<close> \<open>a' \<in> get_return_edges c'\<close> show ?case
    by(cases "upd_cs cs (a'#as')") simp+
qed


lemma vpa_valid_call_list_valid_return_list_vpra:
  "\<lbrakk>valid_path_aux cs cs'; valid_call_list cs n; valid_return_list cs' n'\<rbrakk>
  \<Longrightarrow> valid_path_rev_aux cs' (rev cs)"
proof(induct arbitrary:n n' rule:vpa_induct)
  case (vpa_empty cs)
  from \<open>valid_call_list cs n\<close> show ?case by(rule vpra_empty_valid_call_list_rev)
next
  case (vpa_intra cs a as)
  from \<open>intra_kind (kind a)\<close> \<open>valid_return_list (a#as) n'\<close>
  have False apply(clarsimp simp:valid_return_list_def)
    by(erule_tac x="[]" in allE,clarsimp simp:intra_kind_def)
  thus ?case by simp
next
  case (vpa_Call cs a as Q r p fs)
  from \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close> \<open>valid_return_list (a#as) n'\<close>
  have False apply(clarsimp simp:valid_return_list_def)
    by(erule_tac x="[]" in allE,clarsimp)
  thus ?case by simp
next
  case (vpa_ReturnEmpty cs a as Q p f)
  from \<open>cs = []\<close> show ?case by simp
next
  case (vpa_ReturnCons cs a as Q p f c' cs')
  note IH = \<open>\<And>n n'. \<lbrakk>valid_call_list cs' n; valid_return_list as n'\<rbrakk>
    \<Longrightarrow> valid_path_rev_aux as (rev cs')\<close>
  from \<open>valid_return_list (a#as) n'\<close> have "valid_return_list as (targetnode a)"
    apply(clarsimp simp:valid_return_list_def)
    apply(erule_tac x="a#cs'" in allE)
    by(case_tac cs',auto simp:targetnodes_def)
  from \<open>valid_call_list cs n\<close> \<open>cs = c'#cs'\<close>
  have "valid_call_list cs' (sourcenode c')"
    apply(clarsimp simp:valid_call_list_def)
    apply(erule_tac x="c'#cs'" in allE)
    by(case_tac cs',auto simp:sourcenodes_def)
  from \<open>valid_call_list cs n\<close> \<open>cs = c'#cs'\<close> have "valid_edge c'"
    apply(clarsimp simp:valid_call_list_def)
    by(erule_tac x="[]" in allE,auto)
  with \<open>a \<in> get_return_edges c'\<close> obtain Q' r' p' f' where "kind c' = Q':r'\<hookrightarrow>\<^bsub>p'\<^esub>f'"
    apply(cases "kind c'" rule:edge_kind_cases)
    by(auto dest:only_call_get_return_edges simp:intra_kind_def)
  from IH[OF \<open>valid_call_list cs' (sourcenode c')\<close>
    \<open>valid_return_list as (targetnode a)\<close>]
  have "valid_path_rev_aux as (rev cs')" .
  with \<open>kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f\<close> \<open>cs = c'#cs'\<close> \<open>a \<in> get_return_edges c'\<close> \<open>kind c' = Q':r'\<hookrightarrow>\<^bsub>p'\<^esub>f'\<close>
  show ?case by simp
qed
 


lemma vpa_to_vpra:
  "\<lbrakk>valid_path_aux cs as; valid_path_aux (upd_cs cs as) cs'; 
    n -as\<rightarrow>* n'; valid_call_list cs n; valid_return_list cs' n''\<rbrakk> 
  \<Longrightarrow> valid_path_rev_aux cs' as \<and> valid_path_rev_aux (upd_rev_cs cs' as) (rev cs)"
proof(induct arbitrary:n rule:vpa_induct)
  case vpa_empty thus ?case
    by(fastforce intro:vpa_valid_call_list_valid_return_list_vpra)
next
  case (vpa_intra cs a as)
  note IH = \<open>\<And>n. \<lbrakk>valid_path_aux (upd_cs cs as) cs'; n -as\<rightarrow>* n';
    valid_call_list cs n; valid_return_list cs' n''\<rbrakk>
    \<Longrightarrow> valid_path_rev_aux cs' as \<and>
       valid_path_rev_aux (upd_rev_cs cs' as) (rev cs)\<close>
  from \<open>n -a#as\<rightarrow>* n'\<close> have "n = sourcenode a" and "valid_edge a"
    and "targetnode a -as\<rightarrow>* n'" by(auto intro:path_split_Cons)
  from \<open>valid_edge a\<close> \<open>intra_kind (kind a)\<close>
  have "get_proc (sourcenode a) = get_proc (targetnode a)" by(rule get_proc_intra)
  with \<open>valid_call_list cs n\<close> \<open>n = sourcenode a\<close>
  have "valid_call_list cs (targetnode a)"
    apply(clarsimp simp:valid_call_list_def)
    apply(erule_tac x="cs'" in allE) apply clarsimp
    by(case_tac cs') auto
  from \<open>valid_path_aux (upd_cs cs (a#as)) cs'\<close> \<open>intra_kind (kind a)\<close>
  have "valid_path_aux (upd_cs cs as) cs'"
    by(fastforce simp:intra_kind_def)
  from IH[OF this \<open>targetnode a -as\<rightarrow>* n'\<close> \<open>valid_call_list cs (targetnode a)\<close>
    \<open>valid_return_list cs' n''\<close>]
  have "valid_path_rev_aux cs' as" 
    and "valid_path_rev_aux (upd_rev_cs cs' as) (rev cs)" by simp_all
  from  \<open>intra_kind (kind a)\<close> \<open>valid_path_rev_aux cs' as\<close>
  have "valid_path_rev_aux cs' (a#as)" by(rule vpra_Cons_intra)
  from \<open>intra_kind (kind a)\<close> have "upd_rev_cs cs' (a#as) = upd_rev_cs cs' as"
    by(simp add:upd_rev_cs_Cons_intra)
  with \<open>valid_path_rev_aux (upd_rev_cs cs' as) (rev cs)\<close>
  have "valid_path_rev_aux (upd_rev_cs cs' (a#as)) (rev cs)" by simp
  with \<open>valid_path_rev_aux cs' (a#as)\<close> show ?case by simp
next
  case (vpa_Call cs a as Q r p fs)
  note IH = \<open>\<And>n. \<lbrakk>valid_path_aux (upd_cs (a#cs) as) cs'; n -as\<rightarrow>* n';
    valid_call_list (a#cs) n; valid_return_list cs' n''\<rbrakk>
    \<Longrightarrow> valid_path_rev_aux cs' as \<and>
       valid_path_rev_aux (upd_rev_cs cs' as) (rev (a#cs))\<close>
  from \<open>n -a#as\<rightarrow>* n'\<close> have "n = sourcenode a" and "valid_edge a"
    and "targetnode a -as\<rightarrow>* n'" by(auto intro:path_split_Cons)
  from \<open>valid_edge a\<close> \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close> have "p = get_proc (targetnode a)"
    by(rule get_proc_call[THEN sym])
  from \<open>valid_call_list cs n\<close> \<open>n = sourcenode a\<close>
  have "valid_call_list cs (sourcenode a)" by simp
  with \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close> \<open>valid_edge a\<close> \<open>p = get_proc (targetnode a)\<close>
  have "valid_call_list (a#cs) (targetnode a)"
    apply(clarsimp simp:valid_call_list_def)
    apply(case_tac cs') apply auto
    apply(erule_tac x="list" in allE) apply clarsimp
    by(case_tac list,auto simp:sourcenodes_def)
  from \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close> have "upd_cs cs (a#as) = upd_cs (a#cs) as"
    by simp
  with \<open>valid_path_aux (upd_cs cs (a#as)) cs'\<close>
  have "valid_path_aux (upd_cs (a#cs) as) cs'" by simp
  from IH[OF this \<open>targetnode a -as\<rightarrow>* n'\<close> \<open>valid_call_list (a#cs) (targetnode a)\<close>
    \<open>valid_return_list cs' n''\<close>]
  have "valid_path_rev_aux cs' as"
    and "valid_path_rev_aux (upd_rev_cs cs' as) (rev (a#cs))" by simp_all
  show ?case
  proof(cases "upd_rev_cs cs' as")
    case Nil
    with \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close>
    have "upd_rev_cs cs' (a#as) = []" by(rule upd_rev_cs_Cons_Call_Cons_Empty)
    with \<open>valid_path_rev_aux (upd_rev_cs cs' as) (rev (a#cs))\<close> \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close> Nil
    have "valid_path_rev_aux (upd_rev_cs cs' (a#as)) (rev cs)" by simp
    from Nil \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close> have "valid_path_rev_aux (upd_rev_cs cs' as) ([]@[a])"
      by(simp only:valid_path_rev_aux.simps) clarsimp
    with \<open>valid_path_rev_aux cs' as\<close> have "valid_path_rev_aux cs' ([a]@as)"
      by(fastforce intro:valid_path_rev_aux_Append)
    with \<open>valid_path_rev_aux (upd_rev_cs cs' (a#as)) (rev cs)\<close>
    show ?thesis by simp
  next
    case (Cons cx csx)
    with \<open>valid_path_rev_aux (upd_rev_cs cs' as) (rev (a#cs))\<close> \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close>
    have match:"cx \<in> get_return_edges a" "valid_path_rev_aux csx (rev cs)" by auto
    from \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close> Cons have "upd_rev_cs cs' (a#as) = csx"
      by(rule upd_rev_cs_Cons_Call_Cons)
    with \<open>valid_path_rev_aux (upd_rev_cs cs' as) (rev(a#cs))\<close> \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close> match
    have "valid_path_rev_aux (upd_rev_cs cs' (a#as)) (rev cs)" by simp
    from Cons \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close> match
    have "valid_path_rev_aux (upd_rev_cs cs' as) ([]@[a])"
      by(simp only:valid_path_rev_aux.simps) clarsimp
    with \<open>valid_path_rev_aux cs' as\<close> have "valid_path_rev_aux cs' ([a]@as)"
      by(fastforce intro:valid_path_rev_aux_Append)
    with \<open>valid_path_rev_aux (upd_rev_cs cs' (a#as)) (rev cs)\<close>
    show ?thesis by simp
  qed
next
  case (vpa_ReturnEmpty cs a as Q p f)
  note IH = \<open>\<And>n. \<lbrakk>valid_path_aux (upd_cs [] as) cs'; n -as\<rightarrow>* n';
    valid_call_list [] n; valid_return_list cs' n''\<rbrakk>
    \<Longrightarrow> valid_path_rev_aux cs' as \<and>
       valid_path_rev_aux (upd_rev_cs cs' as) (rev [])\<close>
  from \<open>n -a#as\<rightarrow>* n'\<close> have "n = sourcenode a" and "valid_edge a"
    and "targetnode a -as\<rightarrow>* n'" by(auto intro:path_split_Cons)
  from \<open>cs = []\<close> \<open>kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f\<close> have "upd_cs cs (a#as) = upd_cs [] as"
    by simp
  with \<open>valid_path_aux (upd_cs cs (a#as)) cs'\<close>
  have "valid_path_aux (upd_cs [] as) cs'" by simp
  from IH[OF this \<open>targetnode a -as\<rightarrow>* n'\<close> _ \<open>valid_return_list cs' n''\<close>]
  have "valid_path_rev_aux cs' as" 
    and "valid_path_rev_aux (upd_rev_cs cs' as) (rev [])" 
    by(auto simp:valid_call_list_def)
  from \<open>kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f\<close> \<open>valid_path_rev_aux cs' as\<close>
  have "valid_path_rev_aux cs' (a#as)" by(rule vpra_Cons_Return)
  moreover
  from \<open>cs = []\<close> have "valid_path_rev_aux (upd_rev_cs cs' (a#as)) (rev cs)"
    by simp
  ultimately show ?case by simp
next
  case (vpa_ReturnCons cs a as Q p f cx csx)
  note IH = \<open>\<And>n. \<lbrakk>valid_path_aux (upd_cs csx as) cs'; n -as\<rightarrow>* n';
    valid_call_list csx n; valid_return_list cs' n''\<rbrakk>
    \<Longrightarrow> valid_path_rev_aux cs' as \<and>
       valid_path_rev_aux (upd_rev_cs cs' as) (rev csx)\<close>
  note match = \<open>cs = cx#csx\<close> \<open>a \<in> get_return_edges cx\<close>
  from \<open>n -a#as\<rightarrow>* n'\<close> have "n = sourcenode a" and "valid_edge a"
    and "targetnode a -as\<rightarrow>* n'" by(auto intro:path_split_Cons)
  from \<open>cs = cx#csx\<close> \<open>valid_call_list cs n\<close> have "valid_edge cx"
    apply(clarsimp simp:valid_call_list_def)
    by(erule_tac x="[]" in allE) clarsimp
  with match have "get_proc (sourcenode cx) = get_proc (targetnode a)"
    by(fastforce intro:get_proc_get_return_edge)
  with \<open>valid_call_list cs n\<close> \<open>cs = cx#csx\<close>
  have "valid_call_list csx (targetnode a)"
    apply(clarsimp simp:valid_call_list_def)
    apply(erule_tac x="cx#cs'" in allE) apply clarsimp
    by(case_tac cs',auto simp:sourcenodes_def)
  from \<open>kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f\<close> match have "upd_cs cs (a#as) = upd_cs csx as" by simp
  with \<open>valid_path_aux (upd_cs cs (a#as)) cs'\<close>
  have "valid_path_aux (upd_cs csx as) cs'" by simp
  from IH[OF this \<open>targetnode a -as\<rightarrow>* n'\<close> \<open>valid_call_list csx (targetnode a)\<close>
    \<open>valid_return_list cs' n''\<close>]
  have "valid_path_rev_aux cs' as" 
    and "valid_path_rev_aux (upd_rev_cs cs' as) (rev csx)" by simp_all
  from \<open>kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f\<close> \<open>valid_path_rev_aux cs' as\<close>
  have "valid_path_rev_aux cs' (a#as)" by(rule vpra_Cons_Return)
  from match \<open>valid_edge cx\<close> obtain Q' r' p' f' where "kind cx = Q':r'\<hookrightarrow>\<^bsub>p'\<^esub>f'"
    by(fastforce dest!:only_call_get_return_edges)
  from \<open>kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f\<close> have "upd_rev_cs cs' (a#as) = a#(upd_rev_cs cs' as)"
    by(rule upd_rev_cs_Cons_Return)
  with \<open>valid_path_rev_aux (upd_rev_cs cs' as) (rev csx)\<close> \<open>kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f\<close> 
    \<open>kind cx = Q':r'\<hookrightarrow>\<^bsub>p'\<^esub>f'\<close> match
  have "valid_path_rev_aux (upd_rev_cs cs' (a#as)) (rev cs)"
    by simp
  with \<open>valid_path_rev_aux cs' (a#as)\<close> show ?case by simp
qed


lemma vp_to_vpra:
  "n -as\<rightarrow>\<^sub>\<surd>* n' \<Longrightarrow> valid_path_rev_aux [] as"
by(fastforce elim:vpa_to_vpra[THEN conjunct1] 
            simp:vp_def valid_path_def valid_call_list_def valid_return_list_def)




subsubsection \<open>Same level paths\<close>


fun same_level_path_aux :: "'edge list \<Rightarrow> 'edge list \<Rightarrow> bool"
  where "same_level_path_aux cs [] \<longleftrightarrow> True"
  | "same_level_path_aux cs (a#as) \<longleftrightarrow> 
       (case (kind a) of Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs \<Rightarrow> same_level_path_aux (a#cs) as
                       | Q\<hookleftarrow>\<^bsub>p\<^esub>f \<Rightarrow> case cs of [] \<Rightarrow> False
                                     | c'#cs' \<Rightarrow> a \<in> get_return_edges c' \<and>
                                             same_level_path_aux cs' as
                       |    _ \<Rightarrow> same_level_path_aux cs as)"


lemma slpa_induct [consumes 1,case_names slpa_empty slpa_intra slpa_Call 
  slpa_Return]:
  assumes major: "same_level_path_aux xs ys"
  and rules: "\<And>cs. P cs []"
    "\<And>cs a as. \<lbrakk>intra_kind(kind a); same_level_path_aux cs as; P cs as\<rbrakk> 
      \<Longrightarrow> P cs (a#as)"
    "\<And>cs a as Q r p fs. \<lbrakk>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs; same_level_path_aux (a#cs) as; P (a#cs) as\<rbrakk> 
      \<Longrightarrow> P cs (a#as)"
    "\<And>cs a as Q p f c' cs'. \<lbrakk>kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f; cs = c'#cs'; same_level_path_aux cs' as;
                             a \<in> get_return_edges c'; P cs' as\<rbrakk>
     \<Longrightarrow> P cs (a#as)"
  shows "P xs ys"
using major
apply(induct ys arbitrary: xs)
by(auto intro:rules split:edge_kind.split_asm list.split_asm simp:intra_kind_def)


lemma slpa_cases [consumes 4,case_names intra_path return_intra_path]:
  assumes "same_level_path_aux cs as" and "upd_cs cs as = []"
  and "\<forall>c \<in> set cs. valid_edge c" and "\<forall>a \<in> set as. valid_edge a"
  obtains "\<forall>a \<in> set as. intra_kind(kind a)"
  | asx a asx' Q p f c' cs' where "as = asx@a#asx'" and "same_level_path_aux cs asx"
    and "kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f" and "upd_cs cs asx = c'#cs'" and "upd_cs cs (asx@[a]) = []" 
    and "a \<in> get_return_edges c'" and "valid_edge c'"
    and "\<forall>a \<in> set asx'. intra_kind(kind a)"
proof(atomize_elim)
  from assms
  show "(\<forall>a\<in>set as. intra_kind (kind a)) \<or>
    (\<exists>asx a asx' Q p f c' cs'. as = asx@a#asx' \<and> same_level_path_aux cs asx \<and>
       kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f \<and> upd_cs cs asx = c'#cs' \<and> upd_cs cs (asx@[a]) = [] \<and> 
       a \<in> get_return_edges c' \<and> valid_edge c' \<and> (\<forall>a\<in>set asx'. intra_kind (kind a)))"
  proof(induct rule:slpa_induct)
    case (slpa_empty cs)
    have "\<forall>a\<in>set []. intra_kind (kind a)" by simp
    thus ?case by simp
  next
    case (slpa_intra cs a as)
    note IH = \<open>\<lbrakk>upd_cs cs as = []; \<forall>c\<in>set cs. valid_edge c; \<forall>a'\<in>set as. valid_edge a'\<rbrakk> 
      \<Longrightarrow> (\<forall>a\<in>set as. intra_kind (kind a)) \<or>
      (\<exists>asx a asx' Q p f c' cs'. as = asx@a#asx' \<and> same_level_path_aux cs asx \<and>
        kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f \<and>  upd_cs cs asx = c' # cs' \<and> upd_cs cs (asx@[a]) = [] \<and> 
        a \<in> get_return_edges c' \<and> valid_edge c' \<and> (\<forall>a\<in>set asx'. intra_kind (kind a)))\<close>
    from \<open>\<forall>a'\<in>set (a#as). valid_edge a'\<close> have "\<forall>a'\<in>set as. valid_edge a'" by simp
    from \<open>intra_kind (kind a)\<close> \<open>upd_cs cs (a#as) = []\<close>
    have "upd_cs cs as = []" by(fastforce simp:intra_kind_def)
    from IH[OF this \<open>\<forall>c\<in>set cs. valid_edge c\<close> \<open>\<forall>a'\<in>set as. valid_edge a'\<close>] show ?case
    proof
      assume "\<forall>a\<in>set as. intra_kind (kind a)"
      with \<open>intra_kind (kind a)\<close> have "\<forall>a'\<in>set (a#as). intra_kind (kind a')"
        by simp
      thus ?case by simp
    next
      assume "\<exists>asx a asx' Q p f c' cs'. as = asx@a#asx' \<and> same_level_path_aux cs asx \<and>
                kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f \<and> upd_cs cs asx = c'#cs' \<and> upd_cs cs (asx@[a]) = [] \<and> 
                a \<in> get_return_edges c' \<and> valid_edge c' \<and> 
                (\<forall>a\<in>set asx'. intra_kind (kind a))"
      then obtain asx a' Q p f asx' c' cs' where "as = asx@a'#asx'" 
        and "same_level_path_aux cs asx" and "upd_cs cs (asx@[a']) = []"
        and "upd_cs cs asx = c'#cs'" and assms:"a' \<in> get_return_edges c'"
        "kind a' = Q\<hookleftarrow>\<^bsub>p\<^esub>f" "valid_edge c'" "\<forall>a\<in>set asx'. intra_kind (kind a)"
        by blast
      from \<open>as = asx@a'#asx'\<close> have "a#as = (a#asx)@a'#asx'" by simp
      moreover
      from \<open>intra_kind (kind a)\<close> \<open>same_level_path_aux cs asx\<close>
      have "same_level_path_aux cs (a#asx)" by(fastforce simp:intra_kind_def)
      moreover
      from \<open>upd_cs cs asx = c'#cs'\<close> \<open>intra_kind (kind a)\<close>
      have "upd_cs cs (a#asx) = c'#cs'" by(fastforce simp:intra_kind_def)
      moreover
      from \<open>upd_cs cs (asx@[a']) = []\<close> \<open>intra_kind (kind a)\<close>
      have "upd_cs cs ((a#asx)@[a']) = []" by(fastforce simp:intra_kind_def)
      ultimately show ?case using assms by blast
    qed
  next
    case (slpa_Call cs a as Q r p fs)
    note IH = \<open>\<lbrakk>upd_cs (a#cs) as = []; \<forall>c\<in>set (a#cs). valid_edge c;
      \<forall>a'\<in>set as. valid_edge a'\<rbrakk> \<Longrightarrow> 
      (\<forall>a'\<in>set as. intra_kind (kind a')) \<or>
      (\<exists>asx a' asx' Q' p' f' c' cs'. as = asx@a'#asx' \<and> 
        same_level_path_aux (a#cs) asx \<and> kind a' = Q'\<hookleftarrow>\<^bsub>p'\<^esub>f' \<and> 
        upd_cs (a#cs) asx = c'#cs' \<and> upd_cs (a#cs) (asx@[a']) = [] \<and> 
        a' \<in> get_return_edges c' \<and> valid_edge c' \<and> 
        (\<forall>a'\<in>set asx'. intra_kind (kind a')))\<close>
    from \<open>\<forall>a'\<in>set (a#as). valid_edge a'\<close> have "valid_edge a" 
      and "\<forall>a'\<in>set as. valid_edge a'" by simp_all
    from \<open>\<forall>c\<in>set cs. valid_edge c\<close> \<open>valid_edge a\<close> have "\<forall>c\<in>set (a#cs). valid_edge c"
      by simp
    from \<open>upd_cs cs (a#as) = []\<close> \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close>
    have "upd_cs (a#cs) as = []" by simp
    from IH[OF this \<open>\<forall>c\<in>set (a#cs). valid_edge c\<close> \<open>\<forall>a'\<in>set as. valid_edge a'\<close>]
    show ?case
    proof
      assume "\<forall>a'\<in>set as. intra_kind (kind a')"
      with \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close> have "upd_cs cs (a#as) = a#cs"
        by(fastforce intro:upd_cs_intra_path)
      with \<open>upd_cs cs (a#as) = []\<close> have False by simp
      thus ?case by simp
    next
      assume "\<exists>asx a' asx' Q p f c' cs'. as = asx@a'#asx' \<and> 
                same_level_path_aux (a#cs) asx \<and> kind a' = Q\<hookleftarrow>\<^bsub>p\<^esub>f \<and> 
                upd_cs (a#cs) asx = c'#cs' \<and> upd_cs (a#cs) (asx@[a']) = [] \<and> 
                a' \<in> get_return_edges c' \<and> valid_edge c' \<and> 
                (\<forall>a\<in>set asx'. intra_kind (kind a))"
      then obtain asx a' Q' p' f' asx' c' cs' where "as = asx@a'#asx'" 
        and "same_level_path_aux (a#cs) asx" and "upd_cs (a#cs) (asx@[a']) = []"
        and "upd_cs (a#cs) asx = c'#cs'" and assms:"a' \<in> get_return_edges c'"
        "kind a' = Q'\<hookleftarrow>\<^bsub>p'\<^esub>f'" "valid_edge c'" "\<forall>a\<in>set asx'. intra_kind (kind a)"
        by blast
      from \<open>as = asx@a'#asx'\<close> have "a#as = (a#asx)@a'#asx'" by simp
      moreover
      from \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close> \<open>same_level_path_aux (a#cs) asx\<close>
      have "same_level_path_aux cs (a#asx)" by simp
      moreover
      from \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close> \<open>upd_cs (a#cs) asx = c'#cs'\<close>
      have "upd_cs cs (a#asx) = c'#cs'" by simp
      moreover
      from \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close> \<open>upd_cs (a#cs) (asx@[a']) = []\<close>
      have "upd_cs cs ((a#asx)@[a']) = []" by simp
      ultimately show ?case using assms by blast
    qed
  next
    case (slpa_Return cs a as Q p f c' cs')
    note IH = \<open>\<lbrakk>upd_cs cs' as = []; \<forall>c\<in>set cs'. valid_edge c; 
      \<forall>a'\<in>set as. valid_edge a'\<rbrakk> \<Longrightarrow> 
      (\<forall>a'\<in>set as. intra_kind (kind a')) \<or>
      (\<exists>asx a' asx' Q' p' f' c'' cs''. as = asx@a'#asx' \<and> 
        same_level_path_aux cs' asx \<and> kind a' = Q'\<hookleftarrow>\<^bsub>p'\<^esub>f' \<and> upd_cs cs' asx = c''#cs'' \<and>
        upd_cs cs' (asx@[a']) = [] \<and> a' \<in> get_return_edges c'' \<and> valid_edge c'' \<and> 
        (\<forall>a'\<in>set asx'. intra_kind (kind a')))\<close>
    from \<open>\<forall>a'\<in>set (a#as). valid_edge a'\<close> have "valid_edge a" 
      and "\<forall>a'\<in>set as. valid_edge a'" by simp_all
    from \<open>\<forall>c\<in>set cs. valid_edge c\<close> \<open>cs = c' # cs'\<close>
    have "valid_edge c'" and "\<forall>c\<in>set cs'. valid_edge c" by simp_all
    from \<open>upd_cs cs (a#as) = []\<close> \<open>kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f\<close> \<open>cs = c'#cs'\<close> 
      \<open>a \<in> get_return_edges c'\<close> have "upd_cs cs' as = []" by simp
    from IH[OF this \<open>\<forall>c\<in>set cs'. valid_edge c\<close> \<open>\<forall>a'\<in>set as. valid_edge a'\<close>] show ?case
    proof
      assume "\<forall>a'\<in>set as. intra_kind (kind a')"
      hence "upd_cs cs' as = cs'" by(rule upd_cs_intra_path)
      with \<open>upd_cs cs' as = []\<close> have "cs' = []" by simp
      with \<open>cs = c'#cs'\<close> \<open>a \<in> get_return_edges c'\<close> \<open>kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f\<close>
      have "upd_cs cs [a] = []" by simp
      moreover
      from \<open>cs = c'#cs'\<close> have "upd_cs cs [] \<noteq> []" by simp
      moreover
      have "same_level_path_aux cs []" by simp
      ultimately show ?case 
        using \<open>kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f\<close> \<open>\<forall>a'\<in>set as. intra_kind (kind a')\<close> \<open>cs = c'#cs'\<close>
          \<open>a \<in> get_return_edges c'\<close> \<open>valid_edge c'\<close>
        by fastforce
    next
      assume "\<exists>asx a' asx' Q' p' f' c'' cs''. as = asx@a'#asx' \<and>
        same_level_path_aux cs' asx \<and> kind a' = Q'\<hookleftarrow>\<^bsub>p'\<^esub>f' \<and> upd_cs cs' asx = c''#cs'' \<and>
        upd_cs cs' (asx@[a']) = [] \<and> a' \<in> get_return_edges c'' \<and> valid_edge c'' \<and>
        (\<forall>a'\<in>set asx'. intra_kind (kind a'))"
      then obtain asx a' asx' Q' p' f' c'' cs'' where "as = asx@a'#asx'"
        and "same_level_path_aux cs' asx" and "upd_cs cs' asx = c''#cs''" 
        and "upd_cs cs' (asx@[a']) = []" and assms:"a' \<in> get_return_edges c''" 
        "kind a' = Q'\<hookleftarrow>\<^bsub>p'\<^esub>f'" "valid_edge c''" "\<forall>a'\<in>set asx'. intra_kind (kind a')"
        by blast
      from \<open>as = asx@a'#asx'\<close> have "a#as = (a#asx)@a'#asx'" by simp
      moreover
      from \<open>same_level_path_aux cs' asx\<close> \<open>cs = c'#cs'\<close> \<open>a \<in> get_return_edges c'\<close>
        \<open>kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f\<close>
      have "same_level_path_aux cs (a#asx)" by simp
      moreover
      from \<open>upd_cs cs' asx = c''#cs''\<close> \<open>kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f\<close> \<open>cs = c'#cs'\<close>
      have "upd_cs cs (a#asx) = c''#cs''" by simp
      moreover
      from \<open>upd_cs cs' (asx@[a']) = []\<close> \<open>cs = c'#cs'\<close> \<open>a \<in> get_return_edges c'\<close>
        \<open>kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f\<close>
      have "upd_cs cs ((a#asx)@[a']) = []" by simp
      ultimately show ?case using assms by blast
    qed
  qed
qed


lemma same_level_path_aux_valid_path_aux: 
  "same_level_path_aux cs as \<Longrightarrow> valid_path_aux cs as"
by(induct rule:slpa_induct,auto split:edge_kind.split simp:intra_kind_def)


lemma same_level_path_aux_Append:
  "\<lbrakk>same_level_path_aux cs as; same_level_path_aux (upd_cs cs as) as'\<rbrakk>
  \<Longrightarrow> same_level_path_aux cs (as@as')"
by(induct rule:slpa_induct,auto simp:intra_kind_def)


lemma same_level_path_aux_callstack_Append:
  "same_level_path_aux cs as \<Longrightarrow> same_level_path_aux (cs@cs') as"
by(induct rule:slpa_induct,auto simp:intra_kind_def)


lemma same_level_path_upd_cs_callstack_Append:
  "\<lbrakk>same_level_path_aux cs as; upd_cs cs as = cs'\<rbrakk> 
  \<Longrightarrow> upd_cs (cs@cs'') as = (cs'@cs'')"
by(induct rule:slpa_induct,auto split:edge_kind.split simp:intra_kind_def)


lemma slpa_split:
  assumes "same_level_path_aux cs as" and "as = xs@ys" and "upd_cs cs xs = []"
  shows "same_level_path_aux cs xs" and "same_level_path_aux [] ys"
using assms
proof(induct arbitrary:xs ys rule:slpa_induct)
  case (slpa_empty cs) case 1
  from \<open>[] = xs@ys\<close> show ?case by simp
next
  case (slpa_empty cs) case 2
  from \<open>[] = xs@ys\<close> show ?case by simp
next
  case (slpa_intra cs a as)
  note IH1 = \<open>\<And>xs ys. \<lbrakk>as = xs@ys; upd_cs cs xs = []\<rbrakk> \<Longrightarrow> same_level_path_aux cs xs\<close>
  note IH2 = \<open>\<And>xs ys. \<lbrakk>as = xs@ys; upd_cs cs xs = []\<rbrakk> \<Longrightarrow> same_level_path_aux [] ys\<close>
  { case 1
    show ?case
    proof(cases xs)
      case Nil thus ?thesis by simp
    next
      case (Cons x' xs')
      with \<open>a#as = xs@ys\<close> have "a = x'" and "as = xs'@ys" by simp_all
      with \<open>upd_cs cs xs = []\<close> Cons \<open>intra_kind (kind a)\<close>
      have "upd_cs cs xs' = []" by(fastforce simp:intra_kind_def)
      from IH1[OF \<open>as = xs'@ys\<close> this] have "same_level_path_aux cs xs'" .
      with \<open>a = x'\<close> \<open>intra_kind (kind a)\<close> Cons
      show ?thesis by(fastforce simp:intra_kind_def)
    qed
  next
    case 2
    show ?case
    proof(cases xs)
      case Nil
      with \<open>upd_cs cs xs = []\<close> have "cs = []" by fastforce
      with Nil \<open>a#as = xs@ys\<close> \<open>same_level_path_aux cs as\<close> \<open>intra_kind (kind a)\<close>
      show ?thesis by(cases ys,auto simp:intra_kind_def)
    next
      case (Cons x' xs')
      with \<open>a#as = xs@ys\<close> have "a = x'" and "as = xs'@ys" by simp_all
      with \<open>upd_cs cs xs = []\<close> Cons \<open>intra_kind (kind a)\<close>
      have "upd_cs cs xs' = []" by(fastforce simp:intra_kind_def)
      from IH2[OF \<open>as = xs'@ys\<close> this] show ?thesis .
    qed
  }
next
  case (slpa_Call cs a as Q r p fs)
  note IH1 = \<open>\<And>xs ys. \<lbrakk>as = xs@ys; upd_cs (a#cs) xs = []\<rbrakk> 
    \<Longrightarrow> same_level_path_aux (a#cs) xs\<close>
  note IH2 = \<open>\<And>xs ys. \<lbrakk>as = xs@ys; upd_cs (a#cs) xs = []\<rbrakk> 
    \<Longrightarrow> same_level_path_aux [] ys\<close>
  { case 1
    show ?case
    proof(cases xs)
      case Nil thus ?thesis by simp
    next
      case (Cons x' xs')
      with \<open>a#as = xs@ys\<close> have "a = x'" and "as = xs'@ys" by simp_all
      with \<open>upd_cs cs xs = []\<close> Cons \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close>
      have "upd_cs (a#cs) xs' = []" by simp
      from IH1[OF \<open>as = xs'@ys\<close> this] have "same_level_path_aux (a#cs) xs'" .
      with \<open>a = x'\<close> \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close> Cons show ?thesis by simp
    qed
  next
    case 2
    show ?case
    proof(cases xs)
      case Nil
      with \<open>upd_cs cs xs = []\<close> have "cs = []" by fastforce
      with Nil \<open>a#as = xs@ys\<close> \<open>same_level_path_aux (a#cs) as\<close> \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close>
      show ?thesis by(cases ys) auto
    next
      case (Cons x' xs')
      with \<open>a#as = xs@ys\<close> have "a = x'" and "as = xs'@ys" by simp_all
      with \<open>upd_cs cs xs = []\<close> Cons \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close>
      have "upd_cs (a#cs) xs' = []" by simp
      from IH2[OF \<open>as = xs'@ys\<close> this] show ?thesis .
    qed
  }
next
  case (slpa_Return cs a as Q p f c' cs')
  note IH1 = \<open>\<And>xs ys. \<lbrakk>as = xs@ys; upd_cs cs' xs = []\<rbrakk> \<Longrightarrow> same_level_path_aux cs' xs\<close>
  note IH2 = \<open>\<And>xs ys. \<lbrakk>as = xs@ys; upd_cs cs' xs = []\<rbrakk> \<Longrightarrow> same_level_path_aux [] ys\<close>
  { case 1
    show ?case
    proof(cases xs)
      case Nil thus ?thesis by simp
    next
      case (Cons x' xs')
      with \<open>a#as = xs@ys\<close> have "a = x'" and "as = xs'@ys" by simp_all
      with \<open>upd_cs cs xs = []\<close> Cons \<open>kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f\<close> \<open>cs = c'#cs'\<close>
      have "upd_cs cs' xs' = []" by simp
      from IH1[OF \<open>as = xs'@ys\<close> this] have "same_level_path_aux cs' xs'" .
      with \<open>a = x'\<close> \<open>kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f\<close> \<open>cs = c'#cs'\<close> \<open>a \<in> get_return_edges c'\<close> Cons 
      show ?thesis by simp
    qed
  next
    case 2
    show ?case
    proof(cases xs)
      case Nil
      with \<open>upd_cs cs xs = []\<close> have "cs = []" by fastforce 
      with \<open>cs = c'#cs'\<close> have False by simp
      thus ?thesis by simp
    next
      case (Cons x' xs')
      with \<open>a#as = xs@ys\<close> have "a = x'" and "as = xs'@ys" by simp_all
      with \<open>upd_cs cs xs = []\<close> Cons \<open>kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f\<close> \<open>cs = c'#cs'\<close>
      have "upd_cs cs' xs' = []" by simp
      from IH2[OF \<open>as = xs'@ys\<close> this] show ?thesis .
    qed
  }
qed


lemma slpa_number_Calls_eq_number_Returns:
  "\<lbrakk>same_level_path_aux cs as; upd_cs cs as = []; 
    \<forall>a \<in> set as. valid_edge a; \<forall>c \<in> set cs. valid_edge c\<rbrakk>
  \<Longrightarrow> length [a\<leftarrow>as@cs. \<exists>Q r p fs. kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs] = 
     length [a\<leftarrow>as. \<exists>Q p f. kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f]"
apply(induct rule:slpa_induct)
by(auto split:list.split edge_kind.split intro:only_call_get_return_edges 
         simp:intra_kind_def)


lemma slpa_get_proc:
  "\<lbrakk>same_level_path_aux cs as; upd_cs cs as = []; n -as\<rightarrow>* n'; 
    \<forall>c \<in> set cs. valid_edge c\<rbrakk>
  \<Longrightarrow> (if cs = [] then get_proc n else get_proc(last(sourcenodes cs))) = get_proc n'"
proof(induct arbitrary:n rule:slpa_induct)
  case slpa_empty thus ?case by fastforce
next
  case (slpa_intra cs a as)
  note IH = \<open>\<And>n. \<lbrakk>upd_cs cs as = []; n -as\<rightarrow>* n'; \<forall>a\<in>set cs. valid_edge a\<rbrakk>
    \<Longrightarrow> (if cs = [] then get_proc n else get_proc (last (sourcenodes cs))) = 
        get_proc n'\<close>
  from \<open>intra_kind (kind a)\<close> \<open>upd_cs cs (a#as) = []\<close>
  have "upd_cs cs as = []" by(cases "kind a",auto simp:intra_kind_def)
  from \<open>n -a#as\<rightarrow>* n'\<close> have "n -[]@a#as\<rightarrow>* n'" by simp
  hence "valid_edge a" and "n = sourcenode a" and "targetnode a -as\<rightarrow>* n'"
    by(fastforce dest:path_split)+
  from \<open>valid_edge a\<close> \<open>intra_kind (kind a)\<close> \<open> n = sourcenode a\<close>
  have "get_proc n = get_proc (targetnode a)"
    by(fastforce intro:get_proc_intra)
  from IH[OF \<open>upd_cs cs as = []\<close> \<open>targetnode a -as\<rightarrow>* n'\<close> \<open>\<forall>a\<in>set cs. valid_edge a\<close>]
  have "(if cs = [] then get_proc (targetnode a) 
         else get_proc (last (sourcenodes cs))) = get_proc n'" .
  with \<open>get_proc n = get_proc (targetnode a)\<close> show ?case by auto
next
  case (slpa_Call cs a as Q r p fs)
  note IH = \<open>\<And>n. \<lbrakk>upd_cs (a#cs) as = []; n -as\<rightarrow>* n'; \<forall>a\<in>set (a#cs). valid_edge a\<rbrakk>
    \<Longrightarrow> (if a#cs = [] then get_proc n else get_proc (last (sourcenodes (a#cs)))) = 
        get_proc n'\<close>
  from \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close> \<open>upd_cs cs (a#as) = []\<close>
  have "upd_cs (a#cs) as = []" by simp
  from \<open>n -a#as\<rightarrow>* n'\<close> have "n -[]@a#as\<rightarrow>* n'" by simp
  hence "valid_edge a" and "n = sourcenode a" and "targetnode a -as\<rightarrow>* n'"
    by(fastforce dest:path_split)+
  from \<open>valid_edge a\<close> \<open>\<forall>a\<in>set cs. valid_edge a\<close> have "\<forall>a\<in>set (a#cs). valid_edge a"
    by simp
  from IH[OF \<open>upd_cs (a#cs) as = []\<close> \<open>targetnode a -as\<rightarrow>* n'\<close> this]
  have "get_proc (last (sourcenodes (a#cs))) = get_proc n'" by simp
  with \<open>n = sourcenode a\<close> show ?case by(cases cs,auto simp:sourcenodes_def)
next
  case (slpa_Return cs a as Q p f c' cs')
  note IH = \<open>\<And>n. \<lbrakk>upd_cs cs' as = []; n -as\<rightarrow>* n'; \<forall>a\<in>set cs'. valid_edge a\<rbrakk>
    \<Longrightarrow> (if cs' = [] then get_proc n else get_proc (last (sourcenodes cs'))) = 
       get_proc n'\<close>
  from \<open>\<forall>a\<in>set cs. valid_edge a\<close> \<open>cs = c'#cs'\<close>
  have "valid_edge c'" and "\<forall>a\<in>set cs'. valid_edge a" by simp_all
  from \<open>kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f\<close> \<open>upd_cs cs (a#as) = []\<close> \<open>cs = c'#cs'\<close>
  have "upd_cs cs' as = []" by simp
  from \<open>n -a#as\<rightarrow>* n'\<close> have "n -[]@a#as\<rightarrow>* n'" by simp
  hence "n = sourcenode a" and "targetnode a -as\<rightarrow>* n'"
    by(fastforce dest:path_split)+
  from \<open>valid_edge c'\<close> \<open>a \<in> get_return_edges c'\<close>
  have "get_proc (sourcenode c') = get_proc (targetnode a)"
    by(rule get_proc_get_return_edge)
  from IH[OF \<open>upd_cs cs' as = []\<close> \<open>targetnode a -as\<rightarrow>* n'\<close> \<open>\<forall>a\<in>set cs'. valid_edge a\<close>]
  have "(if cs' = [] then get_proc (targetnode a) 
         else get_proc (last (sourcenodes cs'))) = get_proc n'" .
  with \<open>cs = c'#cs'\<close> \<open>get_proc (sourcenode c') = get_proc (targetnode a)\<close>
  show ?case by(auto simp:sourcenodes_def)
qed


lemma slpa_get_return_edges:
  "\<lbrakk>same_level_path_aux cs as; cs \<noteq> []; upd_cs cs as = [];
  \<forall>xs ys. as = xs@ys \<and> ys \<noteq> [] \<longrightarrow> upd_cs cs xs \<noteq> []\<rbrakk>
  \<Longrightarrow> last as \<in> get_return_edges (last cs)"
proof(induct rule:slpa_induct)
  case (slpa_empty cs)
  from \<open>cs \<noteq> []\<close> \<open>upd_cs cs [] = []\<close> have False by fastforce
  thus ?case by simp
next
  case (slpa_intra cs a as)
  note IH = \<open>\<lbrakk>cs \<noteq> []; upd_cs cs as = []; 
              \<forall>xs ys. as = xs@ys \<and> ys \<noteq> [] \<longrightarrow> upd_cs cs xs \<noteq> []\<rbrakk>
    \<Longrightarrow> last as \<in> get_return_edges (last cs)\<close>
  show ?case
  proof(cases "as = []")
    case True
    with \<open>intra_kind (kind a)\<close> \<open>upd_cs cs (a#as) = []\<close> have "cs = []"
      by(fastforce simp:intra_kind_def)
    with \<open>cs \<noteq> []\<close> have False by simp
    thus ?thesis by simp
  next
    case False
    from \<open>intra_kind (kind a)\<close> \<open>upd_cs cs (a#as) = []\<close> have "upd_cs cs as = []"
      by(fastforce simp:intra_kind_def)
    from \<open>\<forall>xs ys. a#as = xs@ys \<and> ys \<noteq> [] \<longrightarrow> upd_cs cs xs \<noteq> []\<close> \<open>intra_kind (kind a)\<close>
    have "\<forall>xs ys. as = xs@ys \<and> ys \<noteq> [] \<longrightarrow> upd_cs cs xs \<noteq> []"
      apply(clarsimp,erule_tac x="a#xs" in allE)
      by(auto simp:intra_kind_def)
    from IH[OF \<open>cs \<noteq> []\<close> \<open>upd_cs cs as = []\<close> this] 
    have "last as \<in> get_return_edges (last cs)" .
    with False show ?thesis by simp
  qed
next
  case (slpa_Call cs a as Q r p fs)
  note IH = \<open>\<lbrakk>a#cs \<noteq> []; upd_cs (a#cs) as = [];
    \<forall>xs ys. as = xs@ys \<and> ys \<noteq> [] \<longrightarrow> upd_cs (a#cs) xs \<noteq> []\<rbrakk>
    \<Longrightarrow> last as \<in> get_return_edges (last (a#cs))\<close>
  show ?case
  proof(cases "as = []")
    case True
    with \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close> \<open>upd_cs cs (a#as) = []\<close> have "a#cs = []" by simp
    thus ?thesis by simp
  next
    case False
    from \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close> \<open>upd_cs cs (a#as) = []\<close> have "upd_cs (a#cs) as = []"
      by simp
    from \<open>\<forall>xs ys. a#as = xs@ys \<and> ys \<noteq> [] \<longrightarrow> upd_cs cs xs \<noteq> []\<close> \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close>
    have "\<forall>xs ys. as = xs@ys \<and> ys \<noteq> [] \<longrightarrow> upd_cs (a#cs) xs \<noteq> []"
      by(clarsimp,erule_tac x="a#xs" in allE,simp)
    from IH[OF _ \<open>upd_cs (a#cs) as = []\<close> this] 
    have "last as \<in> get_return_edges (last (a#cs))" by simp
    with False \<open>cs \<noteq> []\<close> show ?thesis by(simp add:targetnodes_def)
  qed
next
  case (slpa_Return cs a as Q p f c' cs')
  note IH = \<open>\<lbrakk>cs' \<noteq> []; upd_cs cs' as = []; 
    \<forall>xs ys. as = xs@ys \<and> ys \<noteq> [] \<longrightarrow> upd_cs cs' xs \<noteq> []\<rbrakk>
    \<Longrightarrow> last as \<in> get_return_edges (last cs')\<close>
  show ?case
  proof(cases "as = []")
    case True
    with \<open>kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f\<close> \<open>cs = c'#cs'\<close> \<open>upd_cs cs (a#as) = []\<close>
    have "cs' = []" by simp
    with \<open>cs = c'#cs'\<close> \<open>a \<in> get_return_edges c'\<close> True
    show ?thesis by simp
  next
    case False
    from \<open>kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f\<close> \<open>cs = c'#cs'\<close> \<open>upd_cs cs (a#as) = []\<close>
    have "upd_cs cs' as = []" by simp
    show ?thesis
    proof(cases "cs' = []")
      case True
      with \<open>cs = c'#cs'\<close> \<open>kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f\<close> have "upd_cs cs [a] = []" by simp
      with \<open>\<forall>xs ys. a#as = xs@ys \<and> ys \<noteq> [] \<longrightarrow> upd_cs cs xs \<noteq> []\<close> False have False
        apply(erule_tac x="[a]" in allE) by fastforce
      thus ?thesis by simp
    next
      case False
      from \<open>\<forall>xs ys. a#as = xs@ys \<and> ys \<noteq> [] \<longrightarrow> upd_cs cs xs \<noteq> []\<close>
        \<open>kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f\<close> \<open>cs = c'#cs'\<close>
      have "\<forall>xs ys. as = xs@ys \<and> ys \<noteq> [] \<longrightarrow> upd_cs cs' xs \<noteq> []"
        by(clarsimp,erule_tac x="a#xs" in allE,simp)
      from IH[OF False \<open>upd_cs cs' as = []\<close> this]
      have "last as \<in> get_return_edges (last cs')" .
      with \<open>as \<noteq> []\<close> False \<open>cs = c'#cs'\<close> show ?thesis by(simp add:targetnodes_def)
    qed
  qed
qed


lemma slpa_callstack_length:
  assumes "same_level_path_aux cs as" and "length cs = length cfsx"
  obtains cfx cfsx' where "transfers (kinds as) (cfsx@cf#cfs) = cfsx'@cfx#cfs"
  and "transfers (kinds as) (cfsx@cf#cfs') = cfsx'@cfx#cfs'"
  and "length cfsx' = length (upd_cs cs as)"
proof(atomize_elim)
  from assms show "\<exists>cfsx' cfx. transfers (kinds as) (cfsx@cf#cfs) = cfsx'@cfx#cfs \<and>
    transfers (kinds as) (cfsx@cf#cfs') = cfsx'@cfx#cfs' \<and>
    length cfsx' = length (upd_cs cs as)"
  proof(induct arbitrary:cfsx cf rule:slpa_induct)
    case (slpa_empty cs) thus ?case by(simp add:kinds_def)
  next
    case (slpa_intra cs a as)
    note IH = \<open>\<And>cfsx cf. length cs = length cfsx \<Longrightarrow>
      \<exists>cfsx' cfx. transfers (kinds as) (cfsx@cf#cfs) = cfsx'@cfx#cfs \<and>
                  transfers (kinds as) (cfsx@cf#cfs') = cfsx'@cfx#cfs' \<and>
                  length cfsx' = length (upd_cs cs as)\<close>
    from \<open>intra_kind (kind a)\<close> 
    have "length (upd_cs cs (a#as)) = length (upd_cs cs as)"
      by(fastforce simp:intra_kind_def)
    show ?case
    proof(cases cfsx)
      case Nil
      with \<open>length cs = length cfsx\<close> have "length cs = length []" by simp
      from Nil \<open>intra_kind (kind a)\<close> 
      obtain cfx where transfer:"transfer (kind a) (cfsx@cf#cfs) = []@cfx#cfs"
        "transfer (kind a) (cfsx@cf#cfs') = []@cfx#cfs'"
        by(cases "kind a",auto simp:kinds_def intra_kind_def)
      from IH[OF \<open>length cs = length []\<close>] obtain cfsx' cfx' 
        where "transfers (kinds as) ([]@cfx#cfs) = cfsx'@cfx'#cfs"
        and "transfers (kinds as) ([]@cfx#cfs') = cfsx'@cfx'#cfs'"
        and "length cfsx' = length (upd_cs cs as)" by blast
      with \<open>length (upd_cs cs (a#as)) = length (upd_cs cs as)\<close> transfer
      show ?thesis by(fastforce simp:kinds_def)
    next
      case (Cons x xs)
      with \<open>intra_kind (kind a)\<close> obtain cfx' 
        where transfer:"transfer (kind a) (cfsx@cf#cfs) = (cfx'#xs)@cf#cfs"
        "transfer (kind a) (cfsx@cf#cfs') = (cfx'#xs)@cf#cfs'"
        by(cases "kind a",auto simp:kinds_def intra_kind_def)
      from \<open>length cs = length cfsx\<close> Cons have "length cs = length (cfx'#xs)"
        by simp
      from IH[OF this] obtain cfs'' cf''
        where "transfers (kinds as) ((cfx'#xs)@cf#cfs) = cfs''@cf''#cfs"
        and "transfers (kinds as) ((cfx'#xs)@cf#cfs') = cfs''@cf''#cfs'"
        and "length cfs'' = length (upd_cs cs as)" by blast
      with \<open>length (upd_cs cs (a#as)) = length (upd_cs cs as)\<close> transfer
      show ?thesis by(fastforce simp:kinds_def)
    qed
  next
    case (slpa_Call cs a as Q r p fs)
    note IH = \<open>\<And>cfsx cf. length (a#cs) = length cfsx \<Longrightarrow>
      \<exists>cfsx' cfx. transfers (kinds as) (cfsx@cf#cfs) = cfsx'@cfx#cfs \<and>
                  transfers (kinds as) (cfsx@cf#cfs') = cfsx'@cfx#cfs' \<and>
                  length cfsx' = length (upd_cs (a#cs) as)\<close>
    from \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close>
    obtain cfx where transfer:"transfer (kind a) (cfsx@cf#cfs) = (cfx#cfsx)@cf#cfs"
      "transfer (kind a) (cfsx@cf#cfs') = (cfx#cfsx)@cf#cfs'"
      by(cases cfsx) auto
    from \<open>length cs = length cfsx\<close> have "length (a#cs) = length (cfx#cfsx)"
      by simp
    from IH[OF this] obtain cfsx' cfx' 
      where "transfers (kinds as) ((cfx#cfsx)@cf#cfs) = cfsx'@cfx'#cfs"
      and "transfers (kinds as) ((cfx#cfsx)@cf#cfs') = cfsx'@cfx'#cfs'"
      and "length cfsx' = length (upd_cs (a#cs) as)" by blast
    with \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close> transfer show ?case by(fastforce simp:kinds_def)
  next
     case (slpa_Return cs a as Q p f c' cs')
     note IH = \<open>\<And>cfsx cf. length cs' = length cfsx \<Longrightarrow>
       \<exists>cfsx' cfx. transfers (kinds as) (cfsx@cf#cfs) = cfsx'@cfx#cfs \<and>
                   transfers (kinds as) (cfsx@cf#cfs') = cfsx'@cfx#cfs' \<and>
                   length cfsx' = length (upd_cs cs' as)\<close>
     from \<open>kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f\<close> \<open>cs = c'#cs'\<close>
     have "length (upd_cs cs (a#as)) = length (upd_cs cs' as)" by simp
     show ?case
     proof(cases cs')
       case Nil
       with \<open>cs = c'#cs'\<close> \<open>length cs = length cfsx\<close> obtain cfx
         where [simp]:"cfsx = [cfx]" by(cases cfsx) auto
       with \<open>kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f\<close> obtain cf' 
         where transfer:"transfer (kind a) (cfsx@cf#cfs) = []@cf'#cfs"
         "transfer (kind a) (cfsx@cf#cfs') = []@cf'#cfs'"
         by fastforce
       from Nil have "length cs' = length []" by simp
       from IH[OF this] obtain cfsx' cfx' 
         where "transfers (kinds as) ([]@cf'#cfs) = cfsx'@cfx'#cfs"
         and "transfers (kinds as) ([]@cf'#cfs') = cfsx'@cfx'#cfs'"
         and "length cfsx' = length (upd_cs cs' as)" by blast
       with \<open>length (upd_cs cs (a#as)) = length (upd_cs cs' as)\<close> transfer
       show ?thesis by(fastforce simp:kinds_def)
    next
      case (Cons cx csx)
      with \<open>cs = c'#cs'\<close> \<open>length cs = length cfsx\<close> obtain x x' xs
        where [simp]:"cfsx = x#x'#xs" and "length xs = length csx"
        by(cases cfsx,auto,case_tac list,fastforce+)
      with \<open>kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f\<close> obtain cf' 
        where transfer:"transfer (kind a) ((x#x'#xs)@cf#cfs) = (cf'#xs)@cf#cfs"
        "transfer (kind a) ((x#x'#xs)@cf#cfs') = (cf'#xs)@cf#cfs'"
        by fastforce
      from \<open>cs = c'#cs'\<close> \<open>length cs = length cfsx\<close> have "length cs' = length (cf'#xs)"
        by simp
      from IH[OF this] obtain cfsx' cfx 
        where "transfers (kinds as) ((cf'#xs)@cf#cfs) = cfsx'@cfx#cfs"
        and "transfers (kinds as) ((cf'#xs)@cf#cfs') = cfsx'@cfx#cfs'"
        and "length cfsx' = length (upd_cs cs' as)" by blast
      with \<open>length (upd_cs cs (a#as)) = length (upd_cs cs' as)\<close> transfer
      show ?thesis by(fastforce simp:kinds_def)
    qed
  qed
qed


lemma slpa_snoc_intra:
  "\<lbrakk>same_level_path_aux cs as; intra_kind (kind a)\<rbrakk> 
  \<Longrightarrow> same_level_path_aux cs (as@[a])"
by(induct rule:slpa_induct,auto simp:intra_kind_def)


lemma slpa_snoc_Call:
  "\<lbrakk>same_level_path_aux cs as; kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<rbrakk>
  \<Longrightarrow> same_level_path_aux cs (as@[a])"
by(induct rule:slpa_induct,auto simp:intra_kind_def)


lemma vpa_Main_slpa:
  "\<lbrakk>valid_path_aux cs as; m -as\<rightarrow>* m'; as \<noteq> []; 
    valid_call_list cs m; get_proc m' = Main;
    get_proc (case cs of [] \<Rightarrow> m | _ \<Rightarrow> sourcenode (last cs)) = Main\<rbrakk>
  \<Longrightarrow> same_level_path_aux cs as \<and> upd_cs cs as = []"
proof(induct arbitrary:m rule:vpa_induct)
  case (vpa_empty cs) thus ?case by simp
next
  case (vpa_intra cs a as)
  note IH = \<open>\<And>m. \<lbrakk>m -as\<rightarrow>* m'; as \<noteq> []; valid_call_list cs m; get_proc m' = Main;
    get_proc (case cs of [] \<Rightarrow> m | a # list \<Rightarrow> sourcenode (last cs)) = Main\<rbrakk>
    \<Longrightarrow> same_level_path_aux cs as \<and> upd_cs cs as = []\<close>
  from \<open>m -a # as\<rightarrow>* m'\<close> have "sourcenode a = m" and "valid_edge a"
    and "targetnode a -as\<rightarrow>* m'" by(auto elim:path_split_Cons)
  from \<open>valid_edge a\<close> \<open>intra_kind (kind a)\<close> 
  have "get_proc (sourcenode a) = get_proc (targetnode a)" by(rule get_proc_intra)
  show ?case
  proof(cases "as = []")
    case True
    with \<open>targetnode a -as\<rightarrow>* m'\<close> have "targetnode a = m'" by fastforce
    with \<open>get_proc (sourcenode a) = get_proc (targetnode a)\<close> 
      \<open>sourcenode a = m\<close> \<open>get_proc m' = Main\<close>
    have "get_proc m = Main" by simp
    have "cs = []"
    proof(cases cs)
      case Cons
      with \<open>valid_call_list cs m\<close>
      obtain c Q r p fs where "valid_edge c" and "kind c = Q:r\<hookrightarrow>\<^bsub>get_proc m\<^esub>fs"
        by(auto simp:valid_call_list_def,erule_tac x="[]" in allE,
           auto simp:sourcenodes_def)
      with \<open>get_proc m = Main\<close> have "kind c = Q:r\<hookrightarrow>\<^bsub>Main\<^esub>fs" by simp
      with \<open>valid_edge c\<close> have False by(rule Main_no_call_target)
      thus ?thesis by simp
    qed simp
    with True \<open>intra_kind (kind a)\<close> show ?thesis by(fastforce simp:intra_kind_def)
  next
    case False
    from \<open>valid_call_list cs m\<close> \<open>sourcenode a = m\<close>
      \<open>get_proc (sourcenode a) = get_proc (targetnode a)\<close>
    have "valid_call_list cs (targetnode a)"
      apply(clarsimp simp:valid_call_list_def)
      apply(erule_tac x="cs'" in allE)
      apply(erule_tac x="c" in allE)
      by(auto split:list.split)
    from \<open>get_proc (case cs of [] \<Rightarrow> m | _ \<Rightarrow> sourcenode (last cs)) = Main\<close>
      \<open>sourcenode a = m\<close> \<open>get_proc (sourcenode a) = get_proc (targetnode a)\<close>
    have "get_proc (case cs of [] \<Rightarrow> targetnode a | _ \<Rightarrow> sourcenode (last cs)) = Main"
      by(cases cs) auto
    from IH[OF \<open>targetnode a -as\<rightarrow>* m'\<close> False \<open>valid_call_list cs (targetnode a)\<close>
      \<open>get_proc m' = Main\<close> this]
    have "same_level_path_aux cs as \<and> upd_cs cs as = []" .
    with \<open>intra_kind (kind a)\<close> show ?thesis by(fastforce simp:intra_kind_def)
  qed
next
  case (vpa_Call cs a as Q r p fs)
  note IH = \<open>\<And>m. \<lbrakk>m -as\<rightarrow>* m'; as \<noteq> []; valid_call_list (a # cs) m; 
    get_proc m' = Main; 
    get_proc (case a # cs of [] \<Rightarrow> m | _ \<Rightarrow> sourcenode (last (a # cs))) = Main\<rbrakk>
    \<Longrightarrow> same_level_path_aux (a # cs) as \<and> upd_cs (a # cs) as = []\<close>
  from \<open>m -a # as\<rightarrow>* m'\<close> have "sourcenode a = m" and "valid_edge a"
    and "targetnode a -as\<rightarrow>* m'" by(auto elim:path_split_Cons)
  from \<open>valid_edge a\<close> \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close> have "get_proc (targetnode a) = p"
    by(rule get_proc_call)
  show ?case
  proof(cases "as = []")
    case True
    with \<open>targetnode a -as\<rightarrow>* m'\<close> have "targetnode a = m'" by fastforce
    with \<open>get_proc (targetnode a) = p\<close> \<open>get_proc m' = Main\<close> \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close>
    have "kind a = Q:r\<hookrightarrow>\<^bsub>Main\<^esub>fs" by simp
    with \<open>valid_edge a\<close> have False by(rule Main_no_call_target)
    thus ?thesis by simp
  next
    case False
    from \<open>get_proc (targetnode a) = p\<close> \<open>valid_call_list cs m\<close> \<open>valid_edge a\<close>
      \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close> \<open>sourcenode a = m\<close>
    have "valid_call_list (a # cs) (targetnode a)"
      apply(clarsimp simp:valid_call_list_def)
      apply(case_tac cs') apply auto
      apply(erule_tac x="list" in allE)
      by(case_tac list)(auto simp:sourcenodes_def)
    from \<open>get_proc (case cs of [] \<Rightarrow> m | _ \<Rightarrow> sourcenode (last cs)) = Main\<close>
      \<open>sourcenode a = m\<close>
    have "get_proc (case a # cs of [] \<Rightarrow> targetnode a 
      | _ \<Rightarrow> sourcenode (last (a # cs))) = Main"
      by(cases cs) auto
    from IH[OF \<open>targetnode a -as\<rightarrow>* m'\<close> False \<open>valid_call_list (a#cs) (targetnode a)\<close>
      \<open>get_proc m' = Main\<close> this]
    have "same_level_path_aux (a # cs) as \<and> upd_cs (a # cs) as = []" .
    with \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close> show ?thesis by simp
  qed
next
  case (vpa_ReturnEmpty cs a as Q p f)
  note IH = \<open>\<And>m. \<lbrakk>m -as\<rightarrow>* m'; as \<noteq> []; valid_call_list [] m; get_proc m' = Main;
    get_proc (case [] of [] \<Rightarrow> m | a # list \<Rightarrow> sourcenode (last [])) = Main\<rbrakk>
    \<Longrightarrow> same_level_path_aux [] as \<and> upd_cs [] as = []\<close>
  from \<open>m -a # as\<rightarrow>* m'\<close> have "sourcenode a = m" and "valid_edge a"
    and "targetnode a -as\<rightarrow>* m'" by(auto elim:path_split_Cons)
  from \<open>valid_edge a\<close> \<open>kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f\<close> have "get_proc (sourcenode a) = p" 
    by(rule get_proc_return)
  from \<open>get_proc (case cs of [] \<Rightarrow> m | a # list \<Rightarrow> sourcenode (last cs)) = Main\<close>
    \<open>cs = []\<close>
  have "get_proc m = Main" by simp
  with \<open>sourcenode a = m\<close> \<open>get_proc (sourcenode a) = p\<close> have "p = Main" by simp
  with \<open>kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f\<close> have "kind a = Q\<hookleftarrow>\<^bsub>Main\<^esub>f" by simp
  with \<open>valid_edge a\<close> have False by(rule Main_no_return_source)
  thus ?case by simp
next
  case (vpa_ReturnCons cs a as Q p f c' cs')
  note IH = \<open>\<And>m. \<lbrakk>m -as\<rightarrow>* m'; as \<noteq> []; valid_call_list cs' m; get_proc m' = Main;
    get_proc (case cs' of [] \<Rightarrow> m | a # list \<Rightarrow> sourcenode (last cs')) = Main\<rbrakk>
    \<Longrightarrow> same_level_path_aux cs' as \<and> upd_cs cs' as = []\<close>
  from \<open>m -a # as\<rightarrow>* m'\<close> have "sourcenode a = m" and "valid_edge a"
    and "targetnode a -as\<rightarrow>* m'" by(auto elim:path_split_Cons)
  from \<open>valid_edge a\<close> \<open>kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f\<close> have "get_proc (sourcenode a) = p" 
    by(rule get_proc_return)
  from \<open>valid_call_list cs m\<close> \<open>cs = c' # cs'\<close>
  have "valid_edge c'" 
    by(auto simp:valid_call_list_def,erule_tac x="[]" in allE,auto)
  from \<open>valid_edge c'\<close> \<open>a \<in> get_return_edges c'\<close>
  have "get_proc (sourcenode c') = get_proc (targetnode a)"
    by(rule get_proc_get_return_edge)
  show ?case
  proof(cases "as = []")
    case True
    with \<open>targetnode a -as\<rightarrow>* m'\<close> have "targetnode a = m'" by fastforce
    with \<open>get_proc m' = Main\<close> have "get_proc (targetnode a) = Main" by simp
    from \<open>get_proc (sourcenode c') = get_proc (targetnode a)\<close>
      \<open>get_proc (targetnode a) = Main\<close>
    have "get_proc (sourcenode c') = Main" by simp
    have "cs' = []"
    proof(cases cs')
      case (Cons cx csx)
      with \<open>cs = c' # cs'\<close> \<open>valid_call_list cs m\<close>
      obtain Qx rx fsx where "valid_edge cx" 
        and "kind cx = Qx:rx\<hookrightarrow>\<^bsub>get_proc (sourcenode c')\<^esub>fsx"
        by(auto simp:valid_call_list_def,erule_tac x="[c']" in allE,
           auto simp:sourcenodes_def)
      with \<open>get_proc (sourcenode c') = Main\<close> have "kind cx = Qx:rx\<hookrightarrow>\<^bsub>Main\<^esub>fsx" by simp
      with \<open>valid_edge cx\<close> have False by(rule Main_no_call_target)
      thus ?thesis by simp
    qed simp
    with True \<open>cs = c' # cs'\<close> \<open>a \<in> get_return_edges c'\<close> \<open>kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f\<close>
    show ?thesis by simp
  next
    case False
    from \<open>valid_call_list cs m\<close> \<open>cs = c' # cs'\<close>
      \<open>get_proc (sourcenode c') = get_proc (targetnode a)\<close>
    have "valid_call_list cs' (targetnode a)"
      apply(clarsimp simp:valid_call_list_def)
      apply(hypsubst_thin)
      apply(erule_tac x="c' # cs'" in allE)
      by(case_tac cs')(auto simp:sourcenodes_def)
    from \<open>get_proc (case cs of [] \<Rightarrow> m | a # list \<Rightarrow> sourcenode (last cs)) = Main\<close>
      \<open>cs = c' # cs'\<close> \<open>get_proc (sourcenode c') = get_proc (targetnode a)\<close>
    have "get_proc (case cs' of [] \<Rightarrow> targetnode a 
      | _ \<Rightarrow> sourcenode (last cs')) = Main"
      by(cases cs') auto
    from IH[OF \<open>targetnode a -as\<rightarrow>* m'\<close> False \<open>valid_call_list cs' (targetnode a)\<close>
      \<open>get_proc m' = Main\<close> this]
    have "same_level_path_aux cs' as \<and> upd_cs cs' as = []" .
    with \<open>kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f\<close> \<open>cs = c' # cs'\<close> \<open>a \<in> get_return_edges c'\<close>
    show ?thesis by simp
  qed
qed



definition same_level_path :: "'edge list \<Rightarrow> bool"
  where "same_level_path as \<equiv> same_level_path_aux [] as \<and> upd_cs [] as = []"


lemma same_level_path_valid_path:
  "same_level_path as \<Longrightarrow> valid_path as"
by(fastforce intro:same_level_path_aux_valid_path_aux
             simp:same_level_path_def valid_path_def)


lemma same_level_path_Append:
  "\<lbrakk>same_level_path as; same_level_path as'\<rbrakk> \<Longrightarrow> same_level_path (as@as')"
by(fastforce elim:same_level_path_aux_Append upd_cs_Append simp:same_level_path_def)


lemma same_level_path_number_Calls_eq_number_Returns:
  "\<lbrakk>same_level_path as; \<forall>a \<in> set as. valid_edge a\<rbrakk> \<Longrightarrow> 
  length [a\<leftarrow>as. \<exists>Q r p fs. kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs] = length [a\<leftarrow>as. \<exists>Q p f. kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f]"
by(fastforce dest:slpa_number_Calls_eq_number_Returns simp:same_level_path_def)


lemma same_level_path_valid_path_Append:
  "\<lbrakk>same_level_path as; valid_path as'\<rbrakk> \<Longrightarrow> valid_path (as@as')"
  by(fastforce intro:valid_path_aux_Append elim:same_level_path_aux_valid_path_aux
               simp:valid_path_def same_level_path_def)

lemma valid_path_same_level_path_Append:
  "\<lbrakk>valid_path as; same_level_path as'\<rbrakk> \<Longrightarrow> valid_path (as@as')"
  apply(auto simp:valid_path_def same_level_path_def)
  apply(erule valid_path_aux_Append)
  by(fastforce intro!:same_level_path_aux_valid_path_aux 
                dest:same_level_path_aux_callstack_Append)

lemma intras_same_level_path:
  assumes "\<forall>a \<in> set as. intra_kind(kind a)" shows "same_level_path as"
proof -
  from \<open>\<forall>a \<in> set as. intra_kind(kind a)\<close> have "same_level_path_aux [] as"
    by(induct as)(auto simp:intra_kind_def)
  moreover
  from \<open>\<forall>a \<in> set as. intra_kind(kind a)\<close> have "upd_cs [] as = []"
    by(induct as)(auto simp:intra_kind_def)
  ultimately show ?thesis by(simp add:same_level_path_def)
qed


definition same_level_path' :: "'node \<Rightarrow> 'edge list \<Rightarrow> 'node \<Rightarrow> bool" 
  ("_ -_\<rightarrow>\<^bsub>sl\<^esub>* _" [51,0,0] 80)
where slp_def:"n -as\<rightarrow>\<^bsub>sl\<^esub>* n' \<equiv> n -as\<rightarrow>* n' \<and> same_level_path as"

lemma slp_vp: "n -as\<rightarrow>\<^bsub>sl\<^esub>* n' \<Longrightarrow> n -as\<rightarrow>\<^sub>\<surd>* n'"
by(fastforce intro:same_level_path_valid_path simp:slp_def vp_def)


lemma intra_path_slp: "n -as\<rightarrow>\<^sub>\<iota>* n' \<Longrightarrow> n -as\<rightarrow>\<^bsub>sl\<^esub>* n'"
by(fastforce intro:intras_same_level_path simp:slp_def intra_path_def)


lemma slp_Append:
  "\<lbrakk>n -as\<rightarrow>\<^bsub>sl\<^esub>* n''; n'' -as'\<rightarrow>\<^bsub>sl\<^esub>* n'\<rbrakk> \<Longrightarrow> n -as@as'\<rightarrow>\<^bsub>sl\<^esub>* n'"
  by(fastforce simp:slp_def intro:path_Append same_level_path_Append)


lemma slp_vp_Append:
  "\<lbrakk>n -as\<rightarrow>\<^bsub>sl\<^esub>* n''; n'' -as'\<rightarrow>\<^sub>\<surd>* n'\<rbrakk> \<Longrightarrow> n -as@as'\<rightarrow>\<^sub>\<surd>* n'"
  by(fastforce simp:slp_def vp_def intro:path_Append same_level_path_valid_path_Append)


lemma vp_slp_Append:
  "\<lbrakk>n -as\<rightarrow>\<^sub>\<surd>* n''; n'' -as'\<rightarrow>\<^bsub>sl\<^esub>* n'\<rbrakk> \<Longrightarrow> n -as@as'\<rightarrow>\<^sub>\<surd>* n'"
  by(fastforce simp:slp_def vp_def intro:path_Append valid_path_same_level_path_Append)


lemma slp_get_proc:
  "n -as\<rightarrow>\<^bsub>sl\<^esub>* n' \<Longrightarrow> get_proc n = get_proc n'"
by(fastforce dest:slpa_get_proc simp:same_level_path_def slp_def)


lemma same_level_path_inner_path:
  assumes "n -as\<rightarrow>\<^bsub>sl\<^esub>* n'"
  obtains as' where "n -as'\<rightarrow>\<^sub>\<iota>* n'" and "set(sourcenodes as') \<subseteq> set(sourcenodes as)"
proof(atomize_elim)
  from \<open>n -as\<rightarrow>\<^bsub>sl\<^esub>* n'\<close> have "n -as\<rightarrow>* n'" and "same_level_path as"
    by(simp_all add:slp_def)
  from \<open>same_level_path as\<close> have "same_level_path_aux [] as" and "upd_cs [] as = []"
    by(simp_all add:same_level_path_def)
  from \<open>n -as\<rightarrow>* n'\<close> \<open>same_level_path_aux [] as\<close> \<open>upd_cs [] as = []\<close>
  show "\<exists>as'. n -as'\<rightarrow>\<^sub>\<iota>* n' \<and> set(sourcenodes as') \<subseteq> set(sourcenodes as)"
  proof(induct as arbitrary:n rule:length_induct)
    fix as n
    assume IH:"\<forall>as''. length as'' < length as \<longrightarrow>
      (\<forall>n''. n'' -as''\<rightarrow>* n' \<longrightarrow> same_level_path_aux [] as'' \<longrightarrow>
           upd_cs [] as'' = [] \<longrightarrow>
           (\<exists>as'. n'' -as'\<rightarrow>\<^sub>\<iota>* n' \<and> set (sourcenodes as') \<subseteq> set (sourcenodes as'')))"
      and "n -as\<rightarrow>* n'" and "same_level_path_aux [] as" and "upd_cs [] as = []"
    show "\<exists>as'. n -as'\<rightarrow>\<^sub>\<iota>* n' \<and> set (sourcenodes as') \<subseteq> set (sourcenodes as)"
    proof(cases as)
      case Nil
      with \<open>n -as\<rightarrow>* n'\<close> show ?thesis by(fastforce simp:intra_path_def)
    next
      case (Cons a' as')
      with \<open>n -as\<rightarrow>* n'\<close> Cons have "n = sourcenode a'" and "valid_edge a'" 
        and "targetnode a' -as'\<rightarrow>* n'"
        by(auto intro:path_split_Cons)
      show ?thesis
      proof(cases "kind a'" rule:edge_kind_cases)
        case Intra
        with Cons \<open>same_level_path_aux [] as\<close> have "same_level_path_aux [] as'"
          by(fastforce simp:intra_kind_def)
        moreover
        from Intra Cons \<open>upd_cs [] as = []\<close> have "upd_cs [] as' = []"
          by(fastforce simp:intra_kind_def)
        ultimately obtain as'' where "targetnode a' -as''\<rightarrow>\<^sub>\<iota>* n'"
          and "set (sourcenodes as'') \<subseteq> set (sourcenodes as')"
          using IH Cons \<open>targetnode a' -as'\<rightarrow>* n'\<close>
          by(erule_tac x="as'" in allE) auto
        from \<open>n = sourcenode a'\<close> \<open>valid_edge a'\<close> Intra \<open>targetnode a' -as''\<rightarrow>\<^sub>\<iota>* n'\<close>
        have "n -a'#as''\<rightarrow>\<^sub>\<iota>* n'" by(fastforce intro:Cons_path simp:intra_path_def)
        with \<open>set (sourcenodes as'') \<subseteq> set (sourcenodes as')\<close> Cons show ?thesis
          by(rule_tac x="a'#as''" in exI,auto simp:sourcenodes_def)
      next
        case (Call Q p f)
        with Cons \<open>same_level_path_aux [] as\<close>
        have "same_level_path_aux [a'] as'" by simp
        from Call Cons \<open>upd_cs [] as = []\<close> have "upd_cs [a'] as' = []" by simp
        hence "as' \<noteq> []" by fastforce
        with \<open>upd_cs [a'] as' = []\<close> obtain xs ys where "as' = xs@ys" and "xs \<noteq> []"
        and "upd_cs [a'] xs = []" and "upd_cs [] ys = []"
        and "\<forall>xs' ys'. xs = xs'@ys' \<and> ys' \<noteq> [] \<longrightarrow> upd_cs [a'] xs' \<noteq> []"
          by -(erule upd_cs_empty_split,auto)
        from \<open>same_level_path_aux [a'] as'\<close> \<open>as' = xs@ys\<close> \<open>upd_cs [a'] xs = []\<close>
        have "same_level_path_aux [a'] xs" and "same_level_path_aux [] ys"
          by(auto intro:slpa_split)
        from \<open>same_level_path_aux [a'] xs\<close> \<open>upd_cs [a'] xs = []\<close>
          \<open>\<forall>xs' ys'. xs = xs'@ys' \<and> ys' \<noteq> [] \<longrightarrow> upd_cs [a'] xs' \<noteq> []\<close>
        have "last xs \<in> get_return_edges (last [a'])"
          by(fastforce intro!:slpa_get_return_edges)
        with \<open>valid_edge a'\<close> Call
        obtain a where "valid_edge a" and "sourcenode a = sourcenode a'"
          and "targetnode a = targetnode (last xs)" and "kind a = (\<lambda>cf. False)\<^sub>\<surd>"
          by -(drule call_return_node_edge,auto)
        from \<open>targetnode a = targetnode (last xs)\<close> \<open>xs \<noteq> []\<close>
        have "targetnode a = targetnode (last (a'#xs))" by simp
        from \<open>as' = xs@ys\<close> \<open>xs \<noteq> []\<close> Cons have "length ys < length as" by simp
        from \<open>targetnode a' -as'\<rightarrow>* n'\<close> \<open>as' = xs@ys\<close> \<open>xs \<noteq> []\<close>
        have "targetnode (last (a'#xs)) -ys\<rightarrow>* n'"
          by(cases xs rule:rev_cases,auto dest:path_split)
        with IH \<open>length ys < length as\<close> \<open>same_level_path_aux [] ys\<close>
          \<open>upd_cs [] ys = []\<close>
        obtain as'' where "targetnode (last (a'#xs)) -as''\<rightarrow>\<^sub>\<iota>* n'"
          and "set(sourcenodes as'') \<subseteq> set(sourcenodes ys)"
          apply(erule_tac x="ys" in allE) apply clarsimp
          apply(erule_tac x="targetnode (last (a'#xs))" in allE) 
          by clarsimp
        from \<open>sourcenode a = sourcenode a'\<close> \<open>n = sourcenode a'\<close>
          \<open>targetnode a = targetnode (last (a'#xs))\<close> \<open>valid_edge a\<close>
          \<open>kind a = (\<lambda>cf. False)\<^sub>\<surd>\<close> \<open>targetnode (last (a'#xs)) -as''\<rightarrow>\<^sub>\<iota>* n'\<close>
        have "n -a#as''\<rightarrow>\<^sub>\<iota>* n'"
          by(fastforce intro:Cons_path simp:intra_path_def intra_kind_def)
        moreover
        from \<open>set(sourcenodes as'') \<subseteq> set(sourcenodes ys)\<close> Cons \<open>as' = xs@ys\<close>
          \<open>sourcenode a = sourcenode a'\<close>
        have "set(sourcenodes (a#as'')) \<subseteq> set(sourcenodes as)"
          by(auto simp:sourcenodes_def)
        ultimately show ?thesis by blast
      next
        case (Return Q p f)
        with Cons \<open>same_level_path_aux [] as\<close> have False by simp
        thus ?thesis by simp
      qed
    qed
  qed
qed


lemma slp_callstack_length_equal:
  assumes "n -as\<rightarrow>\<^bsub>sl\<^esub>* n'" obtains cf' where "transfers (kinds as) (cf#cfs) = cf'#cfs"
  and "transfers (kinds as) (cf#cfs') = cf'#cfs'"
proof(atomize_elim)
  from \<open>n -as\<rightarrow>\<^bsub>sl\<^esub>* n'\<close> have "same_level_path_aux [] as" and "upd_cs [] as = []"
    by(simp_all add:slp_def same_level_path_def)
  then obtain cfx cfsx where "transfers (kinds as) (cf#cfs) = cfsx@cfx#cfs"
    and "transfers (kinds as) (cf#cfs') = cfsx@cfx#cfs'"
    and "length cfsx = length (upd_cs [] as)"
    by(fastforce elim:slpa_callstack_length)
  with \<open>upd_cs [] as = []\<close> have "cfsx = []" by(cases cfsx) auto
  with \<open>transfers (kinds as) (cf#cfs) = cfsx@cfx#cfs\<close>
    \<open>transfers (kinds as) (cf#cfs') = cfsx@cfx#cfs'\<close>
  show "\<exists>cf'. transfers (kinds as) (cf#cfs) = cf'#cfs \<and> 
    transfers (kinds as) (cf#cfs') = cf'#cfs'" by fastforce
qed


lemma slp_cases [consumes 1,case_names intra_path return_intra_path]:
  assumes "m -as\<rightarrow>\<^bsub>sl\<^esub>* m'"
  obtains "m -as\<rightarrow>\<^sub>\<iota>* m'"
  | as' a as'' Q p f where "as = as'@a#as''" and "kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f"
  and "m -as'@[a]\<rightarrow>\<^bsub>sl\<^esub>* targetnode a" and "targetnode a -as''\<rightarrow>\<^sub>\<iota>* m'"
proof(atomize_elim)
  from \<open>m -as\<rightarrow>\<^bsub>sl\<^esub>* m'\<close> have "m -as\<rightarrow>* m'" and "same_level_path_aux [] as"
    and "upd_cs [] as = []" by(simp_all add:slp_def same_level_path_def)
  from \<open>m -as\<rightarrow>* m'\<close> have "\<forall>a \<in> set as. valid_edge a" by(rule path_valid_edges)
  have "\<forall>a \<in> set []. valid_edge a" by simp
  with \<open>same_level_path_aux [] as\<close> \<open>upd_cs [] as = []\<close> \<open>\<forall>a \<in> set []. valid_edge a\<close>
    \<open>\<forall>a \<in> set as. valid_edge a\<close>
  show "m -as\<rightarrow>\<^sub>\<iota>* m' \<or>
    (\<exists>as' a as'' Q p f. as = as' @ a # as'' \<and> kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f \<and>
    m -as' @ [a]\<rightarrow>\<^bsub>sl\<^esub>* targetnode a \<and> targetnode a -as''\<rightarrow>\<^sub>\<iota>* m')"
  proof(cases rule:slpa_cases)
    case intra_path
    with \<open>m -as\<rightarrow>* m'\<close> have "m -as\<rightarrow>\<^sub>\<iota>* m'" by(simp add:intra_path_def)
    thus ?thesis by blast
  next
    case (return_intra_path as' a as'' Q p f c' cs')
    from \<open>m -as\<rightarrow>* m'\<close> \<open>as = as' @ a # as''\<close>
    have "m -as'\<rightarrow>* sourcenode a" and "valid_edge a" and "targetnode a -as''\<rightarrow>* m'"
      by(auto intro:path_split)
    from \<open>m -as'\<rightarrow>* sourcenode a\<close> \<open>valid_edge a\<close>
    have "m -as'@[a]\<rightarrow>* targetnode a" by(fastforce intro:path_Append path_edge)
    with \<open>same_level_path_aux [] as'\<close> \<open>upd_cs [] as' = c' # cs'\<close> \<open>kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f\<close>
      \<open>a \<in> get_return_edges c'\<close>
    have "same_level_path_aux [] (as'@[a])"
      by(fastforce intro:same_level_path_aux_Append)
    with \<open>upd_cs [] (as' @ [a]) = []\<close> \<open>m -as'@[a]\<rightarrow>* targetnode a\<close>
    have "m -as'@[a]\<rightarrow>\<^bsub>sl\<^esub>* targetnode a" by(simp add:slp_def same_level_path_def)
    moreover
    from \<open>\<forall>a\<in>set as''. intra_kind (kind a)\<close> \<open>targetnode a -as''\<rightarrow>* m'\<close>
    have "targetnode a -as''\<rightarrow>\<^sub>\<iota>* m'" by(simp add:intra_path_def)
    ultimately show ?thesis using \<open>as = as' @ a # as''\<close> \<open>kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f\<close> by blast
  qed
qed


function same_level_path_rev_aux :: "'edge list \<Rightarrow> 'edge list \<Rightarrow> bool"
  where "same_level_path_rev_aux cs [] \<longleftrightarrow> True"
  | "same_level_path_rev_aux cs (as@[a]) \<longleftrightarrow> 
       (case (kind a) of Q\<hookleftarrow>\<^bsub>p\<^esub>f \<Rightarrow> same_level_path_rev_aux (a#cs) as
                       | Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs \<Rightarrow> case cs of [] \<Rightarrow> False
                                     | c'#cs' \<Rightarrow> c' \<in> get_return_edges a \<and>
                                             same_level_path_rev_aux cs' as
                       |    _ \<Rightarrow> same_level_path_rev_aux cs as)"
by auto(case_tac b rule:rev_cases,auto)
termination by lexicographic_order


lemma slpra_induct [consumes 1,case_names slpra_empty slpra_intra slpra_Return
  slpra_Call]:
  assumes major: "same_level_path_rev_aux xs ys"
  and rules: "\<And>cs. P cs []"
    "\<And>cs a as. \<lbrakk>intra_kind(kind a); same_level_path_rev_aux cs as; P cs as\<rbrakk> 
      \<Longrightarrow> P cs (as@[a])"
    "\<And>cs a as Q p f. \<lbrakk>kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f; same_level_path_rev_aux (a#cs) as; P (a#cs) as\<rbrakk> 
      \<Longrightarrow> P cs (as@[a])"
    "\<And>cs a as Q r p fs c' cs'. \<lbrakk>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs; cs = c'#cs'; 
                   same_level_path_rev_aux cs' as; c' \<in> get_return_edges a; P cs' as\<rbrakk>
     \<Longrightarrow> P cs (as@[a])"
  shows "P xs ys"
using major
apply(induct ys arbitrary: xs rule:rev_induct)
by(auto intro:rules split:edge_kind.split_asm list.split_asm simp:intra_kind_def)


lemma same_level_path_rev_aux_Append:
  "\<lbrakk>same_level_path_rev_aux cs as'; same_level_path_rev_aux (upd_rev_cs cs as') as\<rbrakk>
  \<Longrightarrow> same_level_path_rev_aux cs (as@as')"
by(induct rule:slpra_induct,
   auto simp:intra_kind_def simp del:append_assoc simp:append_assoc[THEN sym])


lemma slpra_to_slpa:
  "\<lbrakk>same_level_path_rev_aux cs as; upd_rev_cs cs as = []; n -as\<rightarrow>* n'; 
  valid_return_list cs n'\<rbrakk>
  \<Longrightarrow> same_level_path_aux [] as \<and> same_level_path_aux (upd_cs [] as) cs \<and>
     upd_cs (upd_cs [] as) cs = []"
proof(induct arbitrary:n' rule:slpra_induct)
  case slpra_empty thus ?case by simp
next
  case (slpra_intra cs a as)
  note IH = \<open>\<And>n'. \<lbrakk>upd_rev_cs cs as = []; n -as\<rightarrow>* n'; valid_return_list cs n'\<rbrakk>
    \<Longrightarrow> same_level_path_aux [] as \<and> same_level_path_aux (upd_cs [] as) cs \<and>
       upd_cs (upd_cs [] as) cs = []\<close>
  from \<open>n -as@[a]\<rightarrow>* n'\<close> have "n -as\<rightarrow>* sourcenode a" and "valid_edge a"
    and "n' = targetnode a" by(auto intro:path_split_snoc)
  from \<open>valid_edge a\<close> \<open>intra_kind (kind a)\<close>
  have "get_proc (sourcenode a) = get_proc (targetnode a)"
    by(rule get_proc_intra)
  with \<open>valid_return_list cs n'\<close> \<open>n' = targetnode a\<close>
  have "valid_return_list cs (sourcenode a)"
    apply(clarsimp simp:valid_return_list_def)
    apply(erule_tac x="cs'" in allE) apply clarsimp
    by(case_tac cs')(auto simp:targetnodes_def)
  from \<open>upd_rev_cs cs (as@[a]) = []\<close> \<open>intra_kind (kind a)\<close>
  have "upd_rev_cs cs as = []" by(fastforce simp:intra_kind_def)
  from \<open>valid_edge a\<close> \<open>intra_kind (kind a)\<close>
  have "get_proc (sourcenode a) = get_proc (targetnode a)" by(rule get_proc_intra)
  from IH[OF \<open>upd_rev_cs cs as = []\<close> \<open>n -as\<rightarrow>* sourcenode a\<close>
    \<open>valid_return_list cs (sourcenode a)\<close>]
  have "same_level_path_aux [] as" 
    and "same_level_path_aux (upd_cs [] as) cs"
    and "upd_cs (upd_cs [] as) cs = []" by simp_all
  from \<open>same_level_path_aux [] as\<close> \<open>intra_kind (kind a)\<close>
  have "same_level_path_aux [] (as@[a])" by(rule slpa_snoc_intra)
  from \<open>intra_kind (kind a)\<close>
  have "upd_cs [] (as@[a]) = upd_cs [] as"
    by(fastforce simp:upd_cs_Append intra_kind_def)
  moreover
  from \<open>same_level_path_aux [] as\<close> \<open>intra_kind (kind a)\<close>
  have "same_level_path_aux [] (as@[a])" by(rule slpa_snoc_intra)
  ultimately show ?case using \<open>same_level_path_aux (upd_cs [] as) cs\<close>
    \<open>upd_cs (upd_cs [] as) cs = []\<close>
    by simp
next
  case (slpra_Return cs a as Q p f)
  note IH = \<open>\<And>n' n''. \<lbrakk>upd_rev_cs (a#cs) as = []; n -as\<rightarrow>* n';
    valid_return_list (a#cs) n'\<rbrakk>
  \<Longrightarrow> same_level_path_aux [] as \<and>
     same_level_path_aux (upd_cs [] as) (a#cs) \<and>
     upd_cs (upd_cs [] as) (a#cs) = []\<close>
  from \<open>n -as@[a]\<rightarrow>* n'\<close> have "n -as\<rightarrow>* sourcenode a" and "valid_edge a"
    and "n' = targetnode a" by(auto intro:path_split_snoc)
  from \<open>valid_edge a\<close> \<open>kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f\<close> have "p = get_proc (sourcenode a)"
     by(rule get_proc_return[THEN sym])
   from \<open>valid_return_list cs n'\<close> \<open>n' = targetnode a\<close>
   have "valid_return_list cs (targetnode a)" by simp
   with \<open>valid_edge a\<close> \<open>kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f\<close> \<open>p = get_proc (sourcenode a)\<close>
   have "valid_return_list (a#cs) (sourcenode a)"
     apply(clarsimp simp:valid_return_list_def)
     apply(case_tac cs') apply auto
     apply(erule_tac x="list" in allE) apply clarsimp
     by(case_tac list,auto simp:targetnodes_def)
   from \<open>upd_rev_cs cs (as@[a]) = []\<close> \<open>kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f\<close>
   have "upd_rev_cs (a#cs) as = []" by simp
   from IH[OF this \<open>n -as\<rightarrow>* sourcenode a\<close> \<open>valid_return_list (a#cs) (sourcenode a)\<close>]
   have "same_level_path_aux [] as"
     and "same_level_path_aux (upd_cs [] as) (a#cs)"
     and "upd_cs (upd_cs [] as) (a#cs) = []" by simp_all
   show ?case 
  proof(cases "upd_cs [] as")
    case Nil
    with \<open>kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f\<close> \<open>same_level_path_aux (upd_cs [] as) (a#cs)\<close>
    have False by simp
    thus ?thesis by simp
  next
    case (Cons cx csx)
    with \<open>kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f\<close> \<open>same_level_path_aux (upd_cs [] as) (a#cs)\<close>
    obtain Qx fx 
      where match:"a \<in> get_return_edges cx" "same_level_path_aux csx cs" by auto
    from \<open>kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f\<close> Cons have "upd_cs [] (as@[a]) = csx"
      by(rule upd_cs_snoc_Return_Cons)
    with \<open>same_level_path_aux (upd_cs [] as) (a#cs)\<close>
      \<open>kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f\<close> match
    have "same_level_path_aux (upd_cs [] (as@[a])) cs" by simp
    from \<open>upd_cs [] (as@[a]) = csx\<close> \<open>kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f\<close> Cons
      \<open>upd_cs (upd_cs [] as) (a#cs) = []\<close>
    have "upd_cs (upd_cs [] (as@[a])) cs = []" by simp
    from Cons \<open>kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f\<close> match
    have "same_level_path_aux (upd_cs [] as) [a]" by simp
    with \<open>same_level_path_aux [] as\<close> have "same_level_path_aux [] (as@[a])"
      by(rule same_level_path_aux_Append)
    with \<open>same_level_path_aux (upd_cs [] (as@[a])) cs\<close>
      \<open>upd_cs (upd_cs [] (as@[a])) cs = []\<close>
    show ?thesis by simp
  qed
next
  case (slpra_Call cs a as Q r p fs cx csx)
  note IH = \<open>\<And>n'. \<lbrakk>upd_rev_cs csx as = []; n -as\<rightarrow>* n'; valid_return_list csx n'\<rbrakk>
    \<Longrightarrow> same_level_path_aux [] as \<and>
       same_level_path_aux (upd_cs [] as) csx \<and> upd_cs (upd_cs [] as) csx = []\<close>
  note match = \<open>cs = cx#csx\<close> \<open>cx \<in> get_return_edges a\<close>
  from \<open>n -as@[a]\<rightarrow>* n'\<close> have "n -as\<rightarrow>* sourcenode a" and "valid_edge a"
    and "n' = targetnode a" by(auto intro:path_split_snoc)
  from \<open>valid_edge a\<close> match 
  have "get_proc (sourcenode a) = get_proc (targetnode cx)"
    by(fastforce intro:get_proc_get_return_edge)
  with \<open>valid_return_list cs n'\<close> \<open>cs = cx#csx\<close>
  have "valid_return_list csx (sourcenode a)"
    apply(clarsimp simp:valid_return_list_def)
    apply(erule_tac x="cx#cs'" in allE) apply clarsimp
    by(case_tac cs',auto simp:targetnodes_def)
  from \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close> match \<open>upd_rev_cs cs (as@[a]) = []\<close>
  have "upd_rev_cs csx as = []" by simp
  from IH[OF this \<open>n -as\<rightarrow>* sourcenode a\<close> \<open>valid_return_list csx (sourcenode a)\<close>]
  have "same_level_path_aux [] as"
    and "same_level_path_aux (upd_cs [] as) csx" and "upd_cs (upd_cs [] as) csx = []"
    by simp_all
  from \<open>same_level_path_aux [] as\<close> \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close>
  have "same_level_path_aux [] (as@[a])" by(rule slpa_snoc_Call)
  from \<open>valid_edge a\<close> \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close> match obtain Q' f' where "kind cx = Q'\<hookleftarrow>\<^bsub>p\<^esub>f'"
    by(fastforce dest!:call_return_edges)
  from \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close> have "upd_cs [] (as@[a]) = a#(upd_cs [] as)"
    by(rule upd_cs_snoc_Call)
  with \<open>same_level_path_aux (upd_cs [] as) csx\<close> \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close> 
    \<open>kind cx = Q'\<hookleftarrow>\<^bsub>p\<^esub>f'\<close> match
  have "same_level_path_aux (upd_cs [] (as@[a])) cs" by simp
  from \<open>upd_cs (upd_cs [] as) csx = []\<close> \<open>upd_cs [] (as@[a]) = a#(upd_cs [] as)\<close>
    \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close> \<open>kind cx = Q'\<hookleftarrow>\<^bsub>p\<^esub>f'\<close> match
  have "upd_cs (upd_cs [] (as@[a])) cs = []" by simp
  with \<open>same_level_path_aux [] (as@[a])\<close>
    \<open>same_level_path_aux (upd_cs [] (as@[a])) cs\<close> show ?case by simp
qed


subsubsection \<open>Lemmas on paths with \<open>(_Entry_)\<close>\<close>

lemma path_Entry_target [dest]:
  assumes "n -as\<rightarrow>* (_Entry_)"
  shows "n = (_Entry_)" and "as = []"
using \<open>n -as\<rightarrow>* (_Entry_)\<close>
proof(induct n as n'\<equiv>"(_Entry_)" rule:path.induct)
  case (Cons_path n'' as a n)
  from \<open>n'' = (_Entry_)\<close> \<open>targetnode a = n''\<close> \<open>valid_edge a\<close> have False
    by -(rule Entry_target,simp_all)
  { case 1
    from \<open>False\<close> show ?case ..
  next
    case 2
    from \<open>False\<close> show ?case ..
  }
qed simp_all



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
  proof(rule ccontr)
    assume "\<not> (_Entry_) \<notin> set (sourcenodes (tl (a#as)))"
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


lemma Entry_no_inner_return_path: 
  assumes "(_Entry_) -as@[a]\<rightarrow>* n" and "\<forall>a \<in> set as. intra_kind(kind a)"
  and "kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f"
  shows "False"
proof -
  from \<open>(_Entry_) -as@[a]\<rightarrow>* n\<close> have "(_Entry_) -as\<rightarrow>* sourcenode a" 
    and "valid_edge a" and "targetnode a = n" by(auto intro:path_split_snoc)
  from \<open>(_Entry_) -as\<rightarrow>* sourcenode a\<close> \<open>\<forall>a \<in> set as. intra_kind(kind a)\<close>
  have "(_Entry_) -as\<rightarrow>\<^sub>\<iota>* sourcenode a" by(simp add:intra_path_def)
  hence "get_proc (sourcenode a) = Main"
    by(fastforce dest:intra_path_get_procs simp:get_proc_Entry)
  with \<open>valid_edge a\<close> \<open>kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f\<close> have "p = Main"
    by(fastforce dest:get_proc_return)
  with \<open>valid_edge a\<close> \<open>kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f\<close> show ?thesis
    by(fastforce intro:Main_no_return_source)
qed



lemma vpra_no_slpra:
  "\<lbrakk>valid_path_rev_aux cs as; n -as\<rightarrow>* n'; valid_return_list cs n'; cs \<noteq> [];
    \<forall>xs ys. as = xs@ys \<longrightarrow> (\<not> same_level_path_rev_aux cs ys \<or> upd_rev_cs cs ys \<noteq> [])\<rbrakk>
  \<Longrightarrow> \<exists>a Q f. valid_edge a \<and> kind a = Q\<hookleftarrow>\<^bsub>get_proc n\<^esub>f"
proof(induct arbitrary:n' rule:vpra_induct)
  case (vpra_empty cs)
  from \<open>valid_return_list cs n'\<close> \<open>cs \<noteq> []\<close> obtain Q f where "valid_edge (hd cs)"
    and "kind (hd cs) = Q\<hookleftarrow>\<^bsub>get_proc n'\<^esub>f"
    apply(unfold valid_return_list_def)
    apply(drule hd_Cons_tl[THEN sym])
    apply(erule_tac x="[]" in allE) 
    apply(erule_tac x="hd cs" in allE)
    by auto
  from \<open>n -[]\<rightarrow>* n'\<close> have "n = n'" by fastforce
  with \<open>valid_edge (hd cs)\<close> \<open>kind (hd cs) = Q\<hookleftarrow>\<^bsub>get_proc n'\<^esub>f\<close> show ?case by blast
next
  case (vpra_intra cs a as)
  note IH = \<open>\<And>n'. \<lbrakk>n -as\<rightarrow>* n'; valid_return_list cs n'; cs \<noteq> [];
    \<forall>xs ys. as = xs@ys \<longrightarrow> \<not> same_level_path_rev_aux cs ys \<or> upd_rev_cs cs ys \<noteq> []\<rbrakk>
    \<Longrightarrow> \<exists>a Q f. valid_edge a \<and> kind a = Q\<hookleftarrow>\<^bsub>get_proc n\<^esub>f\<close>
  note all = \<open>\<forall>xs ys. as@[a] = xs@ys 
    \<longrightarrow> \<not> same_level_path_rev_aux cs ys \<or> upd_rev_cs cs ys \<noteq> []\<close>
  from \<open>n -as@[a]\<rightarrow>* n'\<close> have "n -as\<rightarrow>* sourcenode a" and "valid_edge a"
    and "targetnode a = n'" by(auto intro:path_split_snoc)
  from \<open>valid_return_list cs n'\<close> \<open>cs \<noteq> []\<close> obtain Q f where "valid_edge (hd cs)"
    and "kind (hd cs) = Q\<hookleftarrow>\<^bsub>get_proc n'\<^esub>f"
    apply(unfold valid_return_list_def)
    apply(drule hd_Cons_tl[THEN sym])
    apply(erule_tac x="[]" in allE) 
    apply(erule_tac x="hd cs" in allE)
    by auto
  from \<open>valid_edge a\<close> \<open>intra_kind (kind a)\<close>
  have "get_proc (sourcenode a) = get_proc (targetnode a)" by(rule get_proc_intra)
  with \<open>kind (hd cs) = Q\<hookleftarrow>\<^bsub>get_proc n'\<^esub>f\<close> \<open>targetnode a = n'\<close>
  have "kind (hd cs) = Q\<hookleftarrow>\<^bsub>get_proc (sourcenode a)\<^esub>f" by simp
  from \<open>valid_return_list cs n'\<close> \<open>targetnode a = n'\<close>
    \<open>get_proc (sourcenode a) = get_proc (targetnode a)\<close>
  have "valid_return_list cs (sourcenode a)"
    apply(clarsimp simp:valid_return_list_def)
    apply(erule_tac x="cs'" in allE)
    apply(erule_tac x="c" in allE)
    by(auto split:list.split)
  from all \<open>intra_kind (kind a)\<close>
  have "\<forall>xs ys. as = xs@ys 
    \<longrightarrow> \<not> same_level_path_rev_aux cs ys \<or> upd_rev_cs cs ys \<noteq> []"
    apply clarsimp apply(erule_tac x="xs" in allE)
    by(auto simp:intra_kind_def)
  from IH[OF \<open>n -as\<rightarrow>* sourcenode a\<close> \<open>valid_return_list cs (sourcenode a)\<close>
    \<open>cs \<noteq> []\<close> this] show ?case .
next
  case (vpra_Return cs a as Q p f)
  note IH = \<open>\<And>n'. \<lbrakk>n -as\<rightarrow>* n'; valid_return_list (a#cs) n'; a#cs \<noteq> [];
   \<forall>xs ys. as = xs @ ys \<longrightarrow>
    \<not> same_level_path_rev_aux (a#cs) ys \<or> upd_rev_cs (a#cs) ys \<noteq> []\<rbrakk>
  \<Longrightarrow> \<exists>a Q f. valid_edge a \<and> kind a = Q\<hookleftarrow>\<^bsub>get_proc n\<^esub>f\<close>
  from \<open>n -as@[a]\<rightarrow>* n'\<close> have "n -as\<rightarrow>* sourcenode a" and "valid_edge a"
    and "targetnode a = n'" by(auto intro:path_split_snoc)
  from \<open>valid_edge a\<close> \<open>kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f\<close> have "get_proc (sourcenode a) = p"
    by(rule get_proc_return)
  with \<open>kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f\<close> \<open>valid_return_list cs n'\<close> \<open>valid_edge a\<close> \<open>targetnode a = n'\<close>
  have "valid_return_list (a#cs) (sourcenode a)"
    apply(clarsimp simp:valid_return_list_def)
    apply(case_tac cs') apply auto
    apply(erule_tac x="list" in allE)
    apply(erule_tac x="c" in allE)
    by(auto split:list.split simp:targetnodes_def)
  from \<open>\<forall>xs ys. as@[a] = xs@ys \<longrightarrow>
    \<not> same_level_path_rev_aux cs ys \<or> upd_rev_cs cs ys \<noteq> []\<close> \<open>kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f\<close>
  have "\<forall>xs ys. as = xs@ys \<longrightarrow>
    \<not> same_level_path_rev_aux (a#cs) ys \<or> upd_rev_cs (a#cs) ys \<noteq> []"
    apply clarsimp apply(erule_tac x="xs" in allE)
    by auto
  from IH[OF \<open>n -as\<rightarrow>* sourcenode a\<close> \<open>valid_return_list (a#cs) (sourcenode a)\<close>
    _ this] show ?case by simp
next
  case (vpra_CallEmpty cs a as Q p fs)
  from \<open>cs = []\<close> \<open>cs \<noteq> []\<close> have False by simp
  thus ?case by simp
next
  case (vpra_CallCons cs a as Q r p fs c' cs')
  note IH = \<open>\<And>n'. \<lbrakk>n -as\<rightarrow>* n'; valid_return_list cs' n'; cs' \<noteq> [];
    \<forall>xs ys. as = xs@ys \<longrightarrow>
       \<not> same_level_path_rev_aux cs' ys \<or> upd_rev_cs cs' ys \<noteq> []\<rbrakk>
    \<Longrightarrow> \<exists>a Q f. valid_edge a \<and> kind a = Q\<hookleftarrow>\<^bsub>get_proc n\<^esub>f\<close>
  note all = \<open>\<forall>xs ys. as@[a] = xs@ys \<longrightarrow>
     \<not> same_level_path_rev_aux cs ys \<or> upd_rev_cs cs ys \<noteq> []\<close>
  from \<open>n -as@[a]\<rightarrow>* n'\<close> have "n -as\<rightarrow>* sourcenode a" and "valid_edge a"
    and "targetnode a = n'" by(auto intro:path_split_snoc)
  from \<open>valid_return_list cs n'\<close> \<open>cs = c'#cs'\<close> have "valid_edge c'"
    apply(clarsimp simp:valid_return_list_def)
    apply(erule_tac x="[]" in allE)
    by auto
  show ?case
  proof(cases "cs' = []")
    case True
    with \<open>cs = c'#cs'\<close> \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close> \<open>c' \<in> get_return_edges a\<close>
    have "same_level_path_rev_aux cs ([]@[a])"
      and "upd_rev_cs cs ([]@[a]) = []"
      by(simp only:same_level_path_rev_aux.simps upd_rev_cs.simps,clarsimp)+
    with all have False by(erule_tac x="as" in allE) fastforce
    thus ?thesis by simp
  next
    case False
    with \<open>valid_return_list cs n'\<close> \<open>cs = c'#cs'\<close>
    have "valid_return_list cs' (targetnode c')"
      apply(clarsimp simp:valid_return_list_def)
      apply(hypsubst_thin)
      apply(erule_tac x="c'#cs'" in allE)
      apply(auto simp:targetnodes_def)
       apply(case_tac cs') apply auto
      apply(case_tac list) apply(auto simp:targetnodes_def)
      done
    from \<open>valid_edge a\<close> \<open>c' \<in> get_return_edges a\<close>
    have "get_proc (sourcenode a) = get_proc (targetnode c')"
      by(rule get_proc_get_return_edge)
    with \<open>valid_return_list cs' (targetnode c')\<close>
    have "valid_return_list cs' (sourcenode a)"
      apply(clarsimp simp:valid_return_list_def)
      apply(hypsubst_thin)
    apply(erule_tac x="cs'" in allE)
    apply(erule_tac x="c" in allE)
    by(auto split:list.split)
    from all \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close> \<open>cs = c'#cs'\<close> \<open>c' \<in> get_return_edges a\<close>
    have "\<forall>xs ys. as = xs@ys 
      \<longrightarrow> \<not> same_level_path_rev_aux cs' ys \<or> upd_rev_cs cs' ys \<noteq> []"
      apply clarsimp apply(erule_tac x="xs" in allE)
      by auto  
    from IH[OF \<open>n -as\<rightarrow>* sourcenode a\<close> \<open>valid_return_list cs' (sourcenode a)\<close>
      False this] show ?thesis .
  qed
qed


lemma valid_Entry_path_cases:
  assumes "(_Entry_) -as\<rightarrow>\<^sub>\<surd>* n" and "as \<noteq> []"
  shows "(\<exists>a' as'. as = as'@[a'] \<and> intra_kind(kind a')) \<or>
         (\<exists>a' as' Q r p fs. as = as'@[a'] \<and> kind a' = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs) \<or>
         (\<exists>as' as'' n'. as = as'@as'' \<and> as'' \<noteq> [] \<and> n' -as''\<rightarrow>\<^bsub>sl\<^esub>* n)"
proof -
  from \<open>as \<noteq> []\<close> obtain a' as' where "as = as'@[a']" by(cases as rule:rev_cases) auto
  thus ?thesis
  proof(cases "kind a'" rule:edge_kind_cases)
    case Intra with \<open>as = as'@[a']\<close> show ?thesis by simp
  next
    case Call with \<open>as = as'@[a']\<close> show ?thesis by simp
  next
    case (Return Q p f)
    from \<open>(_Entry_) -as\<rightarrow>\<^sub>\<surd>* n\<close> have "(_Entry_) -as\<rightarrow>* n" and "valid_path_rev_aux [] as"
      by(auto intro:vp_to_vpra simp:vp_def valid_path_def)
    from \<open>(_Entry_) -as\<rightarrow>* n\<close> \<open>as = as'@[a']\<close>
    have "(_Entry_) -as'\<rightarrow>* sourcenode a'" and "valid_edge a'" 
      and "targetnode a' = n"
      by(auto intro:path_split_snoc)
    from \<open>valid_path_rev_aux [] as\<close> \<open>as = as'@[a']\<close> Return
    have "valid_path_rev_aux [a'] as'" by simp
    from \<open>valid_edge a'\<close> Return
    have "valid_return_list [a'] (sourcenode a')"
      apply(clarsimp simp:valid_return_list_def)
      apply(case_tac cs') 
      by(auto intro:get_proc_return[THEN sym])
    show ?thesis
    proof(cases "\<forall>xs ys. as' = xs@ys \<longrightarrow> 
        (\<not> same_level_path_rev_aux [a'] ys \<or> upd_rev_cs [a'] ys \<noteq> [])")
      case True
      with \<open>valid_path_rev_aux [a'] as'\<close> \<open>(_Entry_) -as'\<rightarrow>* sourcenode a'\<close>
        \<open>valid_return_list [a'] (sourcenode a')\<close>
      obtain ax Qx fx where "valid_edge ax" and "kind ax = Qx\<hookleftarrow>\<^bsub>get_proc (_Entry_)\<^esub>fx"
        by(fastforce dest!:vpra_no_slpra)
      hence False by(fastforce intro:Main_no_return_source simp:get_proc_Entry)
      thus ?thesis by simp
    next
      case False
      then obtain xs ys where "as' = xs@ys" and "same_level_path_rev_aux [a'] ys"
        and "upd_rev_cs [a'] ys = []" by auto
      with Return have "same_level_path_rev_aux [] (ys@[a'])"
        and "upd_rev_cs [] (ys@[a']) = []" by simp_all
      from \<open>upd_rev_cs [a'] ys = []\<close> have "ys \<noteq> []" by auto
      with \<open>(_Entry_) -as'\<rightarrow>* sourcenode a'\<close> \<open>as' = xs@ys\<close>
      have "hd(sourcenodes ys) -ys\<rightarrow>* sourcenode a'"
        by(cases ys)(auto dest:path_split_second simp:sourcenodes_def)
      with \<open>targetnode a' = n\<close> \<open>valid_edge a'\<close>
      have "hd(sourcenodes ys) -ys@[a']\<rightarrow>* n"
        by(fastforce intro:path_Append path_edge)
      with \<open>same_level_path_rev_aux [] (ys@[a'])\<close> \<open>upd_rev_cs [] (ys@[a']) = []\<close>
      have "same_level_path (ys@[a'])"
        by(fastforce dest:slpra_to_slpa simp:same_level_path_def valid_return_list_def)
      with \<open>hd(sourcenodes ys) -ys@[a']\<rightarrow>* n\<close> have "hd(sourcenodes ys) -ys@[a']\<rightarrow>\<^bsub>sl\<^esub>* n"
        by(simp add:slp_def)
      with \<open>as = as'@[a']\<close> \<open>as' = xs@ys\<close> Return
      have "\<exists>as' as'' n'. as = as'@as'' \<and> as'' \<noteq> [] \<and> n' -as''\<rightarrow>\<^bsub>sl\<^esub>* n"
        by(rule_tac x="xs" in exI) auto
      thus ?thesis by simp
    qed
  qed
qed


lemma valid_Entry_path_ascending_path:
  assumes "(_Entry_) -as\<rightarrow>\<^sub>\<surd>* n"
  obtains as' where "(_Entry_) -as'\<rightarrow>\<^sub>\<surd>* n" 
  and "set(sourcenodes as') \<subseteq> set(sourcenodes as)"
  and "\<forall>a' \<in> set as'. intra_kind(kind a') \<or> (\<exists>Q r p fs. kind a' = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs)"
proof(atomize_elim)
  from \<open>(_Entry_) -as\<rightarrow>\<^sub>\<surd>* n\<close>
  show "\<exists>as'. (_Entry_) -as'\<rightarrow>\<^sub>\<surd>* n \<and> set(sourcenodes as') \<subseteq> set(sourcenodes as)\<and>
              (\<forall>a' \<in> set as'. intra_kind(kind a') \<or> (\<exists>Q r p fs. kind a' = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs))"
  proof(induct as arbitrary:n rule:length_induct)
    fix as n
    assume IH:"\<forall>as''. length as'' < length as \<longrightarrow>
      (\<forall>n'. (_Entry_) -as''\<rightarrow>\<^sub>\<surd>* n' \<longrightarrow>
       (\<exists>as'. (_Entry_) -as'\<rightarrow>\<^sub>\<surd>* n' \<and> set (sourcenodes as') \<subseteq> set (sourcenodes as'') \<and>
              (\<forall>a'\<in>set as'. intra_kind (kind a') \<or> (\<exists>Q r p fs. kind a' = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs))))"
      and "(_Entry_) -as\<rightarrow>\<^sub>\<surd>* n"
    show "\<exists>as'. (_Entry_) -as'\<rightarrow>\<^sub>\<surd>* n \<and> set(sourcenodes as') \<subseteq> set(sourcenodes as)\<and>
              (\<forall>a' \<in> set as'. intra_kind(kind a') \<or> (\<exists>Q r p fs. kind a' = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs))"
    proof(cases "as = []")
      case True
      with \<open>(_Entry_) -as\<rightarrow>\<^sub>\<surd>* n\<close> show ?thesis by(fastforce simp:sourcenodes_def vp_def)
    next
      case False
      with \<open>(_Entry_) -as\<rightarrow>\<^sub>\<surd>* n\<close>
      have "((\<exists>a' as'. as = as'@[a'] \<and> intra_kind(kind a')) \<or>
         (\<exists>a' as' Q r p fs. as = as'@[a'] \<and> kind a' = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs)) \<or>
         (\<exists>as' as'' n'. as = as'@as'' \<and> as'' \<noteq> [] \<and> n' -as''\<rightarrow>\<^bsub>sl\<^esub>* n)"
        by(fastforce dest!:valid_Entry_path_cases)
      thus ?thesis apply -
      proof(erule disjE)+
        assume "\<exists>a' as'. as = as'@[a'] \<and> intra_kind(kind a')"
        then obtain a' as' where "as = as'@[a']" and "intra_kind(kind a')" by blast
        from \<open>(_Entry_) -as\<rightarrow>\<^sub>\<surd>* n\<close> \<open>as = as'@[a']\<close>
        have "(_Entry_) -as'\<rightarrow>\<^sub>\<surd>* sourcenode a'" and "valid_edge a'"
          and "targetnode a' = n"
          by(auto intro:vp_split_snoc)
        from \<open>valid_edge a'\<close> \<open>intra_kind(kind a')\<close>
        have "sourcenode a' -[a']\<rightarrow>\<^bsub>sl\<^esub>* targetnode a'"
          by(fastforce intro:path_edge intras_same_level_path simp:slp_def)
        from IH \<open>(_Entry_) -as'\<rightarrow>\<^sub>\<surd>* sourcenode a'\<close> \<open>as = as'@[a']\<close>
        obtain xs where "(_Entry_) -xs\<rightarrow>\<^sub>\<surd>* sourcenode a'" 
          and "set (sourcenodes xs) \<subseteq> set (sourcenodes as')"
          and "\<forall>a'\<in>set xs. intra_kind (kind a') \<or> (\<exists>Q r p fs. kind a' = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs)"
          apply(erule_tac x="as'" in allE) by auto
        from \<open>(_Entry_) -xs\<rightarrow>\<^sub>\<surd>* sourcenode a'\<close> \<open>sourcenode a' -[a']\<rightarrow>\<^bsub>sl\<^esub>* targetnode a'\<close>
        have "(_Entry_) -xs@[a']\<rightarrow>\<^sub>\<surd>* targetnode a'" by(rule vp_slp_Append)
        with \<open>targetnode a' = n\<close> have "(_Entry_) -xs@[a']\<rightarrow>\<^sub>\<surd>* n" by simp
        moreover
        from \<open>set (sourcenodes xs) \<subseteq> set (sourcenodes as')\<close> \<open>as = as'@[a']\<close>
        have "set (sourcenodes (xs@[a'])) \<subseteq> set (sourcenodes as)"
          by(auto simp:sourcenodes_def)
        moreover
        from \<open>\<forall>a'\<in>set xs. intra_kind (kind a') \<or> (\<exists>Q r p fs. kind a' = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs)\<close> 
          \<open>intra_kind(kind a')\<close>
        have "\<forall>a'\<in>set (xs@[a']). intra_kind (kind a') \<or> 
                                 (\<exists>Q r p fs. kind a' = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs)"
          by fastforce
        ultimately show ?thesis by blast
      next
        assume "\<exists>a' as' Q r p fs. as = as'@[a'] \<and> kind a' = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs"
        then obtain a' as' Q r p fs where "as = as'@[a']" and "kind a' = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs" 
          by blast
        from \<open>(_Entry_) -as\<rightarrow>\<^sub>\<surd>* n\<close> \<open>as = as'@[a']\<close>
        have "(_Entry_) -as'\<rightarrow>\<^sub>\<surd>* sourcenode a'" and "valid_edge a'"
          and "targetnode a' = n"
          by(auto intro:vp_split_snoc)
        from IH \<open>(_Entry_) -as'\<rightarrow>\<^sub>\<surd>* sourcenode a'\<close> \<open>as = as'@[a']\<close>
        obtain xs where "(_Entry_) -xs\<rightarrow>\<^sub>\<surd>* sourcenode a'" 
          and "set (sourcenodes xs) \<subseteq> set (sourcenodes as')"
          and "\<forall>a'\<in>set xs. intra_kind (kind a') \<or> (\<exists>Q r p fs. kind a' = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs)"
          apply(erule_tac x="as'" in allE) by auto
        from \<open>targetnode a' = n\<close> \<open>valid_edge a'\<close> \<open>kind a' = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close>
          \<open>(_Entry_) -xs\<rightarrow>\<^sub>\<surd>* sourcenode a'\<close>
        have "(_Entry_) -xs@[a']\<rightarrow>\<^sub>\<surd>* n"
          by(fastforce intro:path_Append path_edge vpa_snoc_Call 
                       simp:vp_def valid_path_def)
        moreover
        from \<open>set (sourcenodes xs) \<subseteq> set (sourcenodes as')\<close> \<open>as = as'@[a']\<close>
        have "set (sourcenodes (xs@[a'])) \<subseteq> set (sourcenodes as)"
          by(auto simp:sourcenodes_def)
        moreover
        from \<open>\<forall>a'\<in>set xs. intra_kind (kind a') \<or> (\<exists>Q r p fs. kind a' = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs)\<close> 
          \<open>kind a' = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close>
        have "\<forall>a'\<in>set (xs@[a']). intra_kind (kind a') \<or> 
                                 (\<exists>Q r p fs. kind a' = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs)"
          by fastforce
        ultimately show ?thesis by blast
      next
        assume "\<exists>as' as'' n'. as = as'@as'' \<and> as'' \<noteq> [] \<and> n' -as''\<rightarrow>\<^bsub>sl\<^esub>* n"
        then obtain as' as'' n' where "as = as'@as''" and "as'' \<noteq> []"
          and "n' -as''\<rightarrow>\<^bsub>sl\<^esub>* n" by blast
        from \<open>(_Entry_) -as\<rightarrow>\<^sub>\<surd>* n\<close> \<open>as = as'@as''\<close> \<open>as'' \<noteq> []\<close>
        have "(_Entry_) -as'\<rightarrow>\<^sub>\<surd>* hd(sourcenodes as'')"
          by(cases as'',auto intro:vp_split simp:sourcenodes_def)
        from \<open>n' -as''\<rightarrow>\<^bsub>sl\<^esub>* n\<close> \<open>as'' \<noteq> []\<close> have "hd(sourcenodes as'') = n'"
          by(fastforce intro:path_sourcenode simp:slp_def)
        from \<open>as = as'@as''\<close> \<open>as'' \<noteq> []\<close> have "length as' < length as" by simp
        with IH \<open>(_Entry_) -as'\<rightarrow>\<^sub>\<surd>* hd(sourcenodes as'')\<close>
          \<open>hd(sourcenodes as'') = n'\<close>
        obtain xs where "(_Entry_) -xs\<rightarrow>\<^sub>\<surd>* n'" 
          and "set (sourcenodes xs) \<subseteq> set (sourcenodes as')"
          and "\<forall>a'\<in>set xs. intra_kind (kind a') \<or> (\<exists>Q r p fs. kind a' = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs)"
          apply(erule_tac x="as'" in allE) by auto
        from \<open>n' -as''\<rightarrow>\<^bsub>sl\<^esub>* n\<close> obtain ys where "n' -ys\<rightarrow>\<^sub>\<iota>* n"
          and "set(sourcenodes ys) \<subseteq> set(sourcenodes as'')"
          by(erule same_level_path_inner_path)
        from \<open>(_Entry_) -xs\<rightarrow>\<^sub>\<surd>* n'\<close> \<open>n' -ys\<rightarrow>\<^sub>\<iota>* n\<close> have "(_Entry_) -xs@ys\<rightarrow>\<^sub>\<surd>* n"
          by(fastforce intro:vp_slp_Append intra_path_slp)
        moreover
        from \<open>set (sourcenodes xs) \<subseteq> set (sourcenodes as')\<close>
          \<open>set(sourcenodes ys) \<subseteq> set(sourcenodes as'')\<close> \<open>as = as'@as''\<close>
        have "set (sourcenodes (xs@ys)) \<subseteq> set(sourcenodes as)"
          by(auto simp:sourcenodes_def)
        moreover
        from \<open>\<forall>a'\<in>set xs. intra_kind (kind a') \<or> (\<exists>Q r p fs. kind a' = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs)\<close>
          \<open>n' -ys\<rightarrow>\<^sub>\<iota>* n\<close>
        have "\<forall>a'\<in>set (xs@ys). intra_kind (kind a') \<or> (\<exists>Q r p fs. kind a' = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs)"
          by(fastforce simp:intra_path_def)
        ultimately show ?thesis by blast
      qed
    qed
  qed
qed



end

end
