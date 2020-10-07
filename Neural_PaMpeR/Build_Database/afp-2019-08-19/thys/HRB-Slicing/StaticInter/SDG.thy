section \<open>SDG\<close>

theory SDG imports CFGExit_wf Postdomination begin

subsection \<open>The nodes of the SDG\<close>

datatype 'node SDG_node = 
    CFG_node 'node
  | Formal_in  "'node \<times> nat"
  | Formal_out "'node \<times> nat"
  | Actual_in  "'node \<times> nat"
  | Actual_out "'node \<times> nat"

fun parent_node :: "'node SDG_node \<Rightarrow> 'node"
  where "parent_node (CFG_node n) = n"
  | "parent_node (Formal_in (m,x)) = m"
  | "parent_node (Formal_out (m,x)) = m"
  | "parent_node (Actual_in (m,x)) = m"
  | "parent_node (Actual_out (m,x)) = m"


locale SDG = CFGExit_wf sourcenode targetnode kind valid_edge Entry 
    get_proc get_return_edges procs Main Exit Def Use ParamDefs ParamUses +
  Postdomination sourcenode targetnode kind valid_edge Entry 
    get_proc get_return_edges procs Main Exit
  for sourcenode :: "'edge \<Rightarrow> 'node" and targetnode :: "'edge \<Rightarrow> 'node"
  and kind :: "'edge \<Rightarrow> ('var,'val,'ret,'pname) edge_kind" 
  and valid_edge :: "'edge \<Rightarrow> bool"
  and Entry :: "'node" ("'('_Entry'_')")  and get_proc :: "'node \<Rightarrow> 'pname"
  and get_return_edges :: "'edge \<Rightarrow> 'edge set"
  and procs :: "('pname \<times> 'var list \<times> 'var list) list" and Main :: "'pname"
  and Exit::"'node"  ("'('_Exit'_')") 
  and Def :: "'node \<Rightarrow> 'var set" and Use :: "'node \<Rightarrow> 'var set"
  and ParamDefs :: "'node \<Rightarrow> 'var list" and ParamUses :: "'node \<Rightarrow> 'var set list"

begin


fun valid_SDG_node :: "'node SDG_node \<Rightarrow> bool"
  where "valid_SDG_node (CFG_node n) \<longleftrightarrow> valid_node n"
  | "valid_SDG_node (Formal_in (m,x)) \<longleftrightarrow>
  (\<exists>a Q r p fs ins outs. valid_edge a \<and> (kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs) \<and> targetnode a = m \<and> 
  (p,ins,outs) \<in> set procs \<and> x < length ins)"
  | "valid_SDG_node (Formal_out (m,x)) \<longleftrightarrow>
  (\<exists>a Q p f ins outs. valid_edge a \<and> (kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f) \<and> sourcenode a = m \<and> 
  (p,ins,outs) \<in> set procs \<and> x < length outs)"
  | "valid_SDG_node (Actual_in (m,x)) \<longleftrightarrow>
  (\<exists>a Q r p fs ins outs. valid_edge a \<and> (kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs) \<and> sourcenode a = m \<and> 
  (p,ins,outs) \<in> set procs \<and> x < length ins)"
  | "valid_SDG_node (Actual_out (m,x)) \<longleftrightarrow>
  (\<exists>a Q p f ins outs. valid_edge a \<and> (kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f) \<and> targetnode a = m \<and> 
  (p,ins,outs) \<in> set procs \<and> x < length outs)"


lemma valid_SDG_CFG_node: 
  "valid_SDG_node n \<Longrightarrow> valid_node (parent_node n)"
by(cases n) auto


lemma Formal_in_parent_det:
  assumes "valid_SDG_node (Formal_in (m,x))" and "valid_SDG_node (Formal_in (m',x'))"
  and "get_proc m = get_proc m'"
  shows "m = m'"
proof -
  from \<open>valid_SDG_node (Formal_in (m,x))\<close> obtain a Q r p fs ins outs
    where "valid_edge a" and "kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs" and "targetnode a = m"
    and "(p,ins,outs) \<in> set procs" and "x < length ins" by fastforce
  from \<open>valid_SDG_node (Formal_in (m',x'))\<close> obtain a' Q' r' p' f' ins' outs'
    where "valid_edge a'" and "kind a' = Q':r'\<hookrightarrow>\<^bsub>p'\<^esub>f'" and "targetnode a' = m'"
    and "(p',ins',outs') \<in> set procs" and "x' < length ins'" by fastforce
  from \<open>valid_edge a\<close> \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close> \<open>targetnode a = m\<close>
  have "get_proc m = p" by(fastforce intro:get_proc_call)
  moreover
  from \<open>valid_edge a'\<close> \<open>kind a' = Q':r'\<hookrightarrow>\<^bsub>p'\<^esub>f'\<close> \<open>targetnode a' = m'\<close>
  have "get_proc m' = p'" by(fastforce intro:get_proc_call)
  ultimately have "p = p'" using \<open>get_proc m = get_proc m'\<close> by simp
  with \<open>valid_edge a\<close> \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close> \<open>valid_edge a'\<close> \<open>kind a' = Q':r'\<hookrightarrow>\<^bsub>p'\<^esub>f'\<close>
    \<open>targetnode a = m\<close> \<open>targetnode a' = m'\<close>
  show ?thesis by(fastforce intro:same_proc_call_unique_target)
qed


lemma valid_SDG_node_parent_Entry:
  assumes "valid_SDG_node n" and "parent_node n = (_Entry_)"
  shows "n = CFG_node (_Entry_)"
proof(cases n)
  case CFG_node with \<open>parent_node n = (_Entry_)\<close> show ?thesis by simp
next
  case (Formal_in z)
  with \<open>parent_node n = (_Entry_)\<close> obtain x 
    where [simp]:"z = ((_Entry_),x)" by(cases z) auto
  with \<open>valid_SDG_node n\<close> Formal_in obtain a where "valid_edge a"
    and "targetnode a = (_Entry_)" by auto
  hence False by -(rule Entry_target,simp+)
  thus ?thesis by simp
next
  case (Formal_out z)
  with \<open>parent_node n = (_Entry_)\<close> obtain x 
    where [simp]:"z = ((_Entry_),x)" by(cases z) auto
  with \<open>valid_SDG_node n\<close> Formal_out obtain a Q p f where "valid_edge a"
    and "kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f" and  "sourcenode a = (_Entry_)" by auto
  from \<open>valid_edge a\<close> \<open>kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f\<close> have "get_proc (sourcenode a) = p"
    by(rule get_proc_return)
  with \<open>sourcenode a = (_Entry_)\<close> have "p = Main"
    by(auto simp:get_proc_Entry)
  with \<open>valid_edge a\<close> \<open>kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f\<close> have False
    by(fastforce intro:Main_no_return_source)
  thus ?thesis by simp
next
  case (Actual_in z)
  with \<open>parent_node n = (_Entry_)\<close> obtain x 
    where [simp]:"z = ((_Entry_),x)" by(cases z) auto
  with \<open>valid_SDG_node n\<close> Actual_in obtain a Q r p fs where "valid_edge a"
    and "kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs" and "sourcenode a = (_Entry_)" by fastforce
  hence False by -(rule Entry_no_call_source,auto)
  thus ?thesis by simp
next
  case (Actual_out z)
  with \<open>parent_node n = (_Entry_)\<close> obtain x 
    where [simp]:"z = ((_Entry_),x)" by(cases z) auto
  with \<open>valid_SDG_node n\<close> Actual_out obtain a where "valid_edge a"
    "targetnode a = (_Entry_)" by auto
  hence False by -(rule Entry_target,simp+)
  thus ?thesis by simp
qed


lemma valid_SDG_node_parent_Exit:
  assumes "valid_SDG_node n" and "parent_node n = (_Exit_)"
  shows "n = CFG_node (_Exit_)"
proof(cases n)
  case CFG_node with \<open>parent_node n = (_Exit_)\<close> show ?thesis by simp
next
  case (Formal_in z)
  with \<open>parent_node n = (_Exit_)\<close> obtain x 
    where [simp]:"z = ((_Exit_),x)" by(cases z) auto
  with \<open>valid_SDG_node n\<close> Formal_in obtain a Q r p fs where "valid_edge a"
    and "kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs" and "targetnode a = (_Exit_)" by fastforce
  from \<open>valid_edge a\<close> \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close> have "get_proc (targetnode a) = p"
    by(rule get_proc_call)
  with \<open>targetnode a = (_Exit_)\<close> have "p = Main"
    by(auto simp:get_proc_Exit)
  with \<open>valid_edge a\<close> \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close> have False
    by(fastforce intro:Main_no_call_target)
  thus ?thesis by simp
next
  case (Formal_out z)
  with \<open>parent_node n = (_Exit_)\<close> obtain x 
    where [simp]:"z = ((_Exit_),x)" by(cases z) auto
  with \<open>valid_SDG_node n\<close> Formal_out obtain a where "valid_edge a"
    and "sourcenode a = (_Exit_)" by auto
  hence False by -(rule Exit_source,simp+)
  thus ?thesis by simp
next
  case (Actual_in z)
  with \<open>parent_node n = (_Exit_)\<close> obtain x 
    where [simp]:"z = ((_Exit_),x)" by(cases z) auto
  with \<open>valid_SDG_node n\<close> Actual_in obtain a where "valid_edge a"
    and "sourcenode a = (_Exit_)" by auto
  hence False by -(rule Exit_source,simp+)
  thus ?thesis by simp
next
  case (Actual_out z)
  with \<open>parent_node n = (_Exit_)\<close> obtain x 
    where [simp]:"z = ((_Exit_),x)" by(cases z) auto
  with \<open>valid_SDG_node n\<close> Actual_out obtain a Q p f where "valid_edge a"
    and "kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f" and "targetnode a = (_Exit_)" by auto
  hence False by -(erule Exit_no_return_target,auto)
  thus ?thesis by simp
qed


subsection \<open>Data dependence\<close>

inductive SDG_Use :: "'var \<Rightarrow> 'node SDG_node \<Rightarrow> bool" ("_ \<in> Use\<^bsub>SDG\<^esub> _")
where CFG_Use_SDG_Use:
  "\<lbrakk>valid_node m; V \<in> Use m; n = CFG_node m\<rbrakk> \<Longrightarrow> V \<in> Use\<^bsub>SDG\<^esub> n"
  | Actual_in_SDG_Use:
  "\<lbrakk>valid_SDG_node n; n = Actual_in (m,x); V \<in> (ParamUses m)!x\<rbrakk> \<Longrightarrow> V \<in> Use\<^bsub>SDG\<^esub> n"
  | Formal_out_SDG_Use:
  "\<lbrakk>valid_SDG_node n; n = Formal_out (m,x); get_proc m = p; (p,ins,outs) \<in> set procs;
    V = outs!x\<rbrakk> \<Longrightarrow> V \<in> Use\<^bsub>SDG\<^esub> n"


abbreviation notin_SDG_Use :: "'var \<Rightarrow> 'node SDG_node \<Rightarrow> bool"  ("_ \<notin> Use\<^bsub>SDG\<^esub> _")
  where "V \<notin> Use\<^bsub>SDG\<^esub> n \<equiv> \<not> V \<in> Use\<^bsub>SDG\<^esub> n"


lemma in_Use_valid_SDG_node:
  "V \<in> Use\<^bsub>SDG\<^esub> n \<Longrightarrow> valid_SDG_node n"
by(induct rule:SDG_Use.induct,auto intro:valid_SDG_CFG_node)


lemma SDG_Use_parent_Use: 
  "V \<in> Use\<^bsub>SDG\<^esub> n \<Longrightarrow> V \<in> Use (parent_node n)"
proof(induct rule:SDG_Use.induct)
  case CFG_Use_SDG_Use thus ?case by simp
next
  case (Actual_in_SDG_Use n m x V)
  from \<open>valid_SDG_node n\<close> \<open>n = Actual_in (m, x)\<close> obtain a Q r p fs ins outs
    where "valid_edge a" and "kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs" and "sourcenode a = m"
    and "(p,ins,outs) \<in> set procs" and "x < length ins" by fastforce
  from \<open>valid_edge a\<close> \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close> \<open>(p,ins,outs) \<in> set procs\<close>
  have "length(ParamUses (sourcenode a)) = length ins"
    by(fastforce intro:ParamUses_call_source_length)
  with \<open>x < length ins\<close>
  have "(ParamUses (sourcenode a))!x \<in> set (ParamUses (sourcenode a))" by simp
  with \<open>V \<in> (ParamUses m)!x\<close> \<open>sourcenode a = m\<close>
  have "V \<in> Union (set (ParamUses m))" by fastforce
  with \<open>valid_edge a\<close> \<open>sourcenode a = m\<close> \<open>n = Actual_in (m, x)\<close> show ?case
    by(fastforce intro:ParamUses_in_Use)
next
  case (Formal_out_SDG_Use n m x p ins outs V)
  from \<open>valid_SDG_node n\<close> \<open>n = Formal_out (m, x)\<close> obtain a Q p' f ins' outs'
    where "valid_edge a" and "kind a = Q\<hookleftarrow>\<^bsub>p'\<^esub>f" and "sourcenode a = m"
    and "(p',ins',outs') \<in> set procs" and "x < length outs'" by fastforce
  from \<open>valid_edge a\<close> \<open>kind a = Q\<hookleftarrow>\<^bsub>p'\<^esub>f\<close> have "get_proc (sourcenode a) = p'"
    by(rule get_proc_return)
  with \<open>get_proc m = p\<close> \<open>sourcenode a = m\<close> have [simp]:"p = p'" by simp
  with \<open>(p',ins',outs') \<in> set procs\<close> \<open>(p,ins,outs) \<in> set procs\<close> unique_callers
  have [simp]:"ins' = ins" "outs' = outs" by(auto dest:distinct_fst_isin_same_fst)
  from \<open>x < length outs'\<close> \<open>V = outs ! x\<close> have "V \<in> set outs" by fastforce
  with \<open>valid_edge a\<close> \<open>kind a = Q\<hookleftarrow>\<^bsub>p'\<^esub>f\<close> \<open>(p,ins,outs) \<in> set procs\<close>
  have "V \<in> Use (sourcenode a)" by(fastforce intro:outs_in_Use)
  with \<open>sourcenode a = m\<close> \<open>valid_SDG_node n\<close> \<open>n = Formal_out (m, x)\<close>
  show ?case by simp
qed



inductive SDG_Def :: "'var \<Rightarrow> 'node SDG_node \<Rightarrow> bool" ("_ \<in> Def\<^bsub>SDG\<^esub> _")
where CFG_Def_SDG_Def:
  "\<lbrakk>valid_node m; V \<in> Def m; n = CFG_node m\<rbrakk> \<Longrightarrow> V \<in> Def\<^bsub>SDG\<^esub> n"
  | Formal_in_SDG_Def:
  "\<lbrakk>valid_SDG_node n; n = Formal_in (m,x); get_proc m = p; (p,ins,outs) \<in> set procs;
    V = ins!x\<rbrakk> \<Longrightarrow> V \<in> Def\<^bsub>SDG\<^esub> n"
  | Actual_out_SDG_Def:
  "\<lbrakk>valid_SDG_node n; n = Actual_out (m,x); V = (ParamDefs m)!x\<rbrakk> \<Longrightarrow> V \<in> Def\<^bsub>SDG\<^esub> n"

abbreviation notin_SDG_Def :: "'var \<Rightarrow> 'node SDG_node \<Rightarrow> bool"  ("_ \<notin> Def\<^bsub>SDG\<^esub> _")
  where "V \<notin> Def\<^bsub>SDG\<^esub> n \<equiv> \<not> V \<in> Def\<^bsub>SDG\<^esub> n"


lemma in_Def_valid_SDG_node:
  "V \<in> Def\<^bsub>SDG\<^esub> n \<Longrightarrow> valid_SDG_node n"
by(induct rule:SDG_Def.induct,auto intro:valid_SDG_CFG_node)


lemma SDG_Def_parent_Def: 
  "V \<in> Def\<^bsub>SDG\<^esub> n \<Longrightarrow> V \<in> Def (parent_node n)"
proof(induct rule:SDG_Def.induct)
  case CFG_Def_SDG_Def thus ?case by simp
next
  case (Formal_in_SDG_Def n m x p ins outs V)
  from \<open>valid_SDG_node n\<close> \<open>n = Formal_in (m, x)\<close> obtain a Q r p' fs ins' outs'
    where "valid_edge a" and "kind a = Q:r\<hookrightarrow>\<^bsub>p'\<^esub>fs" and "targetnode a = m"
    and "(p',ins',outs') \<in> set procs" and "x < length ins'" by fastforce
  from \<open>valid_edge a\<close> \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p'\<^esub>fs\<close> have "get_proc (targetnode a) = p'"
    by(rule get_proc_call)
  with \<open>get_proc m = p\<close> \<open>targetnode a = m\<close> have [simp]:"p = p'" by simp
  with \<open>(p',ins',outs') \<in> set procs\<close> \<open>(p,ins,outs) \<in> set procs\<close> unique_callers
  have [simp]:"ins' = ins" "outs' = outs" by(auto dest:distinct_fst_isin_same_fst)
  from \<open>x < length ins'\<close> \<open>V = ins ! x\<close> have "V \<in> set ins" by fastforce
  with \<open>valid_edge a\<close> \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p'\<^esub>fs\<close> \<open>(p,ins,outs) \<in> set procs\<close>
  have "V \<in> Def (targetnode a)" by(fastforce intro:ins_in_Def)
  with \<open>targetnode a = m\<close> \<open>valid_SDG_node n\<close> \<open>n = Formal_in (m, x)\<close>
  show ?case by simp
next
  case (Actual_out_SDG_Def n m x V)
  from \<open>valid_SDG_node n\<close> \<open>n = Actual_out (m, x)\<close> obtain a Q p f ins outs
    where "valid_edge a" and "kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f" and "targetnode a = m"
    and "(p,ins,outs) \<in> set procs" and "x < length outs" by fastforce
  from \<open>valid_edge a\<close> \<open>kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f\<close> \<open>(p,ins,outs) \<in> set procs\<close>
  have "length(ParamDefs (targetnode a)) = length outs" 
    by(rule ParamDefs_return_target_length)
  with \<open>x < length outs\<close> \<open>V = ParamDefs m ! x\<close> \<open>targetnode a = m\<close>
  have "V \<in> set (ParamDefs (targetnode a))" by(fastforce simp:set_conv_nth)
  with \<open>n = Actual_out (m, x)\<close> \<open>targetnode a = m\<close> \<open>valid_edge a\<close>
  show ?case by(fastforce intro:ParamDefs_in_Def)
qed



definition data_dependence :: "'node SDG_node \<Rightarrow> 'var \<Rightarrow> 'node SDG_node \<Rightarrow> bool" 
("_ influences _ in _" [51,0,0])
  where "n influences V in n' \<equiv> \<exists>as. (V \<in> Def\<^bsub>SDG\<^esub> n) \<and> (V \<in> Use\<^bsub>SDG\<^esub> n') \<and> 
  (parent_node n -as\<rightarrow>\<^sub>\<iota>* parent_node n') \<and>
  (\<forall>n''. valid_SDG_node n'' \<and> parent_node n'' \<in> set (sourcenodes (tl as))
         \<longrightarrow> V \<notin> Def\<^bsub>SDG\<^esub> n'')"


subsection \<open>Control dependence\<close>

definition control_dependence :: "'node \<Rightarrow> 'node \<Rightarrow> bool" 
  ("_ controls _" [51,0])
where "n controls n' \<equiv> \<exists>a a' as. n -a#as\<rightarrow>\<^sub>\<iota>* n' \<and> n' \<notin> set(sourcenodes (a#as)) \<and>
    intra_kind(kind a) \<and> n' postdominates (targetnode a) \<and> 
    valid_edge a' \<and> intra_kind(kind a') \<and> sourcenode a' = n \<and> 
    \<not> n' postdominates (targetnode a')"


lemma control_dependence_path:
  assumes "n controls n'" obtains as where "n -as\<rightarrow>\<^sub>\<iota>* n'" and "as \<noteq> []"
using \<open>n controls n'\<close>
by(fastforce simp:control_dependence_def)


lemma Exit_does_not_control [dest]:
  assumes "(_Exit_) controls n'" shows "False"
proof -
  from \<open>(_Exit_) controls n'\<close> obtain a where "valid_edge a"
    and "sourcenode a = (_Exit_)" by(auto simp:control_dependence_def)
  thus ?thesis by(rule Exit_source)
qed


lemma Exit_not_control_dependent: 
  assumes "n controls n'" shows "n' \<noteq> (_Exit_)"
proof -
  from \<open>n controls n'\<close> obtain a as where "n -a#as\<rightarrow>\<^sub>\<iota>* n'"
    and "n' postdominates (targetnode a)"
    by(auto simp:control_dependence_def)
  from \<open>n -a#as\<rightarrow>\<^sub>\<iota>* n'\<close> have "valid_edge a" 
    by(fastforce elim:path.cases simp:intra_path_def)
  hence "valid_node (targetnode a)" by simp
  with \<open>n' postdominates (targetnode a)\<close> \<open>n -a#as\<rightarrow>\<^sub>\<iota>* n'\<close> show ?thesis
    by(fastforce elim:Exit_no_postdominator)
qed


lemma which_node_intra_standard_control_dependence_source:
  assumes "nx -as@a#as'\<rightarrow>\<^sub>\<iota>* n" and "sourcenode a = n'" and "sourcenode a' = n'"
  and "n \<notin> set(sourcenodes (a#as'))" and "valid_edge a'" and "intra_kind(kind a')"
  and "inner_node n" and "\<not> method_exit n" and "\<not> n postdominates (targetnode a')"
  and last:"\<forall>ax ax'. ax \<in> set as' \<and> sourcenode ax = sourcenode ax' \<and>
    valid_edge ax' \<and> intra_kind(kind ax') \<longrightarrow> n postdominates targetnode ax'"
  shows "n' controls n"
proof -
  from \<open>nx -as@a#as'\<rightarrow>\<^sub>\<iota>* n\<close> \<open>sourcenode a = n'\<close> have "n' -a#as'\<rightarrow>\<^sub>\<iota>* n"
    by(fastforce dest:path_split_second simp:intra_path_def)
  from \<open>nx -as@a#as'\<rightarrow>\<^sub>\<iota>* n\<close> have "valid_edge a"
    by(fastforce intro:path_split simp:intra_path_def)
  show ?thesis
  proof(cases "n postdominates (targetnode a)")
    case True
    with \<open>n' -a#as'\<rightarrow>\<^sub>\<iota>* n\<close> \<open>n \<notin> set(sourcenodes (a#as'))\<close>
      \<open>valid_edge a'\<close> \<open>intra_kind(kind a')\<close> \<open>sourcenode a' = n'\<close> 
      \<open>\<not> n postdominates (targetnode a')\<close> show ?thesis
      by(fastforce simp:control_dependence_def intra_path_def)
  next
    case False
    show ?thesis
    proof(cases "as' = []")
      case True
      with \<open>n' -a#as'\<rightarrow>\<^sub>\<iota>* n\<close> have "targetnode a = n" 
        by(fastforce elim:path.cases simp:intra_path_def)
      with \<open>inner_node n\<close> \<open>\<not> method_exit n\<close> have "n postdominates (targetnode a)"
        by(fastforce dest:inner_is_valid intro:postdominate_refl)
      with \<open>\<not> n postdominates (targetnode a)\<close> show ?thesis by simp
    next
      case False
      with \<open>nx -as@a#as'\<rightarrow>\<^sub>\<iota>* n\<close> have "targetnode a -as'\<rightarrow>\<^sub>\<iota>* n"
        by(fastforce intro:path_split simp:intra_path_def)
     with \<open>\<not> n postdominates (targetnode a)\<close> \<open>valid_edge a\<close> \<open>inner_node n\<close>
        \<open>targetnode a -as'\<rightarrow>\<^sub>\<iota>* n\<close>
      obtain asx pex where "targetnode a -asx\<rightarrow>\<^sub>\<iota>* pex" and "method_exit pex"
        and "n \<notin> set (sourcenodes asx)"
        by(fastforce dest:inner_is_valid simp:postdominate_def)
      show ?thesis
      proof(cases "\<exists>asx'. asx = as'@asx'")
        case True
        then obtain asx' where [simp]:"asx = as'@asx'" by blast
        from \<open>targetnode a -asx\<rightarrow>\<^sub>\<iota>* pex\<close> \<open>targetnode a -as'\<rightarrow>\<^sub>\<iota>* n\<close>
          \<open>as' \<noteq> []\<close> \<open>method_exit pex\<close> \<open>\<not> method_exit n\<close>
        obtain a'' as'' where "asx' = a''#as'' \<and> sourcenode a'' = n"
          by(cases asx')(auto dest:path_split path_det simp:intra_path_def)
        hence "n \<in> set(sourcenodes asx)" by(simp add:sourcenodes_def)
        with \<open>n \<notin> set (sourcenodes asx)\<close> have False by simp
        thus ?thesis by simp
      next
        case False
        hence "\<forall>asx'. asx \<noteq> as'@asx'" by simp
        then obtain j asx' where "asx = (take j as')@asx'"
          and "j < length as'" and "\<forall>k > j. \<forall>asx''. asx \<noteq> (take k as')@asx''"
          by(auto elim:path_split_general)
        from \<open>asx = (take j as')@asx'\<close> \<open>j < length as'\<close>
        have "\<exists>as'1 as'2. asx = as'1@asx' \<and> 
          as' = as'1@as'2 \<and> as'2 \<noteq> [] \<and> as'1 = take j as'"
          by simp(rule_tac x= "drop j as'" in exI,simp)
        then obtain as'1 as'' where "asx = as'1@asx'"
          and "as'1 = take j as'"
          and "as' = as'1@as''" and "as'' \<noteq> []" by blast
        from \<open>as' = as'1@as''\<close> \<open>as'' \<noteq> []\<close> obtain a1 as'2 
          where "as' = as'1@a1#as'2" and "as'' = a1#as'2"
          by(cases as'') auto
        have "asx' \<noteq> []"
        proof(cases "asx' = []")
          case True
          with \<open>asx = as'1@asx'\<close> \<open>as' = as'1@as''\<close> \<open>as'' = a1#as'2\<close>
          have "as' = asx@a1#as'2" by simp
          with \<open>n' -a#as'\<rightarrow>\<^sub>\<iota>* n\<close> have "n' -(a#asx)@a1#as'2\<rightarrow>\<^sub>\<iota>* n" by simp
          hence "n' -(a#asx)@a1#as'2\<rightarrow>* n" 
            and "\<forall>ax \<in> set((a#asx)@a1#as'2). intra_kind(kind ax)"
            by(simp_all add:intra_path_def)
          from \<open>n' -(a#asx)@a1#as'2\<rightarrow>* n\<close>
          have "n' -a#asx\<rightarrow>* sourcenode a1" and "valid_edge a1"
            by -(erule path_split)+
          from \<open>\<forall>ax \<in> set((a#asx)@a1#as'2). intra_kind(kind ax)\<close> 
          have "\<forall>ax \<in> set(a#asx). intra_kind(kind ax)" by simp
          with \<open>n' -a#asx\<rightarrow>* sourcenode a1\<close> have "n' -a#asx\<rightarrow>\<^sub>\<iota>* sourcenode a1"
            by(simp add:intra_path_def)
          hence "targetnode a -asx\<rightarrow>\<^sub>\<iota>* sourcenode a1"
            by(fastforce intro:path_split_Cons simp:intra_path_def)
          with \<open>targetnode a -asx\<rightarrow>\<^sub>\<iota>* pex\<close> have "pex = sourcenode a1"
            by(fastforce intro:path_det simp:intra_path_def)
          from \<open>\<forall>ax \<in> set((a#asx)@a1#as'2). intra_kind(kind ax)\<close>
          have "intra_kind (kind a1)" by simp
          from \<open>method_exit pex\<close> have False
          proof(rule method_exit_cases)
            assume "pex = (_Exit_)"
            with \<open>pex = sourcenode a1\<close> have "sourcenode a1 = (_Exit_)" by simp
            with \<open>valid_edge a1\<close> show False by(rule Exit_source)
          next
            fix a Q f p assume "pex = sourcenode a" and "valid_edge a"
              and "kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f"
            from \<open>valid_edge a\<close> \<open>kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f\<close> \<open>pex = sourcenode a\<close> 
              \<open>pex = sourcenode a1\<close> \<open>valid_edge a1\<close> \<open>intra_kind (kind a1)\<close>
            show False by(fastforce dest:return_edges_only simp:intra_kind_def)
          qed
          thus ?thesis by simp
        qed simp
        with \<open>asx = as'1@asx'\<close> obtain a2 asx'1 
          where "asx = as'1@a2#asx'1"
          and "asx' = a2#asx'1" by(cases asx') auto
        from \<open>n' -a#as'\<rightarrow>\<^sub>\<iota>* n\<close> \<open>as' = as'1@a1#as'2\<close> 
        have "n' -(a#as'1)@a1#as'2\<rightarrow>\<^sub>\<iota>* n" by simp
        hence "n' -(a#as'1)@a1#as'2\<rightarrow>* n" 
          and "\<forall>ax \<in> set((a#as'1)@a1#as'2). intra_kind(kind ax)"
          by(simp_all add: intra_path_def)
        from \<open>n' -(a#as'1)@a1#as'2\<rightarrow>* n\<close> have "n' -a#as'1\<rightarrow>* sourcenode a1"
          and "valid_edge a1" by -(erule path_split)+
        from \<open>\<forall>ax \<in> set((a#as'1)@a1#as'2). intra_kind(kind ax)\<close>
        have "\<forall>ax \<in> set(a#as'1). intra_kind(kind ax)" by simp
        with \<open>n' -a#as'1\<rightarrow>* sourcenode a1\<close> have "n' -a#as'1\<rightarrow>\<^sub>\<iota>* sourcenode a1"
          by(simp add:intra_path_def)
        hence "targetnode a -as'1\<rightarrow>\<^sub>\<iota>* sourcenode a1"
          by(fastforce intro:path_split_Cons simp:intra_path_def)
        from \<open>targetnode a -asx\<rightarrow>\<^sub>\<iota>* pex\<close> \<open>asx = as'1@a2#asx'1\<close>
        have "targetnode a -as'1@a2#asx'1\<rightarrow>* pex" by(simp add:intra_path_def)
        hence "targetnode a -as'1\<rightarrow>* sourcenode a2" and "valid_edge a2"
          and "targetnode a2 -asx'1\<rightarrow>* pex" by(auto intro:path_split)
        from \<open>targetnode a2 -asx'1\<rightarrow>* pex\<close> \<open>asx = as'1@a2#asx'1\<close>
          \<open>targetnode a -asx\<rightarrow>\<^sub>\<iota>* pex\<close>
        have "targetnode a2 -asx'1\<rightarrow>\<^sub>\<iota>* pex" by(simp add:intra_path_def)
        from \<open>targetnode a -as'1\<rightarrow>* sourcenode a2\<close> 
          \<open>targetnode a -as'1\<rightarrow>\<^sub>\<iota>* sourcenode a1\<close> 
        have "sourcenode a1 = sourcenode a2"
          by(fastforce intro:path_det simp:intra_path_def)
        from \<open>asx = as'1@a2#asx'1\<close> \<open>n \<notin> set (sourcenodes asx)\<close>
        have "n \<notin> set (sourcenodes asx'1)" by(simp add:sourcenodes_def)
        with \<open>targetnode a2 -asx'1\<rightarrow>\<^sub>\<iota>* pex\<close> \<open>method_exit pex\<close>
          \<open>asx = as'1@a2#asx'1\<close>
        have "\<not> n postdominates targetnode a2" by(fastforce simp:postdominate_def)
        from \<open>asx = as'1@a2#asx'1\<close> \<open>targetnode a -asx\<rightarrow>\<^sub>\<iota>* pex\<close>
        have "intra_kind (kind a2)" by(simp add:intra_path_def)
        from \<open>as' = as'1@a1#as'2\<close> have "a1 \<in> set as'" by simp
        with \<open>sourcenode a1 = sourcenode a2\<close> last \<open>valid_edge a2\<close> 
          \<open>intra_kind (kind a2)\<close>
        have "n postdominates targetnode a2" by blast
        with \<open>\<not> n postdominates targetnode a2\<close> have False by simp
        thus ?thesis by simp
      qed
    qed
  qed
qed



subsection \<open>SDG without summary edges\<close>


inductive cdep_edge :: "'node SDG_node \<Rightarrow> 'node SDG_node \<Rightarrow> bool" 
    ("_ \<longrightarrow>\<^bsub>cd\<^esub> _" [51,0] 80)
  and ddep_edge :: "'node SDG_node \<Rightarrow> 'var \<Rightarrow> 'node SDG_node \<Rightarrow> bool"
    ("_ -_\<rightarrow>\<^sub>d\<^sub>d _" [51,0,0] 80)
  and call_edge :: "'node SDG_node \<Rightarrow> 'pname \<Rightarrow> 'node SDG_node \<Rightarrow> bool" 
    ("_ -_\<rightarrow>\<^bsub>call\<^esub> _" [51,0,0] 80)
  and return_edge :: "'node SDG_node \<Rightarrow> 'pname \<Rightarrow> 'node SDG_node \<Rightarrow> bool" 
    ("_ -_\<rightarrow>\<^bsub>ret\<^esub> _" [51,0,0] 80)
  and param_in_edge :: "'node SDG_node \<Rightarrow> 'pname \<Rightarrow> 'var \<Rightarrow> 'node SDG_node \<Rightarrow> bool"
    ("_ -_:_\<rightarrow>\<^bsub>in\<^esub> _" [51,0,0,0] 80)
  and param_out_edge :: "'node SDG_node \<Rightarrow> 'pname \<Rightarrow> 'var \<Rightarrow> 'node SDG_node \<Rightarrow> bool"
    ("_ -_:_\<rightarrow>\<^bsub>out\<^esub> _" [51,0,0,0] 80)
  and SDG_edge :: "'node SDG_node \<Rightarrow> 'var option \<Rightarrow> 
                          ('pname \<times> bool) option \<Rightarrow> 'node SDG_node \<Rightarrow> bool"

where
    (* Syntax *)
  "n \<longrightarrow>\<^bsub>cd\<^esub> n' == SDG_edge n None None n'"
  | "n -V\<rightarrow>\<^sub>d\<^sub>d n' == SDG_edge n (Some V) None n'"
  | "n -p\<rightarrow>\<^bsub>call\<^esub> n' == SDG_edge n None (Some(p,True)) n'"
  | "n -p\<rightarrow>\<^bsub>ret\<^esub> n' == SDG_edge n None (Some(p,False)) n'"
  | "n -p:V\<rightarrow>\<^bsub>in\<^esub> n' == SDG_edge n (Some V) (Some(p,True)) n'"
  | "n -p:V\<rightarrow>\<^bsub>out\<^esub> n' == SDG_edge n (Some V) (Some(p,False)) n'"

    (* Rules *)
  | SDG_cdep_edge:
    "\<lbrakk>n = CFG_node m; n' = CFG_node m'; m controls m'\<rbrakk> \<Longrightarrow> n \<longrightarrow>\<^bsub>cd\<^esub> n'"
  | SDG_proc_entry_exit_cdep:
    "\<lbrakk>valid_edge a; kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs; n = CFG_node (targetnode a);
      a' \<in> get_return_edges a; n' = CFG_node (sourcenode a')\<rbrakk> \<Longrightarrow> n \<longrightarrow>\<^bsub>cd\<^esub> n'"
  | SDG_parent_cdep_edge:
    "\<lbrakk>valid_SDG_node n'; m = parent_node n'; n = CFG_node m; n \<noteq> n'\<rbrakk> 
      \<Longrightarrow> n \<longrightarrow>\<^bsub>cd\<^esub> n'"
  | SDG_ddep_edge:"n influences V in n' \<Longrightarrow> n -V\<rightarrow>\<^sub>d\<^sub>d n'"
  | SDG_call_edge:
    "\<lbrakk>valid_edge a; kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs; n = CFG_node (sourcenode a); 
      n' = CFG_node (targetnode a)\<rbrakk> \<Longrightarrow> n -p\<rightarrow>\<^bsub>call\<^esub> n'"
  | SDG_return_edge:
    "\<lbrakk>valid_edge a; kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f; n = CFG_node (sourcenode a); 
      n' = CFG_node (targetnode a)\<rbrakk> \<Longrightarrow> n -p\<rightarrow>\<^bsub>ret\<^esub> n'"
  | SDG_param_in_edge:
    "\<lbrakk>valid_edge a; kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs; (p,ins,outs) \<in> set procs; V = ins!x;
      x < length ins; n = Actual_in (sourcenode a,x); n' = Formal_in (targetnode a,x)\<rbrakk>
      \<Longrightarrow> n -p:V\<rightarrow>\<^bsub>in\<^esub> n'"
  | SDG_param_out_edge:
    "\<lbrakk>valid_edge a; kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f; (p,ins,outs) \<in> set procs; V = outs!x;
      x < length outs; n = Formal_out (sourcenode a,x); 
      n' = Actual_out (targetnode a,x)\<rbrakk>
      \<Longrightarrow> n -p:V\<rightarrow>\<^bsub>out\<^esub> n'"


lemma cdep_edge_cases:
  "\<lbrakk>n \<longrightarrow>\<^bsub>cd\<^esub> n'; (parent_node n) controls (parent_node n') \<Longrightarrow> P;
    \<And>a Q r p fs a'. \<lbrakk>valid_edge a; kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs; a' \<in> get_return_edges a;
                  parent_node n = targetnode a; parent_node n' = sourcenode a'\<rbrakk> \<Longrightarrow> P;
    \<And>m. \<lbrakk>n = CFG_node m; m = parent_node n'; n \<noteq> n'\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
by -(erule SDG_edge.cases,auto)


lemma SDG_edge_valid_SDG_node:
  assumes "SDG_edge n Vopt popt n'" 
  shows "valid_SDG_node n" and "valid_SDG_node n'"
using \<open>SDG_edge n Vopt popt n'\<close>
proof(induct rule:SDG_edge.induct)
  case (SDG_cdep_edge n m n' m') 
  thus "valid_SDG_node n" "valid_SDG_node n'"
    by(fastforce elim:control_dependence_path elim:path_valid_node 
                simp:intra_path_def)+
next
  case (SDG_proc_entry_exit_cdep a Q r p f n a' n') case 1
  from \<open>valid_edge a\<close> \<open>n = CFG_node (targetnode a)\<close> show ?case by simp
next
  case (SDG_proc_entry_exit_cdep a Q r p f n a' n') case 2
  from \<open>valid_edge a\<close> \<open>a' \<in> get_return_edges a\<close> have "valid_edge a'" 
    by(rule get_return_edges_valid)
  with \<open>n' = CFG_node (sourcenode a')\<close> show ?case by simp
next
  case (SDG_ddep_edge n V n')
  thus "valid_SDG_node n" "valid_SDG_node n'" 
    by(auto intro:in_Use_valid_SDG_node in_Def_valid_SDG_node
             simp:data_dependence_def)
qed(fastforce intro:valid_SDG_CFG_node)+


lemma valid_SDG_node_cases: 
  assumes "valid_SDG_node n"
  shows "n = CFG_node (parent_node n) \<or> CFG_node (parent_node n) \<longrightarrow>\<^bsub>cd\<^esub> n"
proof(cases n)
  case (CFG_node m) thus ?thesis by simp
next
  case (Formal_in z)
  from \<open>n = Formal_in z\<close> obtain m x where "z = (m,x)" by(cases z) auto
  with \<open>valid_SDG_node n\<close> \<open>n = Formal_in z\<close> have "CFG_node (parent_node n) \<longrightarrow>\<^bsub>cd\<^esub> n"
    by -(rule SDG_parent_cdep_edge,auto)
  thus ?thesis by fastforce
next
  case (Formal_out z)
  from \<open>n = Formal_out z\<close> obtain m x where "z = (m,x)" by(cases z) auto
  with \<open>valid_SDG_node n\<close> \<open>n = Formal_out z\<close> have "CFG_node (parent_node n) \<longrightarrow>\<^bsub>cd\<^esub> n"
    by -(rule SDG_parent_cdep_edge,auto)
  thus ?thesis by fastforce
next
  case (Actual_in z)
  from \<open>n = Actual_in z\<close> obtain m x where "z = (m,x)" by(cases z) auto
  with \<open>valid_SDG_node n\<close> \<open>n = Actual_in z\<close> have "CFG_node (parent_node n) \<longrightarrow>\<^bsub>cd\<^esub> n"
    by -(rule SDG_parent_cdep_edge,auto)
  thus ?thesis by fastforce
next
  case (Actual_out z)
  from \<open>n = Actual_out z\<close> obtain m x where "z = (m,x)" by(cases z) auto
  with \<open>valid_SDG_node n\<close> \<open>n = Actual_out z\<close> have "CFG_node (parent_node n) \<longrightarrow>\<^bsub>cd\<^esub> n"
    by -(rule SDG_parent_cdep_edge,auto)
  thus ?thesis by fastforce
qed


lemma SDG_cdep_edge_CFG_node: "n \<longrightarrow>\<^bsub>cd\<^esub> n' \<Longrightarrow> \<exists>m. n = CFG_node m"
by(induct n Vopt\<equiv>"None::'var option" popt\<equiv>"None::('pname \<times> bool) option" n' 
   rule:SDG_edge.induct) auto

lemma SDG_call_edge_CFG_node: "n -p\<rightarrow>\<^bsub>call\<^esub> n' \<Longrightarrow> \<exists>m. n = CFG_node m"
by(induct n Vopt\<equiv>"None::'var option" popt\<equiv>"Some(p,True)" n' 
   rule:SDG_edge.induct) auto

lemma SDG_return_edge_CFG_node: "n -p\<rightarrow>\<^bsub>ret\<^esub> n' \<Longrightarrow> \<exists>m. n = CFG_node m"
by(induct n Vopt\<equiv>"None::'var option" popt\<equiv>"Some(p,False)" n' 
   rule:SDG_edge.induct) auto



lemma SDG_call_or_param_in_edge_unique_CFG_call_edge:
  "SDG_edge n Vopt (Some(p,True)) n'
  \<Longrightarrow> \<exists>!a. valid_edge a \<and> sourcenode a = parent_node n \<and> 
          targetnode a = parent_node n' \<and> (\<exists>Q r fs. kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs)"
proof(induct n Vopt "Some(p,True)" n' rule:SDG_edge.induct)
  case (SDG_call_edge a Q r fs n n')
  { fix a' 
    assume "valid_edge a'" and "sourcenode a' = parent_node n"
      and "targetnode a' = parent_node n'"
    from \<open>sourcenode a' = parent_node n\<close> \<open>n = CFG_node (sourcenode a)\<close>
    have "sourcenode a' = sourcenode a" by fastforce
    moreover from \<open>targetnode a' = parent_node n'\<close> \<open>n' = CFG_node (targetnode a)\<close>
    have "targetnode a' = targetnode a" by fastforce
    ultimately have "a' = a" using \<open>valid_edge a'\<close> \<open>valid_edge a\<close>
      by(fastforce intro:edge_det) }
  with \<open>valid_edge a\<close> \<open>n = CFG_node (sourcenode a)\<close> \<open>n' = CFG_node (targetnode a)\<close>
    \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close> show ?case by(fastforce intro!:ex1I[of _ a])
next
  case (SDG_param_in_edge a Q r fs ins outs V x n n')
  { fix a' 
    assume "valid_edge a'" and "sourcenode a' = parent_node n"
      and "targetnode a' = parent_node n'"
    from \<open>sourcenode a' = parent_node n\<close> \<open>n = Actual_in (sourcenode a,x)\<close>
    have "sourcenode a' = sourcenode a" by fastforce
    moreover from \<open>targetnode a' = parent_node n'\<close> \<open>n' = Formal_in (targetnode a,x)\<close>
    have "targetnode a' = targetnode a" by fastforce
    ultimately have "a' = a" using \<open>valid_edge a'\<close> \<open>valid_edge a\<close>
      by(fastforce intro:edge_det) }
  with \<open>valid_edge a\<close> \<open>n = Actual_in (sourcenode a,x)\<close> 
    \<open>n' = Formal_in (targetnode a,x)\<close> \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close>
  show ?case by(fastforce intro!:ex1I[of _ a])
qed simp_all


lemma SDG_return_or_param_out_edge_unique_CFG_return_edge:
  "SDG_edge n Vopt (Some(p,False)) n'
  \<Longrightarrow> \<exists>!a. valid_edge a \<and> sourcenode a = parent_node n \<and> 
          targetnode a = parent_node n' \<and> (\<exists>Q f. kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f)"
proof(induct n Vopt "Some(p,False)" n' rule:SDG_edge.induct)
  case (SDG_return_edge a Q f n n')
  { fix a' 
    assume "valid_edge a'" and "sourcenode a' = parent_node n" 
      and "targetnode a' = parent_node n'"
    from \<open>sourcenode a' = parent_node n\<close> \<open>n = CFG_node (sourcenode a)\<close>
    have "sourcenode a' = sourcenode a" by fastforce
    moreover from \<open>targetnode a' = parent_node n'\<close> \<open>n' = CFG_node (targetnode a)\<close>
    have "targetnode a' = targetnode a" by fastforce
    ultimately have "a' = a" using \<open>valid_edge a'\<close> \<open>valid_edge a\<close>
      by(fastforce intro:edge_det) }
  with \<open>valid_edge a\<close> \<open>n = CFG_node (sourcenode a)\<close> \<open>n' = CFG_node (targetnode a)\<close>
    \<open>kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f\<close> show ?case by(fastforce intro!:ex1I[of _ a])
next
  case (SDG_param_out_edge a Q f ins outs V x n n')
  { fix a' 
    assume "valid_edge a'" and "sourcenode a' = parent_node n"
      and "targetnode a' = parent_node n'"
    from \<open>sourcenode a' = parent_node n\<close> \<open>n = Formal_out (sourcenode a,x)\<close>
    have "sourcenode a' = sourcenode a" by fastforce
    moreover from \<open>targetnode a' = parent_node n'\<close> \<open>n' = Actual_out (targetnode a,x)\<close>
    have "targetnode a' = targetnode a" by fastforce
    ultimately have "a' = a" using \<open>valid_edge a'\<close> \<open>valid_edge a\<close>
      by(fastforce intro:edge_det) }
  with \<open>valid_edge a\<close> \<open>n = Formal_out (sourcenode a,x)\<close>
    \<open>n' = Actual_out (targetnode a,x)\<close> \<open>kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f\<close>
  show ?case by(fastforce intro!:ex1I[of _ a])
qed simp_all


lemma Exit_no_SDG_edge_source:
  "SDG_edge (CFG_node (_Exit_)) Vopt popt n' \<Longrightarrow> False"
proof(induct "CFG_node (_Exit_)" Vopt popt n' rule:SDG_edge.induct)
  case (SDG_cdep_edge m n' m')
  hence "(_Exit_) controls m'" by simp
  thus ?case by fastforce
next
  case (SDG_proc_entry_exit_cdep a Q r p fs a' n')
  from \<open>CFG_node (_Exit_) = CFG_node (targetnode a)\<close>
  have "targetnode a = (_Exit_)" by simp
  from \<open>valid_edge a\<close> \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close> have "get_proc (targetnode a) = p"
    by(rule get_proc_call)
  with \<open>targetnode a = (_Exit_)\<close> have "p = Main"
    by(auto simp:get_proc_Exit)
  with \<open>valid_edge a\<close> \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close> have False
    by(fastforce intro:Main_no_call_target)
  thus ?thesis by simp
next
  case (SDG_parent_cdep_edge n' m)
  from \<open>CFG_node (_Exit_) = CFG_node m\<close> 
  have [simp]:"m = (_Exit_)" by simp
  with \<open>valid_SDG_node n'\<close> \<open>m = parent_node n'\<close> \<open>CFG_node (_Exit_) \<noteq> n'\<close>
  have False by -(drule valid_SDG_node_parent_Exit,simp+)
  thus ?thesis by simp
next
  case (SDG_ddep_edge V n')
  hence "(CFG_node (_Exit_)) influences V in n'" by simp
  with Exit_empty show ?case
    by(fastforce dest:path_Exit_source SDG_Def_parent_Def 
                simp:data_dependence_def intra_path_def)
next
  case (SDG_call_edge a Q r p fs n')
  from \<open>CFG_node (_Exit_) = CFG_node (sourcenode a)\<close>
  have "sourcenode a = (_Exit_)" by simp
  with \<open>valid_edge a\<close> show ?case by(rule Exit_source)
next
  case (SDG_return_edge a Q p f n')
  from \<open>CFG_node (_Exit_) = CFG_node (sourcenode a)\<close>
  have "sourcenode a = (_Exit_)" by simp
  with \<open>valid_edge a\<close> show ?case by(rule Exit_source)
qed simp_all


subsection \<open>Intraprocedural paths in the SDG\<close>

inductive intra_SDG_path :: 
  "'node SDG_node \<Rightarrow> 'node SDG_node list \<Rightarrow> 'node SDG_node \<Rightarrow> bool"
("_ i-_\<rightarrow>\<^sub>d* _" [51,0,0] 80) 

where iSp_Nil:
  "valid_SDG_node n \<Longrightarrow> n i-[]\<rightarrow>\<^sub>d* n"

  | iSp_Append_cdep:
  "\<lbrakk>n i-ns\<rightarrow>\<^sub>d* n''; n'' \<longrightarrow>\<^bsub>cd\<^esub> n'\<rbrakk> \<Longrightarrow> n i-ns@[n'']\<rightarrow>\<^sub>d* n'"

  | iSp_Append_ddep:
  "\<lbrakk>n i-ns\<rightarrow>\<^sub>d* n''; n'' -V\<rightarrow>\<^sub>d\<^sub>d n'; n'' \<noteq> n'\<rbrakk> \<Longrightarrow> n i-ns@[n'']\<rightarrow>\<^sub>d* n'"


lemma intra_SDG_path_Append:
  "\<lbrakk>n'' i-ns'\<rightarrow>\<^sub>d* n'; n i-ns\<rightarrow>\<^sub>d* n''\<rbrakk> \<Longrightarrow> n i-ns@ns'\<rightarrow>\<^sub>d* n'"
by(induct rule:intra_SDG_path.induct,
   auto intro:intra_SDG_path.intros simp:append_assoc[THEN sym] simp del:append_assoc)


lemma intra_SDG_path_valid_SDG_node:
  assumes "n i-ns\<rightarrow>\<^sub>d* n'" shows "valid_SDG_node n" and "valid_SDG_node n'"
using \<open>n i-ns\<rightarrow>\<^sub>d* n'\<close>
by(induct rule:intra_SDG_path.induct,
   auto intro:SDG_edge_valid_SDG_node valid_SDG_CFG_node)


lemma intra_SDG_path_intra_CFG_path:
  assumes "n i-ns\<rightarrow>\<^sub>d* n'"
  obtains as where "parent_node n -as\<rightarrow>\<^sub>\<iota>* parent_node n'" 
proof(atomize_elim)
  from \<open>n i-ns\<rightarrow>\<^sub>d* n'\<close>
  show "\<exists>as. parent_node n -as\<rightarrow>\<^sub>\<iota>* parent_node n'"
  proof(induct rule:intra_SDG_path.induct)
    case (iSp_Nil n)
    from \<open>valid_SDG_node n\<close> have "valid_node (parent_node n)"
      by(rule valid_SDG_CFG_node)
    hence "parent_node n -[]\<rightarrow>* parent_node n" by(rule empty_path)
    thus ?case by(auto simp:intra_path_def)
  next
    case (iSp_Append_cdep n ns n'' n')
    from \<open>\<exists>as. parent_node n -as\<rightarrow>\<^sub>\<iota>* parent_node n''\<close>
    obtain as where "parent_node n -as\<rightarrow>\<^sub>\<iota>* parent_node n''" by blast
    from \<open>n'' \<longrightarrow>\<^bsub>cd\<^esub> n'\<close> show ?case
    proof(rule cdep_edge_cases)
      assume "parent_node n'' controls parent_node n'"
      then obtain as' where "parent_node n'' -as'\<rightarrow>\<^sub>\<iota>* parent_node n'" and "as' \<noteq> []"
        by(erule control_dependence_path)
      with \<open>parent_node n -as\<rightarrow>\<^sub>\<iota>* parent_node n''\<close> 
      have "parent_node n -as@as'\<rightarrow>\<^sub>\<iota>* parent_node n'" by -(rule intra_path_Append)
      thus ?thesis by blast
    next
      fix a Q r p fs a'
      assume "valid_edge a" and "kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs" and "a' \<in> get_return_edges a"
        and "parent_node n'' = targetnode a" and "parent_node n' = sourcenode a'"
      then obtain a'' where "valid_edge a''" and "sourcenode a'' = targetnode a"
        and "targetnode a'' = sourcenode a'" and "kind a'' = (\<lambda>cf. False)\<^sub>\<surd>"
        by(auto dest:intra_proc_additional_edge)
      hence "targetnode a -[a'']\<rightarrow>\<^sub>\<iota>* sourcenode a'"
        by(fastforce dest:path_edge simp:intra_path_def intra_kind_def)
      with \<open>parent_node n'' = targetnode a\<close> \<open>parent_node n' = sourcenode a'\<close> 
      have "\<exists>as'. parent_node n'' -as'\<rightarrow>\<^sub>\<iota>* parent_node n' \<and> as' \<noteq> []" by fastforce
      then obtain as' where "parent_node n'' -as'\<rightarrow>\<^sub>\<iota>* parent_node n'" and "as' \<noteq> []"
        by blast
      with \<open>parent_node n -as\<rightarrow>\<^sub>\<iota>* parent_node n''\<close>
      have "parent_node n -as@as'\<rightarrow>\<^sub>\<iota>* parent_node n'" by -(rule intra_path_Append)
      thus ?thesis by blast
    next
      fix m assume "n'' = CFG_node m" and "m = parent_node n'"
      with \<open>parent_node n -as\<rightarrow>\<^sub>\<iota>* parent_node n''\<close> show ?thesis by fastforce
    qed
  next
    case (iSp_Append_ddep n ns n'' V n')
    from \<open>\<exists>as. parent_node n -as\<rightarrow>\<^sub>\<iota>* parent_node n''\<close>
    obtain as where "parent_node n -as\<rightarrow>\<^sub>\<iota>* parent_node n''" by blast 
    from \<open>n'' -V\<rightarrow>\<^sub>d\<^sub>d n'\<close> have "n'' influences V in n'"
      by(fastforce elim:SDG_edge.cases)
    then obtain as' where "parent_node n'' -as'\<rightarrow>\<^sub>\<iota>* parent_node n'"
      by(auto simp:data_dependence_def)
    with \<open>parent_node n -as\<rightarrow>\<^sub>\<iota>* parent_node n''\<close> 
    have "parent_node n -as@as'\<rightarrow>\<^sub>\<iota>* parent_node n'" by -(rule intra_path_Append)
    thus ?case by blast
  qed
qed


subsection \<open>Control dependence paths in the SDG\<close>

inductive cdep_SDG_path :: 
  "'node SDG_node \<Rightarrow> 'node SDG_node list \<Rightarrow> 'node SDG_node \<Rightarrow> bool"
("_ cd-_\<rightarrow>\<^sub>d* _" [51,0,0] 80) 

where cdSp_Nil:
  "valid_SDG_node n \<Longrightarrow> n cd-[]\<rightarrow>\<^sub>d* n"

  | cdSp_Append_cdep:
  "\<lbrakk>n cd-ns\<rightarrow>\<^sub>d* n''; n'' \<longrightarrow>\<^bsub>cd\<^esub> n'\<rbrakk> \<Longrightarrow> n cd-ns@[n'']\<rightarrow>\<^sub>d* n'"


lemma cdep_SDG_path_intra_SDG_path:
  "n cd-ns\<rightarrow>\<^sub>d* n' \<Longrightarrow> n i-ns\<rightarrow>\<^sub>d* n'"
by(induct rule:cdep_SDG_path.induct,auto intro:intra_SDG_path.intros)


lemma Entry_cdep_SDG_path:
  assumes "(_Entry_) -as\<rightarrow>\<^sub>\<iota>* n'" and "inner_node n'" and "\<not> method_exit n'"
  obtains ns where "CFG_node (_Entry_) cd-ns\<rightarrow>\<^sub>d* CFG_node n'"
  and "ns \<noteq> []" and "\<forall>n'' \<in> set ns. parent_node n'' \<in> set(sourcenodes as)"
proof(atomize_elim)
  from \<open>(_Entry_) -as\<rightarrow>\<^sub>\<iota>* n'\<close> \<open>inner_node n'\<close> \<open>\<not> method_exit n'\<close>
  show "\<exists>ns. CFG_node (_Entry_) cd-ns\<rightarrow>\<^sub>d* CFG_node n' \<and> ns \<noteq> [] \<and>
    (\<forall>n'' \<in> set ns. parent_node n'' \<in> set(sourcenodes as))"
  proof(induct as arbitrary:n' rule:length_induct)
    fix as n'
    assume IH:"\<forall>as'. length as' < length as \<longrightarrow>
      (\<forall>n''. (_Entry_) -as'\<rightarrow>\<^sub>\<iota>* n'' \<longrightarrow> inner_node n'' \<longrightarrow> \<not> method_exit n'' \<longrightarrow>
        (\<exists>ns. CFG_node (_Entry_) cd-ns\<rightarrow>\<^sub>d* CFG_node n'' \<and> ns \<noteq> [] \<and>
              (\<forall>nx\<in>set ns. parent_node nx \<in> set (sourcenodes as'))))"
      and "(_Entry_) -as\<rightarrow>\<^sub>\<iota>* n'" and "inner_node n'" and "\<not> method_exit n'"
    thus "\<exists>ns. CFG_node (_Entry_) cd-ns\<rightarrow>\<^sub>d* CFG_node n' \<and> ns \<noteq> [] \<and>
      (\<forall>n''\<in>set ns. parent_node n'' \<in> set (sourcenodes as))"
    proof -
      have "\<exists>ax asx zs. (_Entry_) -ax#asx\<rightarrow>\<^sub>\<iota>* n' \<and> n' \<notin> set (sourcenodes (ax#asx)) \<and> 
                        as = (ax#asx)@zs"
      proof(cases "n' \<in> set (sourcenodes as)")
        case True
        hence "\<exists>n'' \<in> set(sourcenodes as). n' = n''" by simp
        then obtain ns' ns'' where "sourcenodes as = ns'@n'#ns''"
          and "\<forall>n'' \<in> set ns'. n' \<noteq> n''"
          by(fastforce elim!:split_list_first_propE)
        from \<open>sourcenodes as = ns'@n'#ns''\<close> obtain xs ys ax
          where "sourcenodes xs = ns'" and "as = xs@ax#ys"
          and "sourcenode ax = n'"
          by(fastforce elim:map_append_append_maps simp:sourcenodes_def)
        from \<open>\<forall>n'' \<in> set ns'. n' \<noteq> n''\<close> \<open>sourcenodes xs = ns'\<close>
        have "n' \<notin> set(sourcenodes xs)" by fastforce
        from \<open>(_Entry_) -as\<rightarrow>\<^sub>\<iota>* n'\<close> \<open>as = xs@ax#ys\<close> have "(_Entry_) -xs@ax#ys\<rightarrow>\<^sub>\<iota>* n'"
          by simp
        with \<open>sourcenode ax = n'\<close> have "(_Entry_) -xs\<rightarrow>\<^sub>\<iota>* n'" 
          by(fastforce dest:path_split simp:intra_path_def)
        with \<open>inner_node n'\<close> have "xs \<noteq> []"
          by(fastforce elim:path.cases simp:intra_path_def)
        with \<open>n' \<notin> set(sourcenodes xs)\<close> \<open>(_Entry_) -xs\<rightarrow>\<^sub>\<iota>* n'\<close> \<open>as = xs@ax#ys\<close>
        show ?thesis by(cases xs) auto
      next
        case False
        with \<open>(_Entry_) -as\<rightarrow>\<^sub>\<iota>* n'\<close> \<open>inner_node n'\<close>
        show ?thesis by(cases as)(auto elim:path.cases simp:intra_path_def)
      qed
      then obtain ax asx zs where "(_Entry_) -ax#asx\<rightarrow>\<^sub>\<iota>* n'" 
        and "n' \<notin> set (sourcenodes (ax#asx))" and "as = (ax#asx)@zs" by blast
      show ?thesis
      proof(cases "\<forall>a' a''. a' \<in> set asx \<and> sourcenode a' = sourcenode a'' \<and> 
          valid_edge a'' \<and> intra_kind(kind a'') \<longrightarrow> n' postdominates targetnode a''")
        case True
        have "(_Exit_) -[]\<rightarrow>\<^sub>\<iota>* (_Exit_)" 
          by(fastforce intro:empty_path simp:intra_path_def)
        hence "\<not> n' postdominates (_Exit_)"
          by(fastforce simp:postdominate_def sourcenodes_def method_exit_def)
        from \<open>(_Entry_) -ax#asx\<rightarrow>\<^sub>\<iota>* n'\<close> have "(_Entry_) -[]@ax#asx\<rightarrow>\<^sub>\<iota>* n'" by simp
        from \<open>(_Entry_) -ax#asx\<rightarrow>\<^sub>\<iota>* n'\<close> have [simp]:"sourcenode ax = (_Entry_)" 
          and "valid_edge ax"
          by(auto intro:path_split_Cons simp:intra_path_def)
        from Entry_Exit_edge obtain a' where "sourcenode a' = (_Entry_)"
          and "targetnode a' = (_Exit_)" and "valid_edge a'" 
          and "intra_kind(kind a')" by(auto simp:intra_kind_def)
        with \<open>(_Entry_) -[]@ax#asx\<rightarrow>\<^sub>\<iota>* n'\<close> \<open>\<not> n' postdominates (_Exit_)\<close>
          \<open>valid_edge ax\<close> True \<open>sourcenode ax = (_Entry_)\<close> 
          \<open>n' \<notin> set (sourcenodes (ax#asx))\<close> \<open>inner_node n'\<close> \<open>\<not> method_exit n'\<close>
        have "sourcenode ax controls n'"
          by -(erule which_node_intra_standard_control_dependence_source
                     [of _ _ _ _ _ _ a'],auto)
        hence "CFG_node (_Entry_) \<longrightarrow>\<^bsub>cd\<^esub> CFG_node n'"
          by(fastforce intro:SDG_cdep_edge)
        hence "CFG_node (_Entry_) cd-[]@[CFG_node (_Entry_)]\<rightarrow>\<^sub>d* CFG_node n'"
          by(fastforce intro:cdSp_Append_cdep cdSp_Nil)
        moreover
        from \<open>as = (ax#asx)@zs\<close> have "(_Entry_) \<in> set(sourcenodes as)"
          by(simp add:sourcenodes_def)
        ultimately show ?thesis by fastforce
      next
        case False
        hence "\<exists>a' \<in> set asx. \<exists>a''. sourcenode a' = sourcenode a'' \<and> valid_edge a'' \<and>
          intra_kind(kind a'') \<and> \<not> n' postdominates targetnode a''"
          by fastforce
        then obtain ax' asx' asx'' where "asx = asx'@ax'#asx'' \<and>
          (\<exists>a''. sourcenode ax' = sourcenode a'' \<and> valid_edge a'' \<and>
          intra_kind(kind a'') \<and> \<not> n' postdominates targetnode a'') \<and>
          (\<forall>z \<in> set asx''. \<not> (\<exists>a''. sourcenode z = sourcenode a'' \<and> valid_edge a'' \<and>
          intra_kind(kind a'') \<and> \<not> n' postdominates targetnode a''))"
          by(blast elim!:split_list_last_propE)
        then obtain ai where "asx = asx'@ax'#asx''"
          and "sourcenode ax' = sourcenode ai"
          and "valid_edge ai" and "intra_kind(kind ai)"
          and "\<not> n' postdominates targetnode ai"
          and "\<forall>z \<in> set asx''. \<not> (\<exists>a''. sourcenode z = sourcenode a'' \<and> 
          valid_edge a'' \<and> intra_kind(kind a'') \<and> \<not> n' postdominates targetnode a'')"
          by blast
        from \<open>(_Entry_) -ax#asx\<rightarrow>\<^sub>\<iota>* n'\<close> \<open>asx = asx'@ax'#asx''\<close>
        have "(_Entry_) -(ax#asx')@ax'#asx''\<rightarrow>\<^sub>\<iota>* n'" by simp
        from \<open>n' \<notin> set (sourcenodes (ax#asx))\<close> \<open>asx = asx'@ax'#asx''\<close>
        have "n' \<notin> set (sourcenodes (ax'#asx''))"
          by(auto simp:sourcenodes_def)
        with \<open>inner_node n'\<close> \<open>\<not> n' postdominates targetnode ai\<close>
          \<open>n' \<notin> set (sourcenodes (ax'#asx''))\<close> \<open>sourcenode ax' = sourcenode ai\<close>
          \<open>\<forall>z \<in> set asx''. \<not> (\<exists>a''. sourcenode z = sourcenode a'' \<and> 
          valid_edge a'' \<and> intra_kind(kind a'') \<and> \<not> n' postdominates targetnode a'')\<close>
          \<open>valid_edge ai\<close> \<open>intra_kind(kind ai)\<close> \<open>\<not> method_exit n'\<close>
          \<open>(_Entry_) -(ax#asx')@ax'#asx''\<rightarrow>\<^sub>\<iota>* n'\<close>
        have "sourcenode ax' controls n'"
          by(fastforce intro!:which_node_intra_standard_control_dependence_source)
        hence "CFG_node (sourcenode ax') \<longrightarrow>\<^bsub>cd\<^esub> CFG_node n'"
          by(fastforce intro:SDG_cdep_edge)
        from \<open>(_Entry_) -(ax#asx')@ax'#asx''\<rightarrow>\<^sub>\<iota>* n'\<close>
        have "(_Entry_) -ax#asx'\<rightarrow>\<^sub>\<iota>* sourcenode ax'" and "valid_edge ax'"
          by(auto intro:path_split simp:intra_path_def simp del:append_Cons)
        from \<open>asx = asx'@ax'#asx''\<close> \<open>as = (ax#asx)@zs\<close>
        have "length (ax#asx') < length as" by simp
        from \<open>valid_edge ax'\<close> have "valid_node (sourcenode ax')" by simp
        hence "inner_node (sourcenode ax')"
        proof(cases "sourcenode ax'" rule:valid_node_cases)
          case Entry 
          with \<open>(_Entry_) -ax#asx'\<rightarrow>\<^sub>\<iota>* sourcenode ax'\<close>
          have "(_Entry_) -ax#asx'\<rightarrow>* (_Entry_)" by(simp add:intra_path_def)
          hence False by(fastforce dest:path_Entry_target)
          thus ?thesis by simp
        next
          case Exit
          with \<open>valid_edge ax'\<close> have False by(rule Exit_source)
          thus ?thesis by simp
        qed simp
        from \<open>asx = asx'@ax'#asx''\<close> \<open>(_Entry_) -ax#asx\<rightarrow>\<^sub>\<iota>* n'\<close>
        have "intra_kind (kind ax')" by(simp add:intra_path_def)
        have "\<not> method_exit (sourcenode ax')"
        proof
          assume "method_exit (sourcenode ax')"
          thus False
          proof(rule method_exit_cases)
            assume "sourcenode ax' = (_Exit_)"
            with \<open>valid_edge ax'\<close> show False by(rule Exit_source)
          next
            fix x Q f p assume " sourcenode ax' = sourcenode x"
              and "valid_edge x" and "kind x = Q\<hookleftarrow>\<^bsub>p\<^esub>f"
            from \<open>valid_edge x\<close> \<open>kind x = Q\<hookleftarrow>\<^bsub>p\<^esub>f\<close> \<open>sourcenode ax' = sourcenode x\<close>
            \<open>valid_edge ax'\<close> \<open>intra_kind (kind ax')\<close> show False
              by(fastforce dest:return_edges_only simp:intra_kind_def)
          qed
        qed
        with IH \<open>length (ax#asx') < length as\<close> \<open>(_Entry_) -ax#asx'\<rightarrow>\<^sub>\<iota>* sourcenode ax'\<close>
          \<open>inner_node (sourcenode ax')\<close>
        obtain ns where "CFG_node (_Entry_) cd-ns\<rightarrow>\<^sub>d* CFG_node (sourcenode ax')"
          and "ns \<noteq> []" 
          and "\<forall>n'' \<in> set ns. parent_node n'' \<in> set(sourcenodes (ax#asx'))"
          by blast
        from \<open>CFG_node (_Entry_) cd-ns\<rightarrow>\<^sub>d* CFG_node (sourcenode ax')\<close>
          \<open>CFG_node (sourcenode ax') \<longrightarrow>\<^bsub>cd\<^esub> CFG_node n'\<close>
        have "CFG_node (_Entry_) cd-ns@[CFG_node (sourcenode ax')]\<rightarrow>\<^sub>d* CFG_node n'"
          by(fastforce intro:cdSp_Append_cdep)
        from \<open>as = (ax#asx)@zs\<close> \<open>asx = asx'@ax'#asx''\<close>
        have "sourcenode ax' \<in> set(sourcenodes as)" by(simp add:sourcenodes_def)
        with \<open>\<forall>n'' \<in> set ns. parent_node n'' \<in> set(sourcenodes (ax#asx'))\<close>
          \<open>as = (ax#asx)@zs\<close> \<open>asx = asx'@ax'#asx''\<close>
        have "\<forall>n'' \<in> set (ns@[CFG_node (sourcenode ax')]).
          parent_node n'' \<in> set(sourcenodes as)"
          by(fastforce simp:sourcenodes_def)
        with \<open>CFG_node (_Entry_) cd-ns@[CFG_node (sourcenode ax')]\<rightarrow>\<^sub>d* CFG_node n'\<close>
        show ?thesis by fastforce
      qed
    qed
  qed
qed


lemma in_proc_cdep_SDG_path:
  assumes "n -as\<rightarrow>\<^sub>\<iota>* n'" and "n \<noteq> n'" and "n' \<noteq> (_Exit_)" and "valid_edge a"
  and "kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs" and "targetnode a = n"
  obtains ns where "CFG_node n cd-ns\<rightarrow>\<^sub>d* CFG_node n'"
  and "ns \<noteq> []" and "\<forall>n'' \<in> set ns. parent_node n'' \<in> set(sourcenodes as)"
proof(atomize_elim)
  show "\<exists>ns. CFG_node n cd-ns\<rightarrow>\<^sub>d* CFG_node n' \<and>
             ns \<noteq> [] \<and> (\<forall>n''\<in>set ns. parent_node n'' \<in> set (sourcenodes as))"
  proof(cases "\<forall>ax. valid_edge ax \<and> sourcenode ax = n' \<longrightarrow> 
                    ax \<notin> get_return_edges a")
    case True
    from \<open>n -as\<rightarrow>\<^sub>\<iota>* n'\<close> \<open>n \<noteq> n'\<close> \<open>n' \<noteq> (_Exit_)\<close>
      \<open>\<forall>ax. valid_edge ax \<and> sourcenode ax = n' \<longrightarrow> ax \<notin> get_return_edges a\<close>
    show "\<exists>ns. CFG_node n cd-ns\<rightarrow>\<^sub>d* CFG_node n' \<and> ns \<noteq> [] \<and>
      (\<forall>n'' \<in> set ns. parent_node n'' \<in> set(sourcenodes as))"
    proof(induct as arbitrary:n' rule:length_induct)
      fix as n'
      assume IH:"\<forall>as'. length as' < length as \<longrightarrow>
        (\<forall>n''. n -as'\<rightarrow>\<^sub>\<iota>* n'' \<longrightarrow> n \<noteq> n'' \<longrightarrow> n'' \<noteq> (_Exit_) \<longrightarrow>
          (\<forall>ax. valid_edge ax \<and> sourcenode ax = n'' \<longrightarrow> ax \<notin> get_return_edges a) \<longrightarrow>
            (\<exists>ns. CFG_node n cd-ns\<rightarrow>\<^sub>d* CFG_node n'' \<and> ns \<noteq> [] \<and>
                  (\<forall>n''\<in>set ns. parent_node n'' \<in> set (sourcenodes as'))))"
        and "n -as\<rightarrow>\<^sub>\<iota>* n'" and "n \<noteq> n'" and "n' \<noteq> (_Exit_)"
        and "\<forall>ax. valid_edge ax \<and> sourcenode ax = n' \<longrightarrow> ax \<notin> get_return_edges a"
      show "\<exists>ns. CFG_node n cd-ns\<rightarrow>\<^sub>d* CFG_node n' \<and> ns \<noteq> [] \<and>
                 (\<forall>n''\<in>set ns. parent_node n'' \<in> set (sourcenodes as))"
      proof(cases "method_exit n'")
        case True
        thus ?thesis
        proof(rule method_exit_cases)
          assume "n' = (_Exit_)"
          with \<open>n' \<noteq> (_Exit_)\<close> have False by simp
          thus ?thesis by simp
        next
          fix a' Q' f' p'
          assume "n' = sourcenode a'" and "valid_edge a'" and "kind a' = Q'\<hookleftarrow>\<^bsub>p'\<^esub>f'"
          from \<open>valid_edge a\<close> \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close> have "get_proc(targetnode a) = p"
            by(rule get_proc_call)
          from \<open>n -as\<rightarrow>\<^sub>\<iota>* n'\<close> have "get_proc n = get_proc n'" 
            by(rule intra_path_get_procs)
          with \<open>get_proc(targetnode a) = p\<close> \<open>targetnode a = n\<close>
          have "get_proc (targetnode a) = get_proc n'" by simp
          from \<open>valid_edge a'\<close> \<open>kind a' = Q'\<hookleftarrow>\<^bsub>p'\<^esub>f'\<close>
          have "get_proc (sourcenode a') = p'" by(rule get_proc_return)
          with \<open>n' = sourcenode a'\<close> \<open>get_proc (targetnode a) = get_proc n'\<close> 
            \<open>get_proc (targetnode a) = p\<close> have "p = p'" by simp
          with \<open>valid_edge a'\<close> \<open>kind a' = Q'\<hookleftarrow>\<^bsub>p'\<^esub>f'\<close>
          obtain ax where "valid_edge ax" and "\<exists>Q r fs. kind ax = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs"
            and "a' \<in> get_return_edges ax" by(auto dest:return_needs_call)
          hence "CFG_node (targetnode ax) \<longrightarrow>\<^bsub>cd\<^esub> CFG_node (sourcenode a')"
            by(fastforce intro:SDG_proc_entry_exit_cdep)
          with \<open>valid_edge ax\<close> 
          have "CFG_node (targetnode ax) cd-[]@[CFG_node (targetnode ax)]\<rightarrow>\<^sub>d* 
            CFG_node (sourcenode a')"
            by(fastforce intro:cdep_SDG_path.intros)
          from \<open>valid_edge a\<close> \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close> \<open>valid_edge ax\<close> 
            \<open>\<exists>Q r fs. kind ax = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close> have "targetnode a = targetnode ax"
            by(fastforce intro:same_proc_call_unique_target)
          from \<open>n -as\<rightarrow>\<^sub>\<iota>* n'\<close> \<open>n \<noteq> n'\<close>
          have "as \<noteq> []" by(fastforce elim:path.cases simp:intra_path_def)
          with \<open>n -as\<rightarrow>\<^sub>\<iota>* n'\<close> have "hd (sourcenodes as) = n"
            by(fastforce intro:path_sourcenode simp:intra_path_def)
          moreover
          from \<open>as \<noteq> []\<close> have "hd (sourcenodes as) \<in> set (sourcenodes as)"
            by(fastforce intro:hd_in_set simp:sourcenodes_def)
          ultimately have "n \<in> set (sourcenodes as)" by simp
          with \<open>n' = sourcenode a'\<close> \<open>targetnode a = targetnode ax\<close>
            \<open>targetnode a = n\<close>
            \<open>CFG_node (targetnode ax) cd-[]@[CFG_node (targetnode ax)]\<rightarrow>\<^sub>d* 
            CFG_node (sourcenode a')\<close>
          show ?thesis by fastforce
        qed
      next
        case False
        from \<open>valid_edge a\<close> \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close> obtain a' 
          where "a' \<in> get_return_edges a"
          by(fastforce dest:get_return_edge_call)
        with \<open>valid_edge a\<close> \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close> obtain Q' f' where "kind a' = Q'\<hookleftarrow>\<^bsub>p\<^esub>f'"
          by(fastforce dest!:call_return_edges)
        with \<open>valid_edge a\<close> \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close> \<open>a' \<in> get_return_edges a\<close> obtain a''
          where "valid_edge a''" and "sourcenode a'' = targetnode a" 
          and "targetnode a'' = sourcenode a'" and "kind a'' = (\<lambda>cf. False)\<^sub>\<surd>"
          by -(drule intra_proc_additional_edge,auto)
        from \<open>valid_edge a\<close> \<open>a' \<in> get_return_edges a\<close> have "valid_edge a'"
          by(rule get_return_edges_valid)
        have "\<exists>ax asx zs. n -ax#asx\<rightarrow>\<^sub>\<iota>* n' \<and> n' \<notin> set (sourcenodes (ax#asx)) \<and> 
                          as = (ax#asx)@zs"
        proof(cases "n' \<in> set (sourcenodes as)")
          case True
          hence "\<exists>n'' \<in> set(sourcenodes as). n' = n''" by simp
          then obtain ns' ns'' where "sourcenodes as = ns'@n'#ns''"
            and "\<forall>n'' \<in> set ns'. n' \<noteq> n''"
            by(fastforce elim!:split_list_first_propE)
          from \<open>sourcenodes as = ns'@n'#ns''\<close> obtain xs ys ax
            where "sourcenodes xs = ns'" and "as = xs@ax#ys"
            and "sourcenode ax = n'"
            by(fastforce elim:map_append_append_maps simp:sourcenodes_def)
          from \<open>\<forall>n'' \<in> set ns'. n' \<noteq> n''\<close> \<open>sourcenodes xs = ns'\<close>
          have "n' \<notin> set(sourcenodes xs)" by fastforce
          from \<open>n -as\<rightarrow>\<^sub>\<iota>* n'\<close> \<open>as = xs@ax#ys\<close> have "n -xs@ax#ys\<rightarrow>\<^sub>\<iota>* n'" by simp
          with \<open>sourcenode ax = n'\<close> have "n -xs\<rightarrow>\<^sub>\<iota>* n'" 
            by(fastforce dest:path_split simp:intra_path_def)
          with \<open>n \<noteq> n'\<close> have "xs \<noteq> []" by(fastforce simp:intra_path_def)
          with \<open>n' \<notin> set(sourcenodes xs)\<close> \<open>n -xs\<rightarrow>\<^sub>\<iota>* n'\<close> \<open>as = xs@ax#ys\<close> show ?thesis
            by(cases xs) auto
        next
          case False
          with \<open>n -as\<rightarrow>\<^sub>\<iota>* n'\<close> \<open>n \<noteq> n'\<close> 
          show ?thesis by(cases as)(auto simp:intra_path_def)
        qed
        then obtain ax asx zs where "n -ax#asx\<rightarrow>\<^sub>\<iota>* n'" 
          and "n' \<notin> set (sourcenodes (ax#asx))" and "as = (ax#asx)@zs" by blast
        from \<open>n -ax#asx\<rightarrow>\<^sub>\<iota>* n'\<close> \<open>n' \<noteq> (_Exit_)\<close> have "inner_node n'"
          by(fastforce intro:path_valid_node simp:inner_node_def intra_path_def)
        from \<open>valid_edge a\<close> \<open>targetnode a = n\<close> have "valid_node n" by fastforce
        show ?thesis
        proof(cases "\<forall>a' a''. a' \<in> set asx \<and> sourcenode a' = sourcenode a'' \<and> 
            valid_edge a'' \<and> intra_kind(kind a'') \<longrightarrow> 
            n' postdominates targetnode a''")
          case True
          from \<open>targetnode a = n\<close> \<open>sourcenode a'' = targetnode a\<close> 
            \<open>kind a'' = (\<lambda>cf. False)\<^sub>\<surd>\<close>
          have "sourcenode a'' = n" and "intra_kind(kind a'')"
            by(auto simp:intra_kind_def)
          { fix as' assume "targetnode a'' -as'\<rightarrow>\<^sub>\<iota>* n'"
            from \<open>valid_edge a'\<close> \<open>targetnode a'' = sourcenode a'\<close> 
              \<open>a' \<in> get_return_edges a\<close> 
              \<open>\<forall>ax. valid_edge ax \<and> sourcenode ax = n' \<longrightarrow> ax \<notin> get_return_edges a\<close>
            have "targetnode a'' \<noteq> n'" by fastforce
            with \<open>targetnode a'' -as'\<rightarrow>\<^sub>\<iota>* n'\<close> obtain ax' where "valid_edge ax'"
              and "targetnode a'' = sourcenode ax'" and "intra_kind(kind ax')"
              by(clarsimp simp:intra_path_def)(erule path.cases,fastforce+)
            from \<open>valid_edge a'\<close> \<open>kind a' = Q'\<hookleftarrow>\<^bsub>p\<^esub>f'\<close> \<open>valid_edge ax'\<close>
              \<open>targetnode a'' = sourcenode a'\<close> \<open>targetnode a'' = sourcenode ax'\<close>
              \<open>intra_kind(kind ax')\<close>
            have False by(fastforce dest:return_edges_only simp:intra_kind_def) }
          hence "\<not> n' postdominates targetnode a''"
            by(fastforce elim:postdominate_implies_inner_path)
          from \<open>n -ax#asx\<rightarrow>\<^sub>\<iota>* n'\<close> have "sourcenode ax = n"
            by(auto intro:path_split_Cons simp:intra_path_def)
          from \<open>n -ax#asx\<rightarrow>\<^sub>\<iota>* n'\<close> have "n -[]@ax#asx\<rightarrow>\<^sub>\<iota>* n'" by simp
          from this \<open>sourcenode a'' = n\<close> \<open>sourcenode ax = n\<close> True
            \<open>n' \<notin> set (sourcenodes (ax#asx))\<close> \<open>valid_edge a''\<close> \<open>intra_kind(kind a'')\<close>
            \<open>inner_node n'\<close> \<open>\<not> method_exit n'\<close> \<open>\<not> n' postdominates targetnode a''\<close>
          have "n controls n'"
            by(fastforce intro!:which_node_intra_standard_control_dependence_source)
          hence "CFG_node n \<longrightarrow>\<^bsub>cd\<^esub> CFG_node n'"
            by(fastforce intro:SDG_cdep_edge)
          with \<open>valid_node n\<close> have "CFG_node n cd-[]@[CFG_node n]\<rightarrow>\<^sub>d* CFG_node n'"
            by(fastforce intro:cdSp_Append_cdep cdSp_Nil)
          moreover
          from \<open>as = (ax#asx)@zs\<close> \<open>sourcenode ax = n\<close> have "n \<in> set(sourcenodes as)"
            by(simp add:sourcenodes_def)
          ultimately show ?thesis by fastforce
        next
          case False
          hence "\<exists>a' \<in> set asx. \<exists>a''. sourcenode a' = sourcenode a'' \<and> 
            valid_edge a'' \<and> intra_kind(kind a'') \<and> 
            \<not> n' postdominates targetnode a''"
            by fastforce
          then obtain ax' asx' asx'' where "asx = asx'@ax'#asx'' \<and>
            (\<exists>a''. sourcenode ax' = sourcenode a'' \<and> valid_edge a'' \<and>
            intra_kind(kind a'') \<and> \<not> n' postdominates targetnode a'') \<and>
            (\<forall>z \<in> set asx''. \<not> (\<exists>a''. sourcenode z = sourcenode a'' \<and> 
            valid_edge a'' \<and> intra_kind(kind a'') \<and> 
            \<not> n' postdominates targetnode a''))"
            by(blast elim!:split_list_last_propE)
          then obtain ai where "asx = asx'@ax'#asx''"
            and "sourcenode ax' = sourcenode ai"
            and "valid_edge ai" and "intra_kind(kind ai)"
            and "\<not> n' postdominates targetnode ai"
            and "\<forall>z \<in> set asx''. \<not> (\<exists>a''. sourcenode z = sourcenode a'' \<and> 
            valid_edge a'' \<and> intra_kind(kind a'') \<and> 
            \<not> n' postdominates targetnode a'')"
            by blast
          from \<open>asx = asx'@ax'#asx''\<close> \<open>n -ax#asx\<rightarrow>\<^sub>\<iota>* n'\<close>
          have "n -(ax#asx')@ax'#asx''\<rightarrow>\<^sub>\<iota>* n'" by simp
          from \<open>n' \<notin> set (sourcenodes (ax#asx))\<close> \<open>asx = asx'@ax'#asx''\<close>
          have "n' \<notin> set (sourcenodes (ax'#asx''))"
            by(auto simp:sourcenodes_def)
          with \<open>inner_node n'\<close> \<open>\<not> n' postdominates targetnode ai\<close>
            \<open>n -(ax#asx')@ax'#asx''\<rightarrow>\<^sub>\<iota>* n'\<close> \<open>sourcenode ax' = sourcenode ai\<close>
            \<open>\<forall>z \<in> set asx''. \<not> (\<exists>a''. sourcenode z = sourcenode a'' \<and> 
            valid_edge a'' \<and> intra_kind(kind a'') \<and> 
            \<not> n' postdominates targetnode a'')\<close>
            \<open>valid_edge ai\<close> \<open>intra_kind(kind ai)\<close> \<open>\<not> method_exit n'\<close>
          have "sourcenode ax' controls n'"
            by(fastforce intro!:which_node_intra_standard_control_dependence_source)
          hence "CFG_node (sourcenode ax') \<longrightarrow>\<^bsub>cd\<^esub> CFG_node n'"
            by(fastforce intro:SDG_cdep_edge)
          from \<open>n -(ax#asx')@ax'#asx''\<rightarrow>\<^sub>\<iota>* n'\<close>
          have "n -ax#asx'\<rightarrow>\<^sub>\<iota>* sourcenode ax'" and "valid_edge ax'"
            by(auto intro:path_split simp:intra_path_def simp del:append_Cons)
          from \<open>asx = asx'@ax'#asx''\<close> \<open>as = (ax#asx)@zs\<close>
          have "length (ax#asx') < length as" by simp
          from \<open>as = (ax#asx)@zs\<close> \<open>asx = asx'@ax'#asx''\<close>
          have "sourcenode ax' \<in> set(sourcenodes as)" by(simp add:sourcenodes_def)
          show ?thesis
          proof(cases "n = sourcenode ax'")
            case True
            with \<open>CFG_node (sourcenode ax') \<longrightarrow>\<^bsub>cd\<^esub> CFG_node n'\<close> \<open>valid_edge ax'\<close>
            have "CFG_node n cd-[]@[CFG_node n]\<rightarrow>\<^sub>d* CFG_node n'"
              by(fastforce intro:cdSp_Append_cdep cdSp_Nil)
            with \<open>sourcenode ax' \<in> set(sourcenodes as)\<close> True show ?thesis by fastforce
          next
            case False
            from \<open>valid_edge ax'\<close> have "sourcenode ax' \<noteq> (_Exit_)"
              by -(rule ccontr,fastforce elim!:Exit_source)
            from \<open>n -ax#asx'\<rightarrow>\<^sub>\<iota>* sourcenode ax'\<close> have "n = sourcenode ax"
              by(fastforce intro:path_split_Cons simp:intra_path_def)
            show ?thesis
            proof(cases "\<forall>ax. valid_edge ax \<and> sourcenode ax = sourcenode ax' \<longrightarrow>
                ax \<notin> get_return_edges a")
              case True
              from \<open>asx = asx'@ax'#asx''\<close> \<open>n -ax#asx\<rightarrow>\<^sub>\<iota>* n'\<close>
              have "intra_kind (kind ax')" by(simp add:intra_path_def)
              have "\<not> method_exit (sourcenode ax')"
              proof
                assume "method_exit (sourcenode ax')"
                thus False
                proof(rule method_exit_cases)
                  assume "sourcenode ax' = (_Exit_)"
                  with \<open>valid_edge ax'\<close> show False by(rule Exit_source)
                next
                  fix x Q f p assume " sourcenode ax' = sourcenode x"
                    and "valid_edge x" and "kind x = Q\<hookleftarrow>\<^bsub>p\<^esub>f"
                  from \<open>valid_edge x\<close> \<open>kind x = Q\<hookleftarrow>\<^bsub>p\<^esub>f\<close> \<open>sourcenode ax' = sourcenode x\<close>
                    \<open>valid_edge ax'\<close> \<open>intra_kind (kind ax')\<close> show False
                    by(fastforce dest:return_edges_only simp:intra_kind_def)
                qed
              qed
              with IH \<open>length (ax#asx') < length as\<close> \<open>n -ax#asx'\<rightarrow>\<^sub>\<iota>* sourcenode ax'\<close>
                \<open>n \<noteq> sourcenode ax'\<close> \<open>sourcenode ax' \<noteq> (_Exit_)\<close> True
              obtain ns where "CFG_node n cd-ns\<rightarrow>\<^sub>d* CFG_node (sourcenode ax')"
                and "ns \<noteq> []" 
                and "\<forall>n''\<in>set ns. parent_node n'' \<in> set (sourcenodes (ax#asx'))"
                by blast
              from \<open>CFG_node n cd-ns\<rightarrow>\<^sub>d* CFG_node (sourcenode ax')\<close>
                \<open>CFG_node (sourcenode ax') \<longrightarrow>\<^bsub>cd\<^esub> CFG_node n'\<close>
              have "CFG_node n cd-ns@[CFG_node (sourcenode ax')]\<rightarrow>\<^sub>d* CFG_node n'"
                by(rule cdSp_Append_cdep)
              moreover
              from \<open>\<forall>n''\<in>set ns. parent_node n'' \<in> set (sourcenodes (ax#asx'))\<close>
                \<open>asx = asx'@ax'#asx''\<close> \<open>as = (ax#asx)@zs\<close>
                \<open>sourcenode ax' \<in> set(sourcenodes as)\<close>
              have "\<forall>n''\<in>set (ns@[CFG_node (sourcenode ax')]). 
                parent_node n'' \<in> set (sourcenodes as)"
                by(fastforce simp:sourcenodes_def)
              ultimately show ?thesis by fastforce
            next
              case False
              then obtain ai' where "valid_edge ai'" 
                and "sourcenode ai' = sourcenode ax'" 
                and "ai' \<in> get_return_edges a" by blast
              with \<open>valid_edge a\<close> \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close> \<open>targetnode a = n\<close>
              have "CFG_node n \<longrightarrow>\<^bsub>cd\<^esub> CFG_node (sourcenode ax')"
                by(fastforce intro!:SDG_proc_entry_exit_cdep[of _ _ _ _ _ _ ai'])
              with \<open>valid_node n\<close>
              have "CFG_node n cd-[]@[CFG_node n]\<rightarrow>\<^sub>d* CFG_node (sourcenode ax')"
                by(fastforce intro:cdSp_Append_cdep cdSp_Nil)
              with \<open>CFG_node (sourcenode ax') \<longrightarrow>\<^bsub>cd\<^esub> CFG_node n'\<close>
              have "CFG_node n cd-[CFG_node n]@[CFG_node (sourcenode ax')]\<rightarrow>\<^sub>d* 
                CFG_node n'"
                by(fastforce intro:cdSp_Append_cdep)
              moreover
              from \<open>sourcenode ax' \<in> set(sourcenodes as)\<close> \<open>n = sourcenode ax\<close>
                \<open>as = (ax#asx)@zs\<close>
              have "\<forall>n''\<in>set ([CFG_node n]@[CFG_node (sourcenode ax')]). 
                parent_node n'' \<in> set (sourcenodes as)"
                by(fastforce simp:sourcenodes_def)
              ultimately show ?thesis by fastforce
            qed
          qed
        qed
      qed
    qed
  next
    case False
    then obtain a' where "valid_edge a'" and "sourcenode a' = n'"
      and "a' \<in> get_return_edges a" by auto
    with \<open>valid_edge a\<close> \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close> \<open>targetnode a = n\<close>
    have "CFG_node n \<longrightarrow>\<^bsub>cd\<^esub> CFG_node n'" by(fastforce intro:SDG_proc_entry_exit_cdep)
    with \<open>valid_edge a\<close> \<open>targetnode a = n\<close>[THEN sym] 
    have "CFG_node n cd-[]@[CFG_node n]\<rightarrow>\<^sub>d* CFG_node n'"
      by(fastforce intro:cdep_SDG_path.intros)
    from \<open>n -as\<rightarrow>\<^sub>\<iota>* n'\<close> \<open>n \<noteq> n'\<close> have "as \<noteq> []"
      by(fastforce elim:path.cases simp:intra_path_def)
    with \<open>n -as\<rightarrow>\<^sub>\<iota>* n'\<close> have "hd (sourcenodes as) = n"
      by(fastforce intro:path_sourcenode simp:intra_path_def)
    with \<open>as \<noteq> []\<close> have "n \<in> set (sourcenodes as)" 
      by(fastforce intro:hd_in_set simp:sourcenodes_def)
    with \<open>CFG_node n cd-[]@[CFG_node n]\<rightarrow>\<^sub>d* CFG_node n'\<close>
    show ?thesis by auto
  qed
qed


subsection \<open>Paths consisting of calls and control dependences\<close>

inductive call_cdep_SDG_path ::
  "'node SDG_node \<Rightarrow> 'node SDG_node list \<Rightarrow> 'node SDG_node \<Rightarrow> bool"
("_ cc-_\<rightarrow>\<^sub>d* _" [51,0,0] 80)
where ccSp_Nil:
  "valid_SDG_node n \<Longrightarrow> n cc-[]\<rightarrow>\<^sub>d* n"

  | ccSp_Append_cdep:
  "\<lbrakk>n cc-ns\<rightarrow>\<^sub>d* n''; n'' \<longrightarrow>\<^bsub>cd\<^esub> n'\<rbrakk> \<Longrightarrow> n cc-ns@[n'']\<rightarrow>\<^sub>d* n'"

  | ccSp_Append_call:
  "\<lbrakk>n cc-ns\<rightarrow>\<^sub>d* n''; n'' -p\<rightarrow>\<^bsub>call\<^esub> n'\<rbrakk> \<Longrightarrow> n cc-ns@[n'']\<rightarrow>\<^sub>d* n'"


lemma cc_SDG_path_Append:
  "\<lbrakk>n'' cc-ns'\<rightarrow>\<^sub>d* n'; n cc-ns\<rightarrow>\<^sub>d* n''\<rbrakk> \<Longrightarrow> n cc-ns@ns'\<rightarrow>\<^sub>d* n'"
by(induct rule:call_cdep_SDG_path.induct,
   auto intro:call_cdep_SDG_path.intros simp:append_assoc[THEN sym] 
                                        simp del:append_assoc)


lemma cdep_SDG_path_cc_SDG_path:
  "n cd-ns\<rightarrow>\<^sub>d* n' \<Longrightarrow> n cc-ns\<rightarrow>\<^sub>d* n'"
by(induct rule:cdep_SDG_path.induct,auto intro:call_cdep_SDG_path.intros)


lemma Entry_cc_SDG_path_to_inner_node:
  assumes "valid_SDG_node n" and "parent_node n \<noteq> (_Exit_)"
  obtains ns where "CFG_node (_Entry_) cc-ns\<rightarrow>\<^sub>d* n"
proof(atomize_elim)
  obtain m where "m = parent_node n" by simp
  from \<open>valid_SDG_node n\<close> have "valid_node (parent_node n)" 
    by(rule valid_SDG_CFG_node)
  thus "\<exists>ns. CFG_node (_Entry_) cc-ns\<rightarrow>\<^sub>d* n"
  proof(cases "parent_node n" rule:valid_node_cases)
    case Entry
    with \<open>valid_SDG_node n\<close> have "n = CFG_node (_Entry_)" 
      by(rule valid_SDG_node_parent_Entry)
    with \<open>valid_SDG_node n\<close> show ?thesis by(fastforce intro:ccSp_Nil)
  next
    case Exit
    with \<open>parent_node n \<noteq> (_Exit_)\<close> have False by simp
    thus ?thesis by simp
  next
    case inner
    with \<open>m = parent_node n\<close> obtain asx where "(_Entry_) -asx\<rightarrow>\<^sub>\<surd>* m"
      by(fastforce dest:Entry_path inner_is_valid)
    then obtain as where "(_Entry_) -as\<rightarrow>\<^sub>\<surd>* m"
      and "\<forall>a' \<in> set as. intra_kind(kind a') \<or> (\<exists>Q r p fs. kind a' = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs)"
      by -(erule valid_Entry_path_ascending_path,fastforce)
    from \<open>inner_node (parent_node n)\<close> \<open>m = parent_node n\<close>
    have "inner_node m" by simp
    with \<open>(_Entry_) -as\<rightarrow>\<^sub>\<surd>* m\<close> \<open>m = parent_node n\<close> \<open>valid_SDG_node n\<close>
      \<open>\<forall>a' \<in> set as. intra_kind(kind a') \<or> (\<exists>Q r p fs. kind a' = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs)\<close>
    show ?thesis
    proof(induct as arbitrary:m n rule:length_induct)
      fix as m n
      assume IH:"\<forall>as'. length as' < length as \<longrightarrow>
        (\<forall>m'. (_Entry_) -as'\<rightarrow>\<^sub>\<surd>* m' \<longrightarrow>
        (\<forall>n'. m' = parent_node n' \<longrightarrow> valid_SDG_node n' \<longrightarrow>
        (\<forall>a' \<in> set as'. intra_kind(kind a') \<or> (\<exists>Q r p fs. kind a' = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs)) \<longrightarrow>
        inner_node m' \<longrightarrow> (\<exists>ns. CFG_node (_Entry_) cc-ns\<rightarrow>\<^sub>d* n')))"
        and "(_Entry_) -as\<rightarrow>\<^sub>\<surd>* m" 
        and "m = parent_node n" and "valid_SDG_node n" and "inner_node m"
        and "\<forall>a' \<in> set as. intra_kind(kind a') \<or> (\<exists>Q r p fs. kind a' = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs)"
      show "\<exists>ns. CFG_node (_Entry_) cc-ns\<rightarrow>\<^sub>d* n"
      proof(cases "\<forall>a' \<in> set as. intra_kind(kind a')")
        case True
        with \<open>(_Entry_) -as\<rightarrow>\<^sub>\<surd>* m\<close> have "(_Entry_) -as\<rightarrow>\<^sub>\<iota>* m"
          by(fastforce simp:intra_path_def vp_def)
        have "\<not> method_exit m"
        proof
          assume "method_exit m"
          thus False
          proof(rule method_exit_cases)
            assume "m = (_Exit_)"
            with \<open>inner_node m\<close> show False by(simp add:inner_node_def)
          next
            fix a Q f p assume "m = sourcenode a" and "valid_edge a"
              and "kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f"
            from \<open>(_Entry_) -as\<rightarrow>\<^sub>\<iota>* m\<close> have "get_proc m = Main"
              by(fastforce dest:intra_path_get_procs simp:get_proc_Entry)
            from \<open>valid_edge a\<close> \<open>kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f\<close>
            have "get_proc (sourcenode a) = p" by(rule get_proc_return)
            with \<open>get_proc m = Main\<close> \<open>m = sourcenode a\<close> have "p = Main" by simp
            with \<open>valid_edge a\<close> \<open>kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f\<close> show False
              by(fastforce intro:Main_no_return_source)
          qed
        qed
        with \<open>inner_node m\<close> \<open>(_Entry_) -as\<rightarrow>\<^sub>\<iota>* m\<close>
        obtain ns where "CFG_node (_Entry_) cd-ns\<rightarrow>\<^sub>d* CFG_node m"
          and "ns \<noteq> []" and "\<forall>n'' \<in> set ns. parent_node n'' \<in> set(sourcenodes as)"
          by -(erule Entry_cdep_SDG_path)
        then obtain n' where "n' \<longrightarrow>\<^bsub>cd\<^esub> CFG_node m"
          and "parent_node n' \<in> set(sourcenodes as)"
          by -(erule cdep_SDG_path.cases,auto)
        from \<open>parent_node n' \<in> set(sourcenodes as)\<close> obtain ms ms' 
          where "sourcenodes as = ms@(parent_node n')#ms'"
          by(fastforce dest:split_list simp:sourcenodes_def)
        then obtain as' a as'' where "ms = sourcenodes as'" 
          and "ms' = sourcenodes as''" and "as = as'@a#as''" 
          and "parent_node n' = sourcenode a"
          by(fastforce elim:map_append_append_maps simp:sourcenodes_def)
        with \<open>(_Entry_) -as\<rightarrow>\<^sub>\<iota>* m\<close> have "(_Entry_) -as'\<rightarrow>\<^sub>\<iota>* parent_node n'"
          by(fastforce intro:path_split simp:intra_path_def)
        from \<open>n' \<longrightarrow>\<^bsub>cd\<^esub> CFG_node m\<close> have "valid_SDG_node n'"
          by(rule SDG_edge_valid_SDG_node)
        hence n'_cases:
          "n' = CFG_node (parent_node n') \<or> CFG_node (parent_node n') \<longrightarrow>\<^bsub>cd\<^esub> n'"
          by(rule valid_SDG_node_cases)
        show ?thesis
        proof(cases "as' = []")
          case True
          with \<open>(_Entry_) -as'\<rightarrow>\<^sub>\<iota>* parent_node n'\<close> have "parent_node n' = (_Entry_)"
            by(fastforce simp:intra_path_def)
          from n'_cases have "\<exists>ns. CFG_node (_Entry_) cd-ns\<rightarrow>\<^sub>d* CFG_node m"
          proof
            assume "n' = CFG_node (parent_node n')"
            with \<open>n' \<longrightarrow>\<^bsub>cd\<^esub> CFG_node m\<close> \<open>parent_node n' = (_Entry_)\<close>
            have "CFG_node (_Entry_) cd-[]@[CFG_node (_Entry_)]\<rightarrow>\<^sub>d* CFG_node m"
              by -(rule cdSp_Append_cdep,rule cdSp_Nil,auto)
            thus ?thesis by fastforce
          next
            assume "CFG_node (parent_node n') \<longrightarrow>\<^bsub>cd\<^esub> n'"
            with \<open>parent_node n' = (_Entry_)\<close>
            have "CFG_node (_Entry_) cd-[]@[CFG_node (_Entry_)]\<rightarrow>\<^sub>d* n'"
              by -(rule cdSp_Append_cdep,rule cdSp_Nil,auto)
            with \<open>n' \<longrightarrow>\<^bsub>cd\<^esub> CFG_node m\<close>
            have "CFG_node (_Entry_) cd-[CFG_node (_Entry_)]@[n']\<rightarrow>\<^sub>d* CFG_node m"
              by(fastforce intro:cdSp_Append_cdep)
            thus ?thesis by fastforce
          qed
          then obtain ns where "CFG_node (_Entry_) cc-ns\<rightarrow>\<^sub>d* CFG_node m"
            by(fastforce intro:cdep_SDG_path_cc_SDG_path)
          show ?thesis
          proof(cases "n = CFG_node m")
            case True
            with \<open>CFG_node (_Entry_) cc-ns\<rightarrow>\<^sub>d* CFG_node m\<close> 
            show ?thesis by fastforce
          next
            case False
            with \<open>inner_node m\<close> \<open>valid_SDG_node n\<close> \<open>m = parent_node n\<close>
            have "CFG_node m \<longrightarrow>\<^bsub>cd\<^esub> n"
              by(fastforce intro:SDG_parent_cdep_edge inner_is_valid)
            with \<open>CFG_node (_Entry_) cc-ns\<rightarrow>\<^sub>d* CFG_node m\<close>
            have "CFG_node (_Entry_) cc-ns@[CFG_node m]\<rightarrow>\<^sub>d* n"
              by(fastforce intro:ccSp_Append_cdep)
            thus ?thesis by fastforce
          qed
        next
          case False
          with \<open>as = as'@a#as''\<close> have "length as' < length as" by simp
          from \<open>(_Entry_) -as'\<rightarrow>\<^sub>\<iota>* parent_node n'\<close> have "valid_node (parent_node n')"
            by(fastforce intro:path_valid_node simp:intra_path_def)
          hence "inner_node (parent_node n')"
          proof(cases "parent_node n'" rule:valid_node_cases)
            case Entry
            with \<open>(_Entry_) -as'\<rightarrow>\<^sub>\<iota>* (parent_node n')\<close>
            have "(_Entry_) -as'\<rightarrow>* (_Entry_)" by(fastforce simp:intra_path_def)
            with False have False by fastforce
            thus ?thesis by simp
          next
            case Exit
            with \<open>n' \<longrightarrow>\<^bsub>cd\<^esub> CFG_node m\<close> have "n' = CFG_node (_Exit_)"
              by -(rule valid_SDG_node_parent_Exit,erule SDG_edge_valid_SDG_node,simp)
            with \<open>n' \<longrightarrow>\<^bsub>cd\<^esub> CFG_node m\<close> Exit have False
              by simp(erule Exit_no_SDG_edge_source)
            thus ?thesis by simp
          next
            case inner
            thus ?thesis by simp
          qed
          from \<open>valid_node (parent_node n')\<close> 
          have "valid_SDG_node (CFG_node (parent_node n'))" by simp
          from \<open>(_Entry_) -as'\<rightarrow>\<^sub>\<iota>* (parent_node n')\<close> 
          have "(_Entry_) -as'\<rightarrow>\<^sub>\<surd>* (parent_node n')"
            by(rule intra_path_vp)
          from \<open>\<forall>a' \<in> set as. intra_kind(kind a') \<or> (\<exists>Q r p fs. kind a' = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs)\<close>
            \<open>as = as'@a#as''\<close>
          have "\<forall>a' \<in> set as'. intra_kind(kind a') \<or> (\<exists>Q r p fs. kind a' = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs)"
            by auto
          with IH \<open>length as' < length as\<close> \<open>(_Entry_) -as'\<rightarrow>\<^sub>\<surd>* (parent_node n')\<close>
            \<open>valid_SDG_node (CFG_node (parent_node n'))\<close> \<open>inner_node (parent_node n')\<close>
          obtain ns where "CFG_node (_Entry_) cc-ns\<rightarrow>\<^sub>d* CFG_node (parent_node n')"
            apply(erule_tac x="as'" in allE) apply clarsimp
            apply(erule_tac x="(parent_node n')" in allE) apply clarsimp
            apply(erule_tac x="CFG_node (parent_node n')" in allE) by clarsimp
          from n'_cases have "\<exists>ns. CFG_node (_Entry_) cc-ns\<rightarrow>\<^sub>d* n'"
          proof
            assume "n' = CFG_node (parent_node n')"
            with \<open>CFG_node (_Entry_) cc-ns\<rightarrow>\<^sub>d* CFG_node (parent_node n')\<close>
            show ?thesis by fastforce
          next
            assume "CFG_node (parent_node n') \<longrightarrow>\<^bsub>cd\<^esub> n'"
            with \<open>CFG_node (_Entry_) cc-ns\<rightarrow>\<^sub>d* CFG_node (parent_node n')\<close>
            have "CFG_node (_Entry_) cc-ns@[CFG_node (parent_node n')]\<rightarrow>\<^sub>d* n'"
              by(fastforce intro:ccSp_Append_cdep)
            thus ?thesis by fastforce
          qed
          then obtain ns' where "CFG_node (_Entry_) cc-ns'\<rightarrow>\<^sub>d* n'" by blast
          with \<open>n' \<longrightarrow>\<^bsub>cd\<^esub> CFG_node m\<close> 
          have "CFG_node (_Entry_) cc-ns'@[n']\<rightarrow>\<^sub>d* CFG_node m"
            by(fastforce intro:ccSp_Append_cdep)
          show ?thesis
          proof(cases "n = CFG_node m")
            case True
            with \<open>CFG_node (_Entry_) cc-ns'@[n']\<rightarrow>\<^sub>d* CFG_node m\<close>
            show ?thesis by fastforce
          next
            case False
            with \<open>inner_node m\<close> \<open>valid_SDG_node n\<close> \<open>m = parent_node n\<close>
            have "CFG_node m \<longrightarrow>\<^bsub>cd\<^esub> n"
              by(fastforce intro:SDG_parent_cdep_edge inner_is_valid)
            with \<open>CFG_node (_Entry_) cc-ns'@[n']\<rightarrow>\<^sub>d* CFG_node m\<close>
            have "CFG_node (_Entry_) cc-(ns'@[n'])@[CFG_node m]\<rightarrow>\<^sub>d* n"
              by(fastforce intro:ccSp_Append_cdep)
            thus ?thesis by fastforce
          qed
        qed
      next
        case False
        hence "\<exists>a' \<in> set as. \<not> intra_kind (kind a')" by fastforce
        then obtain a as' as'' where "as = as'@a#as''" and "\<not> intra_kind (kind a)"
          and "\<forall>a' \<in> set as''. intra_kind (kind a')"
          by(fastforce elim!:split_list_last_propE)
        from \<open>\<forall>a' \<in> set as. intra_kind(kind a') \<or> (\<exists>Q r p fs. kind a' = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs)\<close>
          \<open>as = as'@a#as''\<close> \<open>\<not> intra_kind (kind a)\<close>
        obtain Q r p fs where "kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs" 
          and "\<forall>a' \<in> set as'. intra_kind(kind a') \<or> (\<exists>Q r p fs. kind a' = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs)"
          by auto
        from \<open>as = as'@a#as''\<close> have "length as' < length as" by fastforce
        from \<open>(_Entry_) -as\<rightarrow>\<^sub>\<surd>* m\<close> \<open>as = as'@a#as''\<close>
        have "(_Entry_) -as'\<rightarrow>\<^sub>\<surd>* sourcenode a" and "valid_edge a"
          and "targetnode a -as''\<rightarrow>\<^sub>\<surd>* m"
          by(auto intro:vp_split)
        hence "valid_SDG_node (CFG_node (sourcenode a))" by simp
        have "\<exists>ns'. CFG_node (_Entry_) cc-ns'\<rightarrow>\<^sub>d* CFG_node m"
        proof(cases "targetnode a = m")
          case True
          with \<open>valid_edge a\<close> \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close>
          have "CFG_node (sourcenode a) -p\<rightarrow>\<^bsub>call\<^esub> CFG_node m"
            by(fastforce intro:SDG_call_edge)
          have "\<exists>ns. CFG_node (_Entry_) cc-ns\<rightarrow>\<^sub>d* CFG_node (sourcenode a)"
          proof(cases "as' = []")
            case True
            with \<open>(_Entry_) -as'\<rightarrow>\<^sub>\<surd>* sourcenode a\<close> have "(_Entry_) = sourcenode a"
              by(fastforce simp:vp_def)
            with \<open>CFG_node (sourcenode a) -p\<rightarrow>\<^bsub>call\<^esub> CFG_node m\<close>
            have "CFG_node (_Entry_) cc-[]\<rightarrow>\<^sub>d* CFG_node (sourcenode a)"
              by(fastforce intro:ccSp_Nil SDG_edge_valid_SDG_node)
            thus ?thesis by fastforce
          next
            case False
            from \<open>valid_edge a\<close> have "valid_node (sourcenode a)" by simp
            hence "inner_node (sourcenode a)"
            proof(cases "sourcenode a" rule:valid_node_cases)
              case Entry
              with \<open>(_Entry_) -as'\<rightarrow>\<^sub>\<surd>* sourcenode a\<close>
              have "(_Entry_) -as'\<rightarrow>* (_Entry_)" by(fastforce simp:vp_def)
              with False have False by fastforce
              thus ?thesis by simp
            next
              case Exit
              with \<open>valid_edge a\<close> have False by -(erule Exit_source)
              thus ?thesis by simp
            next
              case inner
              thus ?thesis by simp
            qed
            with IH \<open>length as' < length as\<close> \<open>(_Entry_) -as'\<rightarrow>\<^sub>\<surd>* sourcenode a\<close>
              \<open>valid_SDG_node (CFG_node (sourcenode a))\<close> 
              \<open>\<forall>a' \<in> set as'. intra_kind(kind a') \<or> (\<exists>Q r p fs. kind a' = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs)\<close>
            obtain ns where "CFG_node (_Entry_) cc-ns\<rightarrow>\<^sub>d* CFG_node (sourcenode a)"
              apply(erule_tac x="as'" in allE) apply clarsimp
              apply(erule_tac x="sourcenode a" in allE) apply clarsimp
              apply(erule_tac x="CFG_node (sourcenode a)" in allE) by clarsimp
            thus ?thesis by fastforce
          qed
          then obtain ns where "CFG_node (_Entry_) cc-ns\<rightarrow>\<^sub>d* CFG_node (sourcenode a)"
            by blast
          with \<open>CFG_node (sourcenode a) -p\<rightarrow>\<^bsub>call\<^esub> CFG_node m\<close>
          show ?thesis by(fastforce intro:ccSp_Append_call)
        next
          case False
          from \<open>targetnode a -as''\<rightarrow>\<^sub>\<surd>* m\<close> \<open>\<forall>a' \<in> set as''. intra_kind (kind a')\<close>
          have "targetnode a -as''\<rightarrow>\<^sub>\<iota>* m" by(fastforce simp:vp_def intra_path_def)
          hence "get_proc (targetnode a) = get_proc m" by(rule intra_path_get_procs)
          from \<open>valid_edge a\<close> \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close> have "get_proc (targetnode a) = p"
            by(rule get_proc_call)
          from \<open>inner_node m\<close> \<open>valid_edge a\<close> \<open>targetnode a -as''\<rightarrow>\<^sub>\<iota>* m\<close>
            \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close> \<open>targetnode a \<noteq> m\<close>
          obtain ns where "CFG_node (targetnode a) cd-ns\<rightarrow>\<^sub>d* CFG_node m"
            and "ns \<noteq> []" 
            and "\<forall>n'' \<in> set ns. parent_node n'' \<in> set(sourcenodes as'')"
            by(fastforce elim!:in_proc_cdep_SDG_path)
          then obtain n' where "n' \<longrightarrow>\<^bsub>cd\<^esub> CFG_node m"
            and "parent_node n' \<in> set(sourcenodes as'')"
            by -(erule cdep_SDG_path.cases,auto)
          from \<open>(parent_node n') \<in> set(sourcenodes as'')\<close> obtain ms ms' 
            where "sourcenodes as'' = ms@(parent_node n')#ms'"
            by(fastforce dest:split_list simp:sourcenodes_def)
          then obtain xs a' ys where "ms = sourcenodes xs" 
            and "ms' = sourcenodes ys" and "as'' = xs@a'#ys"
            and "parent_node n' = sourcenode a'"
            by(fastforce elim:map_append_append_maps simp:sourcenodes_def)
          from \<open>(_Entry_) -as\<rightarrow>\<^sub>\<surd>* m\<close> \<open>as = as'@a#as''\<close> \<open>as'' = xs@a'#ys\<close>
          have "(_Entry_) -(as'@a#xs)@a'#ys\<rightarrow>\<^sub>\<surd>* m" by simp
          hence "(_Entry_) -as'@a#xs\<rightarrow>\<^sub>\<surd>* sourcenode a'"
            and "valid_edge a'" by(auto intro:vp_split)
          from \<open>as = as'@a#as''\<close> \<open>as'' = xs@a'#ys\<close> 
          have "length (as'@a#xs) < length as" by simp
          from \<open>valid_edge a'\<close> have "valid_node (sourcenode a')" by simp
          hence "inner_node (sourcenode a')"
          proof(cases "sourcenode a'" rule:valid_node_cases)
            case Entry
            with \<open>(_Entry_) -as'@a#xs\<rightarrow>\<^sub>\<surd>* sourcenode a'\<close>
            have "(_Entry_) -as'@a#xs\<rightarrow>* (_Entry_)" by(fastforce simp:vp_def)
            hence False by fastforce
            thus ?thesis by simp
          next
            case Exit
            with \<open>valid_edge a'\<close> have False by -(erule Exit_source)
            thus ?thesis by simp
          next
            case inner
            thus ?thesis by simp
          qed
          from \<open>valid_edge a'\<close> have "valid_SDG_node (CFG_node (sourcenode a'))"
            by simp
          from \<open>\<forall>a' \<in> set as. intra_kind(kind a') \<or> (\<exists>Q r p fs. kind a' = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs)\<close>
            \<open>as = as'@a#as''\<close> \<open>as'' = xs@a'#ys\<close>
          have "\<forall>a' \<in> set (as'@a#xs). 
            intra_kind(kind a') \<or> (\<exists>Q r p fs. kind a' = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs)"
            by auto
          with IH \<open>length (as'@a#xs) < length as\<close> 
            \<open>(_Entry_) -as'@a#xs\<rightarrow>\<^sub>\<surd>* sourcenode a'\<close>
            \<open>valid_SDG_node (CFG_node (sourcenode a'))\<close>
            \<open>inner_node (sourcenode a')\<close> \<open>parent_node n' = sourcenode a'\<close>
          obtain ns where "CFG_node (_Entry_) cc-ns\<rightarrow>\<^sub>d* CFG_node (parent_node n')"
            apply(erule_tac x="as'@a#xs" in allE) apply clarsimp
            apply(erule_tac x="sourcenode a'" in allE) apply clarsimp
            apply(erule_tac x="CFG_node (sourcenode a')" in allE) by clarsimp
          from \<open>n' \<longrightarrow>\<^bsub>cd\<^esub> CFG_node m\<close> have "valid_SDG_node n'"
            by(rule SDG_edge_valid_SDG_node)
          hence "n' = CFG_node (parent_node n') \<or> CFG_node (parent_node n') \<longrightarrow>\<^bsub>cd\<^esub> n'"
            by(rule valid_SDG_node_cases)
          thus ?thesis
          proof
            assume "n' = CFG_node (parent_node n')"
            with \<open>CFG_node (_Entry_) cc-ns\<rightarrow>\<^sub>d* CFG_node (parent_node n')\<close>
              \<open>n' \<longrightarrow>\<^bsub>cd\<^esub> CFG_node m\<close> show ?thesis
              by(fastforce intro:ccSp_Append_cdep)
          next
            assume "CFG_node (parent_node n') \<longrightarrow>\<^bsub>cd\<^esub> n'"
            with \<open>CFG_node (_Entry_) cc-ns\<rightarrow>\<^sub>d* CFG_node (parent_node n')\<close>
            have "CFG_node (_Entry_) cc-ns@[CFG_node (parent_node n')]\<rightarrow>\<^sub>d* n'"
              by(fastforce intro:ccSp_Append_cdep)
            with \<open>n' \<longrightarrow>\<^bsub>cd\<^esub> CFG_node m\<close> show ?thesis
              by(fastforce intro:ccSp_Append_cdep)
          qed
        qed
        then obtain ns where "CFG_node (_Entry_) cc-ns\<rightarrow>\<^sub>d* CFG_node m" by blast
        show ?thesis
        proof(cases "n = CFG_node m")
          case True
          with \<open>CFG_node (_Entry_) cc-ns\<rightarrow>\<^sub>d* CFG_node m\<close> show ?thesis by fastforce
        next
          case False
          with \<open>inner_node m\<close> \<open>valid_SDG_node n\<close> \<open>m = parent_node n\<close>
          have "CFG_node m \<longrightarrow>\<^bsub>cd\<^esub> n"
            by(fastforce intro:SDG_parent_cdep_edge inner_is_valid)
          with \<open>CFG_node (_Entry_) cc-ns\<rightarrow>\<^sub>d* CFG_node m\<close> show ?thesis
            by(fastforce dest:ccSp_Append_cdep)
        qed
      qed
    qed
  qed
qed


subsection \<open>Same level paths in the SDG\<close>

inductive matched :: "'node SDG_node \<Rightarrow> 'node SDG_node list \<Rightarrow> 'node SDG_node \<Rightarrow> bool"
  where matched_Nil:
  "valid_SDG_node n \<Longrightarrow> matched n [] n"
  | matched_Append_intra_SDG_path:
  "\<lbrakk>matched n ns n''; n'' i-ns'\<rightarrow>\<^sub>d* n'\<rbrakk> \<Longrightarrow> matched n (ns@ns') n'"
  | matched_bracket_call:
  "\<lbrakk>matched n\<^sub>0 ns n\<^sub>1; n\<^sub>1 -p\<rightarrow>\<^bsub>call\<^esub> n\<^sub>2; matched n\<^sub>2 ns' n\<^sub>3; 
    (n\<^sub>3 -p\<rightarrow>\<^bsub>ret\<^esub> n\<^sub>4 \<or> n\<^sub>3 -p:V\<rightarrow>\<^bsub>out\<^esub> n\<^sub>4); valid_edge a; a' \<in> get_return_edges a;
    sourcenode a = parent_node n\<^sub>1; targetnode a = parent_node n\<^sub>2; 
    sourcenode a' = parent_node n\<^sub>3; targetnode a' = parent_node n\<^sub>4\<rbrakk>
  \<Longrightarrow> matched n\<^sub>0 (ns@n\<^sub>1#ns'@[n\<^sub>3]) n\<^sub>4"
  | matched_bracket_param:
  "\<lbrakk>matched n\<^sub>0 ns n\<^sub>1; n\<^sub>1 -p:V\<rightarrow>\<^bsub>in\<^esub> n\<^sub>2; matched n\<^sub>2 ns' n\<^sub>3; 
    n\<^sub>3 -p:V'\<rightarrow>\<^bsub>out\<^esub> n\<^sub>4; valid_edge a; a' \<in> get_return_edges a;
    sourcenode a = parent_node n\<^sub>1; targetnode a = parent_node n\<^sub>2; 
    sourcenode a' = parent_node n\<^sub>3; targetnode a' = parent_node n\<^sub>4\<rbrakk>
  \<Longrightarrow> matched n\<^sub>0 (ns@n\<^sub>1#ns'@[n\<^sub>3]) n\<^sub>4"




lemma matched_Append:
  "\<lbrakk>matched n'' ns' n'; matched n ns n''\<rbrakk> \<Longrightarrow> matched n (ns@ns') n'"
by(induct rule:matched.induct,
   auto intro:matched.intros simp:append_assoc[THEN sym] simp del:append_assoc)


lemma intra_SDG_path_matched:
  assumes "n i-ns\<rightarrow>\<^sub>d* n'" shows "matched n ns n'"
proof -
  from \<open>n i-ns\<rightarrow>\<^sub>d* n'\<close> have "valid_SDG_node n"
    by(rule intra_SDG_path_valid_SDG_node)
  hence "matched n [] n" by(rule matched_Nil)
  with \<open>n i-ns\<rightarrow>\<^sub>d* n'\<close> have "matched n ([]@ns) n'"
    by -(rule matched_Append_intra_SDG_path)
  thus ?thesis by simp
qed


lemma intra_proc_matched:
  assumes "valid_edge a" and "kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs" and "a' \<in> get_return_edges a"
  shows "matched (CFG_node (targetnode a)) [CFG_node (targetnode a)]
                 (CFG_node (sourcenode a'))"
proof -
  from assms have "CFG_node (targetnode a) \<longrightarrow>\<^bsub>cd\<^esub> CFG_node (sourcenode a')" 
    by(fastforce intro:SDG_proc_entry_exit_cdep)
  with \<open>valid_edge a\<close> 
  have "CFG_node (targetnode a) i-[]@[CFG_node (targetnode a)]\<rightarrow>\<^sub>d* 
        CFG_node (sourcenode a')" 
    by(fastforce intro:intra_SDG_path.intros)
  with \<open>valid_edge a\<close> 
  have "matched (CFG_node (targetnode a)) ([]@[CFG_node (targetnode a)])
    (CFG_node (sourcenode a'))"
    by(fastforce intro:matched.intros)
  thus ?thesis by simp
qed


lemma matched_intra_CFG_path:
  assumes "matched n ns n'"
  obtains as where "parent_node n -as\<rightarrow>\<^sub>\<iota>* parent_node n'"
proof(atomize_elim)
  from \<open>matched n ns n'\<close> show "\<exists>as. parent_node n -as\<rightarrow>\<^sub>\<iota>* parent_node n'"
  proof(induct rule:matched.induct)
    case matched_Nil thus ?case
      by(fastforce dest:empty_path valid_SDG_CFG_node simp:intra_path_def)
  next
    case (matched_Append_intra_SDG_path n ns n'' ns' n')
    from \<open>\<exists>as. parent_node n -as\<rightarrow>\<^sub>\<iota>* parent_node n''\<close> obtain as 
      where "parent_node n -as\<rightarrow>\<^sub>\<iota>* parent_node n''" by blast
    from \<open>n'' i-ns'\<rightarrow>\<^sub>d* n'\<close> obtain as' where "parent_node n'' -as'\<rightarrow>\<^sub>\<iota>* parent_node n'"
      by(fastforce elim:intra_SDG_path_intra_CFG_path)
    with \<open>parent_node n -as\<rightarrow>\<^sub>\<iota>* parent_node n''\<close>
    have "parent_node n -as@as'\<rightarrow>\<^sub>\<iota>* parent_node n'"
      by(rule intra_path_Append)
    thus ?case by fastforce
  next
    case (matched_bracket_call n\<^sub>0 ns n\<^sub>1 p n\<^sub>2 ns' n\<^sub>3 n\<^sub>4 V a a')
    from \<open>valid_edge a\<close> \<open>a' \<in> get_return_edges a\<close> \<open>sourcenode a = parent_node n\<^sub>1\<close>
      \<open>targetnode a' = parent_node n\<^sub>4\<close>
    obtain a'' where "valid_edge a''" and "sourcenode a'' = parent_node n\<^sub>1" 
      and "targetnode a'' = parent_node n\<^sub>4" and "kind a'' = (\<lambda>cf. False)\<^sub>\<surd>"
      by(fastforce dest:call_return_node_edge)
    hence "parent_node n\<^sub>1 -[a'']\<rightarrow>* parent_node n\<^sub>4" by(fastforce dest:path_edge)
    moreover
    from \<open>kind a'' = (\<lambda>cf. False)\<^sub>\<surd>\<close> have "\<forall>a \<in> set [a'']. intra_kind(kind a)"
      by(fastforce simp:intra_kind_def)
    ultimately have "parent_node n\<^sub>1 -[a'']\<rightarrow>\<^sub>\<iota>* parent_node n\<^sub>4"
      by(auto simp:intra_path_def)
    with \<open>\<exists>as. parent_node n\<^sub>0 -as\<rightarrow>\<^sub>\<iota>* parent_node n\<^sub>1\<close> show ?case
      by(fastforce intro:intra_path_Append)
  next
    case (matched_bracket_param n\<^sub>0 ns n\<^sub>1 p V n\<^sub>2 ns' n\<^sub>3 V' n\<^sub>4 a a')
    from \<open>valid_edge a\<close> \<open>a' \<in> get_return_edges a\<close> \<open>sourcenode a = parent_node n\<^sub>1\<close>
      \<open>targetnode a' = parent_node n\<^sub>4\<close>
    obtain a'' where "valid_edge a''" and "sourcenode a'' = parent_node n\<^sub>1" 
      and "targetnode a'' = parent_node n\<^sub>4" and "kind a'' = (\<lambda>cf. False)\<^sub>\<surd>"
      by(fastforce dest:call_return_node_edge)
    hence "parent_node n\<^sub>1 -[a'']\<rightarrow>* parent_node n\<^sub>4" by(fastforce dest:path_edge)
    moreover
    from \<open>kind a'' = (\<lambda>cf. False)\<^sub>\<surd>\<close> have "\<forall>a \<in> set [a'']. intra_kind(kind a)"
      by(fastforce simp:intra_kind_def)
    ultimately have "parent_node n\<^sub>1 -[a'']\<rightarrow>\<^sub>\<iota>* parent_node n\<^sub>4"
      by(auto simp:intra_path_def)
    with \<open>\<exists>as. parent_node n\<^sub>0 -as\<rightarrow>\<^sub>\<iota>* parent_node n\<^sub>1\<close> show ?case
      by(fastforce intro:intra_path_Append)
  qed
qed


lemma matched_same_level_CFG_path:
  assumes "matched n ns n'"
  obtains as where "parent_node n -as\<rightarrow>\<^bsub>sl\<^esub>* parent_node n'"
proof(atomize_elim)
  from \<open>matched n ns n'\<close>
  show "\<exists>as. parent_node n -as\<rightarrow>\<^bsub>sl\<^esub>* parent_node n'"
  proof(induct rule:matched.induct)
    case matched_Nil thus ?case 
      by(fastforce dest:empty_path valid_SDG_CFG_node simp:slp_def same_level_path_def)
  next
    case (matched_Append_intra_SDG_path n ns n'' ns' n')
    from \<open>\<exists>as. parent_node n -as\<rightarrow>\<^bsub>sl\<^esub>* parent_node n''\<close>
    obtain as where "parent_node n -as\<rightarrow>\<^bsub>sl\<^esub>* parent_node n''" by blast
    from \<open>n'' i-ns'\<rightarrow>\<^sub>d* n'\<close> obtain as' where "parent_node n'' -as'\<rightarrow>\<^sub>\<iota>* parent_node n'"
      by(erule intra_SDG_path_intra_CFG_path)
    from \<open>parent_node n'' -as'\<rightarrow>\<^sub>\<iota>* parent_node n'\<close>
    have "parent_node n'' -as'\<rightarrow>\<^bsub>sl\<^esub>* parent_node n'" by(rule intra_path_slp)
    with \<open>parent_node n -as\<rightarrow>\<^bsub>sl\<^esub>* parent_node n''\<close>
    have "parent_node n -as@as'\<rightarrow>\<^bsub>sl\<^esub>* parent_node n'"
      by(rule slp_Append)
    thus ?case by fastforce
  next
    case (matched_bracket_call n\<^sub>0 ns n\<^sub>1 p n\<^sub>2 ns' n\<^sub>3 n\<^sub>4 V a a')
    from \<open>valid_edge a\<close> \<open>a' \<in> get_return_edges a\<close>
    obtain Q r p' fs where "kind a = Q:r\<hookrightarrow>\<^bsub>p'\<^esub>fs" 
      by(fastforce dest!:only_call_get_return_edges)
    from \<open>\<exists>as. parent_node n\<^sub>0 -as\<rightarrow>\<^bsub>sl\<^esub>* parent_node n\<^sub>1\<close>
    obtain as where "parent_node n\<^sub>0 -as\<rightarrow>\<^bsub>sl\<^esub>* parent_node n\<^sub>1" by blast
    from \<open>\<exists>as. parent_node n\<^sub>2 -as\<rightarrow>\<^bsub>sl\<^esub>* parent_node n\<^sub>3\<close>
    obtain as' where "parent_node n\<^sub>2 -as'\<rightarrow>\<^bsub>sl\<^esub>* parent_node n\<^sub>3" by blast
    from \<open>valid_edge a\<close> \<open>a' \<in> get_return_edges a\<close> \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p'\<^esub>fs\<close>
    obtain Q' f' where "kind a' = Q'\<hookleftarrow>\<^bsub>p'\<^esub>f'" by(fastforce dest!:call_return_edges)
    from \<open>valid_edge a\<close> \<open>a' \<in> get_return_edges a\<close> have "valid_edge a'" 
      by(rule get_return_edges_valid)
    from \<open>parent_node n\<^sub>2 -as'\<rightarrow>\<^bsub>sl\<^esub>* parent_node n\<^sub>3\<close> have "same_level_path as'"
      by(simp add:slp_def)
    hence "same_level_path_aux ([]@[a]) as'"
      by(fastforce intro:same_level_path_aux_callstack_Append simp:same_level_path_def)
    from \<open>same_level_path as'\<close> have "upd_cs ([]@[a]) as' = ([]@[a])"
      by(fastforce intro:same_level_path_upd_cs_callstack_Append 
                   simp:same_level_path_def)
    with \<open>same_level_path_aux ([]@[a]) as'\<close> \<open>a' \<in> get_return_edges a\<close>
      \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p'\<^esub>fs\<close> \<open>kind a' = Q'\<hookleftarrow>\<^bsub>p'\<^esub>f'\<close>
    have "same_level_path (a#as'@[a'])"
      by(fastforce intro:same_level_path_aux_Append upd_cs_Append 
                   simp:same_level_path_def)
    from \<open>valid_edge a'\<close> \<open>sourcenode a' = parent_node n\<^sub>3\<close>
      \<open>targetnode a' = parent_node n\<^sub>4\<close>
    have "parent_node n\<^sub>3 -[a']\<rightarrow>* parent_node n\<^sub>4" by(fastforce dest:path_edge)
    with \<open>parent_node n\<^sub>2 -as'\<rightarrow>\<^bsub>sl\<^esub>* parent_node n\<^sub>3\<close> 
    have "parent_node n\<^sub>2 -as'@[a']\<rightarrow>* parent_node n\<^sub>4"
      by(fastforce intro:path_Append simp:slp_def)
    with \<open>valid_edge a\<close> \<open>sourcenode a = parent_node n\<^sub>1\<close>
      \<open>targetnode a = parent_node n\<^sub>2\<close>
    have "parent_node n\<^sub>1 -a#as'@[a']\<rightarrow>* parent_node n\<^sub>4" by -(rule Cons_path)
    with \<open>same_level_path (a#as'@[a'])\<close>
    have "parent_node n\<^sub>1 -a#as'@[a']\<rightarrow>\<^bsub>sl\<^esub>* parent_node n\<^sub>4" by(simp add:slp_def)
    with \<open>parent_node n\<^sub>0 -as\<rightarrow>\<^bsub>sl\<^esub>* parent_node n\<^sub>1\<close>
    have "parent_node n\<^sub>0 -as@a#as'@[a']\<rightarrow>\<^bsub>sl\<^esub>* parent_node n\<^sub>4" by(rule slp_Append)
    with \<open>sourcenode a = parent_node n\<^sub>1\<close> \<open>sourcenode a' = parent_node n\<^sub>3\<close>
    show ?case by fastforce
  next
    case (matched_bracket_param n\<^sub>0 ns n\<^sub>1 p V n\<^sub>2 ns' n\<^sub>3 V' n\<^sub>4 a a')
    from \<open>valid_edge a\<close> \<open>a' \<in> get_return_edges a\<close>
    obtain Q r p' fs where "kind a = Q:r\<hookrightarrow>\<^bsub>p'\<^esub>fs" 
      by(fastforce dest!:only_call_get_return_edges)
    from \<open>\<exists>as. parent_node n\<^sub>0 -as\<rightarrow>\<^bsub>sl\<^esub>* parent_node n\<^sub>1\<close>
    obtain as where "parent_node n\<^sub>0 -as\<rightarrow>\<^bsub>sl\<^esub>* parent_node n\<^sub>1" by blast
    from \<open>\<exists>as. parent_node n\<^sub>2 -as\<rightarrow>\<^bsub>sl\<^esub>* parent_node n\<^sub>3\<close>
    obtain as' where "parent_node n\<^sub>2 -as'\<rightarrow>\<^bsub>sl\<^esub>* parent_node n\<^sub>3" by blast
    from \<open>valid_edge a\<close> \<open>a' \<in> get_return_edges a\<close> \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p'\<^esub>fs\<close>
    obtain Q' f' where "kind a' = Q'\<hookleftarrow>\<^bsub>p'\<^esub>f'" by(fastforce dest!:call_return_edges)
    from \<open>valid_edge a\<close> \<open>a' \<in> get_return_edges a\<close> have "valid_edge a'" 
      by(rule get_return_edges_valid)
    from \<open>parent_node n\<^sub>2 -as'\<rightarrow>\<^bsub>sl\<^esub>* parent_node n\<^sub>3\<close> have "same_level_path as'"
      by(simp add:slp_def)
    hence "same_level_path_aux ([]@[a]) as'"
      by(fastforce intro:same_level_path_aux_callstack_Append simp:same_level_path_def)
    from \<open>same_level_path as'\<close> have "upd_cs ([]@[a]) as' = ([]@[a])"
      by(fastforce intro:same_level_path_upd_cs_callstack_Append 
                   simp:same_level_path_def)
    with \<open>same_level_path_aux ([]@[a]) as'\<close> \<open>a' \<in> get_return_edges a\<close>
      \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p'\<^esub>fs\<close> \<open>kind a' = Q'\<hookleftarrow>\<^bsub>p'\<^esub>f'\<close>
    have "same_level_path (a#as'@[a'])"
      by(fastforce intro:same_level_path_aux_Append upd_cs_Append 
                   simp:same_level_path_def)
    from \<open>valid_edge a'\<close> \<open>sourcenode a' = parent_node n\<^sub>3\<close>
      \<open>targetnode a' = parent_node n\<^sub>4\<close>
    have "parent_node n\<^sub>3 -[a']\<rightarrow>* parent_node n\<^sub>4" by(fastforce dest:path_edge)
    with \<open>parent_node n\<^sub>2 -as'\<rightarrow>\<^bsub>sl\<^esub>* parent_node n\<^sub>3\<close> 
    have "parent_node n\<^sub>2 -as'@[a']\<rightarrow>* parent_node n\<^sub>4"
      by(fastforce intro:path_Append simp:slp_def)
    with \<open>valid_edge a\<close> \<open>sourcenode a = parent_node n\<^sub>1\<close>
      \<open>targetnode a = parent_node n\<^sub>2\<close>
    have "parent_node n\<^sub>1 -a#as'@[a']\<rightarrow>* parent_node n\<^sub>4" by -(rule Cons_path)
    with \<open>same_level_path (a#as'@[a'])\<close>
    have "parent_node n\<^sub>1 -a#as'@[a']\<rightarrow>\<^bsub>sl\<^esub>* parent_node n\<^sub>4" by(simp add:slp_def)
    with \<open>parent_node n\<^sub>0 -as\<rightarrow>\<^bsub>sl\<^esub>* parent_node n\<^sub>1\<close>
    have "parent_node n\<^sub>0 -as@a#as'@[a']\<rightarrow>\<^bsub>sl\<^esub>* parent_node n\<^sub>4" by(rule slp_Append)
    with \<open>sourcenode a = parent_node n\<^sub>1\<close> \<open>sourcenode a' = parent_node n\<^sub>3\<close>
    show ?case by fastforce
  qed
qed


subsection \<open>Realizable paths in the SDG\<close>

inductive realizable :: 
  "'node SDG_node \<Rightarrow> 'node SDG_node list \<Rightarrow> 'node SDG_node \<Rightarrow> bool"
  where realizable_matched:"matched n ns n' \<Longrightarrow> realizable n ns n'"
  | realizable_call:
  "\<lbrakk>realizable n\<^sub>0 ns n\<^sub>1; n\<^sub>1 -p\<rightarrow>\<^bsub>call\<^esub> n\<^sub>2 \<or> n\<^sub>1 -p:V\<rightarrow>\<^bsub>in\<^esub> n\<^sub>2; matched n\<^sub>2 ns' n\<^sub>3\<rbrakk>
  \<Longrightarrow> realizable n\<^sub>0 (ns@n\<^sub>1#ns') n\<^sub>3"


lemma realizable_Append_matched:
  "\<lbrakk>realizable n ns n''; matched n'' ns' n'\<rbrakk> \<Longrightarrow> realizable n (ns@ns') n'"
proof(induct rule:realizable.induct)
  case (realizable_matched n ns n'')
  from \<open>matched n'' ns' n'\<close> \<open>matched n ns n''\<close> have "matched n (ns@ns') n'"
    by(rule matched_Append)
  thus ?case by(rule realizable.realizable_matched)
next
  case (realizable_call n\<^sub>0 ns n\<^sub>1 p n\<^sub>2 V ns'' n\<^sub>3)
  from \<open>matched n\<^sub>3 ns' n'\<close> \<open>matched n\<^sub>2 ns'' n\<^sub>3\<close> have "matched n\<^sub>2 (ns''@ns') n'"
    by(rule matched_Append)
  with \<open>realizable n\<^sub>0 ns n\<^sub>1\<close> \<open>n\<^sub>1 -p\<rightarrow>\<^bsub>call\<^esub> n\<^sub>2 \<or> n\<^sub>1 -p:V\<rightarrow>\<^bsub>in\<^esub> n\<^sub>2\<close>
  have "realizable n\<^sub>0 (ns@n\<^sub>1#(ns''@ns')) n'"
    by(rule realizable.realizable_call)
  thus ?case by simp
qed


lemma realizable_valid_CFG_path:
  assumes "realizable n ns n'" 
  obtains as where "parent_node n -as\<rightarrow>\<^sub>\<surd>* parent_node n'"
proof(atomize_elim)
  from \<open>realizable n ns n'\<close> 
  show "\<exists>as. parent_node n -as\<rightarrow>\<^sub>\<surd>* parent_node n'"
  proof(induct rule:realizable.induct)
    case (realizable_matched n ns n')
    from \<open>matched n ns n'\<close> obtain as where "parent_node n -as\<rightarrow>\<^bsub>sl\<^esub>* parent_node n'"
      by(erule matched_same_level_CFG_path)
    thus ?case by(fastforce intro:slp_vp)
  next
    case (realizable_call n\<^sub>0 ns n\<^sub>1 p n\<^sub>2 V ns' n\<^sub>3)
    from \<open>\<exists>as. parent_node n\<^sub>0 -as\<rightarrow>\<^sub>\<surd>* parent_node n\<^sub>1\<close>
    obtain as where "parent_node n\<^sub>0 -as\<rightarrow>\<^sub>\<surd>* parent_node n\<^sub>1" by blast
    from \<open>matched n\<^sub>2 ns' n\<^sub>3\<close> obtain as' where "parent_node n\<^sub>2 -as'\<rightarrow>\<^bsub>sl\<^esub>* parent_node n\<^sub>3"
      by(erule matched_same_level_CFG_path)
    from \<open>n\<^sub>1 -p\<rightarrow>\<^bsub>call\<^esub> n\<^sub>2 \<or> n\<^sub>1 -p:V\<rightarrow>\<^bsub>in\<^esub> n\<^sub>2\<close>
    obtain a Q r fs where "valid_edge a"
      and "sourcenode a = parent_node n\<^sub>1" and "targetnode a = parent_node n\<^sub>2"
      and "kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs" by(fastforce elim:SDG_edge.cases)+
    hence "parent_node n\<^sub>1 -[a]\<rightarrow>* parent_node n\<^sub>2"
      by(fastforce dest:path_edge)
    from \<open>parent_node n\<^sub>0 -as\<rightarrow>\<^sub>\<surd>* parent_node n\<^sub>1\<close> 
    have "parent_node n\<^sub>0 -as\<rightarrow>* parent_node n\<^sub>1" and "valid_path as"
      by(simp_all add:vp_def)
    with \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close> have "valid_path (as@[a])"
      by(fastforce elim:valid_path_aux_Append simp:valid_path_def)
    moreover
    from \<open>parent_node n\<^sub>0 -as\<rightarrow>* parent_node n\<^sub>1\<close> \<open>parent_node n\<^sub>1 -[a]\<rightarrow>* parent_node n\<^sub>2\<close>
    have "parent_node n\<^sub>0 -as@[a]\<rightarrow>* parent_node n\<^sub>2" by(rule path_Append)
    ultimately have "parent_node n\<^sub>0 -as@[a]\<rightarrow>\<^sub>\<surd>* parent_node n\<^sub>2" by(simp add:vp_def)
    with \<open>parent_node n\<^sub>2 -as'\<rightarrow>\<^bsub>sl\<^esub>* parent_node n\<^sub>3\<close> 
    have "parent_node n\<^sub>0 -(as@[a])@as'\<rightarrow>\<^sub>\<surd>* parent_node n\<^sub>3" by -(rule vp_slp_Append)
    with \<open>sourcenode a = parent_node n\<^sub>1\<close> show ?case by fastforce
  qed
qed


lemma cdep_SDG_path_realizable:
  "n cc-ns\<rightarrow>\<^sub>d* n' \<Longrightarrow> realizable n ns n'"
proof(induct rule:call_cdep_SDG_path.induct)
  case (ccSp_Nil n)
  from \<open>valid_SDG_node n\<close> show ?case
    by(fastforce intro:realizable_matched matched_Nil)
next
  case (ccSp_Append_cdep n ns n'' n')
  from \<open>n'' \<longrightarrow>\<^bsub>cd\<^esub> n'\<close> have "valid_SDG_node n''" by(rule SDG_edge_valid_SDG_node)
  hence "matched n'' [] n''" by(rule matched_Nil)
  from \<open>n'' \<longrightarrow>\<^bsub>cd\<^esub> n'\<close> \<open>valid_SDG_node n''\<close>
  have "n'' i-[]@[n'']\<rightarrow>\<^sub>d* n'" 
    by(fastforce intro:iSp_Append_cdep iSp_Nil)
  with \<open>matched n'' [] n''\<close> have "matched n'' ([]@[n'']) n'"
    by(fastforce intro:matched_Append_intra_SDG_path)
  with \<open>realizable n ns n''\<close> show ?case
    by(fastforce intro:realizable_Append_matched)
next
  case (ccSp_Append_call n ns n'' p n')
  from \<open>n'' -p\<rightarrow>\<^bsub>call\<^esub> n'\<close> have "valid_SDG_node n'" by(rule SDG_edge_valid_SDG_node)
  hence "matched n' [] n'" by(rule matched_Nil)
  with \<open>realizable n ns n''\<close> \<open>n'' -p\<rightarrow>\<^bsub>call\<^esub> n'\<close>
  show ?case by(fastforce intro:realizable_call)
qed


subsection \<open>SDG with summary edges\<close>


inductive sum_cdep_edge :: "'node SDG_node \<Rightarrow> 'node SDG_node \<Rightarrow> bool" 
    ("_ s\<longrightarrow>\<^bsub>cd\<^esub> _" [51,0] 80)
  and sum_ddep_edge :: "'node SDG_node \<Rightarrow> 'var \<Rightarrow> 'node SDG_node \<Rightarrow> bool"
    ("_ s-_\<rightarrow>\<^sub>d\<^sub>d _" [51,0,0] 80)
  and sum_call_edge :: "'node SDG_node \<Rightarrow> 'pname \<Rightarrow> 'node SDG_node \<Rightarrow> bool" 
    ("_ s-_\<rightarrow>\<^bsub>call\<^esub> _" [51,0,0] 80)
  and sum_return_edge :: "'node SDG_node \<Rightarrow> 'pname \<Rightarrow> 'node SDG_node \<Rightarrow> bool" 
    ("_ s-_\<rightarrow>\<^bsub>ret\<^esub> _" [51,0,0] 80)
  and sum_param_in_edge :: "'node SDG_node \<Rightarrow> 'pname \<Rightarrow> 'var \<Rightarrow> 'node SDG_node \<Rightarrow> bool"
    ("_ s-_:_\<rightarrow>\<^bsub>in\<^esub> _" [51,0,0,0] 80)
  and sum_param_out_edge :: "'node SDG_node \<Rightarrow> 'pname \<Rightarrow> 'var \<Rightarrow> 'node SDG_node \<Rightarrow> bool"
    ("_ s-_:_\<rightarrow>\<^bsub>out\<^esub> _" [51,0,0,0] 80)
  and sum_summary_edge :: "'node SDG_node \<Rightarrow> 'pname \<Rightarrow> 'node SDG_node \<Rightarrow> bool" 
    ("_ s-_\<rightarrow>\<^bsub>sum\<^esub> _" [51,0] 80)
  and sum_SDG_edge :: "'node SDG_node \<Rightarrow> 'var option \<Rightarrow> 
                          ('pname \<times> bool) option \<Rightarrow> bool \<Rightarrow> 'node SDG_node \<Rightarrow> bool"

where
    (* Syntax *)
  "n s\<longrightarrow>\<^bsub>cd\<^esub> n' == sum_SDG_edge n None None False n'"
  | "n s-V\<rightarrow>\<^sub>d\<^sub>d n' == sum_SDG_edge n (Some V) None False n'"
  | "n s-p\<rightarrow>\<^bsub>call\<^esub> n' == sum_SDG_edge n None (Some(p,True)) False n'"
  | "n s-p\<rightarrow>\<^bsub>ret\<^esub> n' == sum_SDG_edge n None (Some(p,False)) False n'"
  | "n s-p:V\<rightarrow>\<^bsub>in\<^esub> n' == sum_SDG_edge n (Some V) (Some(p,True)) False n'"
  | "n s-p:V\<rightarrow>\<^bsub>out\<^esub> n' == sum_SDG_edge n (Some V) (Some(p,False)) False n'"
  | "n s-p\<rightarrow>\<^bsub>sum\<^esub> n' == sum_SDG_edge n None (Some(p,True)) True n'"

    (* Rules *)
  | sum_SDG_cdep_edge:
    "\<lbrakk>n = CFG_node m; n' = CFG_node m'; m controls m'\<rbrakk> \<Longrightarrow> n s\<longrightarrow>\<^bsub>cd\<^esub> n'"
  | sum_SDG_proc_entry_exit_cdep:
    "\<lbrakk>valid_edge a; kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs; n = CFG_node (targetnode a);
      a' \<in> get_return_edges a; n' = CFG_node (sourcenode a')\<rbrakk> \<Longrightarrow> n s\<longrightarrow>\<^bsub>cd\<^esub> n'"
  | sum_SDG_parent_cdep_edge:
    "\<lbrakk>valid_SDG_node n'; m = parent_node n'; n = CFG_node m; n \<noteq> n'\<rbrakk> 
      \<Longrightarrow> n s\<longrightarrow>\<^bsub>cd\<^esub> n'"
  | sum_SDG_ddep_edge:"n influences V in n' \<Longrightarrow> n s-V\<rightarrow>\<^sub>d\<^sub>d n'"
  | sum_SDG_call_edge:
    "\<lbrakk>valid_edge a; kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs; n = CFG_node (sourcenode a); 
      n' = CFG_node (targetnode a)\<rbrakk> \<Longrightarrow> n s-p\<rightarrow>\<^bsub>call\<^esub> n'"
  | sum_SDG_return_edge:
    "\<lbrakk>valid_edge a; kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>fs; n = CFG_node (sourcenode a); 
      n' = CFG_node (targetnode a)\<rbrakk> \<Longrightarrow> n s-p\<rightarrow>\<^bsub>ret\<^esub> n'"
  | sum_SDG_param_in_edge:
    "\<lbrakk>valid_edge a; kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs; (p,ins,outs) \<in> set procs; V = ins!x;
      x < length ins; n = Actual_in (sourcenode a,x); n' = Formal_in (targetnode a,x)\<rbrakk>
      \<Longrightarrow> n s-p:V\<rightarrow>\<^bsub>in\<^esub> n'"
  | sum_SDG_param_out_edge:
    "\<lbrakk>valid_edge a; kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f; (p,ins,outs) \<in> set procs; V = outs!x;
      x < length outs; n = Formal_out (sourcenode a,x); 
      n' = Actual_out (targetnode a,x)\<rbrakk>
      \<Longrightarrow> n s-p:V\<rightarrow>\<^bsub>out\<^esub> n'"
  | sum_SDG_call_summary_edge:
    "\<lbrakk>valid_edge a; kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs; a' \<in> get_return_edges a; 
      n = CFG_node (sourcenode a); n' = CFG_node (targetnode a')\<rbrakk>
      \<Longrightarrow> n s-p\<rightarrow>\<^bsub>sum\<^esub> n'"
  | sum_SDG_param_summary_edge:
    "\<lbrakk>valid_edge a; kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs; a' \<in> get_return_edges a;
      matched (Formal_in (targetnode a,x)) ns (Formal_out (sourcenode a',x'));
      n = Actual_in (sourcenode a,x); n' = Actual_out (targetnode a',x');
      (p,ins,outs) \<in> set procs; x < length ins; x' < length outs\<rbrakk>
      \<Longrightarrow> n s-p\<rightarrow>\<^bsub>sum\<^esub> n'"



lemma sum_edge_cases:
  "\<lbrakk>n s-p\<rightarrow>\<^bsub>sum\<^esub> n'; 
    \<And>a Q r fs a'. \<lbrakk>valid_edge a; kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs; a' \<in> get_return_edges a;
                n = CFG_node (sourcenode a); n' = CFG_node (targetnode a')\<rbrakk> \<Longrightarrow> P;
    \<And>a Q p r fs a' ns x x' ins outs.
      \<lbrakk>valid_edge a; kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs; a' \<in> get_return_edges a;
       matched (Formal_in (targetnode a,x)) ns (Formal_out (sourcenode a',x'));
       n = Actual_in (sourcenode a,x); n' = Actual_out (targetnode a',x');
       (p,ins,outs) \<in> set procs; x < length ins; x' < length outs\<rbrakk> \<Longrightarrow> P\<rbrakk>
  \<Longrightarrow> P"
by -(erule sum_SDG_edge.cases,auto)



lemma SDG_edge_sum_SDG_edge:
  "SDG_edge n Vopt popt n' \<Longrightarrow> sum_SDG_edge n Vopt popt False n'"
  by(induct rule:SDG_edge.induct,auto intro:sum_SDG_edge.intros)


lemma sum_SDG_edge_SDG_edge:
  "sum_SDG_edge n Vopt popt False n' \<Longrightarrow> SDG_edge n Vopt popt n'"
by(induct n Vopt popt x\<equiv>"False" n' rule:sum_SDG_edge.induct,
   auto intro:SDG_edge.intros)


lemma sum_SDG_edge_valid_SDG_node:
  assumes "sum_SDG_edge n Vopt popt b n'" 
  shows "valid_SDG_node n" and "valid_SDG_node n'"
proof -
  have "valid_SDG_node n \<and> valid_SDG_node n'"
  proof(cases b)
    case True
    with \<open>sum_SDG_edge n Vopt popt b n'\<close> show ?thesis
    proof(induct rule:sum_SDG_edge.induct)
      case (sum_SDG_call_summary_edge a Q r p f a' n n')
      from \<open>valid_edge a\<close> \<open>n = CFG_node (sourcenode a)\<close>
      have "valid_SDG_node n" by fastforce
      from \<open>valid_edge a\<close> \<open>a' \<in> get_return_edges a\<close> have "valid_edge a'"
        by(rule get_return_edges_valid)
      with \<open>n' = CFG_node (targetnode a')\<close> have "valid_SDG_node n'" by fastforce
      with \<open>valid_SDG_node n\<close> show ?case by simp
    next
      case (sum_SDG_param_summary_edge a Q r p fs a' x ns x' n n' ins outs)
      from \<open>valid_edge a\<close> \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close> \<open>n = Actual_in (sourcenode a,x)\<close>
        \<open>(p,ins,outs) \<in> set procs\<close> \<open>x < length ins\<close>
      have "valid_SDG_node n" by fastforce
      from \<open>valid_edge a\<close> \<open>a' \<in> get_return_edges a\<close> have "valid_edge a'"
        by(rule get_return_edges_valid)
      from \<open>valid_edge a\<close> \<open>a' \<in> get_return_edges a\<close> \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close>
      obtain Q' f' where "kind a' = Q'\<hookleftarrow>\<^bsub>p\<^esub>f'" by(fastforce dest!:call_return_edges)
      with \<open>valid_edge a'\<close> \<open>n' = Actual_out (targetnode a',x')\<close>
        \<open>(p,ins,outs) \<in> set procs\<close> \<open>x' < length outs\<close>
      have "valid_SDG_node n'" by fastforce
      with \<open>valid_SDG_node n\<close> show ?case by simp
    qed simp_all
  next
    case False
    with \<open>sum_SDG_edge n Vopt popt b n'\<close> have "SDG_edge n Vopt popt n'"
      by(fastforce intro:sum_SDG_edge_SDG_edge)
    thus ?thesis by(fastforce intro:SDG_edge_valid_SDG_node)
  qed
  thus "valid_SDG_node n" and "valid_SDG_node n'" by simp_all
qed


lemma Exit_no_sum_SDG_edge_source:
  assumes "sum_SDG_edge (CFG_node (_Exit_)) Vopt popt b n'" shows "False"
proof(cases b)
  case True
  with \<open>sum_SDG_edge (CFG_node (_Exit_)) Vopt popt b n'\<close> show ?thesis
  proof(induct "CFG_node (_Exit_)" Vopt popt b n' rule:sum_SDG_edge.induct)
    case (sum_SDG_call_summary_edge a Q r p f a' n')
    from \<open>CFG_node (_Exit_) = CFG_node (sourcenode a)\<close>
    have "sourcenode a = (_Exit_)" by simp
    with \<open>valid_edge a\<close> show ?case by(rule Exit_source)
  next
    case (sum_SDG_param_summary_edge a Q r p f a' x ns x' n' ins outs)
    thus ?case by simp
  qed simp_all
next
  case False
  with \<open>sum_SDG_edge (CFG_node (_Exit_)) Vopt popt b n'\<close> 
  have "SDG_edge (CFG_node (_Exit_)) Vopt popt n'"
    by(fastforce intro:sum_SDG_edge_SDG_edge)
  thus ?thesis by(fastforce intro:Exit_no_SDG_edge_source)
qed


lemma Exit_no_sum_SDG_edge_target:
  "sum_SDG_edge n Vopt popt b (CFG_node (_Exit_)) \<Longrightarrow> False"
proof(induct "CFG_node (_Exit_)" rule:sum_SDG_edge.induct)
  case (sum_SDG_cdep_edge n m m')
  from \<open>m controls m'\<close> \<open>CFG_node (_Exit_) = CFG_node m'\<close>
  have "m controls (_Exit_)" by simp
  hence False by(fastforce dest:Exit_not_control_dependent)
  thus ?case by simp
next
  case (sum_SDG_proc_entry_exit_cdep a Q r p f n a')
  from \<open>valid_edge a\<close> \<open>a' \<in> get_return_edges a\<close> have "valid_edge a'"
    by(rule get_return_edges_valid)
  moreover
  from \<open>CFG_node (_Exit_) = CFG_node (sourcenode a')\<close>
  have "sourcenode a' = (_Exit_)" by simp
  ultimately have False by(rule Exit_source)
  thus ?case by simp
next
  case (sum_SDG_ddep_edge n V) thus ?case
    by(fastforce elim:SDG_Use.cases simp:data_dependence_def)
next
  case (sum_SDG_call_edge a Q r p fs n)
  from \<open>CFG_node (_Exit_) = CFG_node (targetnode a)\<close>
  have "targetnode a = (_Exit_)" by simp
  with \<open>valid_edge a\<close> \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close> have "get_proc (_Exit_) = p"
    by(fastforce intro:get_proc_call)
  hence "p = Main" by(simp add:get_proc_Exit)
  with \<open>valid_edge a\<close> \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close> have False 
    by(fastforce intro:Main_no_call_target)
  thus ?case by simp
next
  case (sum_SDG_return_edge a Q p f n)
  from \<open>CFG_node (_Exit_) = CFG_node (targetnode a)\<close>
  have "targetnode a = (_Exit_)" by simp
  with \<open>valid_edge a\<close> \<open>kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f\<close> have False by(rule Exit_no_return_target)
  thus ?case by simp
next
  case (sum_SDG_call_summary_edge a Q r p fs a' n)
  from \<open>valid_edge a\<close> \<open>a' \<in> get_return_edges a\<close> have "valid_edge a'"
    by(rule get_return_edges_valid)
  from \<open>valid_edge a\<close> \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close> \<open>a' \<in> get_return_edges a\<close>
  obtain Q' f' where "kind a' = Q'\<hookleftarrow>\<^bsub>p\<^esub>f'" by(fastforce dest!:call_return_edges)
  from \<open>CFG_node (_Exit_) = CFG_node (targetnode a')\<close>
  have "targetnode a' = (_Exit_)" by simp
  with \<open>valid_edge a'\<close> \<open>kind a' = Q'\<hookleftarrow>\<^bsub>p\<^esub>f'\<close> have False by(rule Exit_no_return_target)
  thus ?case by simp
qed simp+



lemma sum_SDG_summary_edge_matched:
  assumes "n s-p\<rightarrow>\<^bsub>sum\<^esub> n'" 
  obtains ns where "matched n ns n'" and "n \<in> set ns"
  and "get_proc (parent_node(last ns)) = p"
proof(atomize_elim)
  from \<open>n s-p\<rightarrow>\<^bsub>sum\<^esub> n'\<close> 
  show "\<exists>ns. matched n ns n' \<and> n \<in> set ns \<and> get_proc (parent_node(last ns)) = p"
  proof(induct n "None::'var option" "Some(p,True)" "True" n'
               rule:sum_SDG_edge.induct)
    case (sum_SDG_call_summary_edge a Q r fs a' n n')
    from \<open>valid_edge a\<close> \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close> \<open>n = CFG_node (sourcenode a)\<close>
    have "n -p\<rightarrow>\<^bsub>call\<^esub> CFG_node (targetnode a)" by(fastforce intro:SDG_call_edge)
    hence "valid_SDG_node n" by(rule SDG_edge_valid_SDG_node)
    hence "matched n [] n" by(rule matched_Nil)
    from \<open>valid_edge a\<close> \<open>a' \<in> get_return_edges a\<close> have "valid_edge a'"
      by(rule get_return_edges_valid)
    from \<open>valid_edge a\<close> \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close> \<open>a' \<in> get_return_edges a\<close> 
    have matched:"matched (CFG_node (targetnode a)) [CFG_node (targetnode a)]
      (CFG_node (sourcenode a'))" by(rule intra_proc_matched)
    from \<open>valid_edge a\<close> \<open>a' \<in> get_return_edges a\<close> \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close>
    obtain Q' f' where "kind a' = Q'\<hookleftarrow>\<^bsub>p\<^esub>f'" by(fastforce dest!:call_return_edges)
    with \<open>valid_edge a'\<close> have "get_proc (sourcenode a') = p" by(rule get_proc_return)
    from \<open>valid_edge a'\<close> \<open>kind a' = Q'\<hookleftarrow>\<^bsub>p\<^esub>f'\<close> \<open>n' = CFG_node (targetnode a')\<close>
    have "CFG_node (sourcenode a') -p\<rightarrow>\<^bsub>ret\<^esub> n'" by(fastforce intro:SDG_return_edge)
    from \<open>matched n [] n\<close> \<open>n -p\<rightarrow>\<^bsub>call\<^esub> CFG_node (targetnode a)\<close> matched
      \<open>CFG_node (sourcenode a') -p\<rightarrow>\<^bsub>ret\<^esub> n'\<close> \<open>a' \<in> get_return_edges a\<close>
      \<open>n = CFG_node (sourcenode a)\<close> \<open>n' = CFG_node (targetnode a')\<close> \<open>valid_edge a\<close>
    have "matched n ([]@n#[CFG_node (targetnode a)]@[CFG_node (sourcenode a')]) n'"
      by(fastforce intro:matched_bracket_call)
    with \<open>get_proc (sourcenode a') = p\<close> show ?case by auto
  next
    case (sum_SDG_param_summary_edge a Q r fs a' x ns x' n n' ins outs)
    from \<open>valid_edge a\<close> \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close> \<open>(p,ins,outs) \<in> set procs\<close>
      \<open>x < length ins\<close> \<open>n = Actual_in (sourcenode a,x)\<close>
    have "n -p:ins!x\<rightarrow>\<^bsub>in\<^esub> Formal_in (targetnode a,x)" 
      by(fastforce intro:SDG_param_in_edge)
    hence "valid_SDG_node n" by(rule SDG_edge_valid_SDG_node)
    hence "matched n [] n" by(rule matched_Nil)
    from \<open>valid_edge a\<close> \<open>a' \<in> get_return_edges a\<close> have "valid_edge a'"
      by(rule get_return_edges_valid)
    from \<open>valid_edge a\<close> \<open>a' \<in> get_return_edges a\<close> \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close>
    obtain Q' f' where "kind a' = Q'\<hookleftarrow>\<^bsub>p\<^esub>f'" by(fastforce dest!:call_return_edges)
    with \<open>valid_edge a'\<close> have "get_proc (sourcenode a') = p" by(rule get_proc_return)
    from \<open>valid_edge a'\<close> \<open>kind a' = Q'\<hookleftarrow>\<^bsub>p\<^esub>f'\<close> \<open>(p,ins,outs) \<in> set procs\<close>
      \<open>x' < length outs\<close> \<open>n' = Actual_out (targetnode a',x')\<close>
    have "Formal_out (sourcenode a',x') -p:outs!x'\<rightarrow>\<^bsub>out\<^esub> n'"
      by(fastforce intro:SDG_param_out_edge)
    from \<open>matched n [] n\<close> \<open>n -p:ins!x\<rightarrow>\<^bsub>in\<^esub> Formal_in (targetnode a,x)\<close>
      \<open>matched (Formal_in (targetnode a,x)) ns (Formal_out (sourcenode a',x'))\<close>
      \<open>Formal_out (sourcenode a',x') -p:outs!x'\<rightarrow>\<^bsub>out\<^esub> n'\<close> 
      \<open>a' \<in> get_return_edges a\<close> \<open>n = Actual_in (sourcenode a,x)\<close>
      \<open>n' = Actual_out (targetnode a',x')\<close> \<open>valid_edge a\<close>
    have "matched n ([]@n#ns@[Formal_out (sourcenode a',x')]) n'"
      by(fastforce intro:matched_bracket_param)
    with \<open>get_proc (sourcenode a') = p\<close> show ?case by auto
  qed simp_all
qed


lemma return_edge_determines_call_and_sum_edge:
  assumes "valid_edge a" and "kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f"
  obtains a' Q' r' fs' where "a \<in> get_return_edges a'" and "valid_edge a'"
  and "kind a' = Q':r'\<hookrightarrow>\<^bsub>p\<^esub>fs'" 
  and "CFG_node (sourcenode a') s-p\<rightarrow>\<^bsub>sum\<^esub> CFG_node (targetnode a)"
proof(atomize_elim)
  from \<open>valid_edge a\<close> \<open>kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f\<close>
  have "CFG_node (sourcenode a) s-p\<rightarrow>\<^bsub>ret\<^esub> CFG_node (targetnode a)"
    by(fastforce intro:sum_SDG_return_edge)
  from \<open>valid_edge a\<close> \<open>kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f\<close>
  obtain a' Q' r' fs' where "valid_edge a'" and "kind a' = Q':r'\<hookrightarrow>\<^bsub>p\<^esub>fs'"
    and "a \<in> get_return_edges a'" by(blast dest:return_needs_call)
  hence "CFG_node (sourcenode a') s-p\<rightarrow>\<^bsub>call\<^esub> CFG_node (targetnode a')"
    by(fastforce intro:sum_SDG_call_edge)
  from \<open>valid_edge a'\<close> \<open>kind a' = Q':r'\<hookrightarrow>\<^bsub>p\<^esub>fs'\<close> \<open>valid_edge a\<close> \<open>a \<in> get_return_edges a'\<close>
  have "CFG_node (targetnode a') \<longrightarrow>\<^bsub>cd\<^esub> CFG_node (sourcenode a)"
    by(fastforce intro!:SDG_proc_entry_exit_cdep)
  hence "valid_SDG_node (CFG_node (targetnode a'))"
    by(rule SDG_edge_valid_SDG_node)
  with \<open>CFG_node (targetnode a') \<longrightarrow>\<^bsub>cd\<^esub> CFG_node (sourcenode a)\<close> 
  have "CFG_node (targetnode a') i-[]@[CFG_node (targetnode a')]\<rightarrow>\<^sub>d* 
        CFG_node (sourcenode a)"
    by(fastforce intro:iSp_Append_cdep iSp_Nil)
  from \<open>valid_SDG_node (CFG_node (targetnode a'))\<close> 
  have "matched (CFG_node (targetnode a')) [] (CFG_node (targetnode a'))"
    by(rule matched_Nil)
  with \<open>CFG_node (targetnode a') i-[]@[CFG_node (targetnode a')]\<rightarrow>\<^sub>d* 
        CFG_node (sourcenode a)\<close>
  have "matched (CFG_node (targetnode a')) ([]@[CFG_node (targetnode a')])
                (CFG_node (sourcenode a))"
    by(fastforce intro:matched_Append_intra_SDG_path)
  with \<open>valid_edge a'\<close> \<open>kind a' = Q':r'\<hookrightarrow>\<^bsub>p\<^esub>fs'\<close> \<open>valid_edge a\<close> \<open>kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f\<close>
    \<open>a \<in> get_return_edges a'\<close>
  have "CFG_node (sourcenode a') s-p\<rightarrow>\<^bsub>sum\<^esub> CFG_node (targetnode a)"
    by(fastforce intro!:sum_SDG_call_summary_edge)
  with \<open>a \<in> get_return_edges a'\<close> \<open>valid_edge a'\<close> \<open>kind a' = Q':r'\<hookrightarrow>\<^bsub>p\<^esub>fs'\<close>
  show "\<exists>a' Q' r' fs'. a \<in> get_return_edges a' \<and> valid_edge a' \<and> 
    kind a' = Q':r'\<hookrightarrow>\<^bsub>p\<^esub>fs' \<and> CFG_node (sourcenode a') s-p\<rightarrow>\<^bsub>sum\<^esub> CFG_node (targetnode a)"
    by fastforce
qed
  

subsection \<open>Paths consisting of intraprocedural and summary edges in the SDG\<close>

inductive intra_sum_SDG_path ::
  "'node SDG_node \<Rightarrow> 'node SDG_node list \<Rightarrow> 'node SDG_node \<Rightarrow> bool"
("_ is-_\<rightarrow>\<^sub>d* _" [51,0,0] 80)
where isSp_Nil:
  "valid_SDG_node n \<Longrightarrow> n is-[]\<rightarrow>\<^sub>d* n"

  | isSp_Append_cdep:
  "\<lbrakk>n is-ns\<rightarrow>\<^sub>d* n''; n'' s\<longrightarrow>\<^bsub>cd\<^esub> n'\<rbrakk> \<Longrightarrow> n is-ns@[n'']\<rightarrow>\<^sub>d* n'"

  | isSp_Append_ddep:
  "\<lbrakk>n is-ns\<rightarrow>\<^sub>d* n''; n'' s-V\<rightarrow>\<^sub>d\<^sub>d n'; n'' \<noteq> n'\<rbrakk> \<Longrightarrow> n is-ns@[n'']\<rightarrow>\<^sub>d* n'"

  | isSp_Append_sum:
  "\<lbrakk>n is-ns\<rightarrow>\<^sub>d* n''; n'' s-p\<rightarrow>\<^bsub>sum\<^esub> n'\<rbrakk> \<Longrightarrow> n is-ns@[n'']\<rightarrow>\<^sub>d* n'"


lemma is_SDG_path_Append:
  "\<lbrakk>n'' is-ns'\<rightarrow>\<^sub>d* n'; n is-ns\<rightarrow>\<^sub>d* n''\<rbrakk> \<Longrightarrow> n is-ns@ns'\<rightarrow>\<^sub>d* n'"
by(induct rule:intra_sum_SDG_path.induct,
   auto intro:intra_sum_SDG_path.intros simp:append_assoc[THEN sym] 
                                        simp del:append_assoc)


lemma is_SDG_path_valid_SDG_node:
  assumes "n is-ns\<rightarrow>\<^sub>d* n'" shows "valid_SDG_node n" and "valid_SDG_node n'"
using \<open>n is-ns\<rightarrow>\<^sub>d* n'\<close>
by(induct rule:intra_sum_SDG_path.induct,
   auto intro:sum_SDG_edge_valid_SDG_node valid_SDG_CFG_node)


lemma intra_SDG_path_is_SDG_path:
  "n i-ns\<rightarrow>\<^sub>d* n' \<Longrightarrow> n is-ns\<rightarrow>\<^sub>d* n'"
by(induct rule:intra_SDG_path.induct,
   auto intro:intra_sum_SDG_path.intros SDG_edge_sum_SDG_edge)


lemma is_SDG_path_hd:"\<lbrakk>n is-ns\<rightarrow>\<^sub>d* n'; ns \<noteq> []\<rbrakk> \<Longrightarrow> hd ns = n"
apply(induct rule:intra_sum_SDG_path.induct) apply clarsimp
by(case_tac ns,auto elim:intra_sum_SDG_path.cases)+


lemma intra_sum_SDG_path_rev_induct [consumes 1, case_names "isSp_Nil" 
  "isSp_Cons_cdep"  "isSp_Cons_ddep"  "isSp_Cons_sum"]: 
  assumes "n is-ns\<rightarrow>\<^sub>d* n'"
  and refl:"\<And>n. valid_SDG_node n \<Longrightarrow> P n [] n"
  and step_cdep:"\<And>n ns n' n''. \<lbrakk>n s\<longrightarrow>\<^bsub>cd\<^esub> n''; n'' is-ns\<rightarrow>\<^sub>d* n'; P n'' ns n'\<rbrakk> 
                 \<Longrightarrow> P n (n#ns) n'"
  and step_ddep:"\<And>n ns n' V n''. \<lbrakk>n s-V\<rightarrow>\<^sub>d\<^sub>d n''; n \<noteq> n''; n'' is-ns\<rightarrow>\<^sub>d* n'; 
                                  P n'' ns n'\<rbrakk> \<Longrightarrow> P n (n#ns) n'"
  and step_sum:"\<And>n ns n' p n''. \<lbrakk>n s-p\<rightarrow>\<^bsub>sum\<^esub> n''; n'' is-ns\<rightarrow>\<^sub>d* n'; P n'' ns n'\<rbrakk> 
                 \<Longrightarrow> P n (n#ns) n'"
  shows "P n ns n'"
using \<open>n is-ns\<rightarrow>\<^sub>d* n'\<close>
proof(induct ns arbitrary:n)
  case Nil thus ?case by(fastforce elim:intra_sum_SDG_path.cases intro:refl)
next
  case (Cons nx nsx)
  note IH = \<open>\<And>n. n is-nsx\<rightarrow>\<^sub>d* n' \<Longrightarrow> P n nsx n'\<close>
  from \<open>n is-nx#nsx\<rightarrow>\<^sub>d* n'\<close> have [simp]:"n = nx" 
    by(fastforce dest:is_SDG_path_hd)
  from \<open>n is-nx#nsx\<rightarrow>\<^sub>d* n'\<close>  have "((\<exists>n''. n s\<longrightarrow>\<^bsub>cd\<^esub> n'' \<and> n'' is-nsx\<rightarrow>\<^sub>d* n') \<or>
    (\<exists>n'' V. n s-V\<rightarrow>\<^sub>d\<^sub>d n'' \<and> n \<noteq> n'' \<and> n'' is-nsx\<rightarrow>\<^sub>d* n')) \<or>
    (\<exists>n'' p. n s-p\<rightarrow>\<^bsub>sum\<^esub> n'' \<and> n'' is-nsx\<rightarrow>\<^sub>d* n')"
  proof(induct nsx arbitrary:n' rule:rev_induct)
    case Nil
    from \<open>n is-[nx]\<rightarrow>\<^sub>d* n'\<close> have "n is-[]\<rightarrow>\<^sub>d* nx" 
      and disj:"nx s\<longrightarrow>\<^bsub>cd\<^esub> n' \<or> (\<exists>V. nx s-V\<rightarrow>\<^sub>d\<^sub>d n' \<and> nx \<noteq> n') \<or> (\<exists>p. nx s-p\<rightarrow>\<^bsub>sum\<^esub> n')"
      by(induct n ns\<equiv>"[nx]" n' rule:intra_sum_SDG_path.induct,auto)
    from \<open>n is-[]\<rightarrow>\<^sub>d* nx\<close> have [simp]:"n = nx"
      by(fastforce elim:intra_sum_SDG_path.cases)
    from disj have "valid_SDG_node n'" by(fastforce intro:sum_SDG_edge_valid_SDG_node)
    hence "n' is-[]\<rightarrow>\<^sub>d* n'" by(rule isSp_Nil)
    with disj show ?case by fastforce
  next
    case (snoc x xs)
    note \<open>\<And>n'. n is-nx # xs\<rightarrow>\<^sub>d* n' \<Longrightarrow>
      ((\<exists>n''. n s\<longrightarrow>\<^bsub>cd\<^esub> n'' \<and> n'' is-xs\<rightarrow>\<^sub>d* n') \<or>
      (\<exists>n'' V. n s-V\<rightarrow>\<^sub>d\<^sub>d n'' \<and> n \<noteq> n'' \<and> n'' is-xs\<rightarrow>\<^sub>d* n')) \<or>
      (\<exists>n'' p. n s-p\<rightarrow>\<^bsub>sum\<^esub> n'' \<and> n'' is-xs\<rightarrow>\<^sub>d* n')\<close>
    with \<open>n is-nx#xs@[x]\<rightarrow>\<^sub>d* n'\<close> show ?case
    proof(induct n "nx#xs@[x]" n' rule:intra_sum_SDG_path.induct)
      case (isSp_Append_cdep m ms m'' n')
      note IH = \<open>\<And>n'. m is-nx # xs\<rightarrow>\<^sub>d* n' \<Longrightarrow>
        ((\<exists>n''. m s\<longrightarrow>\<^bsub>cd\<^esub> n'' \<and> n'' is-xs\<rightarrow>\<^sub>d* n') \<or>
        (\<exists>n'' V. m s-V\<rightarrow>\<^sub>d\<^sub>d n'' \<and> m \<noteq> n'' \<and> n'' is-xs\<rightarrow>\<^sub>d* n')) \<or>
        (\<exists>n'' p. m s-p\<rightarrow>\<^bsub>sum\<^esub> n'' \<and> n'' is-xs\<rightarrow>\<^sub>d* n')\<close>
      from \<open>ms @ [m''] = nx#xs@[x]\<close> have [simp]:"ms = nx#xs"
        and [simp]:"m'' = x" by simp_all
      from \<open>m is-ms\<rightarrow>\<^sub>d* m''\<close> have "m is-nx#xs\<rightarrow>\<^sub>d* m''" by simp
      from IH[OF this] obtain n'' where "n'' is-xs\<rightarrow>\<^sub>d* m''"
        and "(m s\<longrightarrow>\<^bsub>cd\<^esub> n'' \<or> (\<exists>V. m s-V\<rightarrow>\<^sub>d\<^sub>d n'' \<and> m \<noteq> n'')) \<or> (\<exists>p. m s-p\<rightarrow>\<^bsub>sum\<^esub> n'')"
        by fastforce
      from \<open>n'' is-xs\<rightarrow>\<^sub>d* m''\<close> \<open>m'' s\<longrightarrow>\<^bsub>cd\<^esub> n'\<close>
      have "n'' is-xs@[m'']\<rightarrow>\<^sub>d* n'" by(rule intra_sum_SDG_path.intros)
      with \<open>(m s\<longrightarrow>\<^bsub>cd\<^esub> n'' \<or> (\<exists>V. m s-V\<rightarrow>\<^sub>d\<^sub>d n'' \<and> m \<noteq> n'')) \<or> (\<exists>p. m s-p\<rightarrow>\<^bsub>sum\<^esub> n'')\<close>
      show ?case by fastforce
    next
      case (isSp_Append_ddep m ms m'' V n')
      note IH = \<open>\<And>n'. m is-nx # xs\<rightarrow>\<^sub>d* n' \<Longrightarrow>
        ((\<exists>n''. m s\<longrightarrow>\<^bsub>cd\<^esub> n'' \<and> n'' is-xs\<rightarrow>\<^sub>d* n') \<or>
        (\<exists>n'' V. m s-V\<rightarrow>\<^sub>d\<^sub>d n'' \<and> m \<noteq> n'' \<and> n'' is-xs\<rightarrow>\<^sub>d* n')) \<or>
        (\<exists>n'' p. m s-p\<rightarrow>\<^bsub>sum\<^esub> n'' \<and> n'' is-xs\<rightarrow>\<^sub>d* n')\<close>
      from \<open>ms @ [m''] = nx#xs@[x]\<close> have [simp]:"ms = nx#xs"
        and [simp]:"m'' = x" by simp_all
      from \<open>m is-ms\<rightarrow>\<^sub>d* m''\<close> have "m is-nx#xs\<rightarrow>\<^sub>d* m''" by simp
      from IH[OF this] obtain n'' where "n'' is-xs\<rightarrow>\<^sub>d* m''"
        and "(m s\<longrightarrow>\<^bsub>cd\<^esub> n'' \<or> (\<exists>V. m s-V\<rightarrow>\<^sub>d\<^sub>d n'' \<and> m \<noteq> n'')) \<or> (\<exists>p. m s-p\<rightarrow>\<^bsub>sum\<^esub> n'')"
        by fastforce
      from \<open>n'' is-xs\<rightarrow>\<^sub>d* m''\<close> \<open>m'' s-V\<rightarrow>\<^sub>d\<^sub>d n'\<close> \<open>m'' \<noteq> n'\<close>
      have "n'' is-xs@[m'']\<rightarrow>\<^sub>d* n'" by(rule intra_sum_SDG_path.intros)
      with \<open>(m s\<longrightarrow>\<^bsub>cd\<^esub> n'' \<or> (\<exists>V. m s-V\<rightarrow>\<^sub>d\<^sub>d n'' \<and> m \<noteq> n'')) \<or> (\<exists>p. m s-p\<rightarrow>\<^bsub>sum\<^esub> n'')\<close>
      show ?case by fastforce
    next
      case (isSp_Append_sum m ms m'' p n')
      note IH = \<open>\<And>n'. m is-nx # xs\<rightarrow>\<^sub>d* n' \<Longrightarrow>
        ((\<exists>n''. m s\<longrightarrow>\<^bsub>cd\<^esub> n'' \<and> n'' is-xs\<rightarrow>\<^sub>d* n') \<or>
        (\<exists>n'' V. m s-V\<rightarrow>\<^sub>d\<^sub>d n'' \<and> m \<noteq> n'' \<and> n'' is-xs\<rightarrow>\<^sub>d* n')) \<or>
        (\<exists>n'' p. m s-p\<rightarrow>\<^bsub>sum\<^esub> n'' \<and> n'' is-xs\<rightarrow>\<^sub>d* n')\<close>
      from \<open>ms @ [m''] = nx#xs@[x]\<close> have [simp]:"ms = nx#xs"
        and [simp]:"m'' = x" by simp_all
      from \<open>m is-ms\<rightarrow>\<^sub>d* m''\<close> have "m is-nx#xs\<rightarrow>\<^sub>d* m''" by simp
      from IH[OF this] obtain n'' where "n'' is-xs\<rightarrow>\<^sub>d* m''"
        and "(m s\<longrightarrow>\<^bsub>cd\<^esub> n'' \<or> (\<exists>V. m s-V\<rightarrow>\<^sub>d\<^sub>d n'' \<and> m \<noteq> n'')) \<or> (\<exists>p. m s-p\<rightarrow>\<^bsub>sum\<^esub> n'')"
        by fastforce
      from \<open>n'' is-xs\<rightarrow>\<^sub>d* m''\<close> \<open>m'' s-p\<rightarrow>\<^bsub>sum\<^esub> n'\<close>
      have "n'' is-xs@[m'']\<rightarrow>\<^sub>d* n'" by(rule intra_sum_SDG_path.intros)
      with \<open>(m s\<longrightarrow>\<^bsub>cd\<^esub> n'' \<or> (\<exists>V. m s-V\<rightarrow>\<^sub>d\<^sub>d n'' \<and> m \<noteq> n'')) \<or> (\<exists>p. m s-p\<rightarrow>\<^bsub>sum\<^esub> n'')\<close>
      show ?case by fastforce
    qed
  qed
  thus ?case apply -
  proof(erule disjE)+
    assume "\<exists>n''. n s\<longrightarrow>\<^bsub>cd\<^esub> n'' \<and> n'' is-nsx\<rightarrow>\<^sub>d* n'"
    then obtain n'' where "n s\<longrightarrow>\<^bsub>cd\<^esub> n''" and "n'' is-nsx\<rightarrow>\<^sub>d* n'" by blast
    from IH[OF \<open>n'' is-nsx\<rightarrow>\<^sub>d* n'\<close>] have "P n'' nsx n'" .
    from step_cdep[OF \<open>n s\<longrightarrow>\<^bsub>cd\<^esub> n''\<close> \<open>n'' is-nsx\<rightarrow>\<^sub>d* n'\<close> this] show ?thesis by simp
  next
    assume "\<exists>n'' V. n s-V\<rightarrow>\<^sub>d\<^sub>d n'' \<and> n \<noteq> n'' \<and> n'' is-nsx\<rightarrow>\<^sub>d* n'"
    then obtain n'' V where "n s-V\<rightarrow>\<^sub>d\<^sub>d n''" and "n \<noteq> n''" and "n'' is-nsx\<rightarrow>\<^sub>d* n'" 
      by blast
    from IH[OF \<open>n'' is-nsx\<rightarrow>\<^sub>d* n'\<close>] have "P n'' nsx n'" .
    from step_ddep[OF \<open>n s-V\<rightarrow>\<^sub>d\<^sub>d n''\<close> \<open>n \<noteq> n''\<close> \<open>n'' is-nsx\<rightarrow>\<^sub>d* n'\<close> this] 
    show ?thesis by simp
  next
    assume "\<exists>n'' p. n s-p\<rightarrow>\<^bsub>sum\<^esub> n'' \<and> n'' is-nsx\<rightarrow>\<^sub>d* n'"
    then obtain n'' p where "n s-p\<rightarrow>\<^bsub>sum\<^esub> n''" and "n'' is-nsx\<rightarrow>\<^sub>d* n'" by blast
    from IH[OF \<open>n'' is-nsx\<rightarrow>\<^sub>d* n'\<close>] have "P n'' nsx n'" .
    from step_sum[OF \<open>n s-p\<rightarrow>\<^bsub>sum\<^esub> n''\<close> \<open>n'' is-nsx\<rightarrow>\<^sub>d* n'\<close> this] show ?thesis by simp
  qed
qed


lemma is_SDG_path_CFG_path:
  assumes "n is-ns\<rightarrow>\<^sub>d* n'"
  obtains as where "parent_node n -as\<rightarrow>\<^sub>\<iota>* parent_node n'" 
proof(atomize_elim)
  from \<open>n is-ns\<rightarrow>\<^sub>d* n'\<close>
  show "\<exists>as. parent_node n -as\<rightarrow>\<^sub>\<iota>* parent_node n'"
  proof(induct rule:intra_sum_SDG_path.induct)
    case (isSp_Nil n)
    from \<open>valid_SDG_node n\<close> have "valid_node (parent_node n)"
      by(rule valid_SDG_CFG_node)
    hence "parent_node n -[]\<rightarrow>* parent_node n" by(rule empty_path)
    thus ?case by(auto simp:intra_path_def)
  next
    case (isSp_Append_cdep n ns n'' n')
    from \<open>\<exists>as. parent_node n -as\<rightarrow>\<^sub>\<iota>* parent_node n''\<close>
    obtain as where "parent_node n -as\<rightarrow>\<^sub>\<iota>* parent_node n''" by blast
    from \<open>n'' s\<longrightarrow>\<^bsub>cd\<^esub> n'\<close>  have "n'' \<longrightarrow>\<^bsub>cd\<^esub> n'" by(rule sum_SDG_edge_SDG_edge)
    thus ?case
    proof(rule cdep_edge_cases)
      assume "parent_node n'' controls parent_node n'"
      then obtain as' where "parent_node n'' -as'\<rightarrow>\<^sub>\<iota>* parent_node n'" and "as' \<noteq> []"
        by(erule control_dependence_path)
      with \<open>parent_node n -as\<rightarrow>\<^sub>\<iota>* parent_node n''\<close> 
      have "parent_node n -as@as'\<rightarrow>\<^sub>\<iota>* parent_node n'" by -(rule intra_path_Append)
      thus ?thesis by blast
    next
      fix a Q r p fs a'
      assume "valid_edge a" and "kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs" and "a' \<in> get_return_edges a"
        and "parent_node n'' = targetnode a" and "parent_node n' = sourcenode a'"
      then obtain a'' where "valid_edge a''" and "sourcenode a'' = targetnode a"
        and "targetnode a'' = sourcenode a'" and "kind a'' = (\<lambda>cf. False)\<^sub>\<surd>"
        by(auto dest:intra_proc_additional_edge)
      hence "targetnode a -[a'']\<rightarrow>\<^sub>\<iota>* sourcenode a'"
        by(fastforce dest:path_edge simp:intra_path_def intra_kind_def)
      with \<open>parent_node n'' = targetnode a\<close> \<open>parent_node n' = sourcenode a'\<close> 
      have "\<exists>as'. parent_node n'' -as'\<rightarrow>\<^sub>\<iota>* parent_node n' \<and> as' \<noteq> []" by fastforce
      then obtain as' where "parent_node n'' -as'\<rightarrow>\<^sub>\<iota>* parent_node n'" and "as' \<noteq> []"
        by blast
      with \<open>parent_node n -as\<rightarrow>\<^sub>\<iota>* parent_node n''\<close>
      have "parent_node n -as@as'\<rightarrow>\<^sub>\<iota>* parent_node n'" by -(rule intra_path_Append)
      thus ?thesis by blast
    next
      fix m assume "n'' = CFG_node m" and "m = parent_node n'"
      with \<open>parent_node n -as\<rightarrow>\<^sub>\<iota>* parent_node n''\<close> show ?thesis by fastforce
    qed
  next
    case (isSp_Append_ddep n ns n'' V n')
    from \<open>\<exists>as. parent_node n -as\<rightarrow>\<^sub>\<iota>* parent_node n''\<close>
    obtain as where "parent_node n -as\<rightarrow>\<^sub>\<iota>* parent_node n''" by blast 
    from \<open>n'' s-V\<rightarrow>\<^sub>d\<^sub>d n'\<close> have "n'' influences V in n'"
      by(fastforce elim:sum_SDG_edge.cases)
    then obtain as' where "parent_node n'' -as'\<rightarrow>\<^sub>\<iota>* parent_node n'"
      by(auto simp:data_dependence_def)
    with \<open>parent_node n -as\<rightarrow>\<^sub>\<iota>* parent_node n''\<close> 
    have "parent_node n -as@as'\<rightarrow>\<^sub>\<iota>* parent_node n'" by -(rule intra_path_Append)
    thus ?case by blast
  next
    case (isSp_Append_sum n ns n'' p n')
    from \<open>\<exists>as. parent_node n -as\<rightarrow>\<^sub>\<iota>* parent_node n''\<close>
    obtain as where "parent_node n -as\<rightarrow>\<^sub>\<iota>* parent_node n''" by blast
    from \<open>n'' s-p\<rightarrow>\<^bsub>sum\<^esub> n'\<close> have "\<exists>as'. parent_node n'' -as'\<rightarrow>\<^sub>\<iota>* parent_node n'"
    proof(rule sum_edge_cases)
      fix a Q fs a'
      assume "valid_edge a" and "a' \<in> get_return_edges a"
        and "n'' = CFG_node (sourcenode a)" and "n' = CFG_node (targetnode a')"
      from \<open>valid_edge a\<close> \<open>a' \<in> get_return_edges a\<close>
      obtain a'' where "sourcenode a -[a'']\<rightarrow>\<^sub>\<iota>* targetnode a'"
        apply - apply(drule call_return_node_edge)
        apply(auto simp:intra_path_def) apply(drule path_edge)
        by(auto simp:intra_kind_def)
      with \<open>n'' = CFG_node (sourcenode a)\<close> \<open>n' = CFG_node (targetnode a')\<close>
      show ?thesis by simp blast
    next
      fix a Q p fs a' ns x x' ins outs
      assume "valid_edge a" and "a' \<in> get_return_edges a"
        and "n'' = Actual_in (sourcenode a, x)" 
        and "n' = Actual_out (targetnode a', x')"
      from \<open>valid_edge a\<close> \<open>a' \<in> get_return_edges a\<close>
      obtain a'' where "sourcenode a -[a'']\<rightarrow>\<^sub>\<iota>* targetnode a'"
        apply - apply(drule call_return_node_edge)
        apply(auto simp:intra_path_def) apply(drule path_edge)
        by(auto simp:intra_kind_def)
      with \<open>n'' = Actual_in (sourcenode a, x)\<close> \<open>n' = Actual_out (targetnode a', x')\<close>
      show ?thesis by simp blast
    qed
    then obtain as' where "parent_node n'' -as'\<rightarrow>\<^sub>\<iota>* parent_node n'" by blast
    with \<open>parent_node n -as\<rightarrow>\<^sub>\<iota>* parent_node n''\<close> 
    have "parent_node n -as@as'\<rightarrow>\<^sub>\<iota>* parent_node n'" by -(rule intra_path_Append)
    thus ?case by blast
  qed
qed


lemma matched_is_SDG_path:
  assumes "matched n ns n'" obtains ns' where "n is-ns'\<rightarrow>\<^sub>d* n'"
proof(atomize_elim)
  from \<open>matched n ns n'\<close> show "\<exists>ns'. n is-ns'\<rightarrow>\<^sub>d* n'"
  proof(induct rule:matched.induct)
    case matched_Nil thus ?case by(fastforce intro:isSp_Nil)
  next
    case matched_Append_intra_SDG_path thus ?case
    by(fastforce intro:is_SDG_path_Append intra_SDG_path_is_SDG_path)
  next
    case (matched_bracket_call n\<^sub>0 ns n\<^sub>1 p n\<^sub>2 ns' n\<^sub>3 n\<^sub>4 V a a')
    from \<open>\<exists>ns'. n\<^sub>0 is-ns'\<rightarrow>\<^sub>d* n\<^sub>1\<close> obtain nsx where "n\<^sub>0 is-nsx\<rightarrow>\<^sub>d* n\<^sub>1" by blast
    from \<open>n\<^sub>1 -p\<rightarrow>\<^bsub>call\<^esub> n\<^sub>2\<close> \<open>sourcenode a = parent_node n\<^sub>1\<close> \<open>targetnode a = parent_node n\<^sub>2\<close>
    have "n\<^sub>1 = CFG_node (sourcenode a)" and "n\<^sub>2 = CFG_node (targetnode a)"
      by(auto elim:SDG_edge.cases)
    from \<open>valid_edge a\<close> \<open>a' \<in> get_return_edges a\<close>
    obtain Q r p' fs where "kind a = Q:r\<hookrightarrow>\<^bsub>p'\<^esub>fs" 
      by(fastforce dest!:only_call_get_return_edges)
    with \<open>n\<^sub>1 -p\<rightarrow>\<^bsub>call\<^esub> n\<^sub>2\<close> \<open>valid_edge a\<close>
      \<open>n\<^sub>1 = CFG_node (sourcenode a)\<close> \<open>n\<^sub>2 = CFG_node (targetnode a)\<close>
    have [simp]:"p' = p" by -(erule SDG_edge.cases,(fastforce dest:edge_det)+)
    from \<open>valid_edge a\<close> \<open>a' \<in> get_return_edges a\<close> have "valid_edge a'"
      by(rule get_return_edges_valid)
    from \<open>n\<^sub>3 -p\<rightarrow>\<^bsub>ret\<^esub> n\<^sub>4 \<or> n\<^sub>3 -p:V\<rightarrow>\<^bsub>out\<^esub> n\<^sub>4\<close> show ?case
    proof
      assume "n\<^sub>3 -p\<rightarrow>\<^bsub>ret\<^esub> n\<^sub>4"
      then obtain ax Q' f' where "valid_edge ax" and "kind ax = Q'\<hookleftarrow>\<^bsub>p\<^esub>f'"
        and "n\<^sub>3 = CFG_node (sourcenode ax)" and "n\<^sub>4 = CFG_node (targetnode ax)"
        by(fastforce elim:SDG_edge.cases)
      with \<open>sourcenode a' = parent_node n\<^sub>3\<close> \<open>targetnode a' = parent_node n\<^sub>4\<close> 
        \<open>valid_edge a'\<close> have [simp]:"ax = a'" by(fastforce dest:edge_det)
      from \<open>valid_edge a\<close> \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p'\<^esub>fs\<close> \<open>valid_edge ax\<close> \<open>kind ax = Q'\<hookleftarrow>\<^bsub>p\<^esub>f'\<close>
        \<open>a' \<in> get_return_edges a\<close> \<open>matched n\<^sub>2 ns' n\<^sub>3\<close>
        \<open>n\<^sub>1 = CFG_node (sourcenode a)\<close> \<open>n\<^sub>2 = CFG_node (targetnode a)\<close>
        \<open>n\<^sub>3 = CFG_node (sourcenode ax)\<close> \<open>n\<^sub>4 = CFG_node (targetnode ax)\<close>
      have "n\<^sub>1 s-p\<rightarrow>\<^bsub>sum\<^esub> n\<^sub>4" 
        by(fastforce intro!:sum_SDG_call_summary_edge[of a _ _ _ _ ax])
      with \<open>n\<^sub>0 is-nsx\<rightarrow>\<^sub>d* n\<^sub>1\<close> have "n\<^sub>0 is-nsx@[n\<^sub>1]\<rightarrow>\<^sub>d* n\<^sub>4" by(rule isSp_Append_sum)
      thus ?case by blast
    next
      assume "n\<^sub>3 -p:V\<rightarrow>\<^bsub>out\<^esub> n\<^sub>4"
      then obtain ax Q' f' x where "valid_edge ax" and "kind ax = Q'\<hookleftarrow>\<^bsub>p\<^esub>f'"
        and "n\<^sub>3 = Formal_out (sourcenode ax,x)" 
        and "n\<^sub>4 = Actual_out (targetnode ax,x)"
        by(fastforce elim:SDG_edge.cases)
      with \<open>sourcenode a' = parent_node n\<^sub>3\<close> \<open>targetnode a' = parent_node n\<^sub>4\<close> 
        \<open>valid_edge a'\<close> have [simp]:"ax = a'" by(fastforce dest:edge_det)
      from \<open>valid_edge ax\<close> \<open>kind ax = Q'\<hookleftarrow>\<^bsub>p\<^esub>f'\<close> \<open>n\<^sub>3 = Formal_out (sourcenode ax,x)\<close>
        \<open>n\<^sub>4 = Actual_out (targetnode ax,x)\<close>
      have "CFG_node (sourcenode a') -p\<rightarrow>\<^bsub>ret\<^esub> CFG_node (targetnode a')"
        by(fastforce intro:SDG_return_edge)
      from \<open>valid_edge a\<close> \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p'\<^esub>fs\<close> \<open>valid_edge a'\<close> 
        \<open>a' \<in> get_return_edges a\<close> \<open>n\<^sub>4 = Actual_out (targetnode ax,x)\<close>
      have "CFG_node (targetnode a) \<longrightarrow>\<^bsub>cd\<^esub> CFG_node (sourcenode a')"
        by(fastforce intro!:SDG_proc_entry_exit_cdep)
      with \<open>n\<^sub>2 = CFG_node (targetnode a)\<close>
      have "matched n\<^sub>2 ([]@([]@[n\<^sub>2])) (CFG_node (sourcenode a'))"
        by(fastforce intro:matched.intros intra_SDG_path.intros 
                          SDG_edge_valid_SDG_node) 
      with \<open>valid_edge a\<close> \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p'\<^esub>fs\<close> \<open>valid_edge a'\<close> \<open>kind ax = Q'\<hookleftarrow>\<^bsub>p\<^esub>f'\<close>
        \<open>a' \<in> get_return_edges a\<close> \<open>n\<^sub>1 = CFG_node (sourcenode a)\<close> 
        \<open>n\<^sub>2 = CFG_node (targetnode a)\<close> \<open>n\<^sub>4 = Actual_out (targetnode ax,x)\<close>
      have "n\<^sub>1 s-p\<rightarrow>\<^bsub>sum\<^esub> CFG_node (targetnode a')"
        by(fastforce intro!:sum_SDG_call_summary_edge[of a _ _ _ _ a'])
      with \<open>n\<^sub>0 is-nsx\<rightarrow>\<^sub>d* n\<^sub>1\<close> have "n\<^sub>0 is-nsx@[n\<^sub>1]\<rightarrow>\<^sub>d* CFG_node (targetnode a')"
        by(rule isSp_Append_sum)
      from \<open>n\<^sub>4 = Actual_out (targetnode ax,x)\<close> \<open>n\<^sub>3 -p:V\<rightarrow>\<^bsub>out\<^esub> n\<^sub>4\<close>
      have "CFG_node (targetnode a') s\<longrightarrow>\<^bsub>cd\<^esub> n\<^sub>4"
        by(fastforce intro:sum_SDG_parent_cdep_edge SDG_edge_valid_SDG_node)
      with \<open>n\<^sub>0 is-nsx@[n\<^sub>1]\<rightarrow>\<^sub>d* CFG_node (targetnode a')\<close>
      have "n\<^sub>0 is-(nsx@[n\<^sub>1])@[CFG_node (targetnode a')]\<rightarrow>\<^sub>d* n\<^sub>4"
        by(rule isSp_Append_cdep)
      thus ?case by blast
    qed
  next
    case (matched_bracket_param n\<^sub>0 ns n\<^sub>1 p V n\<^sub>2 ns' n\<^sub>3 V' n\<^sub>4 a a')
    from \<open>\<exists>ns'. n\<^sub>0 is-ns'\<rightarrow>\<^sub>d* n\<^sub>1\<close> obtain nsx where "n\<^sub>0 is-nsx\<rightarrow>\<^sub>d* n\<^sub>1" by blast
    from \<open>n\<^sub>1 -p:V\<rightarrow>\<^bsub>in\<^esub> n\<^sub>2\<close> \<open>sourcenode a = parent_node n\<^sub>1\<close>
      \<open>targetnode a = parent_node n\<^sub>2\<close> obtain x ins outs
      where "n\<^sub>1 = Actual_in (sourcenode a,x)" and "n\<^sub>2 = Formal_in (targetnode a,x)"
      and "(p,ins,outs) \<in> set procs" and "V = ins!x" and "x < length ins"
      by(fastforce elim:SDG_edge.cases)
    from \<open>valid_edge a\<close> \<open>a' \<in> get_return_edges a\<close>
    obtain Q r p' fs where "kind a = Q:r\<hookrightarrow>\<^bsub>p'\<^esub>fs"
      by(fastforce dest!:only_call_get_return_edges)
    with \<open>n\<^sub>1 -p:V\<rightarrow>\<^bsub>in\<^esub> n\<^sub>2\<close> \<open>valid_edge a\<close>
      \<open>n\<^sub>1 = Actual_in (sourcenode a,x)\<close> \<open>n\<^sub>2 = Formal_in (targetnode a,x)\<close>
    have [simp]:"p' = p" by -(erule SDG_edge.cases,(fastforce dest:edge_det)+)
    from \<open>valid_edge a\<close> \<open>a' \<in> get_return_edges a\<close> have "valid_edge a'"
      by(rule get_return_edges_valid)
    from \<open>n\<^sub>3 -p:V'\<rightarrow>\<^bsub>out\<^esub> n\<^sub>4\<close> obtain ax Q' f' x' ins' outs' where "valid_edge ax" 
      and "kind ax = Q'\<hookleftarrow>\<^bsub>p\<^esub>f'" and "n\<^sub>3 = Formal_out (sourcenode ax,x')" 
      and "n\<^sub>4 = Actual_out (targetnode ax,x')" and "(p,ins',outs') \<in> set procs"
      and "V' = outs'!x'" and "x' < length outs'"
      by(fastforce elim:SDG_edge.cases)
    with \<open>sourcenode a' = parent_node n\<^sub>3\<close> \<open>targetnode a' = parent_node n\<^sub>4\<close>
      \<open>valid_edge a'\<close> have [simp]:"ax = a'" by(fastforce dest:edge_det)
    from unique_callers \<open>(p,ins,outs) \<in> set procs\<close> \<open>(p,ins',outs') \<in> set procs\<close>
    have [simp]:"ins = ins'" "outs = outs'"
      by(auto dest:distinct_fst_isin_same_fst)
    from \<open>valid_edge a\<close> \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p'\<^esub>fs\<close> \<open>valid_edge a'\<close> \<open>kind ax = Q'\<hookleftarrow>\<^bsub>p\<^esub>f'\<close>
      \<open>a' \<in> get_return_edges a\<close> \<open>matched n\<^sub>2 ns' n\<^sub>3\<close> \<open>n\<^sub>1 = Actual_in (sourcenode a,x)\<close> 
      \<open>n\<^sub>2 = Formal_in (targetnode a,x)\<close> \<open>n\<^sub>3 = Formal_out (sourcenode ax,x')\<close>
      \<open>n\<^sub>4 = Actual_out (targetnode ax,x')\<close> \<open>(p,ins,outs) \<in> set procs\<close>
      \<open>x < length ins\<close> \<open>x' < length outs'\<close> \<open>V = ins!x\<close> \<open>V' = outs'!x'\<close>
    have "n\<^sub>1 s-p\<rightarrow>\<^bsub>sum\<^esub> n\<^sub>4" 
      by(fastforce intro!:sum_SDG_param_summary_edge[of a _ _ _ _ a'])
    with \<open>n\<^sub>0 is-nsx\<rightarrow>\<^sub>d* n\<^sub>1\<close> have "n\<^sub>0 is-nsx@[n\<^sub>1]\<rightarrow>\<^sub>d* n\<^sub>4" by(rule isSp_Append_sum)
    thus ?case by blast
  qed
qed


lemma is_SDG_path_matched:
  assumes "n is-ns\<rightarrow>\<^sub>d* n'" obtains ns' where "matched n ns' n'" and "set ns \<subseteq> set ns'"
proof(atomize_elim)
  from \<open>n is-ns\<rightarrow>\<^sub>d* n'\<close> show "\<exists>ns'. matched n ns' n' \<and> set ns \<subseteq> set ns'"
  proof(induct rule:intra_sum_SDG_path.induct)
    case (isSp_Nil n)
    from \<open>valid_SDG_node n\<close> have "matched n [] n" by(rule matched_Nil)
    thus ?case by fastforce
  next
    case (isSp_Append_cdep n ns n'' n')
    from \<open>\<exists>ns'. matched n ns' n'' \<and> set ns \<subseteq> set ns'\<close>
    obtain ns' where "matched n ns' n''" and "set ns \<subseteq> set ns'" by blast
    from \<open>n'' s\<longrightarrow>\<^bsub>cd\<^esub> n'\<close> have "n'' i-[]@[n'']\<rightarrow>\<^sub>d* n'"
      by(fastforce intro:intra_SDG_path.intros sum_SDG_edge_valid_SDG_node 
                        sum_SDG_edge_SDG_edge)
    with \<open>matched n ns' n''\<close> have "matched n (ns'@[n'']) n'"
      by(fastforce intro!:matched_Append_intra_SDG_path)
    with \<open>set ns \<subseteq> set ns'\<close> show ?case by fastforce
  next
    case (isSp_Append_ddep n ns n'' V n')
    from \<open>\<exists>ns'. matched n ns' n'' \<and> set ns \<subseteq> set ns'\<close>
    obtain ns' where "matched n ns' n''" and "set ns \<subseteq> set ns'" by blast
    from \<open>n'' s-V\<rightarrow>\<^sub>d\<^sub>d n'\<close> \<open>n'' \<noteq> n'\<close> have "n'' i-[]@[n'']\<rightarrow>\<^sub>d* n'"
      by(fastforce intro:intra_SDG_path.intros sum_SDG_edge_valid_SDG_node 
                        sum_SDG_edge_SDG_edge)
    with \<open>matched n ns' n''\<close> have "matched n (ns'@[n'']) n'"
      by(fastforce intro!:matched_Append_intra_SDG_path)
    with \<open>set ns \<subseteq> set ns'\<close> show ?case by fastforce
  next
    case (isSp_Append_sum n ns n'' p n')
    from \<open>\<exists>ns'. matched n ns' n'' \<and> set ns \<subseteq> set ns'\<close>
    obtain ns' where "matched n ns' n''" and "set ns \<subseteq> set ns'" by blast
    from \<open>n'' s-p\<rightarrow>\<^bsub>sum\<^esub> n'\<close> obtain ns'' where "matched n'' ns'' n'" and "n'' \<in> set ns''"
      by -(erule sum_SDG_summary_edge_matched)
    with \<open>matched n ns' n''\<close> have "matched n (ns'@ns'') n'" by -(rule matched_Append)
    with \<open>set ns \<subseteq> set ns'\<close> \<open>n'' \<in> set ns''\<close> show ?case by fastforce
  qed
qed


lemma is_SDG_path_intra_CFG_path:
  assumes "n is-ns\<rightarrow>\<^sub>d* n'"
  obtains as where "parent_node n -as\<rightarrow>\<^sub>\<iota>* parent_node n'" 
proof(atomize_elim)
  from \<open>n is-ns\<rightarrow>\<^sub>d* n'\<close>
  show "\<exists>as. parent_node n -as\<rightarrow>\<^sub>\<iota>* parent_node n'"
  proof(induct rule:intra_sum_SDG_path.induct)
    case (isSp_Nil n)
    from \<open>valid_SDG_node n\<close> have "parent_node n -[]\<rightarrow>* parent_node n"
      by(fastforce intro:empty_path valid_SDG_CFG_node)
    thus ?case by(auto simp:intra_path_def)
  next
    case (isSp_Append_cdep n ns n'' n')
    from \<open>\<exists>as. parent_node n -as\<rightarrow>\<^sub>\<iota>* parent_node n''\<close>
    obtain as where "parent_node n -as\<rightarrow>\<^sub>\<iota>* parent_node n''" by blast
    from \<open>n'' s\<longrightarrow>\<^bsub>cd\<^esub> n'\<close> have "n'' \<longrightarrow>\<^bsub>cd\<^esub> n'" by(rule sum_SDG_edge_SDG_edge)
    thus ?case
    proof(rule cdep_edge_cases)
      assume "parent_node n'' controls parent_node n'"
      then obtain as' where "parent_node n'' -as'\<rightarrow>\<^sub>\<iota>* parent_node n'" and "as' \<noteq> []"
        by(erule control_dependence_path)
      with \<open>parent_node n -as\<rightarrow>\<^sub>\<iota>* parent_node n''\<close> 
      have "parent_node n -as@as'\<rightarrow>\<^sub>\<iota>* parent_node n'" by -(rule intra_path_Append)
      thus ?thesis by blast
    next
      fix a Q r p fs a'
      assume "valid_edge a" and "kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs" "a' \<in> get_return_edges a"
        and "parent_node n'' = targetnode a" and "parent_node n' = sourcenode a'"
      then obtain a'' where "valid_edge a''" and "sourcenode a'' = targetnode a"
        and "targetnode a'' = sourcenode a'" and "kind a'' = (\<lambda>cf. False)\<^sub>\<surd>"
        by(auto dest:intra_proc_additional_edge)
      hence "targetnode a -[a'']\<rightarrow>\<^sub>\<iota>* sourcenode a'"
        by(fastforce dest:path_edge simp:intra_path_def intra_kind_def)
      with \<open>parent_node n'' = targetnode a\<close> \<open>parent_node n' = sourcenode a'\<close> 
      have "\<exists>as'. parent_node n'' -as'\<rightarrow>\<^sub>\<iota>* parent_node n' \<and> as' \<noteq> []" by fastforce
      then obtain as' where "parent_node n'' -as'\<rightarrow>\<^sub>\<iota>* parent_node n'" and "as' \<noteq> []"
        by blast
      with \<open>parent_node n -as\<rightarrow>\<^sub>\<iota>* parent_node n''\<close> 
      have "parent_node n -as@as'\<rightarrow>\<^sub>\<iota>* parent_node n'" by -(rule intra_path_Append)
      thus ?thesis by blast
    next
      fix m assume "n'' = CFG_node m" and "m = parent_node n'"
      with \<open>parent_node n -as\<rightarrow>\<^sub>\<iota>* parent_node n''\<close> show ?thesis by fastforce
    qed
  next
    case (isSp_Append_ddep n ns n'' V n')
    from \<open>\<exists>as. parent_node n -as\<rightarrow>\<^sub>\<iota>* parent_node n''\<close>
    obtain as where "parent_node n -as\<rightarrow>\<^sub>\<iota>* parent_node n''"  by blast
    from \<open>n'' s-V\<rightarrow>\<^sub>d\<^sub>d n'\<close> have "n'' influences V in n'"
      by(fastforce elim:sum_SDG_edge.cases)
    then obtain as' where "parent_node n'' -as'\<rightarrow>\<^sub>\<iota>* parent_node n'"
      by(auto simp:data_dependence_def)
    with \<open>parent_node n -as\<rightarrow>\<^sub>\<iota>* parent_node n''\<close> 
    have "parent_node n -as@as'\<rightarrow>\<^sub>\<iota>* parent_node n'" by -(rule intra_path_Append)
    thus ?case by blast
  next
    case (isSp_Append_sum n ns n'' p n')
    from \<open>\<exists>as. parent_node n -as\<rightarrow>\<^sub>\<iota>* parent_node n''\<close>
    obtain as where "parent_node n -as\<rightarrow>\<^sub>\<iota>* parent_node n''"  by blast
    from \<open>n'' s-p\<rightarrow>\<^bsub>sum\<^esub> n'\<close> obtain ns' where "matched n'' ns' n'"
      by -(erule sum_SDG_summary_edge_matched)
    then obtain as' where "parent_node n'' -as'\<rightarrow>\<^sub>\<iota>* parent_node n'"
      by(erule matched_intra_CFG_path)
    with \<open>parent_node n -as\<rightarrow>\<^sub>\<iota>* parent_node n''\<close> 
    have "parent_node n -as@as'\<rightarrow>\<^sub>\<iota>* parent_node n'"
      by(fastforce intro:path_Append simp:intra_path_def)
    thus ?case by blast
  qed
qed


text \<open>SDG paths without return edges\<close>

inductive intra_call_sum_SDG_path ::
  "'node SDG_node \<Rightarrow> 'node SDG_node list \<Rightarrow> 'node SDG_node \<Rightarrow> bool"
("_ ics-_\<rightarrow>\<^sub>d* _" [51,0,0] 80)
where icsSp_Nil:
  "valid_SDG_node n \<Longrightarrow> n ics-[]\<rightarrow>\<^sub>d* n"

  | icsSp_Append_cdep:
  "\<lbrakk>n ics-ns\<rightarrow>\<^sub>d* n''; n'' s\<longrightarrow>\<^bsub>cd\<^esub> n'\<rbrakk> \<Longrightarrow> n ics-ns@[n'']\<rightarrow>\<^sub>d* n'"

  | icsSp_Append_ddep:
  "\<lbrakk>n ics-ns\<rightarrow>\<^sub>d* n''; n'' s-V\<rightarrow>\<^sub>d\<^sub>d n'; n'' \<noteq> n'\<rbrakk> \<Longrightarrow> n ics-ns@[n'']\<rightarrow>\<^sub>d* n'"

  | icsSp_Append_sum:
  "\<lbrakk>n ics-ns\<rightarrow>\<^sub>d* n''; n'' s-p\<rightarrow>\<^bsub>sum\<^esub> n'\<rbrakk> \<Longrightarrow> n ics-ns@[n'']\<rightarrow>\<^sub>d* n'"

  | icsSp_Append_call:
  "\<lbrakk>n ics-ns\<rightarrow>\<^sub>d* n''; n'' s-p\<rightarrow>\<^bsub>call\<^esub> n'\<rbrakk> \<Longrightarrow> n ics-ns@[n'']\<rightarrow>\<^sub>d* n'"

  | icsSp_Append_param_in:
  "\<lbrakk>n ics-ns\<rightarrow>\<^sub>d* n''; n'' s-p:V\<rightarrow>\<^bsub>in\<^esub> n'\<rbrakk> \<Longrightarrow> n ics-ns@[n'']\<rightarrow>\<^sub>d* n'"


lemma ics_SDG_path_valid_SDG_node:
  assumes "n ics-ns\<rightarrow>\<^sub>d* n'" shows "valid_SDG_node n" and "valid_SDG_node n'"
using \<open>n ics-ns\<rightarrow>\<^sub>d* n'\<close>
by(induct rule:intra_call_sum_SDG_path.induct,
   auto intro:sum_SDG_edge_valid_SDG_node valid_SDG_CFG_node)


lemma ics_SDG_path_Append:
  "\<lbrakk>n'' ics-ns'\<rightarrow>\<^sub>d* n'; n ics-ns\<rightarrow>\<^sub>d* n''\<rbrakk> \<Longrightarrow> n ics-ns@ns'\<rightarrow>\<^sub>d* n'"
by(induct rule:intra_call_sum_SDG_path.induct,
   auto intro:intra_call_sum_SDG_path.intros simp:append_assoc[THEN sym] 
                                        simp del:append_assoc)


lemma is_SDG_path_ics_SDG_path:
  "n is-ns\<rightarrow>\<^sub>d* n' \<Longrightarrow> n ics-ns\<rightarrow>\<^sub>d* n'"
by(induct rule:intra_sum_SDG_path.induct,auto intro:intra_call_sum_SDG_path.intros)


lemma cc_SDG_path_ics_SDG_path:
  "n cc-ns\<rightarrow>\<^sub>d* n' \<Longrightarrow> n ics-ns\<rightarrow>\<^sub>d* n'"
by(induct rule:call_cdep_SDG_path.induct,
  auto intro:intra_call_sum_SDG_path.intros SDG_edge_sum_SDG_edge)


lemma ics_SDG_path_split:
  assumes "n ics-ns\<rightarrow>\<^sub>d* n'" and "n'' \<in> set ns" 
  obtains ns' ns'' where "ns = ns'@ns''" and "n ics-ns'\<rightarrow>\<^sub>d* n''" 
  and "n'' ics-ns''\<rightarrow>\<^sub>d* n'"
proof(atomize_elim)
  from \<open>n ics-ns\<rightarrow>\<^sub>d* n'\<close> \<open>n'' \<in> set ns\<close>
  show "\<exists>ns' ns''. ns = ns'@ns'' \<and> n ics-ns'\<rightarrow>\<^sub>d* n'' \<and> n'' ics-ns''\<rightarrow>\<^sub>d* n'"
  proof(induct rule:intra_call_sum_SDG_path.induct)
    case icsSp_Nil thus ?case by simp
  next
    case (icsSp_Append_cdep n ns nx n')
    note IH = \<open>n'' \<in> set ns \<Longrightarrow>
      \<exists>ns' ns''. ns = ns' @ ns'' \<and> n ics-ns'\<rightarrow>\<^sub>d* n'' \<and> n'' ics-ns''\<rightarrow>\<^sub>d* nx\<close>
    from \<open>n'' \<in> set (ns@[nx])\<close> have "n'' \<in> set ns \<or> n'' = nx" by fastforce
    thus ?case
    proof
      assume "n'' \<in> set ns"
      from IH[OF this] obtain ns' ns'' where "ns = ns' @ ns''"
        and "n ics-ns'\<rightarrow>\<^sub>d* n''" and "n'' ics-ns''\<rightarrow>\<^sub>d* nx" by blast
      from \<open>n'' ics-ns''\<rightarrow>\<^sub>d* nx\<close> \<open>nx s\<longrightarrow>\<^bsub>cd\<^esub> n'\<close>
      have "n'' ics-ns''@[nx]\<rightarrow>\<^sub>d* n'"
        by(rule intra_call_sum_SDG_path.icsSp_Append_cdep)
      with \<open>ns = ns'@ns''\<close> \<open>n ics-ns'\<rightarrow>\<^sub>d* n''\<close> show ?thesis by fastforce
    next
      assume "n'' = nx"
      from \<open>nx s\<longrightarrow>\<^bsub>cd\<^esub> n'\<close> have "nx ics-[]\<rightarrow>\<^sub>d* nx"
        by(fastforce intro:icsSp_Nil SDG_edge_valid_SDG_node sum_SDG_edge_SDG_edge)
      with \<open>nx s\<longrightarrow>\<^bsub>cd\<^esub> n'\<close> have "nx ics-[]@[nx]\<rightarrow>\<^sub>d* n'"
        by -(rule intra_call_sum_SDG_path.icsSp_Append_cdep)
      with \<open>n ics-ns\<rightarrow>\<^sub>d* nx\<close> \<open>n'' = nx\<close> show ?thesis by fastforce
    qed
  next
    case (icsSp_Append_ddep n ns nx V n')
    note IH = \<open>n'' \<in> set ns \<Longrightarrow>
      \<exists>ns' ns''. ns = ns' @ ns'' \<and> n ics-ns'\<rightarrow>\<^sub>d* n'' \<and> n'' ics-ns''\<rightarrow>\<^sub>d* nx\<close>
    from \<open>n'' \<in> set (ns@[nx])\<close> have "n'' \<in> set ns \<or> n'' = nx" by fastforce
    thus ?case
    proof
      assume "n'' \<in> set ns"
      from IH[OF this] obtain ns' ns'' where "ns = ns' @ ns''"
        and "n ics-ns'\<rightarrow>\<^sub>d* n''" and "n'' ics-ns''\<rightarrow>\<^sub>d* nx" by blast
      from \<open>n'' ics-ns''\<rightarrow>\<^sub>d* nx\<close> \<open>nx s-V\<rightarrow>\<^sub>d\<^sub>d n'\<close> \<open>nx \<noteq> n'\<close>
      have "n'' ics-ns''@[nx]\<rightarrow>\<^sub>d* n'"
        by(rule intra_call_sum_SDG_path.icsSp_Append_ddep)
      with \<open>ns = ns'@ns''\<close> \<open>n ics-ns'\<rightarrow>\<^sub>d* n''\<close> show ?thesis by fastforce
    next
      assume "n'' = nx"
      from \<open>nx s-V\<rightarrow>\<^sub>d\<^sub>d n'\<close> have "nx ics-[]\<rightarrow>\<^sub>d* nx"
        by(fastforce intro:icsSp_Nil SDG_edge_valid_SDG_node sum_SDG_edge_SDG_edge)
      with \<open>nx s-V\<rightarrow>\<^sub>d\<^sub>d n'\<close> \<open>nx \<noteq> n'\<close> have "nx ics-[]@[nx]\<rightarrow>\<^sub>d* n'"
        by -(rule intra_call_sum_SDG_path.icsSp_Append_ddep)
      with \<open>n ics-ns\<rightarrow>\<^sub>d* nx\<close> \<open>n'' = nx\<close> show ?thesis by fastforce
    qed
  next
    case (icsSp_Append_sum n ns nx p n')
    note IH = \<open>n'' \<in> set ns \<Longrightarrow>
      \<exists>ns' ns''. ns = ns' @ ns'' \<and> n ics-ns'\<rightarrow>\<^sub>d* n'' \<and> n'' ics-ns''\<rightarrow>\<^sub>d* nx\<close>
    from \<open>n'' \<in> set (ns@[nx])\<close> have "n'' \<in> set ns \<or> n'' = nx" by fastforce
    thus ?case
    proof
      assume "n'' \<in> set ns"
      from IH[OF this] obtain ns' ns'' where "ns = ns' @ ns''"
        and "n ics-ns'\<rightarrow>\<^sub>d* n''" and "n'' ics-ns''\<rightarrow>\<^sub>d* nx" by blast
      from \<open>n'' ics-ns''\<rightarrow>\<^sub>d* nx\<close> \<open>nx s-p\<rightarrow>\<^bsub>sum\<^esub> n'\<close>
      have "n'' ics-ns''@[nx]\<rightarrow>\<^sub>d* n'"
        by(rule intra_call_sum_SDG_path.icsSp_Append_sum)
      with \<open>ns = ns'@ns''\<close> \<open>n ics-ns'\<rightarrow>\<^sub>d* n''\<close> show ?thesis by fastforce
    next
      assume "n'' = nx"
      from \<open>nx s-p\<rightarrow>\<^bsub>sum\<^esub> n'\<close> have "valid_SDG_node nx"
        by(fastforce elim:sum_SDG_edge.cases)
      hence "nx ics-[]\<rightarrow>\<^sub>d* nx" by(fastforce intro:icsSp_Nil)
      with \<open>nx s-p\<rightarrow>\<^bsub>sum\<^esub> n'\<close> have "nx ics-[]@[nx]\<rightarrow>\<^sub>d* n'"
        by -(rule intra_call_sum_SDG_path.icsSp_Append_sum)
      with \<open>n ics-ns\<rightarrow>\<^sub>d* nx\<close> \<open>n'' = nx\<close> show ?thesis by fastforce
    qed
  next
    case (icsSp_Append_call n ns nx p n')
    note IH = \<open>n'' \<in> set ns \<Longrightarrow>
      \<exists>ns' ns''. ns = ns' @ ns'' \<and> n ics-ns'\<rightarrow>\<^sub>d* n'' \<and> n'' ics-ns''\<rightarrow>\<^sub>d* nx\<close>
    from \<open>n'' \<in> set (ns@[nx])\<close> have "n'' \<in> set ns \<or> n'' = nx" by fastforce
    thus ?case
    proof
      assume "n'' \<in> set ns"
      from IH[OF this] obtain ns' ns'' where "ns = ns' @ ns''"
        and "n ics-ns'\<rightarrow>\<^sub>d* n''" and "n'' ics-ns''\<rightarrow>\<^sub>d* nx" by blast
      from \<open>n'' ics-ns''\<rightarrow>\<^sub>d* nx\<close> \<open>nx s-p\<rightarrow>\<^bsub>call\<^esub> n'\<close>
      have "n'' ics-ns''@[nx]\<rightarrow>\<^sub>d* n'"
        by(rule intra_call_sum_SDG_path.icsSp_Append_call)
      with \<open>ns = ns'@ns''\<close> \<open>n ics-ns'\<rightarrow>\<^sub>d* n''\<close> show ?thesis by fastforce
    next
      assume "n'' = nx"
      from \<open>nx s-p\<rightarrow>\<^bsub>call\<^esub> n'\<close> have "nx ics-[]\<rightarrow>\<^sub>d* nx"
        by(fastforce intro:icsSp_Nil SDG_edge_valid_SDG_node sum_SDG_edge_SDG_edge)
      with \<open>nx s-p\<rightarrow>\<^bsub>call\<^esub> n'\<close> have "nx ics-[]@[nx]\<rightarrow>\<^sub>d* n'"
        by -(rule intra_call_sum_SDG_path.icsSp_Append_call)
      with \<open>n ics-ns\<rightarrow>\<^sub>d* nx\<close> \<open>n'' = nx\<close> show ?thesis by fastforce
    qed
  next
    case (icsSp_Append_param_in n ns nx p V n')
    note IH = \<open>n'' \<in> set ns \<Longrightarrow>
      \<exists>ns' ns''. ns = ns' @ ns'' \<and> n ics-ns'\<rightarrow>\<^sub>d* n'' \<and> n'' ics-ns''\<rightarrow>\<^sub>d* nx\<close>
    from \<open>n'' \<in> set (ns@[nx])\<close> have "n'' \<in> set ns \<or> n'' = nx" by fastforce
    thus ?case
    proof
      assume "n'' \<in> set ns"
      from IH[OF this] obtain ns' ns'' where "ns = ns' @ ns''"
        and "n ics-ns'\<rightarrow>\<^sub>d* n''" and "n'' ics-ns''\<rightarrow>\<^sub>d* nx" by blast
      from \<open>n'' ics-ns''\<rightarrow>\<^sub>d* nx\<close> \<open>nx s-p:V\<rightarrow>\<^bsub>in\<^esub> n'\<close>
      have "n'' ics-ns''@[nx]\<rightarrow>\<^sub>d* n'"
        by(rule intra_call_sum_SDG_path.icsSp_Append_param_in)
      with \<open>ns = ns'@ns''\<close> \<open>n ics-ns'\<rightarrow>\<^sub>d* n''\<close> show ?thesis by fastforce
    next
      assume "n'' = nx"
      from \<open>nx s-p:V\<rightarrow>\<^bsub>in\<^esub> n'\<close> have "nx ics-[]\<rightarrow>\<^sub>d* nx"
        by(fastforce intro:icsSp_Nil SDG_edge_valid_SDG_node sum_SDG_edge_SDG_edge)
      with \<open>nx s-p:V\<rightarrow>\<^bsub>in\<^esub> n'\<close> have "nx ics-[]@[nx]\<rightarrow>\<^sub>d* n'"
        by -(rule intra_call_sum_SDG_path.icsSp_Append_param_in)
      with \<open>n ics-ns\<rightarrow>\<^sub>d* nx\<close> \<open>n'' = nx\<close> show ?thesis by fastforce
    qed
  qed
qed


lemma realizable_ics_SDG_path:
  assumes "realizable n ns n'" obtains ns' where "n ics-ns'\<rightarrow>\<^sub>d* n'"
proof(atomize_elim)
  from \<open>realizable n ns n'\<close> show "\<exists>ns'. n ics-ns'\<rightarrow>\<^sub>d* n'"
  proof(induct rule:realizable.induct)
    case (realizable_matched n ns n')
    from \<open>matched n ns n'\<close> obtain ns' where "n is-ns'\<rightarrow>\<^sub>d* n'"
      by(erule matched_is_SDG_path)
    thus ?case by(fastforce intro:is_SDG_path_ics_SDG_path)
  next
    case (realizable_call n\<^sub>0 ns n\<^sub>1 p n\<^sub>2 V ns' n\<^sub>3)
    from \<open>\<exists>ns'. n\<^sub>0 ics-ns'\<rightarrow>\<^sub>d* n\<^sub>1\<close> obtain nsx where "n\<^sub>0 ics-nsx\<rightarrow>\<^sub>d* n\<^sub>1" by blast
    with \<open>n\<^sub>1 -p\<rightarrow>\<^bsub>call\<^esub> n\<^sub>2 \<or> n\<^sub>1 -p:V\<rightarrow>\<^bsub>in\<^esub> n\<^sub>2\<close> have "n\<^sub>0 ics-nsx@[n\<^sub>1]\<rightarrow>\<^sub>d* n\<^sub>2"
      by(fastforce intro:SDG_edge_sum_SDG_edge icsSp_Append_call icsSp_Append_param_in)
    from \<open>matched n\<^sub>2 ns' n\<^sub>3\<close> obtain nsx' where "n\<^sub>2 is-nsx'\<rightarrow>\<^sub>d* n\<^sub>3"
      by(erule matched_is_SDG_path)
    hence "n\<^sub>2 ics-nsx'\<rightarrow>\<^sub>d* n\<^sub>3" by(rule is_SDG_path_ics_SDG_path)
    from \<open>n\<^sub>2 ics-nsx'\<rightarrow>\<^sub>d* n\<^sub>3\<close> \<open>n\<^sub>0 ics-nsx@[n\<^sub>1]\<rightarrow>\<^sub>d* n\<^sub>2\<close>
    have "n\<^sub>0 ics-(nsx@[n\<^sub>1])@nsx'\<rightarrow>\<^sub>d* n\<^sub>3" by(rule ics_SDG_path_Append)
    thus ?case by blast
  qed
qed


lemma ics_SDG_path_realizable:
  assumes "n ics-ns\<rightarrow>\<^sub>d* n'" 
  obtains ns' where "realizable n ns' n'" and "set ns \<subseteq> set ns'"
proof(atomize_elim)
  from \<open>n ics-ns\<rightarrow>\<^sub>d* n'\<close> show "\<exists>ns'. realizable n ns' n' \<and> set ns \<subseteq> set ns'"
  proof(induct rule:intra_call_sum_SDG_path.induct)
    case (icsSp_Nil n)
    hence "matched n [] n" by(rule matched_Nil)
    thus ?case by(fastforce intro:realizable_matched)
  next
    case (icsSp_Append_cdep n ns n'' n')
    from \<open>\<exists>ns'. realizable n ns' n'' \<and> set ns \<subseteq> set ns'\<close>
    obtain ns' where "realizable n ns' n''" and "set ns \<subseteq> set ns'" by blast
    from \<open>n'' s\<longrightarrow>\<^bsub>cd\<^esub> n'\<close> have "valid_SDG_node n''" by(rule sum_SDG_edge_valid_SDG_node)
    hence "n'' i-[]\<rightarrow>\<^sub>d* n''" by(rule iSp_Nil)
    with \<open>n'' s\<longrightarrow>\<^bsub>cd\<^esub> n'\<close> have "n'' i-[]@[n'']\<rightarrow>\<^sub>d* n'"
      by(fastforce elim:iSp_Append_cdep sum_SDG_edge_SDG_edge)
    hence "matched n'' [n''] n'" by(fastforce intro:intra_SDG_path_matched)
    with \<open>realizable n ns' n''\<close> have "realizable n (ns'@[n'']) n'"
      by(rule realizable_Append_matched)
    with \<open>set ns \<subseteq> set ns'\<close> show ?case by fastforce
  next
    case (icsSp_Append_ddep n ns n'' V n')
    from \<open>\<exists>ns'. realizable n ns' n'' \<and> set ns \<subseteq> set ns'\<close>
    obtain ns' where "realizable n ns' n''" and "set ns \<subseteq> set ns'" by blast
    from \<open>n'' s-V\<rightarrow>\<^sub>d\<^sub>d n'\<close> have "valid_SDG_node n''"
      by(rule sum_SDG_edge_valid_SDG_node)
    hence "n'' i-[]\<rightarrow>\<^sub>d* n''" by(rule iSp_Nil)
    with \<open>n'' s-V\<rightarrow>\<^sub>d\<^sub>d n'\<close> \<open>n'' \<noteq> n'\<close> have "n'' i-[]@[n'']\<rightarrow>\<^sub>d* n'"
      by(fastforce elim:iSp_Append_ddep sum_SDG_edge_SDG_edge)
    hence "matched n'' [n''] n'" by(fastforce intro:intra_SDG_path_matched)
    with \<open>realizable n ns' n''\<close> have "realizable n (ns'@[n'']) n'"
      by(fastforce intro:realizable_Append_matched)
    with \<open>set ns \<subseteq> set ns'\<close> show ?case by fastforce
  next
    case (icsSp_Append_sum n ns n'' p n')
    from \<open>\<exists>ns'. realizable n ns' n'' \<and> set ns \<subseteq> set ns'\<close>
    obtain ns' where "realizable n ns' n''" and "set ns \<subseteq> set ns'" by blast
    from \<open>n'' s-p\<rightarrow>\<^bsub>sum\<^esub> n'\<close> show ?case
    proof(rule sum_edge_cases)
      fix a Q r fs a'
      assume "valid_edge a" and "kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs" and "a' \<in> get_return_edges a"
        and "n'' = CFG_node (sourcenode a)" and "n' = CFG_node (targetnode a')"
      from \<open>valid_edge a\<close> \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close> \<open>a' \<in> get_return_edges a\<close>
      have match':"matched (CFG_node (targetnode a)) [CFG_node (targetnode a)]
        (CFG_node (sourcenode a'))"
        by(rule intra_proc_matched)
      from \<open>valid_edge a\<close> \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close> \<open>n'' = CFG_node (sourcenode a)\<close>
      have "n'' -p\<rightarrow>\<^bsub>call\<^esub> CFG_node (targetnode a)"
        by(fastforce intro:SDG_call_edge)
      hence "matched n'' [] n''"
        by(fastforce intro:matched_Nil SDG_edge_valid_SDG_node)
      from \<open>valid_edge a\<close> \<open>a' \<in> get_return_edges a\<close> have "valid_edge a'"
        by(rule get_return_edges_valid)
      from \<open>valid_edge a\<close> \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close> \<open>a' \<in> get_return_edges a\<close>
      obtain Q' f' where "kind a' = Q'\<hookleftarrow>\<^bsub>p\<^esub>f'" by(fastforce dest!:call_return_edges)
      from \<open>valid_edge a'\<close> \<open>kind a' = Q'\<hookleftarrow>\<^bsub>p\<^esub>f'\<close> \<open>n' = CFG_node (targetnode a')\<close>
      have "CFG_node (sourcenode a') -p\<rightarrow>\<^bsub>ret\<^esub> n'"
        by(fastforce intro:SDG_return_edge)
      from \<open>matched n'' [] n''\<close> \<open>n'' -p\<rightarrow>\<^bsub>call\<^esub> CFG_node (targetnode a)\<close>
        match' \<open>CFG_node (sourcenode a') -p\<rightarrow>\<^bsub>ret\<^esub> n'\<close> \<open>valid_edge a\<close> 
        \<open>a' \<in> get_return_edges a\<close> \<open>n' = CFG_node (targetnode a')\<close> 
        \<open>n'' = CFG_node (sourcenode a)\<close>
      have "matched n'' ([]@n''#[CFG_node (targetnode a)]@[CFG_node (sourcenode a')])
        n'"
        by(fastforce intro:matched_bracket_call)
      with \<open>realizable n ns' n''\<close>
      have "realizable n 
        (ns'@(n''#[CFG_node (targetnode a),CFG_node (sourcenode a')])) n'"
        by(fastforce intro:realizable_Append_matched)
      with \<open>set ns \<subseteq> set ns'\<close> show ?thesis by fastforce
    next
      fix a Q r p fs a' ns'' x x' ins outs
      assume "valid_edge a" and "kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs" and "a' \<in> get_return_edges a"
        and match':"matched (Formal_in (targetnode a,x)) ns'' 
                            (Formal_out (sourcenode a',x'))"
        and "n'' = Actual_in (sourcenode a,x)" 
        and "n' = Actual_out (targetnode a',x')" and "(p,ins,outs) \<in> set procs" 
        and "x < length ins" and "x' < length outs"
      from \<open>valid_edge a\<close> \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close> \<open>n'' = Actual_in (sourcenode a,x)\<close>
        \<open>(p,ins,outs) \<in> set procs\<close> \<open>x < length ins\<close>
      have "n'' -p:ins!x\<rightarrow>\<^bsub>in\<^esub> Formal_in (targetnode a,x)"
        by(fastforce intro!:SDG_param_in_edge)
      hence "matched n'' [] n''" 
        by(fastforce intro:matched_Nil SDG_edge_valid_SDG_node)
      from \<open>valid_edge a\<close> \<open>a' \<in> get_return_edges a\<close> have "valid_edge a'"
        by(rule get_return_edges_valid)
      from \<open>valid_edge a\<close> \<open>kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close> \<open>a' \<in> get_return_edges a\<close>
      obtain Q' f' where "kind a' = Q'\<hookleftarrow>\<^bsub>p\<^esub>f'" by(fastforce dest!:call_return_edges)
      from \<open>valid_edge a'\<close> \<open>kind a' = Q'\<hookleftarrow>\<^bsub>p\<^esub>f'\<close> \<open>n' = Actual_out (targetnode a',x')\<close>
        \<open>(p,ins,outs) \<in> set procs\<close> \<open>x' < length outs\<close>
      have "Formal_out (sourcenode a',x') -p:outs!x'\<rightarrow>\<^bsub>out\<^esub> n'"
        by(fastforce intro:SDG_param_out_edge)
      from \<open>matched n'' [] n''\<close> \<open>n'' -p:ins!x\<rightarrow>\<^bsub>in\<^esub> Formal_in (targetnode a,x)\<close>
        match' \<open>Formal_out (sourcenode a',x') -p:outs!x'\<rightarrow>\<^bsub>out\<^esub> n'\<close> \<open>valid_edge a\<close> 
        \<open>a' \<in> get_return_edges a\<close> \<open>n' = Actual_out (targetnode a',x')\<close>
        \<open>n'' = Actual_in (sourcenode a,x)\<close>
      have "matched n'' ([]@n''#ns''@[Formal_out (sourcenode a',x')]) n'"
        by(fastforce intro:matched_bracket_param)
      with \<open>realizable n ns' n''\<close>
      have "realizable n (ns'@(n''#ns''@[Formal_out (sourcenode a',x')])) n'"
        by(fastforce intro:realizable_Append_matched)
      with \<open>set ns \<subseteq> set ns'\<close> show ?thesis by fastforce
    qed
  next
    case (icsSp_Append_call n ns n'' p n')
    from \<open>\<exists>ns'. realizable n ns' n'' \<and> set ns \<subseteq> set ns'\<close>
    obtain ns' where "realizable n ns' n''" and "set ns \<subseteq> set ns'" by blast
    from \<open>n'' s-p\<rightarrow>\<^bsub>call\<^esub> n'\<close> have "valid_SDG_node n'"
      by(rule sum_SDG_edge_valid_SDG_node)
    hence "matched n' [] n'" by(rule matched_Nil)
    with \<open>realizable n ns' n''\<close> \<open>n'' s-p\<rightarrow>\<^bsub>call\<^esub> n'\<close>
    have "realizable n (ns'@n''#[]) n'"
      by(fastforce intro:realizable_call sum_SDG_edge_SDG_edge)
    with \<open>set ns \<subseteq> set ns'\<close> show ?case by fastforce
  next
    case (icsSp_Append_param_in n ns n'' p V n')
    from \<open>\<exists>ns'. realizable n ns' n'' \<and> set ns \<subseteq> set ns'\<close>
    obtain ns' where "realizable n ns' n''" and "set ns \<subseteq> set ns'" by blast
    from \<open>n'' s-p:V\<rightarrow>\<^bsub>in\<^esub> n'\<close> have "valid_SDG_node n'"
      by(rule sum_SDG_edge_valid_SDG_node)
    hence "matched n' [] n'" by(rule matched_Nil)
    with \<open>realizable n ns' n''\<close> \<open>n'' s-p:V\<rightarrow>\<^bsub>in\<^esub> n'\<close>
    have "realizable n (ns'@n''#[]) n'"
      by(fastforce intro:realizable_call sum_SDG_edge_SDG_edge)
    with \<open>set ns \<subseteq> set ns'\<close> show ?case by fastforce
  qed
qed



lemma realizable_Append_ics_SDG_path:
  assumes "realizable n ns n''" and "n'' ics-ns'\<rightarrow>\<^sub>d* n'"
  obtains ns'' where "realizable n (ns@ns'') n'"
proof(atomize_elim)
  from \<open>n'' ics-ns'\<rightarrow>\<^sub>d* n'\<close> \<open>realizable n ns n''\<close>
  show "\<exists>ns''. realizable n (ns@ns'') n'"
  proof(induct rule:intra_call_sum_SDG_path.induct)
    case (icsSp_Nil n'') thus ?case by(rule_tac x="[]" in exI) fastforce
  next
    case (icsSp_Append_cdep n'' ns' nx n')
    then obtain ns'' where "realizable n (ns@ns'') nx" by fastforce
    from \<open>nx s\<longrightarrow>\<^bsub>cd\<^esub> n'\<close> have "valid_SDG_node nx" by(rule sum_SDG_edge_valid_SDG_node)
    hence "matched nx [] nx" by(rule matched_Nil)
    from \<open>nx s\<longrightarrow>\<^bsub>cd\<^esub> n'\<close> \<open>valid_SDG_node nx\<close>
    have "nx i-[]@[nx]\<rightarrow>\<^sub>d* n'" 
      by(fastforce intro:iSp_Append_cdep iSp_Nil sum_SDG_edge_SDG_edge)
    with \<open>matched nx [] nx\<close> have "matched nx ([]@[nx]) n'"
      by(fastforce intro:matched_Append_intra_SDG_path)
    with \<open>realizable n (ns@ns'') nx\<close> have "realizable n ((ns@ns'')@[nx]) n'"
      by(fastforce intro:realizable_Append_matched)
    thus ?case by fastforce
  next
    case (icsSp_Append_ddep n'' ns' nx V n')
    then obtain ns'' where "realizable n (ns@ns'') nx" by fastforce
    from \<open>nx s-V\<rightarrow>\<^sub>d\<^sub>d n'\<close> have "valid_SDG_node nx" by(rule sum_SDG_edge_valid_SDG_node)
    hence "matched nx [] nx" by(rule matched_Nil)
    from \<open>nx s-V\<rightarrow>\<^sub>d\<^sub>d n'\<close> \<open>nx \<noteq> n'\<close> \<open>valid_SDG_node nx\<close>
    have "nx i-[]@[nx]\<rightarrow>\<^sub>d* n'" 
      by(fastforce intro:iSp_Append_ddep iSp_Nil sum_SDG_edge_SDG_edge)
    with \<open>matched nx [] nx\<close> have "matched nx ([]@[nx]) n'"
      by(fastforce intro:matched_Append_intra_SDG_path)
    with \<open>realizable n (ns@ns'') nx\<close> have "realizable n ((ns@ns'')@[nx]) n'"
      by(fastforce intro:realizable_Append_matched)
    thus ?case by fastforce
  next
    case (icsSp_Append_sum n'' ns' nx p n')
    then obtain ns'' where "realizable n (ns@ns'') nx" by fastforce
    from \<open>nx s-p\<rightarrow>\<^bsub>sum\<^esub> n'\<close> obtain nsx where "matched nx nsx n'"
      by -(erule sum_SDG_summary_edge_matched)
    with \<open>realizable n (ns@ns'') nx\<close> have "realizable n ((ns@ns'')@nsx) n'"
      by(rule realizable_Append_matched)
    thus ?case by fastforce
  next
    case (icsSp_Append_call n'' ns' nx p n')
    then obtain ns'' where "realizable n (ns@ns'') nx" by fastforce
    from \<open>nx s-p\<rightarrow>\<^bsub>call\<^esub> n'\<close> have "valid_SDG_node n'" by(rule sum_SDG_edge_valid_SDG_node)
    hence "matched n' [] n'" by(rule matched_Nil)
    with \<open>realizable n (ns@ns'') nx\<close> \<open>nx s-p\<rightarrow>\<^bsub>call\<^esub> n'\<close> 
    have "realizable n ((ns@ns'')@[nx]) n'"
      by(fastforce intro:realizable_call sum_SDG_edge_SDG_edge)
    thus ?case by fastforce
  next
    case (icsSp_Append_param_in n'' ns' nx p V n')
    then obtain ns'' where "realizable n (ns@ns'') nx" by fastforce
    from \<open>nx s-p:V\<rightarrow>\<^bsub>in\<^esub> n'\<close> have "valid_SDG_node n'"
      by(rule sum_SDG_edge_valid_SDG_node)
    hence "matched n' [] n'" by(rule matched_Nil)
    with \<open>realizable n (ns@ns'') nx\<close> \<open>nx s-p:V\<rightarrow>\<^bsub>in\<^esub> n'\<close> 
    have "realizable n ((ns@ns'')@[nx]) n'"
      by(fastforce intro:realizable_call sum_SDG_edge_SDG_edge)
    thus ?case by fastforce
  qed
qed
      

subsection \<open>SDG paths without call edges\<close>

inductive intra_return_sum_SDG_path ::
  "'node SDG_node \<Rightarrow> 'node SDG_node list \<Rightarrow> 'node SDG_node \<Rightarrow> bool"
("_ irs-_\<rightarrow>\<^sub>d* _" [51,0,0] 80)
where irsSp_Nil:
  "valid_SDG_node n \<Longrightarrow> n irs-[]\<rightarrow>\<^sub>d* n"

  | irsSp_Cons_cdep:
  "\<lbrakk>n'' irs-ns\<rightarrow>\<^sub>d* n'; n s\<longrightarrow>\<^bsub>cd\<^esub> n''\<rbrakk> \<Longrightarrow> n irs-n#ns\<rightarrow>\<^sub>d* n'"

  | irsSp_Cons_ddep:
  "\<lbrakk>n'' irs-ns\<rightarrow>\<^sub>d* n'; n s-V\<rightarrow>\<^sub>d\<^sub>d n''; n \<noteq> n''\<rbrakk> \<Longrightarrow> n irs-n#ns\<rightarrow>\<^sub>d* n'"

  | irsSp_Cons_sum:
  "\<lbrakk>n'' irs-ns\<rightarrow>\<^sub>d* n'; n s-p\<rightarrow>\<^bsub>sum\<^esub> n''\<rbrakk> \<Longrightarrow> n irs-n#ns\<rightarrow>\<^sub>d* n'"

  | irsSp_Cons_return:
  "\<lbrakk>n'' irs-ns\<rightarrow>\<^sub>d* n'; n s-p\<rightarrow>\<^bsub>ret\<^esub> n''\<rbrakk> \<Longrightarrow> n irs-n#ns\<rightarrow>\<^sub>d* n'"

  | irsSp_Cons_param_out:
  "\<lbrakk>n'' irs-ns\<rightarrow>\<^sub>d* n'; n s-p:V\<rightarrow>\<^bsub>out\<^esub> n''\<rbrakk> \<Longrightarrow> n irs-n#ns\<rightarrow>\<^sub>d* n'"



lemma irs_SDG_path_Append:
  "\<lbrakk>n irs-ns\<rightarrow>\<^sub>d* n''; n'' irs-ns'\<rightarrow>\<^sub>d* n'\<rbrakk> \<Longrightarrow> n irs-ns@ns'\<rightarrow>\<^sub>d* n'"
by(induct rule:intra_return_sum_SDG_path.induct,
   auto intro:intra_return_sum_SDG_path.intros)


lemma is_SDG_path_irs_SDG_path:
  "n is-ns\<rightarrow>\<^sub>d* n' \<Longrightarrow> n irs-ns\<rightarrow>\<^sub>d* n'"
proof(induct rule:intra_sum_SDG_path.induct)
  case (isSp_Nil n)
  from \<open>valid_SDG_node n\<close> show ?case by(rule irsSp_Nil)
next
  case (isSp_Append_cdep n ns n'' n')
  from \<open>n'' s\<longrightarrow>\<^bsub>cd\<^esub> n'\<close> have "n'' irs-[n'']\<rightarrow>\<^sub>d* n'"
    by(fastforce intro:irsSp_Cons_cdep irsSp_Nil sum_SDG_edge_valid_SDG_node)
  with \<open>n irs-ns\<rightarrow>\<^sub>d* n''\<close> show ?case by(rule irs_SDG_path_Append)
next
  case (isSp_Append_ddep n ns n'' V n')
  from \<open>n'' s-V\<rightarrow>\<^sub>d\<^sub>d n'\<close> \<open>n'' \<noteq> n'\<close> have "n'' irs-[n'']\<rightarrow>\<^sub>d* n'"
    by(fastforce intro:irsSp_Cons_ddep irsSp_Nil sum_SDG_edge_valid_SDG_node)
  with \<open>n irs-ns\<rightarrow>\<^sub>d* n''\<close> show ?case by(rule irs_SDG_path_Append)
next
  case (isSp_Append_sum n ns n'' p n')
  from \<open>n'' s-p\<rightarrow>\<^bsub>sum\<^esub> n'\<close> have "n'' irs-[n'']\<rightarrow>\<^sub>d* n'"
    by(fastforce intro:irsSp_Cons_sum irsSp_Nil sum_SDG_edge_valid_SDG_node)
  with \<open>n irs-ns\<rightarrow>\<^sub>d* n''\<close> show ?case by(rule irs_SDG_path_Append)
qed


lemma irs_SDG_path_split:
  assumes "n irs-ns\<rightarrow>\<^sub>d* n'"
  obtains "n is-ns\<rightarrow>\<^sub>d* n'"
  | nsx nsx' nx nx' p where "ns = nsx@nx#nsx'" and "n irs-nsx\<rightarrow>\<^sub>d* nx"
  and "nx s-p\<rightarrow>\<^bsub>ret\<^esub> nx' \<or> (\<exists>V. nx s-p:V\<rightarrow>\<^bsub>out\<^esub> nx')" and "nx' is-nsx'\<rightarrow>\<^sub>d* n'"
proof(atomize_elim)
  from \<open>n irs-ns\<rightarrow>\<^sub>d* n'\<close> show "n is-ns\<rightarrow>\<^sub>d* n' \<or>
    (\<exists>nsx nx nsx' p nx'. ns = nsx@nx#nsx' \<and> n irs-nsx\<rightarrow>\<^sub>d* nx \<and> 
                        (nx s-p\<rightarrow>\<^bsub>ret\<^esub> nx' \<or> (\<exists>V. nx s-p:V\<rightarrow>\<^bsub>out\<^esub> nx')) \<and> nx' is-nsx'\<rightarrow>\<^sub>d* n')"
  proof(induct rule:intra_return_sum_SDG_path.induct)
    case (irsSp_Nil n)
    from \<open>valid_SDG_node n\<close> have "n is-[]\<rightarrow>\<^sub>d* n" by(rule isSp_Nil)
    thus ?case by simp
  next
    case (irsSp_Cons_cdep n'' ns n' n)
    from \<open>n'' is-ns\<rightarrow>\<^sub>d* n' \<or> 
      (\<exists>nsx nx nsx' p nx'. ns = nsx@nx#nsx' \<and> n'' irs-nsx\<rightarrow>\<^sub>d* nx \<and> 
                        (nx s-p\<rightarrow>\<^bsub>ret\<^esub> nx' \<or> (\<exists>V. nx s-p:V\<rightarrow>\<^bsub>out\<^esub> nx')) \<and> nx' is-nsx'\<rightarrow>\<^sub>d* n')\<close>
    show ?case
    proof
      assume "n'' is-ns\<rightarrow>\<^sub>d* n'"
      from \<open>n s\<longrightarrow>\<^bsub>cd\<^esub> n''\<close> have "n is-[]@[n]\<rightarrow>\<^sub>d* n''"
        by(fastforce intro:isSp_Append_cdep isSp_Nil sum_SDG_edge_valid_SDG_node)
      with \<open>n'' is-ns\<rightarrow>\<^sub>d* n'\<close> have "n is-[n]@ns\<rightarrow>\<^sub>d* n'"
        by(fastforce intro:is_SDG_path_Append)
      thus ?case by simp
    next
      assume "\<exists>nsx nx nsx' p nx'. ns = nsx@nx#nsx' \<and> n'' irs-nsx\<rightarrow>\<^sub>d* nx \<and> 
                        (nx s-p\<rightarrow>\<^bsub>ret\<^esub> nx' \<or> (\<exists>V. nx s-p:V\<rightarrow>\<^bsub>out\<^esub> nx')) \<and> nx' is-nsx'\<rightarrow>\<^sub>d* n'"
      then obtain nsx nsx' nx nx' p where "ns = nsx@nx#nsx'" and "n'' irs-nsx\<rightarrow>\<^sub>d* nx"
        and "nx s-p\<rightarrow>\<^bsub>ret\<^esub> nx' \<or> (\<exists>V. nx s-p:V\<rightarrow>\<^bsub>out\<^esub> nx')" and "nx' is-nsx'\<rightarrow>\<^sub>d* n'" by blast
      from \<open>n'' irs-nsx\<rightarrow>\<^sub>d* nx\<close> \<open>n s\<longrightarrow>\<^bsub>cd\<^esub> n''\<close> have "n irs-n#nsx\<rightarrow>\<^sub>d* nx"
        by(rule intra_return_sum_SDG_path.irsSp_Cons_cdep)
      with \<open>ns = nsx@nx#nsx'\<close> \<open>nx s-p\<rightarrow>\<^bsub>ret\<^esub> nx' \<or> (\<exists>V. nx s-p:V\<rightarrow>\<^bsub>out\<^esub> nx')\<close>
        \<open>nx' is-nsx'\<rightarrow>\<^sub>d* n'\<close>
      show ?case by fastforce
    qed
  next
    case (irsSp_Cons_ddep n'' ns n' n V)
    from \<open>n'' is-ns\<rightarrow>\<^sub>d* n' \<or> 
      (\<exists>nsx nx nsx' p nx'. ns = nsx@nx#nsx' \<and> n'' irs-nsx\<rightarrow>\<^sub>d* nx \<and> 
                        (nx s-p\<rightarrow>\<^bsub>ret\<^esub> nx' \<or> (\<exists>V. nx s-p:V\<rightarrow>\<^bsub>out\<^esub> nx')) \<and> nx' is-nsx'\<rightarrow>\<^sub>d* n')\<close>
    show ?case
    proof
      assume "n'' is-ns\<rightarrow>\<^sub>d* n'"
      from \<open>n s-V\<rightarrow>\<^sub>d\<^sub>d n''\<close> \<open>n \<noteq> n''\<close> have "n is-[]@[n]\<rightarrow>\<^sub>d* n''"
        by(fastforce intro:isSp_Append_ddep isSp_Nil sum_SDG_edge_valid_SDG_node)
      with \<open>n'' is-ns\<rightarrow>\<^sub>d* n'\<close> have "n is-[n]@ns\<rightarrow>\<^sub>d* n'"
        by(fastforce intro:is_SDG_path_Append)
      thus ?case by simp
    next
      assume "\<exists>nsx nx nsx' p nx'.  ns = nsx@nx#nsx' \<and> n'' irs-nsx\<rightarrow>\<^sub>d* nx \<and> 
                        (nx s-p\<rightarrow>\<^bsub>ret\<^esub> nx' \<or> (\<exists>V. nx s-p:V\<rightarrow>\<^bsub>out\<^esub> nx')) \<and> nx' is-nsx'\<rightarrow>\<^sub>d* n'"
      then obtain nsx nsx' nx nx' p where "ns = nsx@nx#nsx'" and "n'' irs-nsx\<rightarrow>\<^sub>d* nx"
        and "nx s-p\<rightarrow>\<^bsub>ret\<^esub> nx' \<or> (\<exists>V. nx s-p:V\<rightarrow>\<^bsub>out\<^esub> nx')" and "nx' is-nsx'\<rightarrow>\<^sub>d* n'" by blast
      from \<open>n'' irs-nsx\<rightarrow>\<^sub>d* nx\<close> \<open>n s-V\<rightarrow>\<^sub>d\<^sub>d n''\<close> \<open>n \<noteq> n''\<close> have "n irs-n#nsx\<rightarrow>\<^sub>d* nx"
        by(rule intra_return_sum_SDG_path.irsSp_Cons_ddep)
      with \<open>ns = nsx@nx#nsx'\<close> \<open>nx s-p\<rightarrow>\<^bsub>ret\<^esub> nx' \<or> (\<exists>V. nx s-p:V\<rightarrow>\<^bsub>out\<^esub> nx')\<close>
        \<open>nx' is-nsx'\<rightarrow>\<^sub>d* n'\<close>
      show ?case by fastforce
    qed
  next
    case (irsSp_Cons_sum n'' ns n' n p)
    from \<open>n'' is-ns\<rightarrow>\<^sub>d* n' \<or> 
      (\<exists>nsx nx nsx' p nx'. ns = nsx@nx#nsx' \<and> n'' irs-nsx\<rightarrow>\<^sub>d* nx \<and> 
                        (nx s-p\<rightarrow>\<^bsub>ret\<^esub> nx' \<or> (\<exists>V. nx s-p:V\<rightarrow>\<^bsub>out\<^esub> nx')) \<and> nx' is-nsx'\<rightarrow>\<^sub>d* n')\<close>
    show ?case
    proof
      assume "n'' is-ns\<rightarrow>\<^sub>d* n'"
      from \<open>n s-p\<rightarrow>\<^bsub>sum\<^esub> n''\<close> have "n is-[]@[n]\<rightarrow>\<^sub>d* n''"
        by(fastforce intro:isSp_Append_sum isSp_Nil sum_SDG_edge_valid_SDG_node)
      with \<open>n'' is-ns\<rightarrow>\<^sub>d* n'\<close> have "n is-[n]@ns\<rightarrow>\<^sub>d* n'"
        by(fastforce intro:is_SDG_path_Append)
      thus ?case by simp
    next
      assume "\<exists>nsx nx nsx' p nx'. ns = nsx@nx#nsx' \<and> n'' irs-nsx\<rightarrow>\<^sub>d* nx \<and> 
                        (nx s-p\<rightarrow>\<^bsub>ret\<^esub> nx' \<or> (\<exists>V. nx s-p:V\<rightarrow>\<^bsub>out\<^esub> nx')) \<and> nx' is-nsx'\<rightarrow>\<^sub>d* n'"
      then obtain nsx nsx' nx nx' p' where "ns = nsx@nx#nsx'" and "n'' irs-nsx\<rightarrow>\<^sub>d* nx"
        and "nx s-p'\<rightarrow>\<^bsub>ret\<^esub> nx' \<or> (\<exists>V. nx s-p':V\<rightarrow>\<^bsub>out\<^esub> nx')" 
        and "nx' is-nsx'\<rightarrow>\<^sub>d* n'" by blast
      from \<open>n'' irs-nsx\<rightarrow>\<^sub>d* nx\<close> \<open>n s-p\<rightarrow>\<^bsub>sum\<^esub> n''\<close> have "n irs-n#nsx\<rightarrow>\<^sub>d* nx"
        by(rule intra_return_sum_SDG_path.irsSp_Cons_sum)
      with \<open>ns = nsx@nx#nsx'\<close> \<open>nx s-p'\<rightarrow>\<^bsub>ret\<^esub> nx' \<or> (\<exists>V. nx s-p':V\<rightarrow>\<^bsub>out\<^esub> nx')\<close>
        \<open>nx' is-nsx'\<rightarrow>\<^sub>d* n'\<close>
      show ?case by fastforce
    qed
  next
    case (irsSp_Cons_return n'' ns n' n p)
    from \<open>n'' is-ns\<rightarrow>\<^sub>d* n' \<or> 
      (\<exists>nsx nx nsx' p nx'. ns = nsx@nx#nsx' \<and> n'' irs-nsx\<rightarrow>\<^sub>d* nx \<and> 
                        (nx s-p\<rightarrow>\<^bsub>ret\<^esub> nx' \<or> (\<exists>V. nx s-p:V\<rightarrow>\<^bsub>out\<^esub> nx')) \<and> nx' is-nsx'\<rightarrow>\<^sub>d* n')\<close>
    show ?case
    proof
      assume "n'' is-ns\<rightarrow>\<^sub>d* n'"
      from \<open>n s-p\<rightarrow>\<^bsub>ret\<^esub> n''\<close> have "valid_SDG_node n" by(rule sum_SDG_edge_valid_SDG_node)
      hence "n irs-[]\<rightarrow>\<^sub>d* n" by(rule irsSp_Nil)
      with \<open>n s-p\<rightarrow>\<^bsub>ret\<^esub> n''\<close> \<open>n'' is-ns\<rightarrow>\<^sub>d* n'\<close> show ?thesis by fastforce
    next
      assume "\<exists>nsx nx nsx' p nx'. ns = nsx@nx#nsx' \<and> n'' irs-nsx\<rightarrow>\<^sub>d* nx \<and> 
                        (nx s-p\<rightarrow>\<^bsub>ret\<^esub> nx' \<or> (\<exists>V. nx s-p:V\<rightarrow>\<^bsub>out\<^esub> nx')) \<and> nx' is-nsx'\<rightarrow>\<^sub>d* n'"
      then obtain nsx nsx' nx nx' p' where "ns = nsx@nx#nsx'" and "n'' irs-nsx\<rightarrow>\<^sub>d* nx"
        and "nx s-p'\<rightarrow>\<^bsub>ret\<^esub> nx' \<or> (\<exists>V. nx s-p':V\<rightarrow>\<^bsub>out\<^esub> nx')"
        and "nx' is-nsx'\<rightarrow>\<^sub>d* n'" by blast
      from \<open>n'' irs-nsx\<rightarrow>\<^sub>d* nx\<close> \<open>n s-p\<rightarrow>\<^bsub>ret\<^esub> n''\<close> have "n irs-n#nsx\<rightarrow>\<^sub>d* nx"
        by(rule intra_return_sum_SDG_path.irsSp_Cons_return)
      with \<open>ns = nsx@nx#nsx'\<close> \<open>nx s-p'\<rightarrow>\<^bsub>ret\<^esub> nx' \<or> (\<exists>V. nx s-p':V\<rightarrow>\<^bsub>out\<^esub> nx')\<close>
        \<open>nx' is-nsx'\<rightarrow>\<^sub>d* n'\<close>
      show ?thesis by fastforce
    qed
  next
    case (irsSp_Cons_param_out n'' ns n' n p V)
    from \<open>n'' is-ns\<rightarrow>\<^sub>d* n' \<or> 
      (\<exists>nsx nx nsx' p nx'. ns = nsx@nx#nsx' \<and> n'' irs-nsx\<rightarrow>\<^sub>d* nx \<and> 
                        (nx s-p\<rightarrow>\<^bsub>ret\<^esub> nx' \<or> (\<exists>V. nx s-p:V\<rightarrow>\<^bsub>out\<^esub> nx')) \<and> nx' is-nsx'\<rightarrow>\<^sub>d* n')\<close>
    show ?case
    proof
      assume "n'' is-ns\<rightarrow>\<^sub>d* n'"
      from \<open>n s-p:V\<rightarrow>\<^bsub>out\<^esub> n''\<close> have "valid_SDG_node n"
        by(rule sum_SDG_edge_valid_SDG_node)
      hence "n irs-[]\<rightarrow>\<^sub>d* n" by(rule irsSp_Nil)
      with \<open>n s-p:V\<rightarrow>\<^bsub>out\<^esub> n''\<close> \<open>n'' is-ns\<rightarrow>\<^sub>d* n'\<close> show ?thesis by fastforce
    next
      assume "\<exists>nsx nx nsx' p nx'. ns = nsx@nx#nsx' \<and> n'' irs-nsx\<rightarrow>\<^sub>d* nx \<and> 
                        (nx s-p\<rightarrow>\<^bsub>ret\<^esub> nx' \<or> (\<exists>V. nx s-p:V\<rightarrow>\<^bsub>out\<^esub> nx')) \<and> nx' is-nsx'\<rightarrow>\<^sub>d* n'"
      then obtain nsx nsx' nx nx' p' where "ns = nsx@nx#nsx'" and "n'' irs-nsx\<rightarrow>\<^sub>d* nx"
        and "nx s-p'\<rightarrow>\<^bsub>ret\<^esub> nx' \<or> (\<exists>V. nx s-p':V\<rightarrow>\<^bsub>out\<^esub> nx')" 
        and "nx' is-nsx'\<rightarrow>\<^sub>d* n'" by blast
      from \<open>n'' irs-nsx\<rightarrow>\<^sub>d* nx\<close> \<open>n s-p:V\<rightarrow>\<^bsub>out\<^esub> n''\<close> have "n irs-n#nsx\<rightarrow>\<^sub>d* nx"
        by(rule intra_return_sum_SDG_path.irsSp_Cons_param_out)
      with \<open>ns = nsx@nx#nsx'\<close> \<open>nx s-p'\<rightarrow>\<^bsub>ret\<^esub> nx' \<or> (\<exists>V. nx s-p':V\<rightarrow>\<^bsub>out\<^esub> nx')\<close>
        \<open>nx' is-nsx'\<rightarrow>\<^sub>d* n'\<close>
      show ?thesis by fastforce
    qed
  qed
qed


lemma irs_SDG_path_matched:
  assumes "n irs-ns\<rightarrow>\<^sub>d* n''" and "n'' s-p\<rightarrow>\<^bsub>ret\<^esub> n' \<or> n'' s-p:V\<rightarrow>\<^bsub>out\<^esub> n'"
  obtains nx nsx where "matched nx nsx n'" and "n \<in> set nsx" 
  and "nx s-p\<rightarrow>\<^bsub>sum\<^esub> CFG_node (parent_node n')"
proof(atomize_elim)
  from assms
  show "\<exists>nx nsx. matched nx nsx n' \<and> n \<in> set nsx \<and> 
                 nx s-p\<rightarrow>\<^bsub>sum\<^esub> CFG_node (parent_node n')"
  proof(induct ns arbitrary:n'' n' p V rule:length_induct)
    fix ns n'' n' p V
    assume IH:"\<forall>ns'. length ns' < length ns \<longrightarrow>
      (\<forall>n''. n irs-ns'\<rightarrow>\<^sub>d* n'' \<longrightarrow> 
      (\<forall>nx' p' V'. (n'' s-p'\<rightarrow>\<^bsub>ret\<^esub> nx' \<or> n'' s-p':V'\<rightarrow>\<^bsub>out\<^esub> nx') \<longrightarrow> 
        (\<exists>nx nsx. matched nx nsx nx' \<and> n \<in> set nsx \<and> 
                  nx s-p'\<rightarrow>\<^bsub>sum\<^esub> CFG_node (parent_node nx'))))"
      and "n irs-ns\<rightarrow>\<^sub>d* n''" and "n'' s-p\<rightarrow>\<^bsub>ret\<^esub> n' \<or> n'' s-p:V\<rightarrow>\<^bsub>out\<^esub> n'"
    from \<open>n'' s-p\<rightarrow>\<^bsub>ret\<^esub> n' \<or> n'' s-p:V\<rightarrow>\<^bsub>out\<^esub> n'\<close> have "valid_SDG_node n''"
      by(fastforce intro:sum_SDG_edge_valid_SDG_node)
    from \<open>n'' s-p\<rightarrow>\<^bsub>ret\<^esub> n' \<or> n'' s-p:V\<rightarrow>\<^bsub>out\<^esub> n'\<close>
    have "n'' -p\<rightarrow>\<^bsub>ret\<^esub> n' \<or> n'' -p:V\<rightarrow>\<^bsub>out\<^esub> n'"
      by(fastforce intro:sum_SDG_edge_SDG_edge SDG_edge_sum_SDG_edge)
    from \<open>n'' s-p\<rightarrow>\<^bsub>ret\<^esub> n' \<or> n'' s-p:V\<rightarrow>\<^bsub>out\<^esub> n'\<close>
    have "CFG_node (parent_node n'') s-p\<rightarrow>\<^bsub>ret\<^esub> CFG_node (parent_node n')"
      by(fastforce elim:sum_SDG_edge.cases intro:sum_SDG_return_edge)
    then obtain a Q f where "valid_edge a" and "kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f"
      and "parent_node n'' = sourcenode a" and "parent_node n' = targetnode a"
      by(fastforce elim:sum_SDG_edge.cases)
    from \<open>valid_edge a\<close> \<open>kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f\<close> obtain a' Q' r' fs' 
      where "a \<in> get_return_edges a'" and "valid_edge a'" and "kind a' = Q':r'\<hookrightarrow>\<^bsub>p\<^esub>fs'"
      and "CFG_node (sourcenode a') s-p\<rightarrow>\<^bsub>sum\<^esub> CFG_node (targetnode a)"
      by(erule return_edge_determines_call_and_sum_edge)
    from \<open>valid_edge a'\<close> \<open>kind a' = Q':r'\<hookrightarrow>\<^bsub>p\<^esub>fs'\<close>
    have "CFG_node (sourcenode a') s-p\<rightarrow>\<^bsub>call\<^esub> CFG_node (targetnode a')"
      by(fastforce intro:sum_SDG_call_edge)
    from \<open>CFG_node (parent_node n'') s-p\<rightarrow>\<^bsub>ret\<^esub> CFG_node (parent_node n')\<close> 
    have "get_proc (parent_node n'') = p"
      by(auto elim!:sum_SDG_edge.cases intro:get_proc_return)
    from \<open>n irs-ns\<rightarrow>\<^sub>d* n''\<close>
    show "\<exists>nx nsx. matched nx nsx n' \<and> n \<in> set nsx \<and> 
                   nx s-p\<rightarrow>\<^bsub>sum\<^esub> CFG_node (parent_node n')"
    proof(rule irs_SDG_path_split)
      assume "n is-ns\<rightarrow>\<^sub>d* n''"
      hence "valid_SDG_node n" by(rule is_SDG_path_valid_SDG_node)
      then obtain asx where "(_Entry_) -asx\<rightarrow>\<^sub>\<surd>* parent_node n"
        by(fastforce dest:valid_SDG_CFG_node Entry_path)
      then obtain asx' where "(_Entry_) -asx'\<rightarrow>\<^sub>\<surd>* parent_node n"
        and "\<forall>a' \<in> set asx'. intra_kind(kind a') \<or> (\<exists>Q r p fs. kind a' = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs)"
        by -(erule valid_Entry_path_ascending_path)
      from \<open>n is-ns\<rightarrow>\<^sub>d* n''\<close> obtain as where "parent_node n -as\<rightarrow>\<^sub>\<iota>* parent_node n''"
        by(erule is_SDG_path_CFG_path)
      hence "get_proc (parent_node n) = get_proc (parent_node n'')"
        by(rule intra_path_get_procs)
      from \<open>valid_SDG_node n\<close> have "valid_node (parent_node n)"
        by(rule valid_SDG_CFG_node)
      hence "valid_SDG_node (CFG_node (parent_node n))" by simp
      have "\<exists>a as. valid_edge a \<and> (\<exists>Q p r fs. kind a = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs) \<and>
        targetnode a -as\<rightarrow>\<^sub>\<iota>* parent_node n"
      proof(cases "\<forall>a' \<in> set asx'. intra_kind(kind a')")
        case True
        with \<open>(_Entry_) -asx'\<rightarrow>\<^sub>\<surd>* parent_node n\<close>
        have "(_Entry_) -asx'\<rightarrow>\<^sub>\<iota>* parent_node n"
          by(fastforce simp:intra_path_def vp_def)
        hence "get_proc (_Entry_) = get_proc (parent_node n)"
          by(rule intra_path_get_procs)
        with get_proc_Entry have "get_proc (parent_node n) = Main" by simp
        from \<open>get_proc (parent_node n) = get_proc (parent_node n'')\<close>
          \<open>get_proc (parent_node n) = Main\<close> 
        have "get_proc (parent_node n'') = Main" by simp
        from \<open>valid_edge a\<close> \<open>kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f\<close> have "get_proc (sourcenode a) = p"
          by(rule get_proc_return)
        with \<open>parent_node n'' = sourcenode a\<close> \<open>get_proc (parent_node n'') = Main\<close>
        have "p = Main" by simp
        with \<open>kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f\<close> have "kind a = Q\<hookleftarrow>\<^bsub>Main\<^esub>f" by simp
        with \<open>valid_edge a\<close> have False by(rule Main_no_return_source)
        thus ?thesis by simp
      next
        assume "\<not> (\<forall>a'\<in>set asx'. intra_kind (kind a'))"
        with \<open>\<forall>a' \<in> set asx'. intra_kind(kind a') \<or> (\<exists>Q r p fs. kind a' = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs)\<close>
        have "\<exists>a' \<in> set asx'. \<exists>Q r p fs. kind a' = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs" 
          by(fastforce simp:intra_kind_def)
        then obtain as a' as' where "asx' = as@a'#as'" 
          and "\<exists>Q r p fs. kind a' = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs"
          and "\<forall>a' \<in> set as'. \<not> (\<exists>Q r p fs. kind a' = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs)"
          by(erule split_list_last_propE)
        with \<open>\<forall>a' \<in> set asx'. intra_kind(kind a') \<or> (\<exists>Q r p fs. kind a' = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs)\<close>
        have "\<forall>a'\<in>set as'. intra_kind (kind a')" by(auto simp:intra_kind_def)
        from \<open>(_Entry_) -asx'\<rightarrow>\<^sub>\<surd>* parent_node n\<close> \<open>asx' = as@a'#as'\<close>
        have "valid_edge a'" and "targetnode a' -as'\<rightarrow>* parent_node n"
          by(auto dest:path_split simp:vp_def)
        with \<open>\<forall>a'\<in>set as'. intra_kind (kind a')\<close> \<open>\<exists>Q r p fs. kind a' = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs\<close>
        show ?thesis by(fastforce simp:intra_path_def)
      qed
      then obtain ax asx Qx rx fsx px where "valid_edge ax"
        and "kind ax = Qx:rx\<hookrightarrow>\<^bsub>px\<^esub>fsx" and "targetnode ax -asx\<rightarrow>\<^sub>\<iota>* parent_node n"
        by blast
      from \<open>valid_edge ax\<close> \<open>kind ax = Qx:rx\<hookrightarrow>\<^bsub>px\<^esub>fsx\<close> 
      have "get_proc (targetnode ax) = px"
        by(rule get_proc_call)
      from \<open>targetnode ax -asx\<rightarrow>\<^sub>\<iota>* parent_node n\<close> 
      have "get_proc (targetnode ax) = get_proc (parent_node n)" 
        by(rule intra_path_get_procs)
      with \<open>get_proc (parent_node n) = get_proc (parent_node n'')\<close> 
        \<open>get_proc (targetnode ax) = px\<close>
      have "get_proc (parent_node n'') = px" by simp
      with \<open>get_proc (parent_node n'') = p\<close> have [simp]:"px = p" by simp
      from \<open>valid_edge a'\<close> \<open>valid_edge ax\<close> \<open>kind a' = Q':r'\<hookrightarrow>\<^bsub>p\<^esub>fs'\<close>
        \<open>kind ax = Qx:rx\<hookrightarrow>\<^bsub>px\<^esub>fsx\<close>
      have "targetnode a' = targetnode ax" by simp(rule same_proc_call_unique_target)
      have "parent_node n \<noteq> (_Exit_)"
      proof
        assume "parent_node n = (_Exit_)"
        from \<open>n is-ns\<rightarrow>\<^sub>d* n''\<close> obtain as where "parent_node n -as\<rightarrow>\<^sub>\<iota>* parent_node n''"
          by(erule is_SDG_path_CFG_path)
        with \<open>parent_node n = (_Exit_)\<close>
        have "(_Exit_) -as\<rightarrow>* parent_node n''" by(simp add:intra_path_def)
        hence "parent_node n'' = (_Exit_)" by(fastforce dest:path_Exit_source)
        from \<open>get_proc (parent_node n'') = p\<close> \<open>parent_node n'' = (_Exit_)\<close>
          \<open>parent_node n'' = sourcenode a\<close> get_proc_Exit 
        have "p = Main" by simp
        with \<open>kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f\<close> have "kind a = Q\<hookleftarrow>\<^bsub>Main\<^esub>f" by simp
        with \<open>valid_edge a\<close> show False by(rule Main_no_return_source)
      qed
      have "\<exists>nsx. CFG_node (targetnode a') cd-nsx\<rightarrow>\<^sub>d* CFG_node (parent_node n)"
      proof(cases "targetnode a' = parent_node n")
        case True
        with \<open>valid_SDG_node (CFG_node (parent_node n))\<close> 
        have "CFG_node (targetnode a') cd-[]\<rightarrow>\<^sub>d* CFG_node (parent_node n)"
          by(fastforce intro:cdSp_Nil)
        thus ?thesis by blast
      next
        case False
        with \<open>targetnode ax -asx\<rightarrow>\<^sub>\<iota>* parent_node n\<close> \<open>parent_node n \<noteq> (_Exit_)\<close>
          \<open>valid_edge ax\<close> \<open>kind ax = Qx:rx\<hookrightarrow>\<^bsub>px\<^esub>fsx\<close> \<open>targetnode a' = targetnode ax\<close>
        obtain nsx 
          where "CFG_node (targetnode a') cd-nsx\<rightarrow>\<^sub>d* CFG_node (parent_node n)"
          by(fastforce elim!:in_proc_cdep_SDG_path)
        thus ?thesis by blast
      qed
      then obtain nsx 
        where "CFG_node (targetnode a') cd-nsx\<rightarrow>\<^sub>d* CFG_node (parent_node n)" by blast
      hence "CFG_node (targetnode a') i-nsx\<rightarrow>\<^sub>d* CFG_node (parent_node n)"
        by(rule cdep_SDG_path_intra_SDG_path)
      show ?thesis
      proof(cases ns)
        case Nil
        with \<open>n is-ns\<rightarrow>\<^sub>d* n''\<close> have "n = n''"
          by(fastforce elim:intra_sum_SDG_path.cases)
        from \<open>valid_edge a'\<close> \<open>kind a' = Q':r'\<hookrightarrow>\<^bsub>p\<^esub>fs'\<close> \<open>a \<in> get_return_edges a'\<close>
        have "matched (CFG_node (targetnode a')) [CFG_node (targetnode a')]
          (CFG_node (sourcenode a))" by(rule intra_proc_matched)
        from \<open>valid_SDG_node n''\<close>
        have "n'' = CFG_node (parent_node n'') \<or> CFG_node (parent_node n'') \<longrightarrow>\<^bsub>cd\<^esub> n''"
          by(rule valid_SDG_node_cases)
        hence "\<exists>nsx. CFG_node (parent_node n'') i-nsx\<rightarrow>\<^sub>d* n''"
        proof
          assume "n'' = CFG_node (parent_node n'')"
          with \<open>valid_SDG_node n''\<close> have "CFG_node (parent_node n'') i-[]\<rightarrow>\<^sub>d* n''"
            by(fastforce intro:iSp_Nil)
          thus ?thesis by blast
        next
          assume "CFG_node (parent_node n'') \<longrightarrow>\<^bsub>cd\<^esub> n''"
          from \<open>valid_SDG_node n''\<close> have "valid_node (parent_node n'')"
            by(rule valid_SDG_CFG_node)
          hence "valid_SDG_node (CFG_node (parent_node n''))" by simp
          hence "CFG_node (parent_node n'') i-[]\<rightarrow>\<^sub>d* CFG_node (parent_node n'')"
            by(rule iSp_Nil)
          with \<open>CFG_node (parent_node n'') \<longrightarrow>\<^bsub>cd\<^esub> n''\<close>
          have "CFG_node (parent_node n'') i-[]@[CFG_node (parent_node n'')]\<rightarrow>\<^sub>d* n''"
            by(fastforce intro:iSp_Append_cdep sum_SDG_edge_SDG_edge)
          thus ?thesis by blast
        qed
        with \<open>parent_node n'' = sourcenode a\<close>
        obtain nsx where "CFG_node (sourcenode a) i-nsx\<rightarrow>\<^sub>d* n''" by fastforce
        with \<open>matched (CFG_node (targetnode a')) [CFG_node (targetnode a')]
          (CFG_node (sourcenode a))\<close>
        have "matched (CFG_node (targetnode a')) ([CFG_node (targetnode a')]@nsx) n''"
          by(fastforce intro:matched_Append intra_SDG_path_matched)
        moreover
        from \<open>valid_edge a'\<close> \<open>kind a' = Q':r'\<hookrightarrow>\<^bsub>p\<^esub>fs'\<close>
        have "CFG_node (sourcenode a') -p\<rightarrow>\<^bsub>call\<^esub> CFG_node (targetnode a')"
          by(fastforce intro:SDG_call_edge)
        moreover
        from \<open>valid_edge a'\<close> have "valid_SDG_node (CFG_node (sourcenode a'))"
          by simp
        hence "matched (CFG_node (sourcenode a')) [] (CFG_node (sourcenode a'))"
          by(rule matched_Nil)
        ultimately have "matched (CFG_node (sourcenode a'))
          ([]@(CFG_node (sourcenode a'))#([CFG_node (targetnode a')]@nsx)@[n'']) n'"
          using \<open>n'' s-p\<rightarrow>\<^bsub>ret\<^esub> n' \<or> n'' s-p:V\<rightarrow>\<^bsub>out\<^esub> n'\<close> \<open>parent_node n' = targetnode a\<close>
            \<open>parent_node n'' = sourcenode a\<close> \<open>valid_edge a'\<close> \<open>a \<in> get_return_edges a'\<close>
          by(fastforce intro:matched_bracket_call dest:sum_SDG_edge_SDG_edge)
        with \<open>n = n''\<close> \<open>CFG_node (sourcenode a') s-p\<rightarrow>\<^bsub>sum\<^esub> CFG_node (targetnode a)\<close>
          \<open>parent_node n' = targetnode a\<close>
        show ?thesis by fastforce
      next
        case Cons
        with \<open>n is-ns\<rightarrow>\<^sub>d* n''\<close> have "n \<in> set ns"
          by(induct rule:intra_sum_SDG_path_rev_induct) auto
        from \<open>n is-ns\<rightarrow>\<^sub>d* n''\<close> obtain ns' where "matched n ns' n''" 
          and "set ns \<subseteq> set ns'" by(erule is_SDG_path_matched)
        with \<open>n \<in> set ns\<close> have "n \<in> set ns'" by fastforce
        from \<open>valid_SDG_node n\<close>
        have "n = CFG_node (parent_node n) \<or> CFG_node (parent_node n) \<longrightarrow>\<^bsub>cd\<^esub> n"
          by(rule valid_SDG_node_cases)
        hence "\<exists>nsx. CFG_node (parent_node n) i-nsx\<rightarrow>\<^sub>d* n"
        proof
          assume "n = CFG_node (parent_node n)"
          with \<open>valid_SDG_node n\<close> have "CFG_node (parent_node n) i-[]\<rightarrow>\<^sub>d* n"
            by(fastforce intro:iSp_Nil)
          thus ?thesis by blast
        next
          assume "CFG_node (parent_node n) \<longrightarrow>\<^bsub>cd\<^esub> n"
          from \<open>valid_SDG_node (CFG_node (parent_node n))\<close> 
          have "CFG_node (parent_node n) i-[]\<rightarrow>\<^sub>d* CFG_node (parent_node n)"
            by(rule iSp_Nil)
          with \<open>CFG_node (parent_node n) \<longrightarrow>\<^bsub>cd\<^esub> n\<close>
          have "CFG_node (parent_node n) i-[]@[CFG_node (parent_node n)]\<rightarrow>\<^sub>d* n"
            by(fastforce intro:iSp_Append_cdep sum_SDG_edge_SDG_edge)
          thus ?thesis by blast
        qed
        then obtain nsx' where "CFG_node (parent_node n) i-nsx'\<rightarrow>\<^sub>d* n" by blast
        with \<open>CFG_node (targetnode a') i-nsx\<rightarrow>\<^sub>d* CFG_node (parent_node n)\<close>
        have "CFG_node (targetnode a') i-nsx@nsx'\<rightarrow>\<^sub>d* n"
          by -(rule intra_SDG_path_Append)
        hence "matched (CFG_node (targetnode a')) (nsx@nsx') n"
          by(rule intra_SDG_path_matched)
        with \<open>matched n ns' n''\<close> 
        have "matched (CFG_node (targetnode a')) ((nsx@nsx')@ns') n''"
          by(rule matched_Append)
        moreover
        from \<open>valid_edge a'\<close> \<open>kind a' = Q':r'\<hookrightarrow>\<^bsub>p\<^esub>fs'\<close>
        have "CFG_node (sourcenode a') -p\<rightarrow>\<^bsub>call\<^esub> CFG_node (targetnode a')"
          by(fastforce intro:SDG_call_edge)
        moreover
        from \<open>valid_edge a'\<close> have "valid_SDG_node (CFG_node (sourcenode a'))"
          by simp
        hence "matched (CFG_node (sourcenode a')) [] (CFG_node (sourcenode a'))"
          by(rule matched_Nil)
        ultimately have "matched (CFG_node (sourcenode a')) 
          ([]@(CFG_node (sourcenode a'))#((nsx@nsx')@ns')@[n'']) n'"
          using  \<open>n'' s-p\<rightarrow>\<^bsub>ret\<^esub> n' \<or> n'' s-p:V\<rightarrow>\<^bsub>out\<^esub> n'\<close> \<open>parent_node n' = targetnode a\<close>
            \<open>parent_node n'' = sourcenode a\<close> \<open>valid_edge a'\<close> \<open>a \<in> get_return_edges a'\<close>
          by(fastforce intro:matched_bracket_call dest:sum_SDG_edge_SDG_edge)
        with \<open>CFG_node (sourcenode a') s-p\<rightarrow>\<^bsub>sum\<^esub> CFG_node (targetnode a)\<close>
          \<open>parent_node n' = targetnode a\<close> \<open>n \<in> set ns'\<close>
        show ?thesis by fastforce
      qed
    next
      fix ms ms' m m' px
      assume "ns = ms@m#ms'" and "n irs-ms\<rightarrow>\<^sub>d* m"
        and "m s-px\<rightarrow>\<^bsub>ret\<^esub> m' \<or> (\<exists>V. m s-px:V\<rightarrow>\<^bsub>out\<^esub> m')" and "m' is-ms'\<rightarrow>\<^sub>d* n''"
      from \<open>ns = ms@m#ms'\<close> have "length ms < length ns" by simp
      with IH \<open>n irs-ms\<rightarrow>\<^sub>d* m\<close> \<open>m s-px\<rightarrow>\<^bsub>ret\<^esub> m' \<or> (\<exists>V. m s-px:V\<rightarrow>\<^bsub>out\<^esub> m')\<close> obtain mx msx
        where "matched mx msx m'" and "n \<in> set msx" 
        and "mx s-px\<rightarrow>\<^bsub>sum\<^esub> CFG_node (parent_node m')" by fastforce
      from \<open>m' is-ms'\<rightarrow>\<^sub>d* n''\<close> obtain msx' where "matched m' msx' n''"
        by -(erule is_SDG_path_matched)
      with \<open>matched mx msx m'\<close> have "matched mx (msx@msx') n''"
        by -(rule matched_Append)
      from \<open>m s-px\<rightarrow>\<^bsub>ret\<^esub> m' \<or> (\<exists>V. m s-px:V\<rightarrow>\<^bsub>out\<^esub> m')\<close>
      have "m -px\<rightarrow>\<^bsub>ret\<^esub> m' \<or> (\<exists>V. m -px:V\<rightarrow>\<^bsub>out\<^esub> m')"
        by(auto intro:sum_SDG_edge_SDG_edge SDG_edge_sum_SDG_edge)
      from \<open>m s-px\<rightarrow>\<^bsub>ret\<^esub> m' \<or> (\<exists>V. m s-px:V\<rightarrow>\<^bsub>out\<^esub> m')\<close>
      have "CFG_node (parent_node m) s-px\<rightarrow>\<^bsub>ret\<^esub> CFG_node (parent_node m')"
        by(fastforce elim:sum_SDG_edge.cases intro:sum_SDG_return_edge)
      then obtain ax Qx fx where "valid_edge ax" and "kind ax = Qx\<hookleftarrow>\<^bsub>px\<^esub>fx"
      and "parent_node m = sourcenode ax" and "parent_node m' = targetnode ax"
        by(fastforce elim:sum_SDG_edge.cases)
      from \<open>valid_edge ax\<close> \<open>kind ax = Qx\<hookleftarrow>\<^bsub>px\<^esub>fx\<close> obtain ax' Qx' rx' fsx' 
        where "ax \<in> get_return_edges ax'" and "valid_edge ax'" 
        and "kind ax' = Qx':rx'\<hookrightarrow>\<^bsub>px\<^esub>fsx'"
        and "CFG_node (sourcenode ax') s-px\<rightarrow>\<^bsub>sum\<^esub> CFG_node (targetnode ax)"
        by(erule return_edge_determines_call_and_sum_edge)
      from \<open>valid_edge ax'\<close> \<open>kind ax' = Qx':rx'\<hookrightarrow>\<^bsub>px\<^esub>fsx'\<close>
      have "CFG_node (sourcenode ax') s-px\<rightarrow>\<^bsub>call\<^esub> CFG_node (targetnode ax')"
        by(fastforce intro:sum_SDG_call_edge)
      from \<open>mx s-px\<rightarrow>\<^bsub>sum\<^esub> CFG_node (parent_node m')\<close>
      have "valid_SDG_node mx" by(rule sum_SDG_edge_valid_SDG_node)
      have "\<exists>msx''. CFG_node (targetnode a') cd-msx''\<rightarrow>\<^sub>d* mx"
      proof(cases "targetnode a' = parent_node mx")
        case True
        from \<open>valid_SDG_node mx\<close> 
        have "mx = CFG_node (parent_node mx) \<or> CFG_node (parent_node mx) \<longrightarrow>\<^bsub>cd\<^esub> mx"
          by(rule valid_SDG_node_cases)
        thus ?thesis
        proof
          assume "mx = CFG_node (parent_node mx)"
          with \<open>valid_SDG_node mx\<close> True
          have "CFG_node (targetnode a') cd-[]\<rightarrow>\<^sub>d* mx" by(fastforce intro:cdSp_Nil)
          thus ?thesis by blast
        next
          assume "CFG_node (parent_node mx) \<longrightarrow>\<^bsub>cd\<^esub> mx"
          with \<open>valid_edge a'\<close> True[THEN sym]
          have "CFG_node (targetnode a') cd-[]@[CFG_node (targetnode a')]\<rightarrow>\<^sub>d* mx"
            by(fastforce intro:cdep_SDG_path.intros)
          thus ?thesis by blast
        qed
      next
        case False
        show ?thesis
        proof(cases "\<forall>ai. valid_edge ai \<and> sourcenode ai = parent_node mx
            \<longrightarrow> ai \<notin> get_return_edges a'")
          case True
          { assume "parent_node mx = (_Exit_)"
            with \<open>mx s-px\<rightarrow>\<^bsub>sum\<^esub> CFG_node (parent_node m')\<close>
            obtain ai where "valid_edge ai" and "sourcenode ai = (_Exit_)"
              by -(erule sum_SDG_edge.cases,auto)
            hence False by(rule Exit_source) }
          hence "parent_node mx \<noteq> (_Exit_)" by fastforce
          from \<open>valid_SDG_node mx\<close> have "valid_node (parent_node mx)"
            by(rule valid_SDG_CFG_node)
          then obtain asx where "(_Entry_) -asx\<rightarrow>\<^sub>\<surd>* parent_node mx"
            by(fastforce intro:Entry_path)
          then obtain asx' where "(_Entry_) -asx'\<rightarrow>\<^sub>\<surd>* parent_node mx"
            and "\<forall>a' \<in> set asx'. intra_kind(kind a') \<or> (\<exists>Q r p fs. kind a' = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs)"
            by -(erule valid_Entry_path_ascending_path)
          from \<open>mx s-px\<rightarrow>\<^bsub>sum\<^esub> CFG_node (parent_node m')\<close>
          obtain nsi where "matched mx nsi (CFG_node (parent_node m'))"
            by -(erule sum_SDG_summary_edge_matched)
          then obtain asi where "parent_node mx -asi\<rightarrow>\<^bsub>sl\<^esub>* parent_node m'"
            by(fastforce elim:matched_same_level_CFG_path)
          hence "get_proc (parent_node mx) = get_proc (parent_node m')"
            by(rule slp_get_proc)
          from \<open>m' is-ms'\<rightarrow>\<^sub>d* n''\<close> obtain nsi' where "matched m' nsi' n''"
            by -(erule is_SDG_path_matched)
          then obtain asi' where "parent_node m' -asi'\<rightarrow>\<^bsub>sl\<^esub>* parent_node n''"
            by -(erule matched_same_level_CFG_path)
          hence "get_proc (parent_node m') = get_proc (parent_node n'')"
            by(rule slp_get_proc)
          with \<open>get_proc (parent_node mx) = get_proc (parent_node m')\<close>
          have "get_proc (parent_node mx) = get_proc (parent_node n'')" by simp
          from \<open>get_proc (parent_node n'') = p\<close> 
            \<open>get_proc (parent_node mx) = get_proc (parent_node n'')\<close>
          have "get_proc (parent_node mx) = p" by simp
          have "\<exists>asx. targetnode a' -asx\<rightarrow>\<^sub>\<iota>* parent_node mx"
          proof(cases "\<forall>a' \<in> set asx'. intra_kind(kind a')")
            case True
            with \<open>(_Entry_) -asx'\<rightarrow>\<^sub>\<surd>* parent_node mx\<close> 
            have "(_Entry_) -asx'\<rightarrow>\<^sub>\<iota>* parent_node mx"
              by(simp add:vp_def intra_path_def)
            hence "get_proc (_Entry_) = get_proc (parent_node mx)"
              by(rule intra_path_get_procs)
            with \<open>get_proc (parent_node mx) = p\<close> have "get_proc (_Entry_) = p"
              by simp
            with \<open>CFG_node (parent_node n'') s-p\<rightarrow>\<^bsub>ret\<^esub> CFG_node (parent_node n')\<close>
            have False
              by -(erule sum_SDG_edge.cases,
                auto intro:Main_no_return_source simp:get_proc_Entry)
            thus ?thesis by simp
          next
            case False
            hence "\<exists>a' \<in> set asx'. \<not> intra_kind (kind a')" by fastforce
            then obtain ai as' as'' where "asx' = as'@ai#as''" 
              and "\<not> intra_kind (kind ai)" and "\<forall>a' \<in> set as''. intra_kind (kind a')"
              by(fastforce elim!:split_list_last_propE)
            from \<open>asx' = as'@ai#as''\<close> \<open>\<not> intra_kind (kind ai)\<close>
              \<open>\<forall>a' \<in> set asx'. intra_kind(kind a') \<or> (\<exists>Q r p fs. kind a' = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs)\<close>
            obtain Qi ri pi fsi where "kind ai = Qi:ri\<hookrightarrow>\<^bsub>pi\<^esub>fsi" 
              and "\<forall>a' \<in> set as'. intra_kind(kind a') \<or> 
              (\<exists>Q r p fs. kind a' = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs)"
              by auto
            from \<open>(_Entry_) -asx'\<rightarrow>\<^sub>\<surd>* parent_node mx\<close> \<open>asx' = as'@ai#as''\<close>
              \<open>\<forall>a' \<in> set as''. intra_kind (kind a')\<close>
            have "valid_edge ai" and "targetnode ai -as''\<rightarrow>\<^sub>\<iota>* parent_node mx"
              by(auto intro:path_split simp:vp_def intra_path_def)
            hence "get_proc (targetnode ai) = get_proc (parent_node mx)"
              by -(rule intra_path_get_procs)
            with \<open>get_proc (parent_node mx) = p\<close> \<open>valid_edge ai\<close>
              \<open>kind ai = Qi:ri\<hookrightarrow>\<^bsub>pi\<^esub>fsi\<close>
            have [simp]:"pi = p" by(fastforce dest:get_proc_call)
            from \<open>valid_edge ai\<close> \<open>valid_edge a'\<close> 
              \<open>kind ai = Qi:ri\<hookrightarrow>\<^bsub>pi\<^esub>fsi\<close> \<open>kind a' = Q':r'\<hookrightarrow>\<^bsub>p\<^esub>fs'\<close>
            have "targetnode ai = targetnode a'" 
              by(fastforce intro:same_proc_call_unique_target)
            with \<open>targetnode ai -as''\<rightarrow>\<^sub>\<iota>* parent_node mx\<close>
            show ?thesis by fastforce
          qed
          then obtain asx where "targetnode a' -asx\<rightarrow>\<^sub>\<iota>* parent_node mx" by blast
          from this \<open>valid_edge a'\<close> \<open>kind a' = Q':r'\<hookrightarrow>\<^bsub>p\<^esub>fs'\<close>
            \<open>parent_node mx \<noteq> (_Exit_)\<close> \<open>targetnode a' \<noteq> parent_node mx\<close> True
          obtain msi 
            where "CFG_node(targetnode a') cd-msi\<rightarrow>\<^sub>d* CFG_node(parent_node mx)"
            by(fastforce elim!:in_proc_cdep_SDG_path)
          from \<open>valid_SDG_node mx\<close> 
          have "mx = CFG_node (parent_node mx) \<or> CFG_node (parent_node mx) \<longrightarrow>\<^bsub>cd\<^esub> mx"
            by(rule valid_SDG_node_cases)
          thus ?thesis
          proof
            assume "mx = CFG_node (parent_node mx)"
            with \<open>CFG_node(targetnode a')cd-msi\<rightarrow>\<^sub>d* CFG_node(parent_node mx)\<close>
            show ?thesis by fastforce
          next
            assume "CFG_node (parent_node mx) \<longrightarrow>\<^bsub>cd\<^esub> mx"
            with \<open>CFG_node(targetnode a')cd-msi\<rightarrow>\<^sub>d* CFG_node(parent_node mx)\<close>
            have "CFG_node(targetnode a') cd-msi@[CFG_node(parent_node mx)]\<rightarrow>\<^sub>d* mx"
              by(fastforce intro:cdSp_Append_cdep)
            thus ?thesis by fastforce
          qed
        next
          case False
          then obtain ai where "valid_edge ai" and "sourcenode ai = parent_node mx"
            and "ai \<in> get_return_edges a'" by blast
          with \<open>valid_edge a'\<close> \<open>kind a' = Q':r'\<hookrightarrow>\<^bsub>p\<^esub>fs'\<close>
          have "CFG_node (targetnode a') \<longrightarrow>\<^bsub>cd\<^esub> CFG_node (parent_node mx)"
            by(auto intro:SDG_proc_entry_exit_cdep)       
          with \<open>valid_edge a'\<close> 
          have cd_path:"CFG_node (targetnode a') cd-[]@[CFG_node (targetnode a')]\<rightarrow>\<^sub>d* 
                        CFG_node (parent_node mx)"
            by(fastforce intro:cdSp_Append_cdep cdSp_Nil)
          from \<open>valid_SDG_node mx\<close> 
          have "mx = CFG_node (parent_node mx) \<or> CFG_node (parent_node mx) \<longrightarrow>\<^bsub>cd\<^esub> mx"
            by(rule valid_SDG_node_cases)
          thus ?thesis
          proof
            assume "mx = CFG_node (parent_node mx)"
            with cd_path show ?thesis by fastforce
          next
            assume "CFG_node (parent_node mx) \<longrightarrow>\<^bsub>cd\<^esub> mx"
            with cd_path have "CFG_node (targetnode a') 
              cd-[CFG_node (targetnode a')]@[CFG_node (parent_node mx)]\<rightarrow>\<^sub>d* mx"
              by(fastforce intro:cdSp_Append_cdep)
            thus ?thesis by fastforce
          qed
        qed
      qed
      then obtain msx'' 
        where "CFG_node (targetnode a') cd-msx''\<rightarrow>\<^sub>d* mx" by blast
      hence "CFG_node (targetnode a') i-msx''\<rightarrow>\<^sub>d* mx"
        by(rule cdep_SDG_path_intra_SDG_path)
      with \<open>valid_edge a'\<close> 
      have "matched (CFG_node (targetnode a')) ([]@msx'') mx"
        by(fastforce intro:matched_Append_intra_SDG_path matched_Nil)
      with \<open>matched mx (msx@msx') n''\<close>
      have "matched (CFG_node (targetnode a')) (msx''@(msx@msx')) n''"
        by(fastforce intro:matched_Append)
      with \<open>valid_edge a'\<close> \<open>CFG_node (sourcenode a') s-p\<rightarrow>\<^bsub>call\<^esub> CFG_node (targetnode a')\<close>
        \<open>n'' -p\<rightarrow>\<^bsub>ret\<^esub> n' \<or> n'' -p:V\<rightarrow>\<^bsub>out\<^esub> n'\<close> \<open>a \<in> get_return_edges a'\<close>
        \<open>parent_node n'' = sourcenode a\<close> \<open>parent_node n' = targetnode a\<close>
      have "matched (CFG_node (sourcenode a')) 
        ([]@CFG_node (sourcenode a')#(msx''@(msx@msx'))@[n'']) n'"
        by(fastforce intro:matched_bracket_call matched_Nil sum_SDG_edge_SDG_edge)
      with \<open>n \<in> set msx\<close> \<open>CFG_node (sourcenode a') s-p\<rightarrow>\<^bsub>sum\<^esub> CFG_node (targetnode a)\<close>
        \<open>parent_node n' = targetnode a\<close>
      show ?thesis by fastforce
    qed
  qed
qed


lemma irs_SDG_path_realizable:
  assumes "n irs-ns\<rightarrow>\<^sub>d* n'" and "n \<noteq> n'"
  obtains ns' where "realizable (CFG_node (_Entry_)) ns' n'" and "n \<in> set ns'"
proof(atomize_elim)
  from \<open>n irs-ns\<rightarrow>\<^sub>d* n'\<close>
  have "n = n' \<or> (\<exists>ns'. realizable (CFG_node (_Entry_)) ns' n' \<and> n \<in> set ns')"
  proof(rule irs_SDG_path_split)
    assume "n is-ns\<rightarrow>\<^sub>d* n'"
    show ?thesis
    proof(cases "ns = []")
      case True
      with \<open>n is-ns\<rightarrow>\<^sub>d* n'\<close> have "n = n'" by(fastforce elim:intra_sum_SDG_path.cases)
      thus ?thesis by simp
    next
      case False
      with \<open>n is-ns\<rightarrow>\<^sub>d* n'\<close> have "n \<in> set ns" by(fastforce dest:is_SDG_path_hd)
      from \<open>n is-ns\<rightarrow>\<^sub>d* n'\<close> have "valid_SDG_node n" and "valid_SDG_node n'"
        by(rule is_SDG_path_valid_SDG_node)+
      hence "valid_node (parent_node n)" by -(rule valid_SDG_CFG_node)
      from \<open>n is-ns\<rightarrow>\<^sub>d* n'\<close> obtain ns' where "matched n ns' n'" and "set ns \<subseteq> set ns'"
        by(erule is_SDG_path_matched)
      with \<open>n \<in> set ns\<close> have "n \<in> set ns'" by fastforce
      from \<open>valid_node (parent_node n)\<close>
      show ?thesis
      proof(cases "parent_node n = (_Exit_)")
        case True
        with \<open>valid_SDG_node n\<close> have "n = CFG_node (_Exit_)"
          by(rule valid_SDG_node_parent_Exit)
        from \<open>n is-ns\<rightarrow>\<^sub>d* n'\<close> obtain as where "parent_node n -as\<rightarrow>\<^sub>\<iota>* parent_node n'"
          by -(erule is_SDG_path_intra_CFG_path)
        with \<open>n = CFG_node (_Exit_)\<close> have "parent_node n' = (_Exit_)"
          by(fastforce dest:path_Exit_source simp:intra_path_def)
        with \<open>valid_SDG_node n'\<close> have "n' = CFG_node (_Exit_)"
          by(rule valid_SDG_node_parent_Exit)
        with \<open>n = CFG_node (_Exit_)\<close> show ?thesis by simp
      next
        case False
        with \<open>valid_SDG_node n\<close>
        obtain nsx where "CFG_node (_Entry_) cc-nsx\<rightarrow>\<^sub>d* n"
          by(erule Entry_cc_SDG_path_to_inner_node)
        hence "realizable (CFG_node (_Entry_)) nsx n" 
          by(rule cdep_SDG_path_realizable)
        with \<open>matched n ns' n'\<close>
        have "realizable (CFG_node (_Entry_)) (nsx@ns') n'"
          by -(rule realizable_Append_matched)
        with \<open>n \<in> set ns'\<close> show ?thesis by fastforce
      qed
    qed
  next
    fix nsx nsx' nx nx' p
    assume "ns = nsx@nx#nsx'" and "n irs-nsx\<rightarrow>\<^sub>d* nx"
      and "nx s-p\<rightarrow>\<^bsub>ret\<^esub> nx' \<or> (\<exists>V. nx s-p:V\<rightarrow>\<^bsub>out\<^esub> nx')" and "nx' is-nsx'\<rightarrow>\<^sub>d* n'"
    from \<open>nx s-p\<rightarrow>\<^bsub>ret\<^esub> nx' \<or> (\<exists>V. nx s-p:V\<rightarrow>\<^bsub>out\<^esub> nx')\<close>
    have "CFG_node (parent_node nx) s-p\<rightarrow>\<^bsub>ret\<^esub> CFG_node (parent_node nx')"
      by(fastforce elim:sum_SDG_edge.cases intro:sum_SDG_return_edge)
    then obtain a Q f where "valid_edge a" and "kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f"
      and "parent_node nx = sourcenode a" and "parent_node nx' = targetnode a"
      by(fastforce elim:sum_SDG_edge.cases)
    from \<open>valid_edge a\<close> \<open>kind a = Q\<hookleftarrow>\<^bsub>p\<^esub>f\<close> obtain a' Q' r' fs' 
      where "a \<in> get_return_edges a'" and "valid_edge a'" and "kind a' = Q':r'\<hookrightarrow>\<^bsub>p\<^esub>fs'"
      and "CFG_node (sourcenode a') s-p\<rightarrow>\<^bsub>sum\<^esub> CFG_node (targetnode a)"
      by(erule return_edge_determines_call_and_sum_edge)
    from \<open>valid_edge a'\<close> \<open>kind a' = Q':r'\<hookrightarrow>\<^bsub>p\<^esub>fs'\<close>
    have "CFG_node (sourcenode a') s-p\<rightarrow>\<^bsub>call\<^esub> CFG_node (targetnode a')"
      by(fastforce intro:sum_SDG_call_edge)
    from \<open>n irs-nsx\<rightarrow>\<^sub>d* nx\<close> \<open>nx s-p\<rightarrow>\<^bsub>ret\<^esub> nx' \<or> (\<exists>V. nx s-p:V\<rightarrow>\<^bsub>out\<^esub> nx')\<close>
    obtain m ms where "matched m ms nx'" and "n \<in> set ms"
      and "m s-p\<rightarrow>\<^bsub>sum\<^esub> CFG_node (parent_node nx')"
      by(fastforce elim:irs_SDG_path_matched)
    from \<open>nx' is-nsx'\<rightarrow>\<^sub>d* n'\<close> obtain ms' where "matched nx' ms' n'" 
      and "set nsx' \<subseteq> set ms'" by(erule is_SDG_path_matched)
    with \<open>matched m ms nx'\<close> have "matched m (ms@ms') n'" by -(rule matched_Append)
   from \<open>m s-p\<rightarrow>\<^bsub>sum\<^esub> CFG_node (parent_node nx')\<close> have "valid_SDG_node m"
      by(rule sum_SDG_edge_valid_SDG_node)
    hence "valid_node (parent_node m)" by(rule valid_SDG_CFG_node)
    thus ?thesis
    proof(cases "parent_node m = (_Exit_)")
      case True
      from \<open>m s-p\<rightarrow>\<^bsub>sum\<^esub> CFG_node (parent_node nx')\<close> obtain a where "valid_edge a" 
        and "sourcenode a = parent_node m"
        by(fastforce elim:sum_SDG_edge.cases)
      with True have False by -(rule Exit_source,simp_all)
      thus ?thesis by simp
    next
      case False
      with \<open>valid_SDG_node m\<close>
      obtain ms'' where "CFG_node (_Entry_) cc-ms''\<rightarrow>\<^sub>d* m"
        by(erule Entry_cc_SDG_path_to_inner_node)
      hence "realizable (CFG_node (_Entry_)) ms'' m" 
        by(rule cdep_SDG_path_realizable)
      with \<open>matched m (ms@ms') n'\<close>
      have "realizable (CFG_node (_Entry_)) (ms''@(ms@ms')) n'"
        by -(rule realizable_Append_matched)
      with \<open>n \<in> set ms\<close> show ?thesis by fastforce
    qed
  qed
  with \<open>n \<noteq> n'\<close> show "\<exists>ns'. realizable (CFG_node (_Entry_)) ns' n' \<and> n \<in> set ns'"
    by simp
qed

end

end
