chapter \<open>Dynamic Slicing\<close>

section \<open>Dynamic Program Dependence Graph\<close>

theory DynPDG imports 
  "../Basic/DynDataDependence" 
  "../Basic/CFGExit_wf" 
  "../Basic/DynStandardControlDependence"
  "../Basic/DynWeakControlDependence"
begin

subsection \<open>The dynamic PDG\<close>

locale DynPDG = 
  CFGExit_wf sourcenode targetnode kind valid_edge Entry Def Use state_val Exit
  for sourcenode :: "'edge \<Rightarrow> 'node" and targetnode :: "'edge \<Rightarrow> 'node"
  and kind :: "'edge \<Rightarrow> 'state edge_kind" and valid_edge :: "'edge \<Rightarrow> bool"
  and Entry :: "'node" ("'('_Entry'_')") and Def :: "'node \<Rightarrow> 'var set"
  and Use :: "'node \<Rightarrow> 'var set" and state_val :: "'state \<Rightarrow> 'var \<Rightarrow> 'val"
  and Exit :: "'node" ("'('_Exit'_')") +
  fixes dyn_control_dependence :: "'node \<Rightarrow> 'node \<Rightarrow> 'edge list \<Rightarrow> bool" 
("_ controls _ via _" [51,0,0])
  assumes Exit_not_dyn_control_dependent:"n controls n' via as \<Longrightarrow> n' \<noteq> (_Exit_)"
  assumes dyn_control_dependence_path:
  "n controls n' via as  \<Longrightarrow> n -as\<rightarrow>* n' \<and> as \<noteq> []"

begin

inductive cdep_edge :: "'node \<Rightarrow> 'edge list \<Rightarrow> 'node \<Rightarrow> bool" 
    ("_ -_\<rightarrow>\<^sub>c\<^sub>d _" [51,0,0] 80)
  and ddep_edge :: "'node \<Rightarrow> 'var \<Rightarrow> 'edge list \<Rightarrow> 'node \<Rightarrow> bool"
    ("_ -'{_'}_\<rightarrow>\<^sub>d\<^sub>d _" [51,0,0,0] 80)
  and DynPDG_edge :: "'node \<Rightarrow> 'var option \<Rightarrow> 'edge list \<Rightarrow> 'node \<Rightarrow> bool"

where
      \<comment> \<open>Syntax\<close>
  "n -as\<rightarrow>\<^sub>c\<^sub>d n' == DynPDG_edge n None as n'"
  | "n -{V}as\<rightarrow>\<^sub>d\<^sub>d n' == DynPDG_edge n (Some V) as n'"

      \<comment> \<open>Rules\<close>
  | DynPDG_cdep_edge:
  "n controls n' via as \<Longrightarrow> n -as\<rightarrow>\<^sub>c\<^sub>d n'"

  | DynPDG_ddep_edge:
  "n influences V in n' via as \<Longrightarrow> n -{V}as\<rightarrow>\<^sub>d\<^sub>d n'"


inductive DynPDG_path :: "'node \<Rightarrow> 'edge list \<Rightarrow> 'node \<Rightarrow> bool"
("_ -_\<rightarrow>\<^sub>d* _" [51,0,0] 80) 

where DynPDG_path_Nil:
  "valid_node n \<Longrightarrow> n -[]\<rightarrow>\<^sub>d* n"

  | DynPDG_path_Append_cdep:
  "\<lbrakk>n -as\<rightarrow>\<^sub>d* n''; n'' -as'\<rightarrow>\<^sub>c\<^sub>d n'\<rbrakk> \<Longrightarrow> n -as@as'\<rightarrow>\<^sub>d* n'"

  | DynPDG_path_Append_ddep:
  "\<lbrakk>n -as\<rightarrow>\<^sub>d* n''; n'' -{V}as'\<rightarrow>\<^sub>d\<^sub>d n'\<rbrakk> \<Longrightarrow> n -as@as'\<rightarrow>\<^sub>d* n'"


lemma DynPDG_empty_path_eq_nodes:"n -[]\<rightarrow>\<^sub>d* n' \<Longrightarrow> n = n'"
apply - apply(erule DynPDG_path.cases) 
  apply simp
 apply(auto elim:DynPDG_edge.cases dest:dyn_control_dependence_path)
by(auto elim:DynPDG_edge.cases simp:dyn_data_dependence_def)


lemma DynPDG_path_cdep:"n -as\<rightarrow>\<^sub>c\<^sub>d n' \<Longrightarrow> n -as\<rightarrow>\<^sub>d* n'"
apply(subgoal_tac "n -[]@as\<rightarrow>\<^sub>d* n'")
 apply simp
apply(rule DynPDG_path_Append_cdep, rule DynPDG_path_Nil)
by(auto elim!:DynPDG_edge.cases dest:dyn_control_dependence_path path_valid_node)

lemma DynPDG_path_ddep:"n -{V}as\<rightarrow>\<^sub>d\<^sub>d n' \<Longrightarrow> n -as\<rightarrow>\<^sub>d* n'"
apply(subgoal_tac "n -[]@as\<rightarrow>\<^sub>d* n'")
 apply simp
apply(rule DynPDG_path_Append_ddep, rule DynPDG_path_Nil)
by(auto elim!:DynPDG_edge.cases dest:path_valid_node simp:dyn_data_dependence_def)

lemma DynPDG_path_Append:
  "\<lbrakk>n'' -as'\<rightarrow>\<^sub>d* n'; n -as\<rightarrow>\<^sub>d* n''\<rbrakk> \<Longrightarrow> n -as@as'\<rightarrow>\<^sub>d* n'"
apply(induct rule:DynPDG_path.induct)
  apply(auto intro:DynPDG_path.intros)
 apply(rotate_tac 1,drule DynPDG_path_Append_cdep,simp+)
apply(rotate_tac 1,drule DynPDG_path_Append_ddep,simp+)
done


lemma DynPDG_path_Exit:"\<lbrakk>n -as\<rightarrow>\<^sub>d* n'; n' = (_Exit_)\<rbrakk> \<Longrightarrow> n = (_Exit_)"
apply(induct rule:DynPDG_path.induct)
by(auto elim:DynPDG_edge.cases dest:Exit_not_dyn_control_dependent 
        simp:dyn_data_dependence_def)


lemma DynPDG_path_not_inner:
  "\<lbrakk>n -as\<rightarrow>\<^sub>d* n'; \<not> inner_node n'\<rbrakk> \<Longrightarrow> n = n'"
proof(induct rule:DynPDG_path.induct)
  case (DynPDG_path_Nil n)
  thus ?case by simp
next
  case (DynPDG_path_Append_cdep n as n'' as' n')
  from \<open>n'' -as'\<rightarrow>\<^sub>c\<^sub>d n'\<close> \<open>\<not> inner_node n'\<close> have False
    apply -
    apply(erule DynPDG_edge.cases) apply(auto simp:inner_node_def)
      apply(fastforce dest:dyn_control_dependence_path path_valid_node)
     apply(fastforce dest:dyn_control_dependence_path path_valid_node)
    by(fastforce dest:Exit_not_dyn_control_dependent)
  thus ?case by simp
next
  case (DynPDG_path_Append_ddep n as n'' V as' n')
  from \<open>n'' -{V}as'\<rightarrow>\<^sub>d\<^sub>d n'\<close> \<open>\<not> inner_node n'\<close> have False
    apply -
    apply(erule DynPDG_edge.cases) 
    by(auto dest:path_valid_node simp:inner_node_def dyn_data_dependence_def)
  thus ?case by simp
qed


lemma DynPDG_cdep_edge_CFG_path:
  assumes "n -as\<rightarrow>\<^sub>c\<^sub>d n'" shows "n -as\<rightarrow>* n'" and "as \<noteq> []"
  using \<open>n -as\<rightarrow>\<^sub>c\<^sub>d n'\<close>
  by(auto elim:DynPDG_edge.cases dest:dyn_control_dependence_path)

lemma DynPDG_ddep_edge_CFG_path:
  assumes "n -{V}as\<rightarrow>\<^sub>d\<^sub>d n'" shows "n -as\<rightarrow>* n'" and "as \<noteq> []"
  using \<open>n -{V}as\<rightarrow>\<^sub>d\<^sub>d n'\<close>
  by(auto elim:DynPDG_edge.cases simp:dyn_data_dependence_def)

lemma DynPDG_path_CFG_path:
  "n -as\<rightarrow>\<^sub>d* n' \<Longrightarrow> n -as\<rightarrow>* n'"
proof(induct rule:DynPDG_path.induct)
  case DynPDG_path_Nil thus ?case by(rule empty_path)
next
  case (DynPDG_path_Append_cdep n as n'' as' n')
  from \<open>n'' -as'\<rightarrow>\<^sub>c\<^sub>d n'\<close> have "n'' -as'\<rightarrow>* n'"
    by(rule DynPDG_cdep_edge_CFG_path(1))
  with \<open>n -as\<rightarrow>* n''\<close> show ?case by(rule path_Append)
next
  case (DynPDG_path_Append_ddep n as n'' V as' n')
  from \<open>n'' -{V}as'\<rightarrow>\<^sub>d\<^sub>d n'\<close> have "n'' -as'\<rightarrow>* n'"
    by(rule DynPDG_ddep_edge_CFG_path(1))
  with \<open>n -as\<rightarrow>* n''\<close> show ?case by(rule path_Append)
qed


lemma DynPDG_path_split: 
  "n -as\<rightarrow>\<^sub>d* n' \<Longrightarrow>
  (as = [] \<and> n = n') \<or> 
  (\<exists>n'' asx asx'. (n -asx\<rightarrow>\<^sub>c\<^sub>d n'') \<and> (n'' -asx'\<rightarrow>\<^sub>d* n') \<and> 
        (as = asx@asx')) \<or>
  (\<exists>n'' V asx asx'. (n -{V}asx\<rightarrow>\<^sub>d\<^sub>d n'') \<and> (n'' -asx'\<rightarrow>\<^sub>d* n') \<and> 
        (as = asx@asx'))"
proof(induct rule:DynPDG_path.induct)
  case (DynPDG_path_Nil n) thus ?case by auto
next
  case (DynPDG_path_Append_cdep n as n'' as' n')
  note IH = \<open>as = [] \<and> n = n'' \<or>
    (\<exists>nx asx asx'. n -asx\<rightarrow>\<^sub>c\<^sub>d nx \<and> nx -asx'\<rightarrow>\<^sub>d* n'' \<and> as = asx@asx') \<or>
    (\<exists>nx V asx asx'. n -{V}asx\<rightarrow>\<^sub>d\<^sub>d nx \<and> nx -asx'\<rightarrow>\<^sub>d* n'' \<and> as = asx@asx')\<close>
  from IH show ?case
  proof
    assume "as = [] \<and> n = n''"
    with \<open>n'' -as'\<rightarrow>\<^sub>c\<^sub>d n'\<close> have "valid_node n'"
      by(fastforce intro:path_valid_node(2) DynPDG_path_CFG_path 
                        DynPDG_path_cdep)
    with \<open>as = [] \<and> n = n''\<close> \<open>n'' -as'\<rightarrow>\<^sub>c\<^sub>d n'\<close>
    have "\<exists>n'' asx asx'. n -asx\<rightarrow>\<^sub>c\<^sub>d n'' \<and> n'' -asx'\<rightarrow>\<^sub>d* n' \<and> as@as' = asx@asx'"
      by(auto intro:DynPDG_path_Nil)
    thus ?thesis by simp
  next
    assume "(\<exists>nx asx asx'. n -asx\<rightarrow>\<^sub>c\<^sub>d nx \<and> nx -asx'\<rightarrow>\<^sub>d* n'' \<and> as = asx@asx') \<or>
      (\<exists>nx V asx asx'. n -{V}asx\<rightarrow>\<^sub>d\<^sub>d nx \<and> nx -asx'\<rightarrow>\<^sub>d* n'' \<and> as = asx@asx')"
    thus ?thesis
    proof
      assume "\<exists>nx asx asx'. n -asx\<rightarrow>\<^sub>c\<^sub>d nx \<and> nx -asx'\<rightarrow>\<^sub>d* n'' \<and> as = asx@asx'"
      then obtain nx asx asx' where "n -asx\<rightarrow>\<^sub>c\<^sub>d nx" and "nx -asx'\<rightarrow>\<^sub>d* n''"
        and "as = asx@asx'" by auto
      from \<open>n'' -as'\<rightarrow>\<^sub>c\<^sub>d n'\<close> have "n'' -as'\<rightarrow>\<^sub>d* n'" by(rule DynPDG_path_cdep)
      with \<open>nx -asx'\<rightarrow>\<^sub>d* n''\<close> have "nx -asx'@as'\<rightarrow>\<^sub>d* n'"
        by(fastforce intro:DynPDG_path_Append)
      with \<open>n -asx\<rightarrow>\<^sub>c\<^sub>d nx\<close> \<open>as = asx@asx'\<close>
      have "\<exists>n'' asx asx'. n -asx\<rightarrow>\<^sub>c\<^sub>d n'' \<and> n'' -asx'\<rightarrow>\<^sub>d* n' \<and> as@as' = asx@asx'"
        by auto
      thus ?thesis by simp
    next
      assume "\<exists>nx V asx asx'. n -{V}asx\<rightarrow>\<^sub>d\<^sub>d nx \<and> nx -asx'\<rightarrow>\<^sub>d* n'' \<and> as = asx@asx'"
      then obtain nx V asx asx' where "n -{V}asx\<rightarrow>\<^sub>d\<^sub>d nx" and "nx -asx'\<rightarrow>\<^sub>d* n''"
        and "as = asx@asx'" by auto
      from \<open>n'' -as'\<rightarrow>\<^sub>c\<^sub>d n'\<close> have "n'' -as'\<rightarrow>\<^sub>d* n'" by(rule DynPDG_path_cdep)
      with \<open>nx -asx'\<rightarrow>\<^sub>d* n''\<close> have "nx -asx'@as'\<rightarrow>\<^sub>d* n'"
        by(fastforce intro:DynPDG_path_Append)
      with \<open>n -{V}asx\<rightarrow>\<^sub>d\<^sub>d nx\<close> \<open>as = asx@asx'\<close>
      have "\<exists>n'' V asx asx'. n -{V}asx\<rightarrow>\<^sub>d\<^sub>d n'' \<and> n'' -asx'\<rightarrow>\<^sub>d* n' \<and> as@as' = asx@asx'"
        by auto
      thus ?thesis by simp
    qed
  qed
next
  case (DynPDG_path_Append_ddep n as n'' V as' n')
  note IH = \<open>as = [] \<and> n = n'' \<or>
    (\<exists>nx asx asx'. n -asx\<rightarrow>\<^sub>c\<^sub>d nx \<and> nx -asx'\<rightarrow>\<^sub>d* n'' \<and> as = asx@asx') \<or>
    (\<exists>nx V asx asx'. n -{V}asx\<rightarrow>\<^sub>d\<^sub>d nx \<and> nx -asx'\<rightarrow>\<^sub>d* n'' \<and> as = asx@asx')\<close>
  from IH show ?case
  proof
    assume "as = [] \<and> n = n''"
    with \<open>n'' -{V}as'\<rightarrow>\<^sub>d\<^sub>d n'\<close> have "valid_node n'"
      by(fastforce intro:path_valid_node(2) DynPDG_path_CFG_path 
                        DynPDG_path_ddep)
    with \<open>as = [] \<and> n = n''\<close> \<open>n'' -{V}as'\<rightarrow>\<^sub>d\<^sub>d n'\<close>
    have "\<exists>n'' V asx asx'. n -{V}asx\<rightarrow>\<^sub>d\<^sub>d n'' \<and> n'' -asx'\<rightarrow>\<^sub>d* n' \<and> as@as' = asx@asx'"
      by(fastforce intro:DynPDG_path_Nil)
    thus ?thesis by simp
  next
    assume "(\<exists>nx asx asx'. n -asx\<rightarrow>\<^sub>c\<^sub>d nx \<and> nx -asx'\<rightarrow>\<^sub>d* n'' \<and> as = asx@asx') \<or>
      (\<exists>nx V asx asx'. n -{V}asx\<rightarrow>\<^sub>d\<^sub>d nx \<and> nx -asx'\<rightarrow>\<^sub>d* n'' \<and> as = asx@asx')"
    thus ?thesis
    proof
      assume "\<exists>nx asx asx'. n -asx\<rightarrow>\<^sub>c\<^sub>d nx \<and> nx -asx'\<rightarrow>\<^sub>d* n'' \<and> as = asx@asx'"
      then obtain nx asx asx' where "n -asx\<rightarrow>\<^sub>c\<^sub>d nx" and "nx -asx'\<rightarrow>\<^sub>d* n''"
        and "as = asx@asx'" by auto
      from \<open>n'' -{V}as'\<rightarrow>\<^sub>d\<^sub>d n'\<close> have "n'' -as'\<rightarrow>\<^sub>d* n'" by(rule DynPDG_path_ddep)
      with \<open>nx -asx'\<rightarrow>\<^sub>d* n''\<close> have "nx -asx'@as'\<rightarrow>\<^sub>d* n'"
        by(fastforce intro:DynPDG_path_Append)
      with \<open>n -asx\<rightarrow>\<^sub>c\<^sub>d nx\<close> \<open>as = asx@asx'\<close>
      have "\<exists>n'' asx asx'. n -asx\<rightarrow>\<^sub>c\<^sub>d n'' \<and> n'' -asx'\<rightarrow>\<^sub>d* n' \<and> as@as' = asx@asx'"
        by auto
      thus ?thesis by simp
    next
      assume "\<exists>nx V asx asx'. n -{V}asx\<rightarrow>\<^sub>d\<^sub>d nx \<and> nx -asx'\<rightarrow>\<^sub>d* n'' \<and> as = asx@asx'"
      then obtain nx V' asx asx' where "n -{V'}asx\<rightarrow>\<^sub>d\<^sub>d nx" and "nx -asx'\<rightarrow>\<^sub>d* n''"
        and "as = asx@asx'" by auto
      from \<open>n'' -{V}as'\<rightarrow>\<^sub>d\<^sub>d n'\<close> have "n'' -as'\<rightarrow>\<^sub>d* n'" by(rule DynPDG_path_ddep)
      with \<open>nx -asx'\<rightarrow>\<^sub>d* n''\<close> have "nx -asx'@as'\<rightarrow>\<^sub>d* n'"
        by(fastforce intro:DynPDG_path_Append)
      with \<open>n -{V'}asx\<rightarrow>\<^sub>d\<^sub>d nx\<close> \<open>as = asx@asx'\<close>
      have "\<exists>n'' V asx asx'. n -{V}asx\<rightarrow>\<^sub>d\<^sub>d n'' \<and> n'' -asx'\<rightarrow>\<^sub>d* n' \<and> as@as' = asx@asx'"
        by auto
      thus ?thesis by simp
    qed
  qed
qed


lemma DynPDG_path_rev_cases [consumes 1,
  case_names DynPDG_path_Nil DynPDG_path_cdep_Append DynPDG_path_ddep_Append]:
  "\<lbrakk>n -as\<rightarrow>\<^sub>d* n'; \<lbrakk>as = []; n = n'\<rbrakk> \<Longrightarrow> Q;
    \<And>n'' asx asx'. \<lbrakk>n -asx\<rightarrow>\<^sub>c\<^sub>d n''; n'' -asx'\<rightarrow>\<^sub>d* n'; 
                       as = asx@asx'\<rbrakk> \<Longrightarrow> Q;
    \<And>V n'' asx asx'. \<lbrakk>n -{V}asx\<rightarrow>\<^sub>d\<^sub>d n''; n'' -asx'\<rightarrow>\<^sub>d* n'; 
                       as = asx@asx'\<rbrakk> \<Longrightarrow> Q\<rbrakk>
  \<Longrightarrow> Q"
by(blast dest:DynPDG_path_split)



lemma DynPDG_ddep_edge_no_shorter_ddep_edge:
  assumes ddep:"n -{V}as\<rightarrow>\<^sub>d\<^sub>d n'"
  shows "\<forall>as' a as''. tl as = as'@a#as'' \<longrightarrow> \<not> sourcenode a -{V}a#as''\<rightarrow>\<^sub>d\<^sub>d n'"
proof -
  from ddep have influence:"n influences V in n' via as"
    by(auto elim!:DynPDG_edge.cases)
  then obtain  a asx where as:"as = a#asx"
    and notin:"n \<notin> set (sourcenodes asx)"
    by(auto dest:dyn_influence_source_notin_tl_edges simp:dyn_data_dependence_def)
  from influence as
  have imp:"\<forall>nx \<in> set (sourcenodes asx). V \<notin> Def nx"
    by(auto simp:dyn_data_dependence_def)
  { fix as' a' as'' 
    assume eq:"tl as = as'@a'#as''"
      and ddep':"sourcenode a' -{V}a'#as''\<rightarrow>\<^sub>d\<^sub>d n'"
    from eq as notin have noteq:"sourcenode a' \<noteq> n" by(auto simp:sourcenodes_def)
    from ddep' have "V \<in> Def (sourcenode a')"
      by(auto elim!:DynPDG_edge.cases simp:dyn_data_dependence_def)
    with eq as noteq imp have False by(auto simp:sourcenodes_def) }
  thus ?thesis by blast
qed



lemma no_ddep_same_state:
  assumes path:"n -as\<rightarrow>* n'" and Uses:"V \<in> Use n'" and preds:"preds (kinds as) s"
  and no_dep:"\<forall>as' a as''. as = as'@a#as'' \<longrightarrow> \<not> sourcenode a -{V}a#as''\<rightarrow>\<^sub>d\<^sub>d n'"
  shows "state_val (transfers (kinds as) s) V = state_val s V"
proof -
  { fix n''
    assume inset:"n'' \<in> set (sourcenodes as)" and Defs:"V \<in> Def n''"
    hence "\<exists>nx \<in> set (sourcenodes as). V \<in> Def nx" by auto
    then obtain nx ns' ns'' where nodes:"sourcenodes as = ns'@nx#ns''"
        and Defs':"V \<in> Def nx" and notDef:"\<forall>nx' \<in> set ns''. V \<notin> Def nx'"
      by(fastforce elim!:rightmost_element_property)
    from nodes obtain as' a as''
      where as'':"sourcenodes as'' = ns''" and as:"as=as'@a#as''"
      and source:"sourcenode a = nx"
      by(fastforce elim:map_append_append_maps simp:sourcenodes_def)
    from as path have path':"sourcenode a -a#as''\<rightarrow>* n'"
      by(fastforce dest:path_split_second)
    from notDef as'' source
    have "\<forall>n'' \<in> set (sourcenodes as''). V \<notin> Def n''"
      by(auto simp:sourcenodes_def)
    with path' Defs' Uses source
    have influence:"nx influences V in n' via (a#as'')"
      by(simp add:dyn_data_dependence_def)
    hence "nx \<notin> set (sourcenodes as'')" by(rule dyn_influence_source_notin_tl_edges)
    with influence source
    have "\<exists>asx a'. sourcenode a' -{V}a'#asx\<rightarrow>\<^sub>d\<^sub>d n' \<and> sourcenode a' = nx \<and>
          (\<exists>asx'. a#as'' = asx'@a'#asx)"
      by(fastforce intro:DynPDG_ddep_edge)
    with nodes no_dep as have False by(auto simp:sourcenodes_def) }
  hence "\<forall>n \<in> set (sourcenodes as). V \<notin> Def n" by auto
  with wf path preds show ?thesis by(fastforce intro:CFG_path_no_Def_equal)
qed


lemma DynPDG_ddep_edge_only_first_edge:
  "\<lbrakk>n -{V}a#as\<rightarrow>\<^sub>d\<^sub>d n'; preds (kinds (a#as)) s\<rbrakk> \<Longrightarrow> 
    state_val (transfers (kinds (a#as)) s) V = state_val (transfer (kind a) s) V"
  apply -
  apply(erule DynPDG_edge.cases)
  apply auto
  apply(frule dyn_influence_Cons_source)
  apply(frule dyn_influence_source_notin_tl_edges)
  by(erule dyn_influence_only_first_edge)


lemma Use_value_change_implies_DynPDG_ddep_edge:
  assumes "n -as\<rightarrow>* n'" and "V \<in> Use n'" and "preds (kinds as) s" 
  and "preds (kinds as) s'" and "state_val s V = state_val s' V"
  and "state_val (transfers (kinds as) s) V \<noteq> 
             state_val (transfers (kinds as) s') V"
  obtains as' a as'' where "as = as'@a#as''"
  and "sourcenode a -{V}a#as''\<rightarrow>\<^sub>d\<^sub>d n'"
  and "state_val (transfers (kinds as) s) V = 
       state_val (transfers (kinds (as'@[a])) s) V"
  and "state_val (transfers (kinds as) s') V = 
       state_val (transfers (kinds (as'@[a])) s') V"
proof(atomize_elim)
  show "\<exists>as' a as''. as = as'@a#as'' \<and>
                     sourcenode a -{V}a#as''\<rightarrow>\<^sub>d\<^sub>d n' \<and>
             state_val (transfers (kinds as) s) V = 
             state_val (transfers (kinds (as'@[a])) s) V \<and>
             state_val (transfers (kinds as) s') V = 
             state_val (transfers (kinds (as'@[a])) s') V"
  proof(cases "\<forall>as' a as''. as = as'@a#as'' \<longrightarrow>
                 \<not> sourcenode a -{V}a#as''\<rightarrow>\<^sub>d\<^sub>d n'")
    case True
    with \<open>n -as\<rightarrow>* n'\<close> \<open>V \<in> Use n'\<close> \<open>preds (kinds as) s\<close> \<open>preds (kinds as) s'\<close>
    have "state_val (transfers (kinds as) s) V = state_val s V"
      and "state_val (transfers (kinds as) s') V = state_val s' V"
      by(auto intro:no_ddep_same_state)
    with \<open>state_val s V = state_val s' V\<close> 
      \<open>state_val (transfers (kinds as) s) V \<noteq> state_val (transfers (kinds as) s') V\<close>
    show ?thesis by simp
  next
    case False
    then obtain as' a as'' where [simp]:"as = as'@a#as''"
      and "sourcenode a -{V}a#as''\<rightarrow>\<^sub>d\<^sub>d n'" by auto
    from \<open>preds (kinds as) s\<close> have "preds (kinds (a#as'')) (transfers (kinds as') s)"
      by(simp add:kinds_def preds_split)
    with \<open>sourcenode a -{V}a#as''\<rightarrow>\<^sub>d\<^sub>d n'\<close> have all:
      "state_val (transfers (kinds (a#as'')) (transfers (kinds as') s)) V = 
       state_val (transfer (kind a) (transfers (kinds as') s)) V"
      by(auto dest!:DynPDG_ddep_edge_only_first_edge)
    from \<open>preds (kinds as) s'\<close> 
    have "preds (kinds (a#as'')) (transfers (kinds as') s')"
      by(simp add:kinds_def preds_split)
    with \<open>sourcenode a -{V}a#as''\<rightarrow>\<^sub>d\<^sub>d n'\<close> have all':
      "state_val (transfers (kinds (a#as'')) (transfers (kinds as') s')) V = 
       state_val (transfer (kind a) (transfers (kinds as') s')) V"
      by(auto dest!:DynPDG_ddep_edge_only_first_edge)
    hence eq:"\<And>s. transfers (kinds as) s =
      transfers (kinds (a#as'')) (transfers (kinds as') s)"
      by(simp add:transfers_split[THEN sym] kinds_def)
    with all have "state_val (transfers (kinds as) s) V = 
                   state_val (transfers (kinds (as'@[a])) s) V"
      by(simp add:transfers_split kinds_def)
    moreover
    from eq all' have "state_val (transfers (kinds as) s') V = 
                       state_val (transfers (kinds (as'@[a])) s') V"
      by(simp add:transfers_split kinds_def)
    ultimately show ?thesis using \<open>sourcenode a -{V}a#as''\<rightarrow>\<^sub>d\<^sub>d n'\<close> by simp blast
  qed
qed


end


subsection \<open>Instantiate dynamic PDG\<close>

subsubsection \<open>Standard control dependence\<close>

locale DynStandardControlDependencePDG =
  Postdomination sourcenode targetnode kind valid_edge Entry Exit +
  CFGExit_wf sourcenode targetnode kind valid_edge Entry Def Use state_val Exit
  for sourcenode :: "'edge \<Rightarrow> 'node" and targetnode :: "'edge \<Rightarrow> 'node"
  and kind :: "'edge \<Rightarrow> 'state edge_kind" and valid_edge :: "'edge \<Rightarrow> bool"
  and Entry :: "'node" ("'('_Entry'_')") and Def :: "'node \<Rightarrow> 'var set"
  and Use :: "'node \<Rightarrow> 'var set" and state_val :: "'state \<Rightarrow> 'var \<Rightarrow> 'val"
  and Exit :: "'node" ("'('_Exit'_')")

begin

lemma DynPDG_scd:
  "DynPDG sourcenode targetnode kind valid_edge (_Entry_) 
          Def Use state_val (_Exit_) dyn_standard_control_dependence"
proof(unfold_locales)
  fix n n' as assume "n controls\<^sub>s n' via as"
  show "n' \<noteq> (_Exit_)"
  proof
    assume "n' = (_Exit_)"
    with \<open>n controls\<^sub>s n' via as\<close> show False
      by(fastforce intro:Exit_not_dyn_standard_control_dependent)
  qed
next
  fix n n' as assume "n controls\<^sub>s n' via as"
  thus "n -as\<rightarrow>* n' \<and> as \<noteq> []"
    by(fastforce simp:dyn_standard_control_dependence_def)
qed


end

subsubsection \<open>Weak control dependence\<close>

locale DynWeakControlDependencePDG = 
  StrongPostdomination sourcenode targetnode kind valid_edge Entry Exit +
  CFGExit_wf sourcenode targetnode kind valid_edge Entry Def Use state_val Exit
  for sourcenode :: "'edge \<Rightarrow> 'node" and targetnode :: "'edge \<Rightarrow> 'node"
  and kind :: "'edge \<Rightarrow> 'state edge_kind" and valid_edge :: "'edge \<Rightarrow> bool"
  and Entry :: "'node" ("'('_Entry'_')") and Def :: "'node \<Rightarrow> 'var set"
  and Use :: "'node \<Rightarrow> 'var set" and state_val :: "'state \<Rightarrow> 'var \<Rightarrow> 'val"
  and Exit :: "'node" ("'('_Exit'_')")

begin

lemma DynPDG_wcd:
  "DynPDG sourcenode targetnode kind valid_edge (_Entry_) 
          Def Use state_val (_Exit_) dyn_weak_control_dependence"
proof(unfold_locales)
  fix n n' as assume "n weakly controls n' via as"
  show "n' \<noteq> (_Exit_)"
  proof
    assume "n' = (_Exit_)"
    with \<open>n weakly controls n' via as\<close> show False
      by(fastforce intro:Exit_not_dyn_weak_control_dependent)
  qed
next
  fix n n' as assume "n weakly controls n' via as"
  thus "n -as\<rightarrow>* n' \<and> as \<noteq> []"
    by(fastforce simp:dyn_weak_control_dependence_def)
qed


end


subsection \<open>Data slice\<close>

definition (in CFG) empty_control_dependence :: "'node \<Rightarrow> 'node \<Rightarrow> 'edge list \<Rightarrow> bool"
where "empty_control_dependence n n' as \<equiv> False"

lemma (in CFGExit_wf) DynPDG_scd:
  "DynPDG sourcenode targetnode kind valid_edge (_Entry_)
          Def Use state_val  (_Exit_) empty_control_dependence"
proof(unfold_locales)
  fix n n' as assume "empty_control_dependence n n' as"
  thus "n' \<noteq> (_Exit_)" by(simp add:empty_control_dependence_def)
next
  fix n n' as assume "empty_control_dependence n n' as"
  thus "n -as\<rightarrow>* n' \<and> as \<noteq> []" by(simp add:empty_control_dependence_def)
qed

end
