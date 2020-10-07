section \<open>Program Dependence Graph\<close>

theory PDG imports 
  DataDependence 
  StandardControlDependence
  WeakControlDependence
  "../Basic/CFGExit_wf" 
begin

locale PDG = 
  CFGExit_wf sourcenode targetnode kind valid_edge Entry Def Use state_val Exit
  for sourcenode :: "'edge \<Rightarrow> 'node" and targetnode :: "'edge \<Rightarrow> 'node"
  and kind :: "'edge \<Rightarrow> 'state edge_kind" and valid_edge :: "'edge \<Rightarrow> bool"
  and Entry :: "'node" ("'('_Entry'_')") and Def :: "'node \<Rightarrow> 'var set"
  and Use :: "'node \<Rightarrow> 'var set" and state_val :: "'state \<Rightarrow> 'var \<Rightarrow> 'val"
  and Exit :: "'node" ("'('_Exit'_')") +
  fixes control_dependence :: "'node \<Rightarrow> 'node \<Rightarrow> bool" 
("_ controls _ " [51,0])
  assumes Exit_not_control_dependent:"n controls n' \<Longrightarrow> n' \<noteq> (_Exit_)"
  assumes control_dependence_path:
  "n controls n' 
  \<Longrightarrow> \<exists>as. CFG.path sourcenode targetnode valid_edge n as n' \<and> as \<noteq> []"

begin


inductive cdep_edge :: "'node \<Rightarrow> 'node \<Rightarrow> bool" 
    ("_ \<longrightarrow>\<^sub>c\<^sub>d _" [51,0] 80)
  and ddep_edge :: "'node \<Rightarrow> 'var \<Rightarrow> 'node \<Rightarrow> bool"
    ("_ -_\<rightarrow>\<^sub>d\<^sub>d _" [51,0,0] 80)
  and PDG_edge :: "'node \<Rightarrow> 'var option \<Rightarrow> 'node \<Rightarrow> bool"

where
    (* Syntax *)
  "n \<longrightarrow>\<^sub>c\<^sub>d n' == PDG_edge n None n'"
  | "n -V\<rightarrow>\<^sub>d\<^sub>d n' == PDG_edge n (Some V) n'"

    (* Rules *)
  | PDG_cdep_edge:
  "n controls n' \<Longrightarrow> n \<longrightarrow>\<^sub>c\<^sub>d n'"

  | PDG_ddep_edge:
  "n influences V in n' \<Longrightarrow> n -V\<rightarrow>\<^sub>d\<^sub>d n'"


inductive PDG_path :: "'node \<Rightarrow> 'node \<Rightarrow> bool"
("_ \<longrightarrow>\<^sub>d* _" [51,0] 80) 

where PDG_path_Nil:
  "valid_node n \<Longrightarrow> n \<longrightarrow>\<^sub>d* n"

  | PDG_path_Append_cdep:
  "\<lbrakk>n \<longrightarrow>\<^sub>d* n''; n'' \<longrightarrow>\<^sub>c\<^sub>d n'\<rbrakk> \<Longrightarrow> n \<longrightarrow>\<^sub>d* n'"

  | PDG_path_Append_ddep:
  "\<lbrakk>n \<longrightarrow>\<^sub>d* n''; n'' -V\<rightarrow>\<^sub>d\<^sub>d n'\<rbrakk> \<Longrightarrow> n \<longrightarrow>\<^sub>d* n'"


lemma PDG_path_cdep:"n \<longrightarrow>\<^sub>c\<^sub>d n' \<Longrightarrow> n \<longrightarrow>\<^sub>d* n'"
apply -
apply(rule PDG_path_Append_cdep, rule PDG_path_Nil)
by(auto elim!:PDG_edge.cases dest:control_dependence_path path_valid_node)

lemma PDG_path_ddep:"n -V\<rightarrow>\<^sub>d\<^sub>d n' \<Longrightarrow> n \<longrightarrow>\<^sub>d* n'"
apply -
apply(rule PDG_path_Append_ddep, rule PDG_path_Nil)
by(auto elim!:PDG_edge.cases dest:path_valid_node simp:data_dependence_def)

lemma PDG_path_Append:
  "\<lbrakk>n'' \<longrightarrow>\<^sub>d* n'; n \<longrightarrow>\<^sub>d* n''\<rbrakk> \<Longrightarrow> n \<longrightarrow>\<^sub>d* n'"
by(induct rule:PDG_path.induct,auto intro:PDG_path.intros)


lemma PDG_cdep_edge_CFG_path:
  assumes "n \<longrightarrow>\<^sub>c\<^sub>d n'" obtains as where "n -as\<rightarrow>* n'" and "as \<noteq> []"
  using \<open>n \<longrightarrow>\<^sub>c\<^sub>d n'\<close>
  by(auto elim:PDG_edge.cases dest:control_dependence_path)

lemma PDG_ddep_edge_CFG_path:
  assumes "n -V\<rightarrow>\<^sub>d\<^sub>d n'" obtains as where "n -as\<rightarrow>* n'" and "as \<noteq> []"
  using \<open>n -V\<rightarrow>\<^sub>d\<^sub>d n'\<close>
  by(auto elim!:PDG_edge.cases simp:data_dependence_def)

lemma PDG_path_CFG_path:
  assumes "n \<longrightarrow>\<^sub>d* n'" obtains as where "n -as\<rightarrow>* n'"
proof(atomize_elim)
  from \<open>n \<longrightarrow>\<^sub>d* n'\<close> show "\<exists>as. n -as\<rightarrow>* n'"
  proof(induct rule:PDG_path.induct)
    case (PDG_path_Nil n)
    hence "n -[]\<rightarrow>* n" by(rule empty_path)
    thus ?case by blast
  next
    case (PDG_path_Append_cdep n n'' n')
    from \<open>n'' \<longrightarrow>\<^sub>c\<^sub>d n'\<close> obtain as where "n'' -as\<rightarrow>* n'"
      by(fastforce elim:PDG_cdep_edge_CFG_path)
    with \<open>\<exists>as. n -as\<rightarrow>* n''\<close> obtain as' where "n -as'@as\<rightarrow>* n'"
      by(auto dest:path_Append)
    thus ?case by blast
  next
    case (PDG_path_Append_ddep n n'' V n')
    from \<open>n'' -V\<rightarrow>\<^sub>d\<^sub>d n'\<close> obtain as where "n'' -as\<rightarrow>* n'"
      by(fastforce elim:PDG_ddep_edge_CFG_path)
    with \<open>\<exists>as. n -as\<rightarrow>* n''\<close> obtain as' where "n -as'@as\<rightarrow>* n'"
      by(auto dest:path_Append)
    thus ?case by blast
  qed
qed


lemma PDG_path_Exit:"\<lbrakk>n \<longrightarrow>\<^sub>d* n'; n' = (_Exit_)\<rbrakk> \<Longrightarrow> n = (_Exit_)"
apply(induct rule:PDG_path.induct)
by(auto elim:PDG_edge.cases dest:Exit_not_control_dependent 
        simp:data_dependence_def)


lemma PDG_path_not_inner:
  "\<lbrakk>n \<longrightarrow>\<^sub>d* n'; \<not> inner_node n'\<rbrakk> \<Longrightarrow> n = n'"
proof(induct rule:PDG_path.induct)
  case (PDG_path_Nil n)
  thus ?case by simp
next
  case (PDG_path_Append_cdep n n'' n')
  from \<open>n'' \<longrightarrow>\<^sub>c\<^sub>d n'\<close> \<open>\<not> inner_node n'\<close> have False
    apply -
    apply(erule PDG_edge.cases) apply(auto simp:inner_node_def)
      apply(fastforce dest:control_dependence_path path_valid_node)
     apply(fastforce dest:control_dependence_path path_valid_node)
    by(fastforce dest:Exit_not_control_dependent)
  thus ?case by simp
next
  case (PDG_path_Append_ddep n n'' V n')
  from \<open>n'' -V\<rightarrow>\<^sub>d\<^sub>d n'\<close> \<open>\<not> inner_node n'\<close> have False
    apply -
    apply(erule PDG_edge.cases) 
    by(auto dest:path_valid_node simp:inner_node_def data_dependence_def)
  thus ?case by simp
qed


subsection \<open>Definition of the static backward slice\<close>

text \<open>Node: instead of a single node, we calculate the backward slice of a set
  of nodes.\<close>

definition PDG_BS :: "'node set \<Rightarrow> 'node set"
  where "PDG_BS S \<equiv> {n'. \<exists>n. n' \<longrightarrow>\<^sub>d* n \<and> n \<in> S \<and> valid_node n}"


lemma PDG_BS_valid_node:"n \<in> PDG_BS S \<Longrightarrow> valid_node n"
  by(auto elim:PDG_path_CFG_path dest:path_valid_node simp:PDG_BS_def 
          split:if_split_asm)

lemma Exit_PDG_BS:"n \<in> PDG_BS {(_Exit_)} \<Longrightarrow> n = (_Exit_)"
  by(fastforce dest:PDG_path_Exit simp:PDG_BS_def)


end


subsection \<open>Instantiate static PDG\<close>

subsubsection \<open>Standard control dependence\<close>

locale StandardControlDependencePDG = 
  Postdomination sourcenode targetnode kind valid_edge Entry Exit +
  CFGExit_wf sourcenode targetnode kind valid_edge Entry Def Use state_val Exit
  for sourcenode :: "'edge \<Rightarrow> 'node" and targetnode :: "'edge \<Rightarrow> 'node"
  and kind :: "'edge \<Rightarrow> 'state edge_kind" and valid_edge :: "'edge \<Rightarrow> bool"
  and Entry :: "'node" ("'('_Entry'_')") and Def :: "'node \<Rightarrow> 'var set"
  and Use :: "'node \<Rightarrow> 'var set" and state_val :: "'state \<Rightarrow> 'var \<Rightarrow> 'val"
  and Exit :: "'node" ("'('_Exit'_')")

begin

lemma PDG_scd:
  "PDG sourcenode targetnode kind valid_edge (_Entry_) 
       Def Use state_val (_Exit_) standard_control_dependence"
proof(unfold_locales)
  fix n n' assume "n controls\<^sub>s n'"
  show "n' \<noteq> (_Exit_)"
  proof
    assume "n' = (_Exit_)"
    with \<open>n controls\<^sub>s n'\<close> show False
      by(fastforce intro:Exit_not_standard_control_dependent)
  qed
next
  fix n n' assume "n controls\<^sub>s n'"
  thus "\<exists>as. n -as\<rightarrow>* n' \<and> as \<noteq> []"
    by(fastforce simp:standard_control_dependence_def)
qed


(*<*)
lemmas PDG_cdep_edge = PDG.PDG_cdep_edge[OF PDG_scd]
lemmas PDG_path_Nil = PDG.PDG_path_Nil[OF PDG_scd]
lemmas PDG_path_Append = PDG.PDG_path_Append[OF PDG_scd]
lemmas PDG_path_CFG_path = PDG.PDG_path_CFG_path[OF PDG_scd]
lemmas PDG_path_cdep = PDG.PDG_path_cdep[OF PDG_scd]
lemmas PDG_path_ddep = PDG.PDG_path_ddep[OF PDG_scd]
lemmas PDG_path_not_inner = PDG.PDG_path_not_inner[OF PDG_scd]
lemmas PDG_path_Exit = PDG.PDG_path_Exit[OF PDG_scd]


definition PDG_BS_s :: "'node set \<Rightarrow> 'node set" ("PDG'_BS")
  where "PDG_BS S \<equiv> 
  PDG.PDG_BS sourcenode targetnode valid_edge Def Use standard_control_dependence S"

lemma [simp]: "PDG.PDG_BS sourcenode targetnode valid_edge Def Use 
  standard_control_dependence S = PDG_BS S"
  by(simp add:PDG_BS_s_def)

lemmas PDG_BS_def = PDG.PDG_BS_def[OF PDG_scd,simplified]
lemmas PDG_BS_valid_node = PDG.PDG_BS_valid_node[OF PDG_scd,simplified]
lemmas Exit_PDG_BS = PDG.Exit_PDG_BS[OF PDG_scd,simplified]
(*>*)

end

subsubsection \<open>Weak control dependence\<close>

locale WeakControlDependencePDG = 
  StrongPostdomination sourcenode targetnode kind valid_edge Entry Exit +
  CFGExit_wf sourcenode targetnode kind valid_edge Entry Def Use state_val Exit
  for sourcenode :: "'edge \<Rightarrow> 'node" and targetnode :: "'edge \<Rightarrow> 'node"
  and kind :: "'edge \<Rightarrow> 'state edge_kind" and valid_edge :: "'edge \<Rightarrow> bool"
  and Entry :: "'node" ("'('_Entry'_')") and Def :: "'node \<Rightarrow> 'var set"
  and Use :: "'node \<Rightarrow> 'var set" and state_val :: "'state \<Rightarrow> 'var \<Rightarrow> 'val"
  and Exit :: "'node" ("'('_Exit'_')")

begin

lemma PDG_wcd:
  "PDG sourcenode targetnode kind valid_edge (_Entry_) 
       Def Use state_val (_Exit_) weak_control_dependence"
proof(unfold_locales)
  fix n n' assume "n weakly controls n'"
  show "n' \<noteq> (_Exit_)"
  proof
    assume "n' = (_Exit_)"
    with \<open>n weakly controls n'\<close> show False
      by(fastforce intro:Exit_not_weak_control_dependent)
  qed
next
  fix n n' assume "n weakly controls n'"
  thus "\<exists>as. n -as\<rightarrow>* n' \<and> as \<noteq> []"
    by(fastforce simp:weak_control_dependence_def)
qed

(*<*)
lemmas PDG_cdep_edge = PDG.PDG_cdep_edge[OF PDG_wcd]
lemmas PDG_path_Nil = PDG.PDG_path_Nil[OF PDG_wcd]
lemmas PDG_path_Append = PDG.PDG_path_Append[OF PDG_wcd]
lemmas PDG_path_CFG_path = PDG.PDG_path_CFG_path[OF PDG_wcd]
lemmas PDG_path_cdep = PDG.PDG_path_cdep[OF PDG_wcd]
lemmas PDG_path_ddep = PDG.PDG_path_ddep[OF PDG_wcd]
lemmas PDG_path_not_inner = PDG.PDG_path_not_inner[OF PDG_wcd]
lemmas PDG_path_Exit = PDG.PDG_path_Exit[OF PDG_wcd]


definition PDG_BS_w :: "'node set \<Rightarrow> 'node set" ("PDG'_BS")
  where "PDG_BS S \<equiv> 
  PDG.PDG_BS sourcenode targetnode valid_edge Def Use weak_control_dependence S"

lemma [simp]: "PDG.PDG_BS sourcenode targetnode valid_edge Def Use 
  weak_control_dependence S = PDG_BS S"
  by(simp add:PDG_BS_w_def)

lemmas PDG_BS_def = PDG.PDG_BS_def[OF PDG_wcd,simplified]
lemmas PDG_BS_valid_node = PDG.PDG_BS_valid_node[OF PDG_wcd,simplified]
lemmas Exit_PDG_BS = PDG.Exit_PDG_BS[OF PDG_wcd,simplified]
(*>*)

end

end
