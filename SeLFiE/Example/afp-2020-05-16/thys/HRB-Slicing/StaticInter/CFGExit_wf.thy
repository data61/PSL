theory CFGExit_wf imports CFGExit CFG_wf begin

subsection \<open>New well-formedness lemmas using \<open>(_Exit_)\<close>\<close>

locale CFGExit_wf = CFGExit sourcenode targetnode kind valid_edge Entry 
    get_proc get_return_edges procs Main Exit +
  CFG_wf sourcenode targetnode kind valid_edge Entry 
    get_proc get_return_edges procs Main Def Use ParamDefs ParamUses
  for sourcenode :: "'edge \<Rightarrow> 'node" and targetnode :: "'edge \<Rightarrow> 'node"
  and kind :: "'edge \<Rightarrow> ('var,'val,'ret,'pname) edge_kind" 
  and valid_edge :: "'edge \<Rightarrow> bool"
  and Entry :: "'node" ("'('_Entry'_')")  and get_proc :: "'node \<Rightarrow> 'pname"
  and get_return_edges :: "'edge \<Rightarrow> 'edge set"
  and procs :: "('pname \<times> 'var list \<times> 'var list) list" and Main :: "'pname"
  and Exit::"'node"  ("'('_Exit'_')") 
  and Def :: "'node \<Rightarrow> 'var set" and Use :: "'node \<Rightarrow> 'var set"
  and ParamDefs :: "'node \<Rightarrow> 'var list" 
  and ParamUses :: "'node \<Rightarrow> 'var set list" +
  assumes Exit_empty:"Def (_Exit_) = {} \<and> Use (_Exit_) = {}"

begin

lemma Exit_Use_empty [dest!]: "V \<in> Use (_Exit_) \<Longrightarrow> False"
by(simp add:Exit_empty)

lemma Exit_Def_empty [dest!]: "V \<in> Def (_Exit_) \<Longrightarrow> False"
by(simp add:Exit_empty)

end

end
