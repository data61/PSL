theory CFGExit_wf imports CFGExit CFG_wf begin

subsection \<open>New well-formedness lemmas using \<open>(_Exit_)\<close>\<close>


locale CFGExit_wf = 
  CFG_wf sourcenode targetnode kind valid_edge Entry Def Use state_val +
  CFGExit sourcenode targetnode kind valid_edge Entry Exit 
  for sourcenode :: "'edge \<Rightarrow> 'node" and targetnode :: "'edge \<Rightarrow> 'node"
  and kind :: "'edge \<Rightarrow> 'state edge_kind" and valid_edge :: "'edge \<Rightarrow> bool"
  and Entry :: "'node" ("'('_Entry'_')") and Def :: "'node \<Rightarrow> 'var set"
  and Use :: "'node \<Rightarrow> 'var set" and state_val :: "'state \<Rightarrow> 'var \<Rightarrow> 'val"
  and Exit :: "'node" ("'('_Exit'_')") +
  assumes Exit_empty:"Def (_Exit_) = {} \<and> Use (_Exit_) = {}"

begin

lemma Exit_Use_empty [dest!]: "V \<in> Use (_Exit_) \<Longrightarrow> False"
by(simp add:Exit_empty)

lemma Exit_Def_empty [dest!]: "V \<in> Def (_Exit_) \<Longrightarrow> False"
by(simp add:Exit_empty)

end

end
