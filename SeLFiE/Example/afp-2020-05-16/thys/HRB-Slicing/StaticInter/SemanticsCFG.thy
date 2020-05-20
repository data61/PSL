section \<open>CFG and semantics conform\<close>

theory SemanticsCFG imports CFG begin

locale CFG_semantics_wf = CFG sourcenode targetnode kind valid_edge Entry 
    get_proc get_return_edges procs Main
  for sourcenode :: "'edge \<Rightarrow> 'node" and targetnode :: "'edge \<Rightarrow> 'node"
  and kind :: "'edge \<Rightarrow> ('var,'val,'ret,'pname) edge_kind" 
  and valid_edge :: "'edge \<Rightarrow> bool"
  and Entry :: "'node" ("'('_Entry'_')")  and get_proc :: "'node \<Rightarrow> 'pname"
  and get_return_edges :: "'edge \<Rightarrow> 'edge set"
  and procs :: "('pname \<times> 'var list \<times> 'var list) list" and Main :: "'pname" +
  fixes sem::"'com \<Rightarrow> ('var \<rightharpoonup> 'val) list \<Rightarrow> 'com \<Rightarrow> ('var \<rightharpoonup> 'val) list \<Rightarrow> bool" 
    ("((1\<langle>_,/_\<rangle>) \<Rightarrow>/ (1\<langle>_,/_\<rangle>))" [0,0,0,0] 81)
  fixes identifies::"'node \<Rightarrow> 'com \<Rightarrow> bool" ("_ \<triangleq> _" [51,0] 80)
  assumes fundamental_property:
    "\<lbrakk>n \<triangleq> c; \<langle>c,[cf]\<rangle> \<Rightarrow> \<langle>c',s'\<rangle>\<rbrakk> \<Longrightarrow>
      \<exists>n' as. n -as\<rightarrow>\<^sub>\<surd>* n' \<and> n' \<triangleq> c' \<and> preds (kinds as) [(cf,undefined)] \<and>
              transfers (kinds as) [(cf,undefined)] = cfs' \<and> map fst cfs' = s'"


end
