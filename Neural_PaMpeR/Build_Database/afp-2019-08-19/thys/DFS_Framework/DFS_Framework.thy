section \<open>Basic DFS Framework\<close>
theory DFS_Framework
imports
  Param_DFS
  "Invars/DFS_Invars_Basic"
  "Impl/Structural/Tailrec_Impl"
  "Impl/Structural/Rec_Impl"
  "Impl/Data/Simple_Impl"  
  "Impl/Data/Restr_Impl"  
begin
  text \<open>Entry point for the DFS framework, with basic invariants,
    tail-recursive and recursive implementation, and basic state data 
    structures.\<close>

end
