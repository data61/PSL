theory Refine_Add_Fofu
imports 
  Fofu_Impl_Base 
  DFS_Framework.DFS_Framework_Refine_Aux
begin

  hide_type (open) List_Seg.node    
    
  notation Heap_Monad.return ("return")

(* Refinement Framework VCG control:
  Idea: Put a frame around stuff in the program where the VCG shall not look into
    on outermost pass, and discharge the frame's content with nested vcg call.
    Very useful with subgoal command, to set up some auxiliary context before
    discharging, e.g., interpret locales, etc.
 
*)  
(* TODO: Make this a generic technique:
  Problems: 
    * Splitter will split inside VCG_FRAME (e.g., ifs)

*)  
  
definition VCG_FRAME :: "_ nres \<Rightarrow> _ nres" where "VCG_FRAME m \<equiv> m"
lemma VCG_FRAME_cong[cong]: "VCG_FRAME x \<equiv> VCG_FRAME x" by simp

lemma vcg_intro_frame: "m \<equiv> VCG_FRAME m" unfolding VCG_FRAME_def by simp
lemma vcg_rem_frame: "m\<le>m' \<Longrightarrow> VCG_FRAME m \<le> m'" unfolding VCG_FRAME_def by simp
    
end
