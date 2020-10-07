section \<open>Instantiation of the SDG locale\<close>

theory ProcSDG imports ValidPaths "../StaticInter/SDG" begin

interpretation Proc_SDG:
  SDG sourcenode targetnode kind "valid_edge wfp" "(Main,Entry)"
  get_proc "get_return_edges wfp" "lift_procs wfp" Main "(Main,Exit)"
  "Def wfp" "Use wfp" "ParamDefs wfp" "ParamUses wfp"
  for wfp ..

end
