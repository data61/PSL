section \<open>Basic Declarations\<close>
theory IMP2_Basic_Decls
imports IMP2_Basic_Simpset
begin
  text \<open>Some declarations that are used at several places, and have been factored out.\<close>
  
  
  named_theorems analysis_unfolds \<open>Unfold theorems to be applied prior to program analysis functions\<close>
  
  named_theorems vcg_preprocess_rules \<open>Rules to be applied to goal before VCG\<close>
  
  named_theorems vcg_specs \<open>Specifications declared to VCG\<close>
end
