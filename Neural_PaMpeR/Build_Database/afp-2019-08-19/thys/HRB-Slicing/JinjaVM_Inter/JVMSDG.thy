theory JVMSDG imports JVMCFG_wf JVMPostdomination "../StaticInter/SDG" begin

interpretation JVMCFGExit_wf_new_type:
  CFGExit_wf "sourcenode" "targetnode" "kind" "valid_edge\<^bsub>CFG\<^esub> P"
  "(ClassMain (fst\<^bsub>CFG\<^esub> P), MethodMain (fst\<^bsub>CFG\<^esub> P), None, Enter)"
  "(\<lambda>(C, M, pc, type). (C, M))" "get_return_edges (fst\<^bsub>CFG\<^esub> P)"
  "((ClassMain (fst\<^bsub>CFG\<^esub> P), MethodMain (fst\<^bsub>CFG\<^esub> P)),[],[]) # procs (PROG (fst\<^bsub>CFG\<^esub> P))"
  "(ClassMain (fst\<^bsub>CFG\<^esub> P), MethodMain (fst\<^bsub>CFG\<^esub> P))"
  "(ClassMain (fst\<^bsub>CFG\<^esub> P), MethodMain (fst\<^bsub>CFG\<^esub> P), None, Return)"
  "Def (fst\<^bsub>CFG\<^esub> P)" "Use (fst\<^bsub>CFG\<^esub> P)" "ParamDefs (fst\<^bsub>CFG\<^esub> P)" "ParamUses (fst\<^bsub>CFG\<^esub> P)"
  for P
  unfolding valid_edge_CFG_def
  ..

interpretation JVM_SDG :
  SDG "sourcenode" "targetnode" "kind" "valid_edge\<^bsub>CFG\<^esub> P"
  "(ClassMain (fst\<^bsub>CFG\<^esub> P), MethodMain (fst\<^bsub>CFG\<^esub> P), None, Enter)"
  "(\<lambda>(C, M, pc, type). (C, M))" "get_return_edges (fst\<^bsub>CFG\<^esub> P)"
  "((ClassMain (fst\<^bsub>CFG\<^esub> P), MethodMain (fst\<^bsub>CFG\<^esub> P)),[],[]) # procs (PROG (fst\<^bsub>CFG\<^esub> P))"
  "(ClassMain (fst\<^bsub>CFG\<^esub> P), MethodMain (fst\<^bsub>CFG\<^esub> P))"
  "(ClassMain (fst\<^bsub>CFG\<^esub> P), MethodMain (fst\<^bsub>CFG\<^esub> P), None, Return)"
  "Def (fst\<^bsub>CFG\<^esub> P)" "Use (fst\<^bsub>CFG\<^esub> P)" "ParamDefs (fst\<^bsub>CFG\<^esub> P)" "ParamUses (fst\<^bsub>CFG\<^esub> P)"
  for P
  ..

end
