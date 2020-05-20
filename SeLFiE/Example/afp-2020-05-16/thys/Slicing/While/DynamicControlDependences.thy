section \<open>Interpretations of the various dynamic control dependences\<close>

theory DynamicControlDependences imports AdditionalLemmas "../Dynamic/DynPDG" begin

interpretation WDynStandardControlDependence:
  DynStandardControlDependencePDG sourcenode targetnode kind "valid_edge prog"
                    Entry "Defs prog" "Uses prog" id Exit
  for prog
proof(unfold_locales)
  fix n assume "CFG.valid_node sourcenode targetnode (valid_edge prog) n"
  hence "valid_node prog n" by(simp add:valid_node_def While_CFG.valid_node_def)
  thus "\<exists>as. prog \<turnstile> (_Entry_) -as\<rightarrow>* n" by(rule valid_node_Entry_path)
next
  fix n assume "CFG.valid_node sourcenode targetnode (valid_edge prog) n"
  hence "valid_node prog n" by(simp add:valid_node_def While_CFG.valid_node_def)
  thus "\<exists>as. prog \<turnstile> n -as\<rightarrow>* (_Exit_)" by(rule valid_node_Exit_path)
qed

interpretation WDynWeakControlDependence:
  DynWeakControlDependencePDG sourcenode targetnode kind "valid_edge prog"
                    Entry "Defs prog" "Uses prog" id Exit
  for prog
proof(unfold_locales)
  fix n assume "CFG.valid_node sourcenode targetnode (valid_edge prog) n"
  hence "valid_node prog n" by(simp add:valid_node_def While_CFG.valid_node_def)
  show "finite {n'. \<exists>a'. valid_edge prog a' \<and> sourcenode a' = n \<and>
                         targetnode a' = n'}"
    by(rule finite_successors)
qed

end
