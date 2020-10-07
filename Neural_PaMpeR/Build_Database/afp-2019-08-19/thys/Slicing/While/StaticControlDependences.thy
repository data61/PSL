section \<open>Interpretations of the various static control dependences\<close>

theory StaticControlDependences imports 
  AdditionalLemmas 
  SemanticsWellFormed
begin

lemma WhilePostdomination_aux:
  "Postdomination sourcenode targetnode kind (valid_edge prog) Entry Exit"
proof(unfold_locales)
  fix n assume "CFG.valid_node sourcenode targetnode (valid_edge prog) n"
  hence "valid_node prog n" by(simp add:valid_node_def While_CFG.valid_node_def)
  thus "\<exists>as. prog \<turnstile> (_Entry_) -as\<rightarrow>* n" by(rule valid_node_Entry_path)
next
  fix n assume "CFG.valid_node sourcenode targetnode (valid_edge prog) n"
  hence "valid_node prog n" by(simp add:valid_node_def While_CFG.valid_node_def)
  thus "\<exists>as. prog \<turnstile> n -as\<rightarrow>* (_Exit_)" by(rule valid_node_Exit_path)
qed

interpretation WhilePostdomination: 
  Postdomination sourcenode targetnode kind "valid_edge prog" Entry Exit
by(rule WhilePostdomination_aux)


lemma WhileStrongPostdomination_aux:
  "StrongPostdomination sourcenode targetnode kind (valid_edge prog) Entry Exit"
proof(unfold_locales)
  fix n assume "CFG.valid_node sourcenode targetnode (valid_edge prog) n"
  hence "valid_node prog n" by(simp add:valid_node_def While_CFG.valid_node_def)
  show "finite {n'. \<exists>a'. valid_edge prog a' \<and> sourcenode a' = n \<and>
                         targetnode a' = n'}"
    by(rule finite_successors)
qed

interpretation WhileStrongPostdomination: 
  StrongPostdomination sourcenode targetnode kind "valid_edge prog" Entry Exit
by(rule WhileStrongPostdomination_aux)


subsection \<open>Standard Control Dependence\<close>

lemma WStandardControlDependence_aux:
  "StandardControlDependencePDG sourcenode targetnode kind (valid_edge prog)
  Entry (Defs prog) (Uses prog) id Exit"
by(unfold_locales)

interpretation WStandardControlDependence:
  StandardControlDependencePDG sourcenode targetnode kind "valid_edge prog"
                    Entry "Defs prog" "Uses prog" id Exit
  by(rule WStandardControlDependence_aux)


lemma Fundamental_property_scd_aux: "BackwardSlice_wf sourcenode targetnode kind 
  (valid_edge prog) Entry (Defs prog) (Uses prog) id 
  (WStandardControlDependence.PDG_BS_s prog) reds (labels_nodes prog)"
proof -
  interpret BackwardSlice sourcenode targetnode kind "valid_edge prog" Entry
    "Defs prog" "Uses prog" id
    "StandardControlDependencePDG.PDG_BS_s sourcenode targetnode
    (valid_edge prog) (Defs prog) (Uses prog) Exit"
    by(rule WStandardControlDependence.PDGBackwardSliceCorrect)
  show ?thesis by(unfold_locales)
qed

interpretation Fundamental_property_scd: BackwardSlice_wf sourcenode targetnode kind 
  "valid_edge prog" Entry "Defs prog" "Uses prog" id 
  "WStandardControlDependence.PDG_BS_s prog" reds "labels_nodes prog"
  by(rule Fundamental_property_scd_aux)


subsection \<open>Weak Control Dependence\<close>

lemma WWeakControlDependence_aux:
  "WeakControlDependencePDG sourcenode targetnode kind (valid_edge prog)
  Entry (Defs prog) (Uses prog) id Exit"
by(unfold_locales)

interpretation WWeakControlDependence:
  WeakControlDependencePDG sourcenode targetnode kind "valid_edge prog"
                    Entry "Defs prog" "Uses prog" id Exit
  by(rule WWeakControlDependence_aux)


lemma Fundamental_property_wcd_aux: "BackwardSlice_wf sourcenode targetnode kind 
  (valid_edge prog) Entry (Defs prog) (Uses prog) id 
  (WWeakControlDependence.PDG_BS_w prog) reds (labels_nodes prog)"
proof -
  interpret BackwardSlice sourcenode targetnode kind "valid_edge prog" Entry
    "Defs prog" "Uses prog" id
    "WeakControlDependencePDG.PDG_BS_w sourcenode targetnode
    (valid_edge prog) (Defs prog) (Uses prog) Exit"
    by(rule WWeakControlDependence.WeakPDGBackwardSliceCorrect)
  show ?thesis by(unfold_locales)
qed

interpretation Fundamental_property_wcd: BackwardSlice_wf sourcenode targetnode kind 
  "valid_edge prog" Entry "Defs prog" "Uses prog" id 
  "WWeakControlDependence.PDG_BS_w prog" reds "labels_nodes prog"
  by(rule Fundamental_property_wcd_aux)


subsection \<open>Weak Order Dependence\<close>

lemma Fundamental_property_wod_aux: "BackwardSlice_wf sourcenode targetnode kind 
  (valid_edge prog) Entry (Defs prog) (Uses prog) id 
  (While_CFG_wf.wod_backward_slice prog) reds (labels_nodes prog)"
proof -
  interpret BackwardSlice sourcenode targetnode kind "valid_edge prog" Entry
    "Defs prog" "Uses prog" id
    "CFG_wf.wod_backward_slice sourcenode targetnode (valid_edge prog)
    (Defs prog) (Uses prog)"
    by(rule While_CFG_wf.WODBackwardSliceCorrect)
  show ?thesis by(unfold_locales)
qed

interpretation Fundamental_property_wod: BackwardSlice_wf sourcenode targetnode kind 
  "valid_edge prog" Entry "Defs prog" "Uses prog" id 
  "While_CFG_wf.wod_backward_slice prog" reds "labels_nodes prog"
  by(rule Fundamental_property_wod_aux)

end
