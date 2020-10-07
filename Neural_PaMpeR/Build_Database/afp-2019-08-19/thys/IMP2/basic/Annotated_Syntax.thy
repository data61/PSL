section \<open>Annotated Syntax\<close>
theory Annotated_Syntax
imports "Semantics"
begin

  text \<open>Unfold theorems to strip annotations from program, before it is defined as constant\<close>
  named_theorems vcg_annotation_defs \<open>Definitions of Annotations\<close>

  text \<open>Marker that is inserted around all annotations by the specification parser.\<close>
  definition "ANNOTATION \<equiv> \<lambda>x. x"
  
  subsection \<open>Annotations\<close>
  text \<open>The specification parser must interpret the annotations in the program.\<close>
  
  definition WHILE_annotI :: "(state \<Rightarrow> bool) \<Rightarrow> bexp \<Rightarrow> com \<Rightarrow> com" 
    ("(WHILE {_} _/ DO _)"  [0, 0, 61] 61) 
    where [vcg_annotation_defs]: "WHILE_annotI (I::state \<Rightarrow> bool) \<equiv> While"
    
  lemmas annotate_whileI = WHILE_annotI_def[symmetric]
  
  definition WHILE_annotRVI :: "'a rel \<Rightarrow> (state \<Rightarrow> 'a) \<Rightarrow> (state \<Rightarrow> bool) \<Rightarrow> bexp \<Rightarrow> com \<Rightarrow> com" 
      ("(WHILE {_} {_} {_} _/ DO _)"  [0, 0, 0, 0, 61] 61)
    where [vcg_annotation_defs]: "WHILE_annotRVI R V I \<equiv> While" for R V I
    
  lemmas annotate_whileRVI = WHILE_annotRVI_def[symmetric]
  
  definition WHILE_annotVI :: "(state \<Rightarrow> int) \<Rightarrow> (state \<Rightarrow> bool) \<Rightarrow> bexp \<Rightarrow> com \<Rightarrow> com" 
    ("(WHILE {_} {_} _/ DO _)"  [0, 0, 0, 61] 61)
  where [vcg_annotation_defs]: "WHILE_annotVI V I \<equiv> While" for V I
  lemmas annotate_whileVI = WHILE_annotVI_def[symmetric]
  

  subsection \<open>Hoare-Triples for Annotated Commands\<close>
  text \<open>The command is a function from pre-state to command, as the annotations that are 
    contained in the command may depend on the pre-state!\<close>
  
  type_synonym HT'_type = "program \<Rightarrow> (state \<Rightarrow> bool) \<Rightarrow> (state \<Rightarrow> com) \<Rightarrow> (state \<Rightarrow> state\<Rightarrow>bool) \<Rightarrow> bool"
  
  definition HT'_partial :: HT'_type
    where "HT'_partial \<pi> P c Q \<equiv> (\<forall>s\<^sub>0. P s\<^sub>0 \<longrightarrow> wlp \<pi> (c s\<^sub>0) (Q s\<^sub>0) s\<^sub>0)"
  
  definition HT' :: HT'_type
    where "HT' \<pi> P c Q \<equiv> (\<forall>s\<^sub>0. P s\<^sub>0 \<longrightarrow> wp \<pi> (c s\<^sub>0) (Q s\<^sub>0) s\<^sub>0)"
  
  lemma HT'_eq_HT: "HT' \<pi> P (\<lambda>_. c) Q = HT \<pi> P c Q"
    unfolding HT_def HT'_def ..  
    
  lemma HT'_partial_eq_HT: "HT'_partial \<pi> P (\<lambda>_. c) Q = HT_partial \<pi> P c Q"
    unfolding HT_partial_def HT'_partial_def ..  
  
  lemmas HT'_unfolds = HT'_eq_HT HT'_partial_eq_HT
  
  
  type_synonym 'a \<Theta>elem_t = "(state\<Rightarrow>'a) \<times> ((state \<Rightarrow> bool) \<times> (state \<Rightarrow> com) \<times> (state \<Rightarrow> state\<Rightarrow>bool))"
  
  definition HT'set :: "program \<Rightarrow> 'a \<Theta>elem_t set \<Rightarrow> bool" where "HT'set \<pi> \<Theta> \<equiv> \<forall>(n,(P,c,Q))\<in>\<Theta>. HT' \<pi> P c Q"
  
  definition HT'set_r :: "_ \<Rightarrow> program \<Rightarrow> 'a \<Theta>elem_t set \<Rightarrow> bool" where "HT'set_r r \<pi> \<Theta> \<equiv> \<forall>(n,(P,c,Q))\<in>\<Theta>. HT' \<pi> (\<lambda>s. r n s \<and> P s) c Q"
  
  lemma HT'setI:    
    assumes "wf R"
    assumes RL: "\<And>f P c Q s\<^sub>0. \<lbrakk> HT'set_r (\<lambda>f' s'. ((f' s'),(f s\<^sub>0))\<in>R ) \<pi> \<Theta>; (f,(P,c,Q))\<in>\<Theta>; P s\<^sub>0 \<rbrakk> \<Longrightarrow> wp \<pi> (c s\<^sub>0) (Q s\<^sub>0) s\<^sub>0"
    shows "HT'set \<pi> \<Theta>"
    unfolding HT'set_def HT'_def 
  proof clarsimp
    fix f\<^sub>0 P c Q s\<^sub>0
    assume "(f\<^sub>0,(P,c,Q))\<in>\<Theta>" "P s\<^sub>0"
    with \<open>wf R\<close> show "wp \<pi> (c s\<^sub>0) (Q s\<^sub>0) s\<^sub>0"
    proof (induction "f\<^sub>0 s\<^sub>0" arbitrary: f\<^sub>0 c s\<^sub>0 P Q)
      case less
      note RL' = RL[of f\<^sub>0 s\<^sub>0 P, OF _ less.prems]
      show ?case
        apply (rule RL')
        unfolding HT'set_r_def HT'_def using less.hyps by auto
    qed
  qed  
  
  lemma HT'setD:
    assumes "HT'set \<pi> (insert (f,(P,c,Q)) \<Theta>)"
    shows "HT' \<pi> P c Q" and "HT'set \<pi> \<Theta>"
    using assms unfolding HT'set_def by auto
  
  
  
  

end
