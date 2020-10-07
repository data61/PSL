section \<open>Verification Condition Generator\<close>
theory IMP2_VCG
imports IMP2_Basic_Simpset IMP2_Program_Analysis IMP2_Var_Postprocessor IMP2_Var_Abs
begin

subsection \<open>Preprocessing\<close>

  lemma HT'_I[vcg_preprocess_rules]:
    assumes "\<And>\<ss>\<^sub>0. \<lbrakk> P \<ss>\<^sub>0 \<rbrakk> \<Longrightarrow> wp \<pi> (c \<ss>\<^sub>0) (Q \<ss>\<^sub>0) \<ss>\<^sub>0"
    shows "HT' \<pi> P c Q"
    using assms
    unfolding BB_PROTECT_def HT'_def by auto
  
  lemma HT'_partial_I[vcg_preprocess_rules]:
    assumes "\<And>\<ss>\<^sub>0. \<lbrakk> P \<ss>\<^sub>0 \<rbrakk> \<Longrightarrow> wlp \<pi> (c \<ss>\<^sub>0) (Q \<ss>\<^sub>0) \<ss>\<^sub>0"
    shows "HT'_partial \<pi> P c Q"
    using assms
    unfolding BB_PROTECT_def HT'_partial_def by auto
  
    
  lemmas [vcg_preprocess_rules] = allI impI conjI
    
  method i_vcg_preprocess = 
    (intro vcg_preprocess_rules)?

  subsection \<open>VC rules\<close>


  named_theorems vcg_comb_rules \<open>VCG rules for Combinators\<close>
  
  subsubsection \<open>Goal Indication\<close>  
  text \<open>A marker to indicate where a goal comes from.\<close>
  (* TODO: Noschinski has driven this to the extreme, allowing to generate a 
    complete isar case setup from such annotations. 
    We should adapt (at least parts of) this idea!
  *)
  definition GOAL_INDICATION :: "'a \<Rightarrow> bool" ("\<paragraph>_" [1000])
    where "GOAL_INDICATION _ \<equiv> True"
  
  lemma move_goal_indication_to_front[simp, named_ss vcg_bb]: 
    "NO_MATCH (\<paragraph>x) P \<Longrightarrow> (P\<Longrightarrow>\<paragraph>n\<Longrightarrow>PROP Q) \<equiv> (\<paragraph>n \<Longrightarrow> P \<Longrightarrow> PROP Q)"  
    by (rule swap_prems_eq)
    (* TODO: Would like to use PROP P here, to also move over 
      meta-premises like \<open>\<And>x. a\<Longrightarrow>b\<close>, but \<open>NO_MATCH\<close> requires type! *)
  
  
  
  
  subsubsection \<open>Modularity (Frame) Rules\<close>  
  
  text \<open>Frame rules are only applied if their first assumption can be 
    discharged by a specification rule.\<close>
  named_theorems vcg_frame_rules \<open>Frame rules for VCG Approximation Phase\<close>

    
  lemma vcg_wlp_modularity_rl[vcg_frame_rules]:
    assumes "HT_partial_mods \<pi> mods P c Q"
    assumes "P s"
    assumes "\<And>s'. \<lbrakk>modifies mods s' s; Q s s'\<rbrakk> \<Longrightarrow> Q' s'"
    shows "wlp \<pi> (c) (\<lambda>s'. Q' s') s"
    using vcg_wlp_conseq assms by metis
  
  lemma vcg_wp_modularity_rl[vcg_frame_rules]:
    assumes "HT_mods \<pi> mods P c Q"
    assumes "P s"
    assumes "\<And>s'. \<lbrakk>modifies mods s' s ; Q s s'\<rbrakk> \<Longrightarrow>Q' s'"
    shows "wp \<pi> (c) (\<lambda>s'. Q' s') s"
    using vcg_wp_conseq assms by metis
    
  lemma vcg_wp_wlp_modularity_rl[vcg_frame_rules]:
    assumes "HT_mods \<pi> mods P c Q"
    assumes "P s"
    assumes "\<And>s'. \<lbrakk>modifies mods s' s; Q s s'\<rbrakk> \<Longrightarrow> Q' s'"
    shows "wlp \<pi> (c) (\<lambda>s'. Q' s') s"
    using vcg_wlp_wp_conseq assms by metis
  
  lemmas [named_ss vcg_bb] = Params_def Inline_def
  
  subsubsection \<open>Skip and Sequential Composition\<close>  
  text \<open>Skip and sequential composition are unfolded by the VCG basic simpset\<close>
        
  lemmas [named_ss vcg_bb] = 
    wp_skip_eq wp_seq_eq wlp_skip_eq wlp_seq_eq
    
    
  subsubsection \<open>Assignments\<close>  

  text \<open>Assignments are unfolded, using the UPD_STATE constants with a custom simpset 
    to efficiently handle state updates.
  \<close>
  
  lemmas [named_ss vcg_bb] = 
    aval.simps bval.simps
  
  
  definition UPD_STATE :: "state \<Rightarrow> vname \<Rightarrow> val \<Rightarrow> state" where
    "UPD_STATE s x v \<equiv> s(x:=v)"

  definition UPD_IDX :: "val \<Rightarrow> int \<Rightarrow> pval \<Rightarrow> val" where
    "UPD_IDX av i pv \<equiv> av(i:=pv)"
        
  definition UPD_STATE_IDX :: "state \<Rightarrow> vname \<Rightarrow> int \<Rightarrow> pval \<Rightarrow> state" where
    "UPD_STATE_IDX s x i v \<equiv> s(x:=UPD_IDX (s x) i v)"
    

  lemma [named_ss vcg_bb]:
    "UPD_STATE (s(x:=w)) x v = s(x:=v)"
    "x\<noteq>y \<Longrightarrow> UPD_STATE (s(x:=w)) y v = (UPD_STATE s y v)(x:=w)"  
    "NO_MATCH (SS(XX:=VV)) s \<Longrightarrow> UPD_STATE s x v = s(x:=v)"
    by (auto simp: UPD_STATE_def)
        
  lemma [named_ss vcg_bb]:
    "UPD_STATE_IDX (s(x:=w)) x i v = s(x:=UPD_IDX w i v)"
    "x\<noteq>y \<Longrightarrow> UPD_STATE_IDX (s(x:=w)) y i v = (UPD_STATE_IDX s y i v)(x:=w)"  
    "NO_MATCH (SS(XX:=VV)) s \<Longrightarrow> UPD_STATE_IDX s x i v = s(x:=UPD_IDX (s x) i v)"
    by (auto simp: UPD_STATE_IDX_def)
 
  (* Note (hack): These two rewrite rules exploit inner-to-outer rewrite order
    to ensure that the first rule is applied first.
  *)  
  lemma [named_ss vcg_bb]:  
    "UPD_IDX (a(i:=v)) i = UPD_IDX a i"
    "UPD_IDX a i v = (a(i:=v))"          
    by (auto simp: UPD_IDX_def)
  
  lemma vcg_assign_idx_unfolds[named_ss vcg_bb]:
    "wlp \<pi> (x[i] ::= a) Q s = Q (UPD_STATE_IDX s x (aval i s) (aval a s))"
    "wp \<pi> (x[i] ::= a) Q s = Q (UPD_STATE_IDX s x (aval i s) (aval a s))"
    unfolding UPD_STATE_IDX_def UPD_IDX_def 
    by (simp_all add: wlp_eq wp_eq)
  
  lemma vcg_arraycpy_unfolds[named_ss vcg_bb]:
    "wlp \<pi> (x[] ::= a) Q s = Q (UPD_STATE s x (s a))"
    "wp \<pi> (x[] ::= a) Q s = Q (UPD_STATE s x (s a))"
    unfolding UPD_STATE_def 
    by (simp_all add: wlp_eq wp_eq)

  lemma vcg_arrayinit_unfolds[named_ss vcg_bb]:
    "wlp \<pi> (CLEAR x[]) Q s = Q (UPD_STATE s x (\<lambda>_. 0))"
    "wp \<pi> (CLEAR x[]) Q s = Q (UPD_STATE s x (\<lambda>_. 0))"
    unfolding UPD_STATE_def 
    by (simp_all add: wlp_eq wp_eq)
    
  text \<open>Special case for procedure return value: 
    Insert a renaming to keep name of original variable\<close>  

    
  lemma vcg_AssignIdx_retv_wlp_unfold[named_ss vcg_bb]:
    "wlp \<pi> (AssignIdx_retv x i a) Q s = (NAMING_HINT s a x \<longrightarrow> wlp \<pi> (x[i]::=V a) Q s)"
    unfolding AssignIdx_retv_def NAMING_HINT_def by auto
    
  lemma vcg_AssignIdx_retv_wp_unfold[named_ss vcg_bb]:
    "wp \<pi> (AssignIdx_retv x i a) Q s = (NAMING_HINT s a x \<longrightarrow> wp \<pi> (x[i]::=V a) Q s)"
    unfolding AssignIdx_retv_def NAMING_HINT_def by auto
    
  lemma vcg_ArrayCpy_retv_wlp_unfold[named_ss vcg_bb]:
    "wlp \<pi> (ArrayCpy_retv x a) Q s = (NAMING_HINT s a x \<longrightarrow> wlp \<pi> (x[]::=a) Q s)"  
    unfolding ArrayCpy_retv_def NAMING_HINT_def by auto
    
  lemma vcg_ArrayCpy_retv_wp_unfold[named_ss vcg_bb]:
    "wp \<pi> (ArrayCpy_retv x a) Q s = (NAMING_HINT s a x \<longrightarrow> wp \<pi> (x[]::=a) Q s)"  
    unfolding ArrayCpy_retv_def NAMING_HINT_def by auto

  lemma naming_hint_impI_simp[named_ss vcg_bb]: 
    "Trueprop (NAMING_HINT s a x \<longrightarrow> P) \<equiv> (NAMING_HINT s a x \<Longrightarrow> P)" by rule auto

  subsubsection \<open>Scope\<close>    
    
  lemmas [named_ss vcg_bb] = 
    wp_scope_eq wlp_scope_eq


  subsubsection \<open>While\<close>  
        
  lemma wlp_whileI_modset:
    fixes c \<pi>
    defines [simp]: "modset \<equiv> ANALYZE (lhsv \<pi> c)"
    assumes INIT: "I s\<^sub>0"
    assumes STEP: "\<And>s. \<lbrakk> modifies modset s s\<^sub>0; I s; bval b s \<rbrakk> \<Longrightarrow> wlp \<pi> c (\<lambda>s'. I s') s"
    assumes FINAL: "\<And>s. \<lbrakk> modifies modset s s\<^sub>0; I s; \<not>bval b s \<rbrakk> \<Longrightarrow> Q s"
    shows "wlp \<pi> (WHILE b DO c) Q s\<^sub>0"
    apply (rule wlp_whileI[where I="\<lambda>s. I s \<and> modifies modset s s\<^sub>0"])
    subgoal using INIT by simp
    subgoal
      apply (rule wlp_conseq, rule wlp_strengthen_modset, rule STEP)
         apply (auto dest: modifies_trans simp: modifies_sym)
      done
    subgoal using FINAL by (simp add: modifies_sym)
    done
    
  lemma wp_whileI_modset:
    fixes c \<pi>
    defines [simp]: "modset \<equiv> ANALYZE (lhsv \<pi> c)"
    assumes WF: "wf R"
    assumes INIT: "I s\<^sub>0"
    assumes STEP: "\<And>s. \<lbrakk> modifies modset s s\<^sub>0; I s; bval b s \<rbrakk> \<Longrightarrow> wp \<pi> c (\<lambda>s'. I s' \<and> (s',s)\<in>R) s"
    assumes FINAL: "\<And>s. \<lbrakk> modifies modset s s\<^sub>0; I s; \<not>bval b s \<rbrakk> \<Longrightarrow> Q s"
    shows "wp \<pi> (WHILE b DO c) Q s\<^sub>0"
    apply (rule wp_whileI[where I="\<lambda>s. I s \<and> modifies modset s s\<^sub>0" and R=R])
       apply (rule WF)
      subgoal using INIT by simp
     subgoal
      apply (rule wp_conseq, rule wp_strengthen_modset, rule STEP)
         apply (auto dest: modifies_trans simp: modifies_sym)
      done
    subgoal using FINAL by (simp add: modifies_sym)
    done

  definition invar_var_goal where
    "invar_var_goal I R v s s' \<equiv> I s' \<and> (v s',v s)\<in>R"
  
  lemma invar_var_goalI[vcg_comb_rules]:
    "invar_var_goal I R v s s'" if "\<paragraph>''Invar pres'' \<Longrightarrow> I s'" "\<paragraph>''Var pres'' \<Longrightarrow> (v s',v s)\<in>R"
    using that unfolding invar_var_goal_def GOAL_INDICATION_def by auto
    
        
  lemma wp_while_rl[vcg_comb_rules]:
    assumes "\<paragraph>''rel-wf'' \<Longrightarrow> wf R"
    assumes "\<paragraph>''invar-initial'' \<Longrightarrow> I s\<^sub>0"
    assumes "\<And>s. \<lbrakk> modifies modset s s\<^sub>0; I s; bval b s \<rbrakk> 
      \<Longrightarrow> wp \<pi> c (invar_var_goal I R v s) s"
    assumes "\<And>s. \<lbrakk> \<paragraph>''invar-post''; modifies modset s s\<^sub>0; I s; \<not>bval b s \<rbrakk> \<Longrightarrow> Q s"
    assumes [simp]: "modset = ANALYZE (lhsv \<pi> c)"
    shows "wp \<pi> (WHILE_annotRVI R v I b c) Q s\<^sub>0"
    using wp_whileI_modset[of "inv_image R v" I, OF _ assms(2)] assms(1,3,4)
    unfolding WHILE_annotRVI_def GOAL_INDICATION_def invar_var_goal_def
    by auto
  
  lemma wp_while_rl_dfltR[vcg_comb_rules]: 
    "wp \<pi> (WHILE_annotRVI (measure nat) v I b c) Q s\<^sub>0 \<Longrightarrow> wp \<pi> (WHILE_annotVI v I b c) Q s\<^sub>0"
    unfolding WHILE_annotRVI_def WHILE_annotVI_def
    by auto
    

  lemma wlp_while_rl[vcg_comb_rules]:
    assumes "\<paragraph>''invar-initial'' \<Longrightarrow> I s\<^sub>0"
    assumes "\<And>s. \<lbrakk> \<paragraph>''invar-pres''; modifies modset s s\<^sub>0; I s; bval b s \<rbrakk> \<Longrightarrow> wlp \<pi> c I s"
    assumes "\<And>s. \<lbrakk> \<paragraph>''invar-post''; modifies modset s s\<^sub>0; I s; \<not>bval b s \<rbrakk> \<Longrightarrow> Q s"
    assumes [simp]: "modset = ANALYZE (lhsv \<pi> c)"
    shows "wlp \<pi> (WHILE_annotI I b c) Q s\<^sub>0"
    using wlp_whileI_modset[of I, OF _ assms(2)] assms(1,3,4)
    unfolding WHILE_annotI_def GOAL_INDICATION_def
    by auto
    
  lemma wlp_if_rl[vcg_comb_rules]:
    assumes "\<lbrakk>\<paragraph>''then''; bval b s\<rbrakk> \<Longrightarrow> wlp \<pi> c\<^sub>1 Q s"
    assumes "\<lbrakk>\<paragraph>''else''; \<not>bval b s\<rbrakk> \<Longrightarrow> wlp \<pi> c\<^sub>2 Q s"
    shows "wlp \<pi> (IF b THEN c\<^sub>1 ELSE c\<^sub>2) Q s"
    using assms unfolding GOAL_INDICATION_def
    by (simp add: wlp_if_eq)
        
  lemma wp_if_rl[vcg_comb_rules]:
    assumes "\<lbrakk>\<paragraph>''then''; bval b s\<rbrakk> \<Longrightarrow> wp \<pi> c\<^sub>1 Q s"
    assumes "\<lbrakk>\<paragraph>''else''; \<not>bval b s\<rbrakk> \<Longrightarrow> wp \<pi> c\<^sub>2 Q s"
    shows "wp \<pi> (IF b THEN c\<^sub>1 ELSE c\<^sub>2) Q s"
    using assms unfolding GOAL_INDICATION_def
    by (simp add: wp_if_eq)

    
  subsection \<open>VCG Methods\<close>  
      
  subsubsection \<open>Generation\<close>
  
  method i_vcg_step = 
    (rule vcg_comb_rules)
  | ((rule vcg_frame_rules, rule vcg_specs))
  | (simp (no_asm_use) named_ss vcg_bb: )
    
  method i_vcg_gen = (i_vcg_step; i_vcg_gen)?  
    
  method i_vcg_rem_annot = simp named_ss vcg_bb: ANNOTATION_def
  

  subsubsection \<open>Postprocessing\<close>
  
  method i_vcg_remove_hints = ((determ \<open>thin_tac "modifies _ _ _"\<close>)+)?; i_vcg_remove_renamings_tac
    
  
  text \<open>Postprocessing exposes user annotations completely, and then abstracts over variable names.\<close>
  method i_vcg_postprocess =
    i_vcg_modifies_simp?;
    i_vcg_apply_renamings_tac?;
    i_vcg_remove_hints?;
    (unfold BB_PROTECT_def VAR_def)?;
    i_vcg_postprocess_vars

  subsubsection \<open>Main Method\<close>    
    
  method vcg = 
    i_vcg_preprocess; 
    i_vcg_gen; 
    i_vcg_rem_annot?; 
    i_vcg_postprocess
    
  method vcg_cs = vcg;(clarsimp?)
  

end
