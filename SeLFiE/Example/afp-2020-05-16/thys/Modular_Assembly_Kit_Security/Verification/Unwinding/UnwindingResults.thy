theory UnwindingResults
imports AuxiliaryLemmas
begin

context Unwinding
begin
theorem unwinding_theorem_BSD:
"\<lbrakk> lrf ur; osc ur \<rbrakk> \<Longrightarrow> BSD \<V> Tr\<^bsub>(induceES SES)\<^esub>"
proof -
  assume lrf_true: "lrf ur"
  assume osc_true: "osc ur"

  { (* show that the conclusion of the BSP follows from the assumptions *)
    fix \<alpha> \<beta> c
    assume c_in_C: "c \<in> C\<^bsub>\<V>\<^esub>"
    assume \<beta>c\<alpha>_in_Tr: "((\<beta> @ [c]) @ \<alpha>) \<in> Tr\<^bsub>(induceES SES)\<^esub>"
    assume \<alpha>_contains_no_c: "\<alpha> \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []"
 
    from state_from_induceES_trace[OF \<beta>c\<alpha>_in_Tr] obtain s1'
      where s1'_in_S: "s1' \<in> S\<^bsub>SES\<^esub>" 
      and enabled_s1'_\<alpha>: "enabled SES s1' \<alpha>" 
      and s0_\<beta>c_s1': "s0\<^bsub>SES\<^esub> (\<beta> @ [c])\<Longrightarrow>\<^bsub>SES\<^esub> s1'"
      and reachable_s1': "reachable SES s1'"
      by auto
    
    from path_split_single2[OF s0_\<beta>c_s1'] obtain s1
      where s1_in_S: "s1 \<in> S\<^bsub>SES\<^esub>" 
      and s0_\<beta>_s1: "s0\<^bsub>SES\<^esub> \<beta>\<Longrightarrow>\<^bsub>SES\<^esub> s1" 
      and s1_c_s1': "s1 c\<longrightarrow>\<^bsub>SES\<^esub> s1'"
      and reachable_s1: "reachable SES s1"
      by auto

    from s1_in_S s1'_in_S c_in_C reachable_s1 s1_c_s1' lrf_true 
    have s1'_ur_s1: "((s1', s1) \<in> ur)"
      by (simp add: lrf_def, auto)

    from osc_property[OF osc_true s1_in_S s1'_in_S \<alpha>_contains_no_c reachable_s1
      reachable_s1' enabled_s1'_\<alpha> s1'_ur_s1]
    obtain \<alpha>' 
      where \<alpha>'_contains_no_c: "\<alpha>' \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []"
      and \<alpha>'_V_is_\<alpha>_V: "\<alpha>' \<upharpoonleft> V\<^bsub>\<V>\<^esub> = \<alpha> \<upharpoonleft> V\<^bsub>\<V>\<^esub>"
      and enabled_s1_\<alpha>': "enabled SES s1 \<alpha>'" 
      by auto
  
    have \<beta>\<alpha>'_in_Tr: "\<beta> @ \<alpha>' \<in> Tr\<^bsub>(induceES SES)\<^esub>"
    proof -
      note s0_\<beta>_s1
      moreover
      from enabled_s1_\<alpha>' obtain s2
        where "s1 \<alpha>'\<Longrightarrow>\<^bsub>SES\<^esub> s2"
        by (simp add: enabled_def, auto)
      ultimately have "s0\<^bsub>SES\<^esub> (\<beta> @ \<alpha>') \<Longrightarrow>\<^bsub>SES\<^esub> s2"
        by (rule path_trans)
      thus ?thesis
        by (simp add: induceES_def possible_traces_def enabled_def)
    qed
    
    from \<beta>\<alpha>'_in_Tr \<alpha>'_V_is_\<alpha>_V \<alpha>'_contains_no_c have 
      "\<exists>\<alpha>'. ((\<beta> @ \<alpha>') \<in> (Tr\<^bsub>(induceES SES)\<^esub>) \<and> (\<alpha>' \<upharpoonleft> (V\<^bsub>\<V>\<^esub>)) = (\<alpha> \<upharpoonleft> V\<^bsub>\<V>\<^esub>) \<and> \<alpha>' \<upharpoonleft> C\<^bsub>\<V>\<^esub> = [])"
      by auto
  }
  thus ?thesis 
    by (simp add: BSD_def) 
qed

theorem unwinding_theorem_BSI:
"\<lbrakk> lrb ur; osc ur \<rbrakk> \<Longrightarrow> BSI \<V> Tr\<^bsub>(induceES SES)\<^esub>"
proof -
  assume lrb_true: "lrb ur"
  assume osc_true: "osc ur"
  
  {   (* show that the conclusion of the BSP follows from the assumptions *)
    fix \<alpha> \<beta> c
    assume c_in_C: "c \<in> C\<^bsub>\<V>\<^esub>"
    assume \<beta>\<alpha>_in_ind_Tr: "(\<beta> @ \<alpha>) \<in> Tr\<^bsub>(induceES SES)\<^esub>"
    assume \<alpha>_contains_no_c: "\<alpha> \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []"
    
    from state_from_induceES_trace[OF \<beta>\<alpha>_in_ind_Tr] obtain s1
      where s1_in_S : "s1 \<in> S\<^bsub>SES\<^esub>"
      and path_\<beta>_yields_s1:  "s0\<^bsub>SES\<^esub> \<beta>\<Longrightarrow>\<^bsub>SES\<^esub> s1" 
      and enabled_s1_\<alpha>: "enabled SES s1 \<alpha>"
      and reachable_s1: "reachable SES s1"
      by auto

    from reachable_s1 s1_in_S c_in_C  lrb_true 
    have "\<exists>s1'\<in> S\<^bsub>SES\<^esub>. s1 c\<longrightarrow>\<^bsub>SES\<^esub> s1' \<and> (s1, s1') \<in> ur"
      by(simp add: lrb_def) 
    then obtain s1' 
      where s1'_in_S: "s1' \<in> S\<^bsub>SES\<^esub>"
      and s1_trans_c_s1': "s1 c\<longrightarrow>\<^bsub>SES\<^esub> s1'"
      and s1_s1'_in_ur: "(s1, s1') \<in> ur" 
      by auto

    have reachable_s1': "reachable SES s1'" 
    proof -
      from path_\<beta>_yields_s1 s1_trans_c_s1' have "s0\<^bsub>SES\<^esub> (\<beta> @ [c])\<Longrightarrow>\<^bsub>SES\<^esub> s1'"
        by (rule path_trans_single)
      thus ?thesis by (simp add: reachable_def, auto)
    qed
    
    from osc_property[OF osc_true s1'_in_S s1_in_S \<alpha>_contains_no_c 
      reachable_s1' reachable_s1 enabled_s1_\<alpha> s1_s1'_in_ur]
    obtain \<alpha>' 
      where \<alpha>'_contains_no_c: "\<alpha>' \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []"
      and \<alpha>'_V_is_\<alpha>_V: "\<alpha>' \<upharpoonleft> V\<^bsub>\<V>\<^esub> = \<alpha> \<upharpoonleft> V\<^bsub>\<V>\<^esub>"
      and enabled_s1'_\<alpha>': "enabled SES s1' \<alpha>'" 
      by auto

    have \<beta>c\<alpha>'_in_ind_Tr: "\<beta> @ [c] @ \<alpha>' \<in> Tr\<^bsub>(induceES SES)\<^esub>"
    proof -
      from path_\<beta>_yields_s1 s1_trans_c_s1' have "s0\<^bsub>SES\<^esub> (\<beta> @ [c])\<Longrightarrow>\<^bsub>SES\<^esub> s1'"
        by (rule path_trans_single)
      moreover
      from enabled_s1'_\<alpha>' obtain s2
        where "s1' \<alpha>'\<Longrightarrow>\<^bsub>SES\<^esub> s2"
        by (simp add: enabled_def, auto)
      ultimately have "s0\<^bsub>SES\<^esub> ((\<beta> @ [c]) @ \<alpha>')\<Longrightarrow>\<^bsub>SES\<^esub> s2"
        by (rule path_trans)
      thus ?thesis
        by (simp add: induceES_def possible_traces_def enabled_def)
    qed
    
    from \<beta>c\<alpha>'_in_ind_Tr \<alpha>'_V_is_\<alpha>_V \<alpha>'_contains_no_c 
    have "\<exists>\<alpha>'. \<beta> @ c # \<alpha>' \<in> Tr\<^bsub>(induceES SES)\<^esub> \<and> \<alpha>' \<upharpoonleft> V\<^bsub>\<V>\<^esub> = \<alpha> \<upharpoonleft> V\<^bsub>\<V>\<^esub> \<and> \<alpha>' \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []"
      by auto
  }
  thus ?thesis
    by(simp add: BSI_def)
qed

(* unwinding theorem for BSP BSIA *)
theorem unwinding_theorem_BSIA:
"\<lbrakk> lrbe \<rho> ur; osc ur \<rbrakk> \<Longrightarrow> BSIA \<rho> \<V> Tr\<^bsub>(induceES SES)\<^esub>"
proof -
  assume lrbe_true: "lrbe \<rho> ur"
  assume osc_true: "osc ur"
  
  { (* show that the conclusion of the BSP follows from the assumptions *)
    fix \<alpha> \<beta> c
    assume c_in_C: "c \<in> C\<^bsub>\<V>\<^esub>"
    assume \<beta>\<alpha>_in_ind_Tr: "(\<beta> @ \<alpha>) \<in> Tr\<^bsub>(induceES SES)\<^esub>"
    assume \<alpha>_contains_no_c: "\<alpha> \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []"
    
    assume adm: "Adm \<V> \<rho> Tr\<^bsub>(induceES SES)\<^esub> \<beta> c"
    
    from state_from_induceES_trace[OF \<beta>\<alpha>_in_ind_Tr] 
    obtain s1 
      where s1_in_S : "s1 \<in> S\<^bsub>SES\<^esub>"
      and s0_\<beta>_s1:  "s0\<^bsub>SES\<^esub> \<beta>\<Longrightarrow>\<^bsub>SES\<^esub> s1" 
      and enabled_s1_\<alpha>: "enabled SES s1 \<alpha>"  
      and reachable_s1: "reachable SES s1"
      by auto

        (* case distinction whether En is true or not *)
    have "\<exists>\<alpha>'. \<beta> @ [c] @ \<alpha>' \<in> Tr\<^bsub>(induceES SES)\<^esub> \<and> \<alpha>' \<upharpoonleft> V\<^bsub>\<V>\<^esub> = \<alpha> \<upharpoonleft> V\<^bsub>\<V>\<^esub> \<and> \<alpha>' \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []"
    proof cases
      assume en: "En \<rho> s1 c" (*first case, en is true *)

      from reachable_s1 s1_in_S c_in_C en lrbe_true 
      have "\<exists>s1'\<in> S\<^bsub>SES\<^esub>. s1 c\<longrightarrow>\<^bsub>SES\<^esub> s1' \<and> (s1, s1') \<in> ur"
        by(simp add: lrbe_def) 
      then obtain s1' 
        where s1'_in_S: "s1' \<in> S\<^bsub>SES\<^esub>"
        and s1_trans_c_s1': "s1 c\<longrightarrow>\<^bsub>SES\<^esub> s1'"
        and s1_s1'_in_ur: "(s1, s1') \<in> ur" 
        by auto

      have reachable_s1': "reachable SES s1'" 
      proof -
        from s0_\<beta>_s1 s1_trans_c_s1' have "s0\<^bsub>SES\<^esub> (\<beta> @ [c])\<Longrightarrow>\<^bsub>SES\<^esub> s1'"
          by (rule path_trans_single)
        thus ?thesis by (simp add: reachable_def, auto)
      qed 

      from osc_property[OF osc_true s1'_in_S s1_in_S \<alpha>_contains_no_c 
        reachable_s1' reachable_s1 enabled_s1_\<alpha> s1_s1'_in_ur] 
      obtain \<alpha>' 
        where \<alpha>'_contains_no_c: "\<alpha>' \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []"
        and \<alpha>'_V_is_\<alpha>_V: "\<alpha>' \<upharpoonleft> V\<^bsub>\<V>\<^esub> = \<alpha> \<upharpoonleft> V\<^bsub>\<V>\<^esub>"
        and enabled_s1'_\<alpha>': "enabled SES s1' \<alpha>'" 
        by auto
      
      have \<beta>c\<alpha>'_in_ind_Tr: "\<beta> @ [c] @ \<alpha>' \<in> Tr\<^bsub>(induceES SES)\<^esub>"
      proof -
        from s0_\<beta>_s1 s1_trans_c_s1' have "s0\<^bsub>SES\<^esub> (\<beta> @ [c])\<Longrightarrow>\<^bsub>SES\<^esub> s1'"
          by (rule path_trans_single)
        moreover
        from enabled_s1'_\<alpha>' obtain s2
          where "s1' \<alpha>'\<Longrightarrow>\<^bsub>SES\<^esub> s2"
          by (simp add: enabled_def, auto)
        ultimately have "s0\<^bsub>SES\<^esub> ((\<beta> @ [c]) @ \<alpha>')\<Longrightarrow>\<^bsub>SES\<^esub> s2"
          by (rule path_trans)
        thus ?thesis
          by (simp add: induceES_def possible_traces_def enabled_def)
      qed
      
      from \<beta>c\<alpha>'_in_ind_Tr \<alpha>'_V_is_\<alpha>_V \<alpha>'_contains_no_c show ?thesis
        by auto
    next (* second case, en is false *)
      assume not_en: "\<not> En \<rho> s1 c"
      
      let ?A = "(Adm \<V> \<rho> (Tr\<^bsub>(induceES SES)\<^esub>) \<beta> c)"
      let ?E = "\<exists>s \<in> S\<^bsub>SES\<^esub>. (s0\<^bsub>SES\<^esub> \<beta>\<Longrightarrow>\<^bsub>SES\<^esub> s \<and> En \<rho> s c)"

      { (* show the contraposition of Adm_to_En *)
        assume adm: "?A" 
        
        from s0_\<beta>_s1 have \<beta>_in_Tr: "\<beta> \<in> Tr\<^bsub>(induceES SES)\<^esub>"
          by (simp add: induceES_def possible_traces_def enabled_def)
        
        from  \<beta>_in_Tr adm have "?E"
          by (rule Adm_to_En)
      }
      hence Adm_to_En_contr: "\<not> ?E \<Longrightarrow> \<not> ?A"
        by blast
      with s1_in_S s0_\<beta>_s1 not_en have not_adm: "\<not> ?A"
        by auto
      with adm show ?thesis
        by auto
    qed
  }
  thus ?thesis 
    by (simp add: BSIA_def)
qed

theorem unwinding_theorem_FCD:
"\<lbrakk> fcrf \<Gamma> ur; osc ur \<rbrakk> \<Longrightarrow> FCD \<Gamma> \<V> Tr\<^bsub>(induceES SES)\<^esub>"
proof - 
  assume fcrf: "fcrf \<Gamma> ur"
  assume osc: "osc ur"

  { (* show that the conclusion of the BSP follows from the assumptions *)
    fix \<alpha> \<beta> c v

    assume c_in_C_inter_Y: "c \<in> (C\<^bsub>\<V>\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>\<^esub>)"
    assume v_in_V_inter_Nabla: "v \<in> (V\<^bsub>\<V>\<^esub> \<inter> \<nabla>\<^bsub>\<Gamma>\<^esub>)"
    assume \<beta>cv\<alpha>_in_Tr: "((\<beta> @ [c] @ [v]) @ \<alpha>) \<in> Tr\<^bsub>(induceES SES)\<^esub>"
    assume \<alpha>_contains_no_c: "\<alpha> \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []"

    from state_from_induceES_trace[OF \<beta>cv\<alpha>_in_Tr] obtain s1'
      where s1'_in_S: "s1' \<in> S\<^bsub>SES\<^esub>"
      and s0_\<beta>cv_s1': "s0\<^bsub>SES\<^esub> (\<beta> @ ([c] @ [v]))\<Longrightarrow>\<^bsub>SES\<^esub> s1'"
      and enabled_s1'_\<alpha>: "enabled SES s1' \<alpha>"
      and reachable_s1': "reachable SES s1'"
      by auto
    
    from path_split2[OF s0_\<beta>cv_s1'] obtain s1 
      where s1_in_S: "s1 \<in> S\<^bsub>SES\<^esub>"
      and s0_\<beta>_s1: "s0\<^bsub>SES\<^esub> \<beta>\<Longrightarrow>\<^bsub>SES\<^esub> s1"
      and s1_cv_s1': "s1 ([c] @ [v])\<Longrightarrow>\<^bsub>SES\<^esub> s1'"
      and reachable_s1: "reachable SES s1"
      by (auto)

    from c_in_C_inter_Y v_in_V_inter_Nabla s1_in_S s1'_in_S reachable_s1 s1_cv_s1' fcrf
    have "\<exists>s1'' \<in> S\<^bsub>SES\<^esub>. \<exists>\<delta>. (\<forall>d \<in> (set \<delta>). d \<in> (N\<^bsub>\<V>\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>\<^esub>)) \<and>
      s1 (\<delta> @ [v])\<Longrightarrow>\<^bsub>SES\<^esub> s1'' \<and> (s1', s1'') \<in> ur"
      by (simp add: fcrf_def)
    then obtain s1'' \<delta>
      where s1''_in_S: "s1'' \<in> S\<^bsub>SES\<^esub>"
      and \<delta>_in_N_inter_Delta_star: "(\<forall>d \<in> (set \<delta>). d \<in> (N\<^bsub>\<V>\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>\<^esub>))"
      and s1_\<delta>v_s1'': "s1 (\<delta> @ [v])\<Longrightarrow>\<^bsub>SES\<^esub> s1''"
      and s1'_ur_s1'': "(s1', s1'') \<in> ur" 
      by auto
      
    have reachable_s1'': "reachable SES s1''"
    proof -
      from s0_\<beta>_s1 s1_\<delta>v_s1'' have "s0\<^bsub>SES\<^esub> (\<beta> @ (\<delta> @ [v]))\<Longrightarrow>\<^bsub>SES\<^esub> s1''"
        by (rule path_trans)
      thus ?thesis
        by (simp add: reachable_def, auto)
    qed

    from osc_property[OF  osc s1''_in_S s1'_in_S \<alpha>_contains_no_c 
      reachable_s1'' reachable_s1' enabled_s1'_\<alpha> s1'_ur_s1'']
    obtain \<alpha>' 
      where  \<alpha>'_contains_no_c: "\<alpha>' \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []"
      and \<alpha>'_V_is_\<alpha>_V: "\<alpha>' \<upharpoonleft> V\<^bsub>\<V>\<^esub> = \<alpha> \<upharpoonleft> V\<^bsub>\<V>\<^esub>"
      and enabled_s1''_\<alpha>': "enabled SES s1'' \<alpha>'" 
      by auto

    have \<beta>\<delta>v\<alpha>'_in_Tr: "\<beta> @ \<delta> @ [v] @ \<alpha>' \<in> Tr\<^bsub>(induceES SES)\<^esub>"
      proof -
        from s0_\<beta>_s1 s1_\<delta>v_s1'' have "s0\<^bsub>SES\<^esub> (\<beta> @ \<delta> @ [v])\<Longrightarrow>\<^bsub>SES\<^esub> s1''"
          by (rule path_trans)
        moreover
        from enabled_s1''_\<alpha>' obtain s2
          where "s1'' \<alpha>'\<Longrightarrow>\<^bsub>SES\<^esub> s2"
          by (simp add: enabled_def, auto)
        ultimately have "s0\<^bsub>SES\<^esub> ((\<beta> @ \<delta> @ [v]) @ \<alpha>')\<Longrightarrow>\<^bsub>SES\<^esub> s2"
          by (rule path_trans)
        thus ?thesis
          by (simp add: induceES_def possible_traces_def enabled_def)
      qed

      from \<delta>_in_N_inter_Delta_star \<beta>\<delta>v\<alpha>'_in_Tr \<alpha>'_V_is_\<alpha>_V \<alpha>'_contains_no_c
      have "\<exists>\<alpha>'. \<exists>\<delta>'. set \<delta>' \<subseteq> (N\<^bsub>\<V>\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>\<^esub>) \<and> \<beta> @ \<delta>' @ [v] @ \<alpha>' \<in> Tr\<^bsub>(induceES SES)\<^esub> 
        \<and> \<alpha>' \<upharpoonleft> V\<^bsub>\<V>\<^esub> = \<alpha> \<upharpoonleft> V\<^bsub>\<V>\<^esub> \<and> \<alpha>' \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []"
        by auto
  }
  thus ?thesis
    by (simp add: FCD_def)
qed

theorem unwinding_theorem_FCI:
"\<lbrakk> fcrb \<Gamma> ur; osc ur \<rbrakk> \<Longrightarrow> FCI \<Gamma> \<V> Tr\<^bsub>(induceES SES)\<^esub>"
proof -
  assume fcrb: "fcrb \<Gamma> ur"
  assume osc: "osc ur"

  { (* show that the conclusion of the BSP follows from the assumptions *)
    fix \<alpha> \<beta> c v

    assume c_in_C_inter_Y: "c \<in> (C\<^bsub>\<V>\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>\<^esub>)"
    assume v_in_V_inter_Nabla: "v \<in> (V\<^bsub>\<V>\<^esub> \<inter> \<nabla>\<^bsub>\<Gamma>\<^esub>)"
    assume \<beta>v\<alpha>_in_Tr: "((\<beta> @ [v]) @ \<alpha>) \<in> Tr\<^bsub>(induceES SES)\<^esub>"
    assume \<alpha>_contains_no_c: "\<alpha> \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []"
  
    from state_from_induceES_trace[OF \<beta>v\<alpha>_in_Tr] obtain s1''
      where s1''_in_S: "s1'' \<in> S\<^bsub>SES\<^esub>"
      and s0_\<beta>v_s1'': "s0\<^bsub>SES\<^esub> (\<beta> @ [v]) \<Longrightarrow>\<^bsub>SES\<^esub> s1''"
      and enabled_s1''_\<alpha>: "enabled SES s1'' \<alpha>"
      and reachable_s1'': "reachable SES s1''"
      by auto

    from path_split_single2[OF s0_\<beta>v_s1''] obtain s1 
      where s1_in_S: "s1 \<in> S\<^bsub>SES\<^esub>"
      and s0_\<beta>_s1: "s0\<^bsub>SES\<^esub> \<beta>\<Longrightarrow>\<^bsub>SES\<^esub> s1"
      and s1_v_s1'': "s1 v\<longrightarrow>\<^bsub>SES\<^esub> s1''"
      and reachable_s1: "reachable SES s1"
      by (auto)

    from c_in_C_inter_Y v_in_V_inter_Nabla s1_in_S 
      s1''_in_S reachable_s1 s1_v_s1'' fcrb 
    have "\<exists>s1' \<in> S\<^bsub>SES\<^esub>. \<exists>\<delta>. (\<forall>d \<in> (set \<delta>). d \<in> (N\<^bsub>\<V>\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>\<^esub>))
      \<and> s1 ([c] @ \<delta> @ [v])\<Longrightarrow>\<^bsub>SES\<^esub> s1'
      \<and> (s1'', s1') \<in> ur"
      by (simp add: fcrb_def)
    then obtain s1' \<delta>
      where s1'_in_S: "s1' \<in> S\<^bsub>SES\<^esub>"
      and \<delta>_in_N_inter_Delta_star: "(\<forall>d \<in> (set \<delta>). d \<in> (N\<^bsub>\<V>\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>\<^esub>))"
      and s1_c\<delta>v_s1': "s1 ([c] @ \<delta> @ [v])\<Longrightarrow>\<^bsub>SES\<^esub> s1'"
      and s1''_ur_s1': "(s1'', s1') \<in> ur" 
      by auto

    have reachable_s1': "reachable SES s1'"
    proof -
      from s0_\<beta>_s1 s1_c\<delta>v_s1' have "s0\<^bsub>SES\<^esub> (\<beta> @ ([c] @ \<delta> @ [v]))\<Longrightarrow>\<^bsub>SES\<^esub> s1'"
        by (rule path_trans)
      thus ?thesis
        by (simp add: reachable_def, auto)
    qed
    
    from osc_property[OF osc s1'_in_S s1''_in_S \<alpha>_contains_no_c 
      reachable_s1' reachable_s1'' enabled_s1''_\<alpha> s1''_ur_s1']
    obtain \<alpha>' 
      where  \<alpha>'_contains_no_c: "\<alpha>' \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []"
      and \<alpha>'_V_is_\<alpha>_V: "\<alpha>' \<upharpoonleft> V\<^bsub>\<V>\<^esub> = \<alpha> \<upharpoonleft> V\<^bsub>\<V>\<^esub>"
      and enabled_s1'_\<alpha>': "enabled SES s1' \<alpha>'" 
      by auto

    have \<beta>c\<delta>v\<alpha>'_in_Tr: "\<beta> @ [c] @ \<delta> @ [v] @ \<alpha>' \<in> Tr\<^bsub>(induceES SES)\<^esub>"
    proof -
      let ?l1 = "\<beta> @ [c] @ \<delta> @ [v]"
      let ?l2 = "\<alpha>'"
      from s0_\<beta>_s1 s1_c\<delta>v_s1' have "s0\<^bsub>SES\<^esub> (?l1)\<Longrightarrow>\<^bsub>SES\<^esub> s1'"
        by (rule path_trans)
      moreover
      from enabled_s1'_\<alpha>' obtain s1337 where "s1' ?l2 \<Longrightarrow>\<^bsub>SES\<^esub> s1337"
        by (simp add: enabled_def, auto)
      ultimately have "s0\<^bsub>SES\<^esub> (?l1 @ ?l2)\<Longrightarrow>\<^bsub>SES\<^esub> s1337"
        by (rule path_trans)
      thus ?thesis
        by (simp add: induceES_def possible_traces_def enabled_def) 
    qed

from \<delta>_in_N_inter_Delta_star \<beta>c\<delta>v\<alpha>'_in_Tr \<alpha>'_V_is_\<alpha>_V \<alpha>'_contains_no_c
    have "\<exists>\<alpha>' \<delta>'.
      set \<delta>' \<subseteq> (N\<^bsub>\<V>\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>\<^esub>) \<and> \<beta> @ [c] @ \<delta>' @ [v] @ \<alpha>' \<in> Tr\<^bsub>(induceES SES)\<^esub> 
      \<and> \<alpha>' \<upharpoonleft> V\<^bsub>\<V>\<^esub> = \<alpha> \<upharpoonleft> V\<^bsub>\<V>\<^esub> \<and> \<alpha>' \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []"
      by auto
  }
  thus ?thesis
    by(simp add: FCI_def)     
qed

theorem unwinding_theorem_FCIA:
"\<lbrakk> fcrbe \<Gamma> \<rho> ur; osc ur \<rbrakk> \<Longrightarrow> FCIA \<rho> \<Gamma> \<V> Tr\<^bsub>(induceES SES)\<^esub>"
proof -
  assume fcrbe: "fcrbe \<Gamma> \<rho> ur"
  assume osc: "osc ur"

  { (* show that the conclusion of the BSP follows from the assumptions *)
    fix \<alpha> \<beta> c v

    assume c_in_C_inter_Y: "c \<in> (C\<^bsub>\<V>\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>\<^esub>)"
    assume v_in_V_inter_Nabla: "v \<in> (V\<^bsub>\<V>\<^esub> \<inter> \<nabla>\<^bsub>\<Gamma>\<^esub>)"
    assume \<beta>v\<alpha>_in_Tr: "((\<beta> @ [v]) @ \<alpha>) \<in> Tr\<^bsub>(induceES SES)\<^esub>"
    assume \<alpha>_contains_no_c: "\<alpha> \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []"
    assume adm: "Adm \<V> \<rho> Tr\<^bsub>(induceES SES)\<^esub> \<beta> c"

    from state_from_induceES_trace[OF \<beta>v\<alpha>_in_Tr] obtain s1''
      where s1''_in_S: "s1'' \<in> S\<^bsub>SES\<^esub>"
      and s0_\<beta>v_s1'': "s0\<^bsub>SES\<^esub> (\<beta> @ [v])\<Longrightarrow>\<^bsub>SES\<^esub> s1''"
      and enabled_s1''_\<alpha>: "enabled SES s1'' \<alpha>"
      and reachable_s1'': "reachable SES s1''"
      by auto

    from path_split_single2[OF s0_\<beta>v_s1''] obtain s1 
      where s1_in_S: "s1 \<in> S\<^bsub>SES\<^esub>"
      and s0_\<beta>_s1: "s0\<^bsub>SES\<^esub> \<beta>\<Longrightarrow>\<^bsub>SES\<^esub> s1"
      and s1_v_s1'': "s1 v\<longrightarrow>\<^bsub>SES\<^esub> s1''"
      and reachable_s1: "reachable SES s1"
      by (auto)
    
    have "\<exists>\<alpha>' \<delta>'.(set \<delta>' \<subseteq> (N\<^bsub>\<V>\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>\<^esub>) \<and> \<beta> @ [c] @ \<delta>' @ [v] @ \<alpha>' \<in> Tr\<^bsub>(induceES SES)\<^esub> 
      \<and> \<alpha>' \<upharpoonleft> V\<^bsub>\<V>\<^esub> = \<alpha> \<upharpoonleft> V\<^bsub>\<V>\<^esub> \<and> \<alpha>' \<upharpoonleft> C\<^bsub>\<V>\<^esub> = [])"
    proof (cases)
      assume en: "En \<rho> s1 c"

      from c_in_C_inter_Y v_in_V_inter_Nabla s1_in_S s1''_in_S reachable_s1 s1_v_s1'' en fcrbe
      have "\<exists>s1' \<in> S\<^bsub>SES\<^esub>. \<exists>\<delta>. (\<forall>d \<in> (set \<delta>). d \<in> (N\<^bsub>\<V>\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>\<^esub>))
        \<and> s1 ([c] @ \<delta> @ [v]) \<Longrightarrow>\<^bsub>SES\<^esub> s1'
        \<and> (s1'', s1') \<in> ur"
        by (simp add: fcrbe_def)
      then  obtain s1' \<delta>
        where s1'_in_S: "s1' \<in> S\<^bsub>SES\<^esub>"
        and \<delta>_in_N_inter_Delta_star: "(\<forall>d \<in> (set \<delta>). d \<in> (N\<^bsub>\<V>\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>\<^esub>))"
        and s1_c\<delta>v_s1': "s1 ([c] @ \<delta> @ [v]) \<Longrightarrow>\<^bsub>SES\<^esub> s1'"
        and s1''_ur_s1': "(s1'', s1') \<in> ur"
        by (auto)

      have reachable_s1': "reachable SES s1'"
      proof -
        from s0_\<beta>_s1 s1_c\<delta>v_s1' have "s0\<^bsub>SES\<^esub> (\<beta> @ ([c] @ \<delta> @ [v]))\<Longrightarrow>\<^bsub>SES\<^esub> s1'"
          by (rule path_trans)
        thus ?thesis
          by (simp add: reachable_def, auto)
      qed
      
      from osc_property[OF osc s1'_in_S s1''_in_S \<alpha>_contains_no_c reachable_s1' 
        reachable_s1'' enabled_s1''_\<alpha> s1''_ur_s1']
      obtain \<alpha>' 
        where  \<alpha>'_contains_no_c: "\<alpha>' \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []"
        and \<alpha>'_V_is_\<alpha>_V: "\<alpha>' \<upharpoonleft> V\<^bsub>\<V>\<^esub> = \<alpha> \<upharpoonleft> V\<^bsub>\<V>\<^esub>"
        and enabled_s1'_\<alpha>': "enabled SES s1' \<alpha>'" 
        by auto

      have \<beta>c\<delta>v\<alpha>'_in_Tr: "\<beta> @ [c] @ \<delta> @ [v] @ \<alpha>' \<in> Tr\<^bsub>(induceES SES)\<^esub>"
      proof -
        let ?l1 = "\<beta> @ [c] @ \<delta> @ [v]"
        let ?l2 = "\<alpha>'"
        from s0_\<beta>_s1 s1_c\<delta>v_s1' have "s0\<^bsub>SES\<^esub> (?l1)\<Longrightarrow>\<^bsub>SES\<^esub> s1'"
          by (rule path_trans)
        moreover
        from enabled_s1'_\<alpha>' obtain s1337 where "s1' ?l2\<Longrightarrow>\<^bsub>SES\<^esub> s1337"
          by (simp add: enabled_def, auto)
        ultimately have "s0\<^bsub>SES\<^esub> (?l1 @ ?l2)\<Longrightarrow>\<^bsub>SES\<^esub> s1337"
          by (rule path_trans)
        thus ?thesis
          by (simp add: induceES_def possible_traces_def enabled_def) 
      qed

      from \<delta>_in_N_inter_Delta_star \<beta>c\<delta>v\<alpha>'_in_Tr \<alpha>'_V_is_\<alpha>_V \<alpha>'_contains_no_c
      show ?thesis
        by auto
    next
      assume not_en: "\<not> En \<rho> s1 c"
      
      let ?A = "(Adm \<V> \<rho> Tr\<^bsub>(induceES SES)\<^esub> \<beta> c)"
      let ?E = "\<exists>s \<in> S\<^bsub>SES\<^esub>. (s0\<^bsub>SES\<^esub> \<beta>\<Longrightarrow>\<^bsub>SES\<^esub> s \<and> En \<rho> s c)"

      { (* show the contraposition of Adm_to_En *)
        assume adm: "?A" 
        
        from s0_\<beta>_s1 have \<beta>_in_Tr: "\<beta> \<in> Tr\<^bsub>(induceES SES)\<^esub>"
          by (simp add: induceES_def possible_traces_def enabled_def)
        
        from  \<beta>_in_Tr adm have "?E"
          by (rule Adm_to_En)
      }
      hence Adm_to_En_contr: "\<not> ?E \<Longrightarrow> \<not> ?A"
        by blast
      with s1_in_S s0_\<beta>_s1 not_en have not_adm: "\<not> ?A"
        by auto
      with adm show ?thesis
        by auto
    qed  
  }
  thus ?thesis
    by (simp add: FCIA_def)
qed

theorem unwinding_theorem_SD:
"\<lbrakk> \<V>' = \<lparr> V = (V\<^bsub>\<V>\<^esub> \<union> N\<^bsub>\<V>\<^esub>), N = {}, C = C\<^bsub>\<V>\<^esub> \<rparr>; 
  Unwinding.lrf SES \<V>' ur; Unwinding.osc SES \<V>' ur \<rbrakk> 
  \<Longrightarrow> SD \<V> Tr\<^bsub>(induceES SES)\<^esub>"
proof -
  assume view'_def : "\<V>' = \<lparr>V = (V\<^bsub>\<V>\<^esub> \<union> N\<^bsub>\<V>\<^esub>), N = {}, C = C\<^bsub>\<V>\<^esub>\<rparr>"
  assume lrf_view' : "Unwinding.lrf SES \<V>' ur"
  assume osc_view' : "Unwinding.osc SES \<V>' ur"

  interpret modified_view: Unwinding "SES" "\<V>'"
    by (unfold_locales, rule validSES, simp add: view'_def modified_view_valid)
      
  from lrf_view' osc_view' have BSD_view' : "BSD \<V>' Tr\<^bsub>(induceES SES)\<^esub>"
     by (rule_tac ur="ur" in modified_view.unwinding_theorem_BSD)
  with view'_def BSD_implies_SD_for_modified_view show ?thesis 
    by auto
qed

theorem unwinding_theorem_SI:
"\<lbrakk> \<V>' = \<lparr> V = (V\<^bsub>\<V>\<^esub> \<union> N\<^bsub>\<V>\<^esub>), N = {}, C = C\<^bsub>\<V>\<^esub> \<rparr>; 
  Unwinding.lrb SES \<V>' ur; Unwinding.osc SES \<V>' ur \<rbrakk> 
  \<Longrightarrow> SI \<V> Tr\<^bsub>(induceES SES)\<^esub>"
proof -
  assume view'_def : "\<V>' = \<lparr>V = V\<^bsub>\<V>\<^esub> \<union> N\<^bsub>\<V>\<^esub>, N = {}, C = C\<^bsub>\<V>\<^esub>\<rparr>"
  assume lrb_view' : "Unwinding.lrb SES \<V>' ur"
  assume osc_view' : "Unwinding.osc SES \<V>' ur"

  interpret modified_view: Unwinding "SES" "\<V>'"
    by (unfold_locales, rule validSES, simp add: view'_def modified_view_valid)

  from lrb_view' osc_view' have BSI_view' : "BSI \<V>' Tr\<^bsub>(induceES SES)\<^esub>"
     by (rule_tac ur="ur" in modified_view.unwinding_theorem_BSI)
  with view'_def BSI_implies_SI_for_modified_view show ?thesis 
    by auto
qed

theorem unwinding_theorem_SIA: 
"\<lbrakk> \<V>' = \<lparr> V = (V\<^bsub>\<V>\<^esub> \<union> N\<^bsub>\<V>\<^esub>), N = {}, C = C\<^bsub>\<V>\<^esub> \<rparr>; \<rho> \<V> = \<rho> \<V>'; 
  Unwinding.lrbe SES \<V>' \<rho> ur; Unwinding.osc SES \<V>' ur \<rbrakk> 
  \<Longrightarrow> SIA \<rho> \<V> Tr\<^bsub>(induceES SES)\<^esub>"
proof -
  assume view'_def : "\<V>' = \<lparr>V = V\<^bsub>\<V>\<^esub> \<union> N\<^bsub>\<V>\<^esub>, N = {}, C = C\<^bsub>\<V>\<^esub>\<rparr>"
  assume \<rho>_eq : "\<rho> \<V> = \<rho> \<V>'"
  assume lrbe_view' : "Unwinding.lrbe SES \<V>' \<rho> ur"
  assume osc_view' : "Unwinding.osc SES \<V>' ur"

  interpret modified_view: Unwinding "SES" "\<V>'"
    by (unfold_locales, rule validSES, simp add: view'_def modified_view_valid)

  from lrbe_view' osc_view' have BSIA_view' : "BSIA \<rho> \<V>' Tr\<^bsub>(induceES SES)\<^esub>"
     by (rule_tac ur="ur" in modified_view.unwinding_theorem_BSIA)
  with view'_def BSIA_implies_SIA_for_modified_view \<rho>_eq show ?thesis 
    by auto
qed 

theorem unwinding_theorem_SR:
"\<lbrakk> \<V>' = \<lparr> V = (V\<^bsub>\<V>\<^esub> \<union> N\<^bsub>\<V>\<^esub>), N = {}, C = C\<^bsub>\<V>\<^esub> \<rparr>; 
  Unwinding.lrf SES \<V>' ur; Unwinding.osc SES \<V>' ur \<rbrakk> 
  \<Longrightarrow> SR \<V> Tr\<^bsub>(induceES SES)\<^esub>"
proof -
  assume view'_def : "\<V>' = \<lparr>V = V\<^bsub>\<V>\<^esub> \<union> N\<^bsub>\<V>\<^esub>, N = {}, C = C\<^bsub>\<V>\<^esub>\<rparr>"
  assume lrf_view' : "Unwinding.lrf SES \<V>' ur"
  assume osc_view' : "Unwinding.osc SES \<V>' ur"

  from lrf_view' osc_view' view'_def have S_view : "SD \<V> Tr\<^bsub>(induceES SES)\<^esub>"
     by (rule_tac ur="ur" in  unwinding_theorem_SD, auto)
  with SD_implies_SR show ?thesis
    by auto
qed

theorem unwinding_theorem_D:
"\<lbrakk> lrf ur; osc ur \<rbrakk> \<Longrightarrow> D \<V> Tr\<^bsub>(induceES SES)\<^esub>"
proof -
  assume "lrf ur"
  and "osc ur"
  hence "BSD \<V> Tr\<^bsub>(induceES SES)\<^esub>"
    by (rule unwinding_theorem_BSD)
  thus ?thesis
    by (rule BSD_implies_D)
qed

theorem unwinding_theorem_I:
"\<lbrakk> lrb ur; osc ur \<rbrakk> \<Longrightarrow> I \<V> Tr\<^bsub>(induceES SES)\<^esub>"
proof -
  assume "lrb ur"
  and "osc ur"
  hence "BSI \<V> Tr\<^bsub>(induceES SES)\<^esub>"
    by (rule unwinding_theorem_BSI)
  thus ?thesis
    by (rule BSI_implies_I)
qed

theorem unwinding_theorem_IA:
"\<lbrakk> lrbe \<rho> ur; osc ur \<rbrakk> \<Longrightarrow> IA \<rho> \<V> Tr\<^bsub>(induceES SES)\<^esub>"
proof -
  assume "lrbe \<rho> ur"
  and "osc ur"
  hence "BSIA \<rho> \<V> Tr\<^bsub>(induceES SES)\<^esub>"
    by (rule unwinding_theorem_BSIA)
  thus ?thesis
    by (rule BSIA_implies_IA)
qed

theorem unwinding_theorem_R:
"\<lbrakk> lrf ur; osc ur \<rbrakk> \<Longrightarrow> R \<V> (Tr\<^bsub>(induceES SES)\<^esub>)"
proof -
  assume "lrf ur"
  and "osc ur"
  hence "BSD \<V> Tr\<^bsub>(induceES SES)\<^esub>"
    by (rule unwinding_theorem_BSD)
  hence "D \<V> Tr\<^bsub>(induceES SES)\<^esub>"
    by (rule BSD_implies_D)
  thus ?thesis
    by (rule D_implies_R)
qed

end

end
