section \<open>Priority Maps\<close>
theory IICF_Prio_Map
imports IICF_Map
begin
  text \<open>This interface inherits from maps, and adds some operations\<close>

  (* TODO: Hack! *)  
  lemma uncurry_fun_rel_conv: 
    "(uncurry f, uncurry g) \<in> A\<times>\<^sub>rB \<rightarrow> R \<longleftrightarrow> (f,g)\<in>A\<rightarrow>B\<rightarrow>R"  
    by (auto simp: uncurry_def dest!: fun_relD intro: prod_relI)

  lemma uncurry0_fun_rel_conv: 
    "(uncurry0 f, uncurry0 g) \<in> unit_rel \<rightarrow> R \<longleftrightarrow> (f,g)\<in>R"  
    by (auto dest!: fun_relD)

  lemma RETURN_rel_conv0: "(RETURN f, RETURN g)\<in>\<langle>A\<rangle>nres_rel \<longleftrightarrow> (f,g)\<in>A"
    by (auto simp: nres_rel_def)

  lemma RETURN_rel_conv1: "(RETURN o f, RETURN o g)\<in>A \<rightarrow> \<langle>B\<rangle>nres_rel \<longleftrightarrow> (f,g)\<in>A\<rightarrow>B"
    by (auto simp: nres_rel_def dest!: fun_relD)

  lemma RETURN_rel_conv2: "(RETURN oo f, RETURN oo g)\<in>A \<rightarrow> B \<rightarrow> \<langle>R\<rangle>nres_rel \<longleftrightarrow> (f,g)\<in>A\<rightarrow>B\<rightarrow>R"
    by (auto simp: nres_rel_def dest!: fun_relD)

  lemma RETURN_rel_conv3: "(RETURN ooo f, RETURN ooo g)\<in>A\<rightarrow>B\<rightarrow>C \<rightarrow> \<langle>R\<rangle>nres_rel \<longleftrightarrow> (f,g)\<in>A\<rightarrow>B\<rightarrow>C\<rightarrow>R"
    by (auto simp: nres_rel_def dest!: fun_relD)

  lemmas fref2param_unfold = 
    uncurry_fun_rel_conv uncurry0_fun_rel_conv 
    RETURN_rel_conv0 RETURN_rel_conv1 RETURN_rel_conv2 RETURN_rel_conv3


  (* TODO: Generate these lemmas in sepref_decl_op! *)  
  lemmas param_op_map_update[param] = op_map_update.fref[THEN fref_ncD, unfolded fref2param_unfold]
  lemmas param_op_map_delete[param] = op_map_delete.fref[THEN fref_ncD, unfolded fref2param_unfold]
  lemmas param_op_map_is_empty[param] = op_map_is_empty.fref[THEN fref_ncD, unfolded fref2param_unfold]

  subsection \<open>Additional Operations\<close>

  sepref_decl_op map_update_new: "op_map_update" :: "[\<lambda>((k,v),m). k\<notin>dom m]\<^sub>f (K\<times>\<^sub>rV)\<times>\<^sub>r\<langle>K,V\<rangle>map_rel \<rightarrow> \<langle>K,V\<rangle>map_rel"
    where "single_valued K" "single_valued (K\<inverse>)" .

  sepref_decl_op map_update_ex: "op_map_update" :: "[\<lambda>((k,v),m). k\<in>dom m]\<^sub>f (K\<times>\<^sub>rV)\<times>\<^sub>r\<langle>K,V\<rangle>map_rel \<rightarrow> \<langle>K,V\<rangle>map_rel"
    where "single_valued K" "single_valued (K\<inverse>)" .
    
  sepref_decl_op map_delete_ex: "op_map_delete" :: "[\<lambda>(k,m). k\<in>dom m]\<^sub>f K\<times>\<^sub>r\<langle>K,V\<rangle>map_rel \<rightarrow> \<langle>K,V\<rangle>map_rel"
    where "single_valued K" "single_valued (K\<inverse>)" .

  context
    fixes prio :: "'v \<Rightarrow> 'p::linorder"  
  begin
    sepref_decl_op pm_decrease_key: "op_map_update" 
      :: "[\<lambda>((k,v),m). k\<in>dom m \<and> prio v \<le> prio (the (m k))]\<^sub>f (K\<times>\<^sub>rV)\<times>\<^sub>r\<langle>K,V\<rangle>map_rel \<rightarrow> \<langle>K,(V::('v\<times>'v) set)\<rangle>map_rel"
      where "single_valued K" "single_valued (K\<inverse>)" "IS_BELOW_ID V"
    proof goal_cases  
      case 1 
      have [param]: "((\<le>),(\<le>))\<in>Id\<rightarrow>Id\<rightarrow>bool_rel" by simp
      from 1 show ?case
        apply (parametricity add: param_and_cong1)
        apply (auto simp: IS_BELOW_ID_def map_rel_def dest!: fun_relD)
        done
    qed

    sepref_decl_op pm_increase_key: "op_map_update" 
      :: "[\<lambda>((k,v),m). k\<in>dom m \<and> prio v \<ge> prio (the (m k))]\<^sub>f (K\<times>\<^sub>rV)\<times>\<^sub>r\<langle>K,V\<rangle>map_rel \<rightarrow> \<langle>K,(V::('v\<times>'v) set)\<rangle>map_rel"
      where "single_valued K" "single_valued (K\<inverse>)" "IS_BELOW_ID V"
    proof goal_cases  
      case 1 
      have [param]: "((\<le>),(\<le>))\<in>Id\<rightarrow>Id\<rightarrow>bool_rel" by simp
      from 1 show ?case
        apply (parametricity add: param_and_cong1)
        apply (auto simp: IS_BELOW_ID_def map_rel_def dest!: fun_relD)
        done
    qed


    lemma IS_BELOW_ID_D: "(a,b)\<in>R \<Longrightarrow> IS_BELOW_ID R \<Longrightarrow> a=b" by (auto simp: IS_BELOW_ID_def)

    sepref_decl_op pm_peek_min: "\<lambda>m. SPEC (\<lambda>(k,v). 
      m k = Some v \<and> (\<forall>k' v'. m k' = Some v' \<longrightarrow> prio v \<le> prio v'))"
      :: "[Not o op_map_is_empty]\<^sub>f \<langle>K,V\<rangle>map_rel \<rightarrow> K\<times>\<^sub>r(V::('v\<times>'v) set)"
      where "IS_BELOW_ID V"
      apply (rule frefI)
      apply (intro nres_relI)
      apply (clarsimp simp: pw_le_iff refine_pw_simps)
      apply (rule map_rel_obtain2, assumption, assumption)
      apply1 (intro exI conjI allI impI; assumption?)
    proof -
      fix x y k' v' b w
      assume "(x, y) \<in> \<langle>K, V\<rangle>map_rel" "y k' = Some v'"
      then obtain k v where "(k,k')\<in>K" "(v,v')\<in>V" "x k = Some v"
        by (rule map_rel_obtain1)
        
      assume "IS_BELOW_ID V" "(b, w) \<in> V" 
      with \<open>(v,v')\<in>V\<close> have [simp]: "b=w" "v=v'" by (auto simp: IS_BELOW_ID_def)

      assume "\<forall>k' v'. x k' = Some v' \<longrightarrow> prio b \<le> prio v'"
      with \<open>x k = Some v\<close> show "prio w \<le> prio v'"
        by auto
    qed    

    sepref_decl_op pm_pop_min: "\<lambda>m. SPEC (\<lambda>((k,v),m'). 
        m k = Some v
      \<and> m' = op_map_delete k m  
      \<and> (\<forall>k' v'. m k' = Some v' \<longrightarrow> prio v \<le> prio v')
      )" :: "[Not o op_map_is_empty]\<^sub>f \<langle>K,V\<rangle>map_rel \<rightarrow> (K\<times>\<^sub>r(V::('v\<times>'v) set))\<times>\<^sub>r\<langle>K,V\<rangle>map_rel"
      where "single_valued K" "single_valued (K\<inverse>)" "IS_BELOW_ID V"
      apply (rule frefI)
      apply (intro nres_relI)
      apply (clarsimp simp: pw_le_iff refine_pw_simps simp del: op_map_delete_def)
      apply (rule map_rel_obtain2, assumption, assumption)
      apply (intro exI conjI allI impI; assumption?)
      applyS parametricity
    proof -
      fix x y k' v' b w
      assume "(x, y) \<in> \<langle>K, V\<rangle>map_rel" "y k' = Some v'"
      then obtain k v where "(k,k')\<in>K" "(v,v')\<in>V" "x k = Some v"
        by (rule map_rel_obtain1)
        
      assume "IS_BELOW_ID V" "(b, w) \<in> V" 
      with \<open>(v,v')\<in>V\<close> have [simp]: "b=w" "v=v'" by (auto simp: IS_BELOW_ID_def)

      assume "\<forall>k' v'. x k' = Some v' \<longrightarrow> prio b \<le> prio v'"
      with \<open>x k = Some v\<close> show "prio w \<le> prio v'"
        by auto
    qed    
  end  

end
