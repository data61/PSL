theory CompositionalityResults
imports GeneralizedZippingLemma CompositionSupport
begin

context Compositionality 
begin


(* Theorem 6.4.1 case 1 *)
theorem compositionality_BSD: 
"\<lbrakk> BSD \<V>1 Tr\<^bsub>ES1\<^esub>; BSD \<V>2 Tr\<^bsub>ES2\<^esub> \<rbrakk> \<Longrightarrow> BSD \<V> Tr\<^bsub>(ES1 \<parallel> ES2)\<^esub>"
proof -
  assume BSD_Tr1_v1: "BSD \<V>1 Tr\<^bsub>ES1\<^esub>"
  assume BSD_Tr2_v2: "BSD \<V>2 Tr\<^bsub>ES2\<^esub>"
  {
    fix \<alpha> \<beta> c
    assume c_in_Cv: "c \<in> C\<^bsub>\<V>\<^esub>"
    assume \<beta>c\<alpha>_in_Tr: "(\<beta> @ [c] @ \<alpha>) \<in> Tr\<^bsub>(ES1 \<parallel> ES2)\<^esub>"
    assume \<alpha>_contains_no_c: "\<alpha> \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []"

    interpret CSES1: CompositionSupport "ES1" "\<V>" "\<V>1"  
      using propSepViews unfolding properSeparationOfViews_def 
      by (simp add: CompositionSupport_def validES1 validV1)

    interpret CSES2: CompositionSupport "ES2" "\<V>" "\<V>2"
      using propSepViews unfolding properSeparationOfViews_def 
      by (simp add: CompositionSupport_def validES2 validV2)

    from \<beta>c\<alpha>_in_Tr 
    have  \<beta>c\<alpha>_E1_in_Tr1: "((\<beta> @ [c] @ \<alpha>) \<upharpoonleft> E\<^bsub>ES1\<^esub>) \<in> Tr\<^bsub>ES1\<^esub>"
      and \<beta>c\<alpha>_E2_in_Tr2: "((\<beta> @ [c] @ \<alpha>) \<upharpoonleft> E\<^bsub>ES2\<^esub>) \<in> Tr\<^bsub>ES2\<^esub>"
      by (auto, simp add: composeES_def)+

    from composeES_yields_ES validES1 validES2 have "ES_valid (ES1 \<parallel> ES2)"
      by auto

    with \<beta>c\<alpha>_in_Tr have "set \<beta> \<subseteq> E\<^bsub>(ES1 \<parallel> ES2)\<^esub>"
      by (simp add: ES_valid_def traces_contain_events_def, auto)
    moreover
    have "set (\<alpha> \<upharpoonleft> V\<^bsub>\<V>\<^esub>) \<subseteq> V\<^bsub>\<V>\<^esub>"
      by (simp add: projection_def, auto)
    moreover 
    have "(\<alpha> \<upharpoonleft> V\<^bsub>\<V>\<^esub>) \<upharpoonleft> V\<^bsub>\<V>\<^esub> = (\<alpha> \<upharpoonleft> V\<^bsub>\<V>\<^esub>)"
      by (simp add: projection_def)
    moreover
    from CSES1.BSD_in_subsystem[OF c_in_Cv \<beta>c\<alpha>_E1_in_Tr1 BSD_Tr1_v1]
    obtain \<alpha>1' 
      where \<alpha>1'_1: "((\<beta> \<upharpoonleft> E\<^bsub>ES1\<^esub>) @ \<alpha>1') \<in> Tr\<^bsub>ES1\<^esub>"
      and \<alpha>1'_2: "(\<alpha>1' \<upharpoonleft> V\<^bsub>\<V>1\<^esub>) = (\<alpha> \<upharpoonleft> V\<^bsub>\<V>1\<^esub>)"
      and "\<alpha>1' \<upharpoonleft> C\<^bsub>\<V>1\<^esub> = []"
      by auto
    moreover
    from \<alpha>1'_1 validES1 have \<alpha>1'_in_E1: "set \<alpha>1' \<subseteq> E\<^bsub>ES1\<^esub>"
      by (simp add: ES_valid_def traces_contain_events_def, auto)
    moreover
    from \<alpha>1'_2 propSepViews have "((\<alpha> \<upharpoonleft> V\<^bsub>\<V>\<^esub>) \<upharpoonleft> E\<^bsub>ES1\<^esub>) = (\<alpha>1' \<upharpoonleft> V\<^bsub>\<V>\<^esub>)"
      proof -
        have "((\<alpha> \<upharpoonleft> V\<^bsub>\<V>\<^esub>) \<upharpoonleft> E\<^bsub>ES1\<^esub>) = \<alpha> \<upharpoonleft> (V\<^bsub>\<V>\<^esub> \<inter> E\<^bsub>ES1\<^esub>)"
          by (simp only: projection_def, auto)
        with propSepViews have "((\<alpha> \<upharpoonleft> V\<^bsub>\<V>\<^esub>) \<upharpoonleft> E\<^bsub>ES1\<^esub>) = (\<alpha> \<upharpoonleft> V\<^bsub>\<V>1\<^esub>)"
          unfolding properSeparationOfViews_def by auto
        moreover
        from \<alpha>1'_2 have "(\<alpha>1' \<upharpoonleft> V\<^bsub>\<V>1\<^esub>) = (\<alpha>1' \<upharpoonleft> V\<^bsub>\<V>\<^esub>)"
          proof -
            from \<alpha>1'_in_E1 have "\<alpha>1' \<upharpoonleft> E\<^bsub>ES1\<^esub> = \<alpha>1'"
              by (simp add: list_subset_iff_projection_neutral)
            hence "(\<alpha>1' \<upharpoonleft> E\<^bsub>ES1\<^esub>) \<upharpoonleft> V\<^bsub>\<V>\<^esub> = \<alpha>1' \<upharpoonleft> V\<^bsub>\<V>\<^esub>"
              by simp
            with Vv_is_Vv1_union_Vv2 have "(\<alpha>1' \<upharpoonleft> E\<^bsub>ES1\<^esub>) \<upharpoonleft> (V\<^bsub>\<V>1\<^esub> \<union> V\<^bsub>\<V>2\<^esub>) = \<alpha>1' \<upharpoonleft> V\<^bsub>\<V>\<^esub>"
              by simp
            hence "\<alpha>1' \<upharpoonleft> (E\<^bsub>ES1\<^esub> \<inter> (V\<^bsub>\<V>1\<^esub> \<union> V\<^bsub>\<V>2\<^esub>)) = \<alpha>1' \<upharpoonleft> V\<^bsub>\<V>\<^esub>"
              by (simp only: projection_def, auto)
            hence "\<alpha>1' \<upharpoonleft> (E\<^bsub>ES1\<^esub> \<inter> V\<^bsub>\<V>1\<^esub> \<union> E\<^bsub>ES1\<^esub> \<inter> V\<^bsub>\<V>2\<^esub>) = \<alpha>1' \<upharpoonleft> V\<^bsub>\<V>\<^esub>"
              by (simp add: Int_Un_distrib)
            moreover 
            from validV1 have "E\<^bsub>ES1\<^esub> \<inter> V\<^bsub>\<V>1\<^esub> = V\<^bsub>\<V>1\<^esub>"
              by (simp add: isViewOn_def V_valid_def 
                VC_disjoint_def VN_disjoint_def NC_disjoint_def, auto)
            ultimately have "\<alpha>1' \<upharpoonleft> (V\<^bsub>\<V>1\<^esub> \<union> E\<^bsub>ES1\<^esub> \<inter> V\<^bsub>\<V>2\<^esub>) = \<alpha>1' \<upharpoonleft> V\<^bsub>\<V>\<^esub>"
              by simp
            moreover
            have "E\<^bsub>ES1\<^esub> \<inter> V\<^bsub>\<V>2\<^esub> \<subseteq> V\<^bsub>\<V>1\<^esub>" 
              proof -
                from propSepViews Vv_is_Vv1_union_Vv2 have "(V\<^bsub>\<V>1\<^esub> \<union> V\<^bsub>\<V>2\<^esub>) \<inter> E\<^bsub>ES1\<^esub> = V\<^bsub>\<V>1\<^esub>"
                  unfolding properSeparationOfViews_def by simp
                hence "(V\<^bsub>\<V>1\<^esub> \<inter> E\<^bsub>ES1\<^esub> \<union> V\<^bsub>\<V>2\<^esub> \<inter> E\<^bsub>ES1\<^esub>) = V\<^bsub>\<V>1\<^esub>"
                  by auto
                with validV1 have "(V\<^bsub>\<V>1\<^esub> \<union> V\<^bsub>\<V>2\<^esub> \<inter> E\<^bsub>ES1\<^esub>) = V\<^bsub>\<V>1\<^esub>"
                  by (simp add: isViewOn_def V_valid_def  
                    VC_disjoint_def VN_disjoint_def NC_disjoint_def, auto)
                thus ?thesis
                  by auto
              qed
            ultimately show ?thesis
               by (simp add: Un_absorb2)
          qed
          moreover note \<alpha>1'_2
          ultimately show ?thesis
            by auto
      qed 
    moreover
    from CSES2.BSD_in_subsystem[OF c_in_Cv \<beta>c\<alpha>_E2_in_Tr2 BSD_Tr2_v2]
    obtain \<alpha>2' 
      where \<alpha>2'_1: "((\<beta> \<upharpoonleft> E\<^bsub>ES2\<^esub>) @ \<alpha>2') \<in> Tr\<^bsub>ES2\<^esub>"
      and \<alpha>2'_2: "(\<alpha>2' \<upharpoonleft> V\<^bsub>\<V>2\<^esub>) = (\<alpha> \<upharpoonleft> V\<^bsub>\<V>2\<^esub>)"
      and "\<alpha>2' \<upharpoonleft> C\<^bsub>\<V>2\<^esub> = []"
      by auto
     moreover
    from \<alpha>2'_1 validES2 have \<alpha>2'_in_E2: "set \<alpha>2' \<subseteq> E\<^bsub>ES2\<^esub>"
      by (simp add: ES_valid_def traces_contain_events_def, auto)
    moreover
    from \<alpha>2'_2 propSepViews have "((\<alpha> \<upharpoonleft> V\<^bsub>\<V>\<^esub>) \<upharpoonleft> E\<^bsub>ES2\<^esub>) = (\<alpha>2' \<upharpoonleft> V\<^bsub>\<V>\<^esub>)"
      proof -
        have "((\<alpha> \<upharpoonleft> V\<^bsub>\<V>\<^esub>) \<upharpoonleft> E\<^bsub>ES2\<^esub>) = \<alpha> \<upharpoonleft> (V\<^bsub>\<V>\<^esub> \<inter> E\<^bsub>ES2\<^esub>)"
          by (simp only: projection_def, auto)
        with propSepViews have "((\<alpha> \<upharpoonleft> V\<^bsub>\<V>\<^esub>) \<upharpoonleft> E\<^bsub>ES2\<^esub>) = (\<alpha> \<upharpoonleft> V\<^bsub>\<V>2\<^esub>)"
          unfolding properSeparationOfViews_def by auto
        moreover
        from \<alpha>2'_2 have "(\<alpha>2' \<upharpoonleft> V\<^bsub>\<V>2\<^esub>) = (\<alpha>2' \<upharpoonleft> V\<^bsub>\<V>\<^esub>)"
          proof -
            from \<alpha>2'_in_E2 have "\<alpha>2' \<upharpoonleft> E\<^bsub>ES2\<^esub> = \<alpha>2'"
              by (simp add: list_subset_iff_projection_neutral)
            hence "(\<alpha>2' \<upharpoonleft> E\<^bsub>ES2\<^esub>) \<upharpoonleft> V\<^bsub>\<V>\<^esub> = \<alpha>2' \<upharpoonleft> V\<^bsub>\<V>\<^esub>"
              by simp
            with Vv_is_Vv1_union_Vv2 have "(\<alpha>2' \<upharpoonleft> E\<^bsub>ES2\<^esub>) \<upharpoonleft> (V\<^bsub>\<V>2\<^esub> \<union> V\<^bsub>\<V>1\<^esub>) = \<alpha>2' \<upharpoonleft> V\<^bsub>\<V>\<^esub>"
              by (simp add: Un_commute)
            hence "\<alpha>2' \<upharpoonleft> (E\<^bsub>ES2\<^esub> \<inter> (V\<^bsub>\<V>2\<^esub> \<union> V\<^bsub>\<V>1\<^esub>)) = \<alpha>2' \<upharpoonleft> V\<^bsub>\<V>\<^esub>"
              by (simp only: projection_def, auto)
            hence "\<alpha>2' \<upharpoonleft> (E\<^bsub>ES2\<^esub> \<inter> V\<^bsub>\<V>2\<^esub> \<union> E\<^bsub>ES2\<^esub> \<inter> V\<^bsub>\<V>1\<^esub>) = \<alpha>2' \<upharpoonleft> V\<^bsub>\<V>\<^esub>"
              by (simp add: Int_Un_distrib)
            moreover 
            from validV2 have "E\<^bsub>ES2\<^esub> \<inter> V\<^bsub>\<V>2\<^esub> = V\<^bsub>\<V>2\<^esub>"
              by (simp add: isViewOn_def V_valid_def 
                VC_disjoint_def VN_disjoint_def NC_disjoint_def, auto)
            ultimately have "\<alpha>2' \<upharpoonleft> (V\<^bsub>\<V>2\<^esub> \<union> E\<^bsub>ES2\<^esub> \<inter> V\<^bsub>\<V>1\<^esub>) = \<alpha>2' \<upharpoonleft> V\<^bsub>\<V>\<^esub>"
              by simp
            moreover
            have "E\<^bsub>ES2\<^esub> \<inter> V\<^bsub>\<V>1\<^esub> \<subseteq> V\<^bsub>\<V>2\<^esub>" 
              proof -
                from propSepViews Vv_is_Vv1_union_Vv2 have "(V\<^bsub>\<V>2\<^esub> \<union> V\<^bsub>\<V>1\<^esub>) \<inter> E\<^bsub>ES2\<^esub> = V\<^bsub>\<V>2\<^esub>"
                  unfolding properSeparationOfViews_def by (simp add: Un_commute)
                hence "(V\<^bsub>\<V>2\<^esub> \<inter> E\<^bsub>ES2\<^esub> \<union> V\<^bsub>\<V>1\<^esub> \<inter> E\<^bsub>ES2\<^esub>) = V\<^bsub>\<V>2\<^esub>"
                  by auto
                with validV2 have "(V\<^bsub>\<V>2\<^esub> \<union> V\<^bsub>\<V>1\<^esub> \<inter> E\<^bsub>ES2\<^esub>) = V\<^bsub>\<V>2\<^esub>"
                  by (simp add: isViewOn_def V_valid_def 
                    VC_disjoint_def VN_disjoint_def NC_disjoint_def, auto)
                thus ?thesis
                  by auto
              qed
            ultimately show ?thesis
               by (simp add: Un_absorb2)
          qed
          moreover note \<alpha>2'_2
          ultimately show ?thesis
            by auto
      qed
    moreover note generalized_zipping_lemma
    ultimately have "\<exists>\<alpha>'. ((\<beta> @ \<alpha>') \<in> (Tr\<^bsub>(ES1 \<parallel> ES2)\<^esub>) \<and> (\<alpha>' \<upharpoonleft> V\<^bsub>\<V>\<^esub> = (\<alpha> \<upharpoonleft> V\<^bsub>\<V>\<^esub>)) \<and> \<alpha>' \<upharpoonleft> C\<^bsub>\<V>\<^esub> = [])"
      by blast
  }
  thus ?thesis 
    unfolding BSD_def
    by auto
qed

(* Theorem 6.4.1 case 2 *)
theorem compositionality_BSI: 
"\<lbrakk> BSD \<V>1 Tr\<^bsub>ES1\<^esub>; BSD \<V>2 Tr\<^bsub>ES2\<^esub>; BSI \<V>1 Tr\<^bsub>ES1\<^esub>; BSI \<V>2 Tr\<^bsub>ES2\<^esub> \<rbrakk>
    \<Longrightarrow> BSI \<V> Tr\<^bsub>(ES1 \<parallel> ES2)\<^esub>"
proof -
  assume BSD1: "BSD \<V>1 Tr\<^bsub>ES1\<^esub>"
     and BSD2: "BSD \<V>2 Tr\<^bsub>ES2\<^esub>"
     and BSI1: "BSI \<V>1 Tr\<^bsub>ES1\<^esub>"
     and BSI2: "BSI \<V>2 Tr\<^bsub>ES2\<^esub>"

  {
    fix \<alpha> \<beta> c
    assume c_in_Cv: "c \<in> C\<^bsub>\<V>\<^esub>"
    assume \<beta>\<alpha>_in_Tr: "(\<beta> @ \<alpha>) \<in> Tr\<^bsub>(ES1 \<parallel> ES2)\<^esub>"
    assume \<alpha>_no_Cv: "\<alpha> \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []"
    
    from \<beta>\<alpha>_in_Tr 
    have  \<beta>\<alpha>_E1_in_Tr1: "((\<beta> @ \<alpha>) \<upharpoonleft> E\<^bsub>ES1\<^esub>) \<in> Tr\<^bsub>ES1\<^esub>"
      and \<beta>\<alpha>_E2_in_Tr2: "((\<beta> @ \<alpha>) \<upharpoonleft> E\<^bsub>ES2\<^esub>) \<in> Tr\<^bsub>ES2\<^esub>"
      by (simp add: composeES_def)+

    interpret CSES1: CompositionSupport "ES1" "\<V>" "\<V>1"
      using propSepViews unfolding properSeparationOfViews_def
      by (simp add: CompositionSupport_def validES1 validV1)

    interpret CSES2: CompositionSupport "ES2" "\<V>" "\<V>2"
      using propSepViews unfolding properSeparationOfViews_def 
      by (simp add: CompositionSupport_def validES2 validV2)

    from CSES1.BSD_in_subsystem2[OF \<beta>\<alpha>_E1_in_Tr1 BSD1] obtain \<alpha>1'
      where \<beta>E1\<alpha>1'_in_Tr1: "\<beta> \<upharpoonleft> E\<^bsub>ES1\<^esub> @ \<alpha>1' \<in> Tr\<^bsub>ES1\<^esub>"
      and \<alpha>1'Vv1_is_\<alpha>Vv1: "\<alpha>1' \<upharpoonleft> V\<^bsub>\<V>1\<^esub> = \<alpha> \<upharpoonleft> V\<^bsub>\<V>1\<^esub>"
      and \<alpha>1'Cv1_empty: "\<alpha>1' \<upharpoonleft> C\<^bsub>\<V>1\<^esub> = []"
      by auto

    from CSES2.BSD_in_subsystem2[OF \<beta>\<alpha>_E2_in_Tr2 BSD2] obtain \<alpha>2'
      where \<beta>E2\<alpha>2'_in_Tr2: "\<beta> \<upharpoonleft> E\<^bsub>ES2\<^esub> @ \<alpha>2' \<in> Tr\<^bsub>ES2\<^esub>"
      and \<alpha>2'Vv2_is_\<alpha>Vv2: "\<alpha>2' \<upharpoonleft> V\<^bsub>\<V>2\<^esub> = \<alpha> \<upharpoonleft> V\<^bsub>\<V>2\<^esub>"
      and \<alpha>2'Cv2_empty: "\<alpha>2' \<upharpoonleft> C\<^bsub>\<V>2\<^esub> = []"
      by auto
  
    have "\<exists> \<alpha>1''. (set \<alpha>1'' \<subseteq> E\<^bsub>ES1\<^esub> \<and> ((\<beta> @ [c]) \<upharpoonleft> E\<^bsub>ES1\<^esub>) @ \<alpha>1'' \<in> Tr\<^bsub>ES1\<^esub> 
      \<and> \<alpha>1'' \<upharpoonleft> V\<^bsub>\<V>1\<^esub> = \<alpha> \<upharpoonleft> V\<^bsub>\<V>1\<^esub> \<and> \<alpha>1'' \<upharpoonleft> C\<^bsub>\<V>1\<^esub> = [])"
      proof cases
        assume cE1_empty: "[c] \<upharpoonleft> E\<^bsub>ES1\<^esub> = []"
        
        from \<beta>E1\<alpha>1'_in_Tr1 validES1 have "set \<alpha>1' \<subseteq> E\<^bsub>ES1\<^esub>"
          by (simp add: ES_valid_def traces_contain_events_def, auto)
        moreover
        from cE1_empty \<beta>E1\<alpha>1'_in_Tr1 have "((\<beta> @ [c]) \<upharpoonleft> E\<^bsub>ES1\<^esub>) @ \<alpha>1' \<in> Tr\<^bsub>ES1\<^esub>"
          by (simp only: projection_concatenation_commute, auto)
        moreover
        note \<alpha>1'Vv1_is_\<alpha>Vv1 \<alpha>1'Cv1_empty
        ultimately show ?thesis
          by auto
      next
        assume cE1_not_empty: "[c] \<upharpoonleft> E\<^bsub>ES1\<^esub> \<noteq> []"
        hence c_in_E1: "c \<in> E\<^bsub>ES1\<^esub>"
          by (simp only: projection_def, auto, split if_split_asm, auto)

        from c_in_Cv c_in_E1 propSepViews have "c \<in> C\<^bsub>\<V>1\<^esub>"
          unfolding properSeparationOfViews_def by auto
        moreover
        note \<beta>E1\<alpha>1'_in_Tr1 \<alpha>1'Cv1_empty BSI1
        ultimately obtain \<alpha>1'' 
          where \<beta>E1c\<alpha>1''_in_Tr1: "(\<beta> \<upharpoonleft> E\<^bsub>ES1\<^esub>) @ [c] @ \<alpha>1'' \<in> Tr\<^bsub>ES1\<^esub>"
          and   \<alpha>1''Vv1_is_\<alpha>1'Vv1: "\<alpha>1'' \<upharpoonleft> V\<^bsub>\<V>1\<^esub> = \<alpha>1' \<upharpoonleft> V\<^bsub>\<V>1\<^esub>"
          and   \<alpha>1''Cv1_empty: "\<alpha>1'' \<upharpoonleft> C\<^bsub>\<V>1\<^esub> = []"
          unfolding BSI_def
          by blast
        
        from validES1 \<beta>E1c\<alpha>1''_in_Tr1 have "set \<alpha>1'' \<subseteq> E\<^bsub>ES1\<^esub>"
          by (simp add: ES_valid_def traces_contain_events_def, auto)
        moreover
        from \<beta>E1c\<alpha>1''_in_Tr1 c_in_E1 have "((\<beta> @ [c]) \<upharpoonleft> E\<^bsub>ES1\<^esub>) @ \<alpha>1'' \<in> Tr\<^bsub>ES1\<^esub>"
          by (simp only: projection_concatenation_commute projection_def, auto)
        moreover
        from \<alpha>1''Vv1_is_\<alpha>1'Vv1 \<alpha>1'Vv1_is_\<alpha>Vv1 have "\<alpha>1'' \<upharpoonleft> V\<^bsub>\<V>1\<^esub> = \<alpha> \<upharpoonleft> V\<^bsub>\<V>1\<^esub>"
          by auto
        moreover
        note \<alpha>1''Cv1_empty
        ultimately show ?thesis
          by auto
      qed
    then obtain \<alpha>1''
      where \<alpha>1''_in_E1star: "set \<alpha>1'' \<subseteq> E\<^bsub>ES1\<^esub>" 
      and \<beta>cE1\<alpha>1''_in_Tr1: "((\<beta> @ [c]) \<upharpoonleft> E\<^bsub>ES1\<^esub>) @ \<alpha>1'' \<in> Tr\<^bsub>ES1\<^esub>" 
      and \<alpha>1''Vv1_is_\<alpha>Vv1: "\<alpha>1'' \<upharpoonleft> V\<^bsub>\<V>1\<^esub> = \<alpha> \<upharpoonleft> V\<^bsub>\<V>1\<^esub>"
      and \<alpha>1''Cv1_empty: "\<alpha>1'' \<upharpoonleft> C\<^bsub>\<V>1\<^esub> = []"
      by auto

    have "\<exists> \<alpha>2''. (set \<alpha>2'' \<subseteq> E\<^bsub>ES2\<^esub> 
      \<and> ((\<beta> @ [c]) \<upharpoonleft> E\<^bsub>ES2\<^esub>) @ \<alpha>2'' \<in> Tr\<^bsub>ES2\<^esub> 
      \<and> \<alpha>2'' \<upharpoonleft> V\<^bsub>\<V>2\<^esub> = \<alpha> \<upharpoonleft> V\<^bsub>\<V>2\<^esub> 
      \<and> \<alpha>2'' \<upharpoonleft> C\<^bsub>\<V>2\<^esub> = [])"
      proof cases
        assume cE2_empty: "[c] \<upharpoonleft> E\<^bsub>ES2\<^esub> = []"
        
        from \<beta>E2\<alpha>2'_in_Tr2 validES2 have "set \<alpha>2' \<subseteq> E\<^bsub>ES2\<^esub>"
          by (simp add: ES_valid_def traces_contain_events_def, auto)
        moreover
        from cE2_empty \<beta>E2\<alpha>2'_in_Tr2 have "((\<beta> @ [c]) \<upharpoonleft> E\<^bsub>ES2\<^esub>) @ \<alpha>2' \<in> Tr\<^bsub>ES2\<^esub>"
          by (simp only: projection_concatenation_commute, auto)
        moreover
        note \<alpha>2'Vv2_is_\<alpha>Vv2 \<alpha>2'Cv2_empty
        ultimately show ?thesis
          by auto
      next
        assume cE2_not_empty: "[c] \<upharpoonleft> E\<^bsub>ES2\<^esub> \<noteq> []"
        hence c_in_E2: "c \<in> E\<^bsub>ES2\<^esub>"
          by (simp only: projection_def, auto, split if_split_asm, auto)

        from c_in_Cv c_in_E2 propSepViews have "c \<in> C\<^bsub>\<V>2\<^esub>"
          unfolding properSeparationOfViews_def by auto
        moreover
        note \<beta>E2\<alpha>2'_in_Tr2 \<alpha>2'Cv2_empty BSI2
        ultimately obtain \<alpha>2'' 
          where \<beta>E2c\<alpha>2''_in_Tr2: "(\<beta> \<upharpoonleft> E\<^bsub>ES2\<^esub>) @ [c] @ \<alpha>2'' \<in> Tr\<^bsub>ES2\<^esub>"
          and   \<alpha>2''Vv2_is_\<alpha>2'Vv2: "\<alpha>2'' \<upharpoonleft> V\<^bsub>\<V>2\<^esub> = \<alpha>2' \<upharpoonleft> V\<^bsub>\<V>2\<^esub>"
          and   \<alpha>2''Cv2_empty: "\<alpha>2'' \<upharpoonleft> C\<^bsub>\<V>2\<^esub> = []"
          unfolding BSI_def
          by blast
        
        from validES2 \<beta>E2c\<alpha>2''_in_Tr2 have "set \<alpha>2'' \<subseteq> E\<^bsub>ES2\<^esub>"
          by (simp add: ES_valid_def traces_contain_events_def, auto)
        moreover
        from \<beta>E2c\<alpha>2''_in_Tr2 c_in_E2 have "((\<beta> @ [c]) \<upharpoonleft> E\<^bsub>ES2\<^esub>) @ \<alpha>2'' \<in> Tr\<^bsub>ES2\<^esub>"
          by (simp only: projection_concatenation_commute projection_def, auto)
        moreover
        from \<alpha>2''Vv2_is_\<alpha>2'Vv2 \<alpha>2'Vv2_is_\<alpha>Vv2 have "\<alpha>2'' \<upharpoonleft> V\<^bsub>\<V>2\<^esub> = \<alpha> \<upharpoonleft> V\<^bsub>\<V>2\<^esub>"
          by auto
        moreover
        note \<alpha>2''Cv2_empty
        ultimately show ?thesis
          by auto
      qed
    then obtain \<alpha>2''
      where \<alpha>2''_in_E2star: "set \<alpha>2'' \<subseteq> E\<^bsub>ES2\<^esub>" 
      and \<beta>cE2\<alpha>2''_in_Tr2: "((\<beta> @ [c]) \<upharpoonleft> E\<^bsub>ES2\<^esub>) @ \<alpha>2'' \<in> Tr\<^bsub>ES2\<^esub>" 
      and \<alpha>2''Vv2_is_\<alpha>Vv2: "\<alpha>2'' \<upharpoonleft> V\<^bsub>\<V>2\<^esub> = \<alpha> \<upharpoonleft> V\<^bsub>\<V>2\<^esub>"
      and \<alpha>2''Cv2_empty: "\<alpha>2'' \<upharpoonleft> C\<^bsub>\<V>2\<^esub> = []"
      by auto 
    
    (* apply the generalized zipping lemma *)
    from VIsViewOnE c_in_Cv \<beta>\<alpha>_in_Tr have "set (\<beta> @ [c]) \<subseteq> E\<^bsub>(ES1 \<parallel> ES2)\<^esub>"
      by (simp add: isViewOn_def V_valid_def VC_disjoint_def 
        VN_disjoint_def NC_disjoint_def composeES_def, auto)
    moreover
    have "set (\<alpha> \<upharpoonleft> V\<^bsub>\<V>\<^esub>) \<subseteq> V\<^bsub>\<V>\<^esub>"
      by (simp add: projection_def, auto)
    moreover
    note \<alpha>1''_in_E1star \<alpha>2''_in_E2star \<beta>cE1\<alpha>1''_in_Tr1 \<beta>cE2\<alpha>2''_in_Tr2
    moreover
    have "(\<alpha> \<upharpoonleft> V\<^bsub>\<V>\<^esub>) \<upharpoonleft> E\<^bsub>ES1\<^esub> = \<alpha>1'' \<upharpoonleft> V\<^bsub>\<V>\<^esub>"
      proof -
        from  \<alpha>1''Vv1_is_\<alpha>Vv1 propSepViews have "\<alpha> \<upharpoonleft> (V\<^bsub>\<V>\<^esub> \<inter> E\<^bsub>ES1\<^esub>) = \<alpha>1'' \<upharpoonleft> (E\<^bsub>ES1\<^esub> \<inter> V\<^bsub>\<V>\<^esub>)"
          unfolding properSeparationOfViews_def by (simp add: Int_commute)
        hence "\<alpha> \<upharpoonleft> V\<^bsub>\<V>\<^esub> \<upharpoonleft> E\<^bsub>ES1\<^esub> = \<alpha>1'' \<upharpoonleft> E\<^bsub>ES1\<^esub> \<upharpoonleft> V\<^bsub>\<V>\<^esub>"
          by (simp add: projection_def)
        with \<alpha>1''_in_E1star show ?thesis
          by (simp add: list_subset_iff_projection_neutral)
      qed
    moreover
    have "(\<alpha> \<upharpoonleft> V\<^bsub>\<V>\<^esub>) \<upharpoonleft> E\<^bsub>ES2\<^esub> = \<alpha>2'' \<upharpoonleft> V\<^bsub>\<V>\<^esub>"
      proof -
        from  \<alpha>2''Vv2_is_\<alpha>Vv2 propSepViews have "\<alpha> \<upharpoonleft> (V\<^bsub>\<V>\<^esub> \<inter> E\<^bsub>ES2\<^esub>) = \<alpha>2'' \<upharpoonleft> (E\<^bsub>ES2\<^esub> \<inter> V\<^bsub>\<V>\<^esub>)"
          unfolding properSeparationOfViews_def  by (simp add: Int_commute)
        hence "\<alpha> \<upharpoonleft> V\<^bsub>\<V>\<^esub> \<upharpoonleft> E\<^bsub>ES2\<^esub> = \<alpha>2'' \<upharpoonleft> E\<^bsub>ES2\<^esub> \<upharpoonleft> V\<^bsub>\<V>\<^esub>"
          by (simp add: projection_def)
        with \<alpha>2''_in_E2star show ?thesis
          by (simp add: list_subset_iff_projection_neutral)
      qed
    moreover
    note \<alpha>1''Cv1_empty \<alpha>2''Cv2_empty generalized_zipping_lemma
    ultimately have "\<exists>\<alpha>'. (\<beta> @ [c]) @ \<alpha>' \<in> Tr\<^bsub>(ES1 \<parallel> ES2)\<^esub> \<and> \<alpha>' \<upharpoonleft> V\<^bsub>\<V>\<^esub> = \<alpha> \<upharpoonleft> V\<^bsub>\<V>\<^esub> \<and> \<alpha>' \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []"
      by blast
  }
  thus ?thesis
    unfolding BSI_def
    by auto
qed

(* Theorem 6.4.1 case 3 *)
theorem compositionality_BSIA: 
"\<lbrakk> BSD \<V>1 Tr\<^bsub>ES1\<^esub>; BSD \<V>2 Tr\<^bsub>ES2\<^esub>; BSIA \<rho>1 \<V>1 Tr\<^bsub>ES1\<^esub>; BSIA \<rho>2 \<V>2 Tr\<^bsub>ES2\<^esub>; 
  (\<rho>1 \<V>1) \<subseteq> (\<rho> \<V>) \<inter> E\<^bsub>ES1\<^esub>; (\<rho>2 \<V>2) \<subseteq> (\<rho> \<V>) \<inter> E\<^bsub>ES2\<^esub> \<rbrakk> 
    \<Longrightarrow> BSIA \<rho> \<V> (Tr\<^bsub>(ES1 \<parallel> ES2)\<^esub>)"
proof -
  assume BSD1: "BSD \<V>1 Tr\<^bsub>ES1\<^esub>"
  and BSD2: "BSD \<V>2 Tr\<^bsub>ES2\<^esub>"
  and BSIA1: "BSIA \<rho>1 \<V>1 Tr\<^bsub>ES1\<^esub>"
  and BSIA2: "BSIA \<rho>2 \<V>2 Tr\<^bsub>ES2\<^esub>"
  and \<rho>1v1_subset_\<rho>v_inter_E1: "(\<rho>1 \<V>1) \<subseteq> (\<rho> \<V>) \<inter> E\<^bsub>ES1\<^esub>"
  and \<rho>2v2_subset_\<rho>v_inter_E2:"(\<rho>2 \<V>2) \<subseteq> (\<rho> \<V>) \<inter> E\<^bsub>ES2\<^esub>"

  {
    fix \<alpha> \<beta> c
    assume c_in_Cv: "c \<in> C\<^bsub>\<V>\<^esub>"
    assume \<beta>\<alpha>_in_Tr: "(\<beta> @ \<alpha>) \<in> Tr\<^bsub>(ES1 \<parallel> ES2)\<^esub>"
    assume \<alpha>_no_Cv: "\<alpha> \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []"
    assume Adm: "(Adm \<V> \<rho> Tr\<^bsub>(ES1 \<parallel> ES2)\<^esub> \<beta> c)"
    then obtain \<gamma>
      where \<gamma>\<rho>v_is_\<beta>\<rho>v: "\<gamma> \<upharpoonleft> (\<rho> \<V>) = \<beta> \<upharpoonleft> (\<rho> \<V>)"
      and \<gamma>c_in_Tr: "(\<gamma> @ [c]) \<in> Tr\<^bsub>(ES1 \<parallel> ES2)\<^esub>"
      unfolding Adm_def
      by auto

    from \<beta>\<alpha>_in_Tr 
    have  \<beta>\<alpha>_E1_in_Tr1: "((\<beta> @ \<alpha>) \<upharpoonleft> E\<^bsub>ES1\<^esub>) \<in> Tr\<^bsub>ES1\<^esub>"
      and \<beta>\<alpha>_E2_in_Tr2: "((\<beta> @ \<alpha>) \<upharpoonleft> E\<^bsub>ES2\<^esub>) \<in> Tr\<^bsub>ES2\<^esub>"
      by (simp add: composeES_def)+

    interpret CSES1: CompositionSupport "ES1" "\<V>" "\<V>1"
      using propSepViews unfolding properSeparationOfViews_def 
      by (simp add: CompositionSupport_def validES1 validV1)

    interpret CSES2: CompositionSupport "ES2" "\<V>" "\<V>2"
      using propSepViews unfolding properSeparationOfViews_def 
      by (simp add: CompositionSupport_def validES2 validV2)


    from CSES1.BSD_in_subsystem2[OF \<beta>\<alpha>_E1_in_Tr1 BSD1] obtain \<alpha>1'
      where \<beta>E1\<alpha>1'_in_Tr1: "\<beta> \<upharpoonleft> E\<^bsub>ES1\<^esub> @ \<alpha>1' \<in> Tr\<^bsub>ES1\<^esub>"
      and \<alpha>1'Vv1_is_\<alpha>Vv1: "\<alpha>1' \<upharpoonleft> V\<^bsub>\<V>1\<^esub> = \<alpha> \<upharpoonleft> V\<^bsub>\<V>1\<^esub>"
      and \<alpha>1'Cv1_empty: "\<alpha>1' \<upharpoonleft> C\<^bsub>\<V>1\<^esub> = []"
      by auto

    from CSES2.BSD_in_subsystem2[OF \<beta>\<alpha>_E2_in_Tr2 BSD2] obtain \<alpha>2'
      where \<beta>E2\<alpha>2'_in_Tr2: "\<beta> \<upharpoonleft> E\<^bsub>ES2\<^esub> @ \<alpha>2' \<in> Tr\<^bsub>ES2\<^esub>"
      and \<alpha>2'Vv2_is_\<alpha>Vv2: "\<alpha>2' \<upharpoonleft> V\<^bsub>\<V>2\<^esub> = \<alpha> \<upharpoonleft> V\<^bsub>\<V>2\<^esub>"
      and \<alpha>2'Cv2_empty: "\<alpha>2' \<upharpoonleft> C\<^bsub>\<V>2\<^esub> = []"
      by auto

    have "\<exists> \<alpha>1''. (set \<alpha>1'' \<subseteq> E\<^bsub>ES1\<^esub> 
      \<and> ((\<beta> @ [c]) \<upharpoonleft> E\<^bsub>ES1\<^esub>) @ \<alpha>1'' \<in> Tr\<^bsub>ES1\<^esub> 
      \<and> \<alpha>1'' \<upharpoonleft> V\<^bsub>\<V>1\<^esub> = \<alpha> \<upharpoonleft> V\<^bsub>\<V>1\<^esub> 
      \<and> \<alpha>1'' \<upharpoonleft> C\<^bsub>\<V>1\<^esub> = [])"
      proof cases
        assume cE1_empty: "[c] \<upharpoonleft> E\<^bsub>ES1\<^esub> = []"
        
        from \<beta>E1\<alpha>1'_in_Tr1 validES1 have "set \<alpha>1' \<subseteq> E\<^bsub>ES1\<^esub>"
          by (simp add: ES_valid_def traces_contain_events_def, auto)
        moreover
        from cE1_empty \<beta>E1\<alpha>1'_in_Tr1 have "((\<beta> @ [c]) \<upharpoonleft> E\<^bsub>ES1\<^esub>) @ \<alpha>1' \<in> Tr\<^bsub>ES1\<^esub>"
          by (simp only: projection_concatenation_commute, auto)
        moreover
        note \<alpha>1'Vv1_is_\<alpha>Vv1 \<alpha>1'Cv1_empty
        ultimately show ?thesis
          by auto
      next
        assume cE1_not_empty: "[c] \<upharpoonleft> E\<^bsub>ES1\<^esub> \<noteq> []"
        hence c_in_E1: "c \<in> E\<^bsub>ES1\<^esub>"
          by (simp only: projection_def, auto, split if_split_asm, auto)

        from c_in_Cv c_in_E1 propSepViews have "c \<in> C\<^bsub>\<V>1\<^esub>"
          unfolding properSeparationOfViews_def by auto
        moreover
        note \<beta>E1\<alpha>1'_in_Tr1 \<alpha>1'Cv1_empty
        moreover
        have "(Adm \<V>1 \<rho>1 Tr\<^bsub>ES1\<^esub> (\<beta> \<upharpoonleft> E\<^bsub>ES1\<^esub>) c)" 
          proof -
            from c_in_E1 \<gamma>c_in_Tr have "(\<gamma> \<upharpoonleft> E\<^bsub>ES1\<^esub>) @ [c] \<in> Tr\<^bsub>ES1\<^esub>"
              by (simp add: projection_def composeES_def)
            moreover
            have "\<gamma> \<upharpoonleft> E\<^bsub>ES1\<^esub> \<upharpoonleft> (\<rho>1 \<V>1) = \<beta> \<upharpoonleft> E\<^bsub>ES1\<^esub> \<upharpoonleft> (\<rho>1 \<V>1)"
              proof -
                from \<gamma>\<rho>v_is_\<beta>\<rho>v have "\<gamma> \<upharpoonleft> E\<^bsub>ES1\<^esub> \<upharpoonleft> (\<rho> \<V>) = \<beta> \<upharpoonleft> E\<^bsub>ES1\<^esub> \<upharpoonleft> (\<rho> \<V>)"
                  by (metis projection_commute)
                with \<rho>1v1_subset_\<rho>v_inter_E1 have "\<gamma> \<upharpoonleft> (\<rho>1 \<V>1) = \<beta> \<upharpoonleft> (\<rho>1 \<V>1)"
                  by (metis Int_subset_iff \<gamma>\<rho>v_is_\<beta>\<rho>v projection_subset_elim)
                thus ?thesis
                  by (metis projection_commute)
              qed
           ultimately show ?thesis unfolding Adm_def
              by auto
          qed
        moreover
        note BSIA1
        ultimately obtain \<alpha>1'' 
          where \<beta>E1c\<alpha>1''_in_Tr1: "(\<beta> \<upharpoonleft> E\<^bsub>ES1\<^esub>) @ [c] @ \<alpha>1'' \<in> Tr\<^bsub>ES1\<^esub>"
          and   \<alpha>1''Vv1_is_\<alpha>1'Vv1: "\<alpha>1'' \<upharpoonleft> V\<^bsub>\<V>1\<^esub> = \<alpha>1' \<upharpoonleft> V\<^bsub>\<V>1\<^esub>"
          and   \<alpha>1''Cv1_empty: "\<alpha>1'' \<upharpoonleft> C\<^bsub>\<V>1\<^esub> = []"
          unfolding BSIA_def
          by blast
        
        from validES1 \<beta>E1c\<alpha>1''_in_Tr1 have "set \<alpha>1'' \<subseteq> E\<^bsub>ES1\<^esub>"
          by (simp add: ES_valid_def traces_contain_events_def, auto)
        moreover
        from \<beta>E1c\<alpha>1''_in_Tr1 c_in_E1 have "((\<beta> @ [c]) \<upharpoonleft> E\<^bsub>ES1\<^esub>) @ \<alpha>1'' \<in> Tr\<^bsub>ES1\<^esub>"
          by (simp only: projection_concatenation_commute projection_def, auto)
        moreover
        from \<alpha>1''Vv1_is_\<alpha>1'Vv1 \<alpha>1'Vv1_is_\<alpha>Vv1 have "\<alpha>1'' \<upharpoonleft> V\<^bsub>\<V>1\<^esub> = \<alpha> \<upharpoonleft> V\<^bsub>\<V>1\<^esub>"
          by auto
        moreover
        note \<alpha>1''Cv1_empty
        ultimately show ?thesis
          by auto
      qed
    then obtain \<alpha>1''
      where \<alpha>1''_in_E1star: "set \<alpha>1'' \<subseteq> E\<^bsub>ES1\<^esub>" 
      and \<beta>cE1\<alpha>1''_in_Tr1: "((\<beta> @ [c]) \<upharpoonleft> E\<^bsub>ES1\<^esub>) @ \<alpha>1'' \<in> Tr\<^bsub>ES1\<^esub>" 
      and \<alpha>1''Vv1_is_\<alpha>Vv1: "\<alpha>1'' \<upharpoonleft> V\<^bsub>\<V>1\<^esub> = \<alpha> \<upharpoonleft> V\<^bsub>\<V>1\<^esub>"
      and \<alpha>1''Cv1_empty: "\<alpha>1'' \<upharpoonleft> C\<^bsub>\<V>1\<^esub> = []"
      by auto

    have "\<exists> \<alpha>2''. (set \<alpha>2'' \<subseteq> E\<^bsub>ES2\<^esub> 
      \<and> ((\<beta> @ [c]) \<upharpoonleft> E\<^bsub>ES2\<^esub>) @ \<alpha>2'' \<in> Tr\<^bsub>ES2\<^esub> 
      \<and> \<alpha>2'' \<upharpoonleft> V\<^bsub>\<V>2\<^esub> = \<alpha> \<upharpoonleft> V\<^bsub>\<V>2\<^esub> 
      \<and> \<alpha>2'' \<upharpoonleft> C\<^bsub>\<V>2\<^esub> = [])"
      proof cases
        assume cE2_empty: "[c] \<upharpoonleft> E\<^bsub>ES2\<^esub> = []"
        
        from \<beta>E2\<alpha>2'_in_Tr2 validES2 have "set \<alpha>2' \<subseteq> E\<^bsub>ES2\<^esub>"
          by (simp add: ES_valid_def traces_contain_events_def, auto)
        moreover
        from cE2_empty \<beta>E2\<alpha>2'_in_Tr2 have "((\<beta> @ [c]) \<upharpoonleft> E\<^bsub>ES2\<^esub>) @ \<alpha>2' \<in> Tr\<^bsub>ES2\<^esub>"
          by (simp only: projection_concatenation_commute, auto)
        moreover
        note \<alpha>2'Vv2_is_\<alpha>Vv2 \<alpha>2'Cv2_empty
        ultimately show ?thesis
          by auto
      next
        assume cE2_not_empty: "[c] \<upharpoonleft> E\<^bsub>ES2\<^esub> \<noteq> []"
        hence c_in_E2: "c \<in> E\<^bsub>ES2\<^esub>"
          by (simp only: projection_def, auto, split if_split_asm, auto)

        from c_in_Cv c_in_E2 propSepViews have "c \<in> C\<^bsub>\<V>2\<^esub>"
          unfolding properSeparationOfViews_def by auto
        moreover
        note \<beta>E2\<alpha>2'_in_Tr2 \<alpha>2'Cv2_empty
        moreover
        have "(Adm \<V>2 \<rho>2 Tr\<^bsub>ES2\<^esub> (\<beta> \<upharpoonleft> E\<^bsub>ES2\<^esub>) c)" 
          proof -
            from c_in_E2 \<gamma>c_in_Tr have "(\<gamma> \<upharpoonleft> E\<^bsub>ES2\<^esub>) @ [c] \<in> Tr\<^bsub>ES2\<^esub>"
              by (simp add: projection_def composeES_def)
            moreover
            have "\<gamma> \<upharpoonleft> E\<^bsub>ES2\<^esub> \<upharpoonleft> (\<rho>2 \<V>2) = \<beta> \<upharpoonleft> E\<^bsub>ES2\<^esub> \<upharpoonleft> (\<rho>2 \<V>2)"
              proof -
                from \<gamma>\<rho>v_is_\<beta>\<rho>v have "\<gamma> \<upharpoonleft> E\<^bsub>ES2\<^esub> \<upharpoonleft> (\<rho> \<V>) = \<beta> \<upharpoonleft> E\<^bsub>ES2\<^esub> \<upharpoonleft> (\<rho> \<V>)"
                  by (metis projection_commute)
                with \<rho>2v2_subset_\<rho>v_inter_E2 have "\<gamma> \<upharpoonleft> (\<rho>2 \<V>2) = \<beta> \<upharpoonleft> (\<rho>2 \<V>2)"
                  by (metis Int_subset_iff \<gamma>\<rho>v_is_\<beta>\<rho>v projection_subset_elim)
                thus ?thesis
                  by (metis projection_commute)
              qed
           ultimately show ?thesis unfolding Adm_def
              by auto
          qed
        moreover
        note BSIA2
        ultimately obtain \<alpha>2'' 
          where \<beta>E2c\<alpha>2''_in_Tr2: "(\<beta> \<upharpoonleft> E\<^bsub>ES2\<^esub>) @ [c] @ \<alpha>2'' \<in> Tr\<^bsub>ES2\<^esub>"
          and   \<alpha>2''Vv2_is_\<alpha>2'Vv2: "\<alpha>2'' \<upharpoonleft> V\<^bsub>\<V>2\<^esub> = \<alpha>2' \<upharpoonleft> V\<^bsub>\<V>2\<^esub>"
          and   \<alpha>2''Cv2_empty: "\<alpha>2'' \<upharpoonleft> C\<^bsub>\<V>2\<^esub> = []"
          unfolding BSIA_def
          by blast
        
        from validES2 \<beta>E2c\<alpha>2''_in_Tr2 have "set \<alpha>2'' \<subseteq> E\<^bsub>ES2\<^esub>"
          by (simp add: ES_valid_def traces_contain_events_def, auto)
        moreover
        from \<beta>E2c\<alpha>2''_in_Tr2 c_in_E2 have "((\<beta> @ [c]) \<upharpoonleft> E\<^bsub>ES2\<^esub>) @ \<alpha>2'' \<in> Tr\<^bsub>ES2\<^esub>"
          by (simp only: projection_concatenation_commute projection_def, auto)
        moreover
        from \<alpha>2''Vv2_is_\<alpha>2'Vv2 \<alpha>2'Vv2_is_\<alpha>Vv2 have "\<alpha>2'' \<upharpoonleft> V\<^bsub>\<V>2\<^esub> = \<alpha> \<upharpoonleft> V\<^bsub>\<V>2\<^esub>"
          by auto
        moreover
        note \<alpha>2''Cv2_empty
        ultimately show ?thesis
          by auto
      qed
    then obtain \<alpha>2''
      where \<alpha>2''_in_E2star: "set \<alpha>2'' \<subseteq> E\<^bsub>ES2\<^esub>" 
      and \<beta>cE2\<alpha>2''_in_Tr2: "((\<beta> @ [c]) \<upharpoonleft> E\<^bsub>ES2\<^esub>) @ \<alpha>2'' \<in> Tr\<^bsub>ES2\<^esub>" 
      and \<alpha>2''Vv2_is_\<alpha>Vv2: "\<alpha>2'' \<upharpoonleft> V\<^bsub>\<V>2\<^esub> = \<alpha> \<upharpoonleft> V\<^bsub>\<V>2\<^esub>"
      and \<alpha>2''Cv2_empty: "\<alpha>2'' \<upharpoonleft> C\<^bsub>\<V>2\<^esub> = []"
      by auto
    
    (* apply the generalized zipping lemma *)
    from VIsViewOnE c_in_Cv \<beta>\<alpha>_in_Tr have "set (\<beta> @ [c]) \<subseteq> E\<^bsub>(ES1 \<parallel> ES2)\<^esub>"
      by (simp add: isViewOn_def V_valid_def VC_disjoint_def 
        VN_disjoint_def NC_disjoint_def composeES_def, auto)
    moreover
    have "set (\<alpha> \<upharpoonleft> V\<^bsub>\<V>\<^esub>) \<subseteq> V\<^bsub>\<V>\<^esub>"
      by (simp add: projection_def, auto)
    moreover
    note \<alpha>1''_in_E1star \<alpha>2''_in_E2star \<beta>cE1\<alpha>1''_in_Tr1 \<beta>cE2\<alpha>2''_in_Tr2
    moreover
    have "(\<alpha> \<upharpoonleft> V\<^bsub>\<V>\<^esub>) \<upharpoonleft> E\<^bsub>ES1\<^esub> = \<alpha>1'' \<upharpoonleft> V\<^bsub>\<V>\<^esub>"
      proof -
        from  \<alpha>1''Vv1_is_\<alpha>Vv1 propSepViews 
        have "\<alpha> \<upharpoonleft> (V\<^bsub>\<V>\<^esub> \<inter> E\<^bsub>ES1\<^esub>) = \<alpha>1'' \<upharpoonleft> (E\<^bsub>ES1\<^esub> \<inter> V\<^bsub>\<V>\<^esub>)"
         unfolding properSeparationOfViews_def by (simp add: Int_commute)
        hence "\<alpha> \<upharpoonleft> V\<^bsub>\<V>\<^esub> \<upharpoonleft> E\<^bsub>ES1\<^esub> = \<alpha>1'' \<upharpoonleft> E\<^bsub>ES1\<^esub> \<upharpoonleft> V\<^bsub>\<V>\<^esub>"
          by (simp add: projection_def)
        with \<alpha>1''_in_E1star show ?thesis
          by (simp add: list_subset_iff_projection_neutral)
      qed
    moreover
    have "(\<alpha> \<upharpoonleft> V\<^bsub>\<V>\<^esub>) \<upharpoonleft> E\<^bsub>ES2\<^esub> = \<alpha>2'' \<upharpoonleft> V\<^bsub>\<V>\<^esub>"
      proof -
        from  \<alpha>2''Vv2_is_\<alpha>Vv2 propSepViews 
        have "\<alpha> \<upharpoonleft> (V\<^bsub>\<V>\<^esub> \<inter> E\<^bsub>ES2\<^esub>) = \<alpha>2'' \<upharpoonleft> (E\<^bsub>ES2\<^esub> \<inter> V\<^bsub>\<V>\<^esub>)"
          unfolding properSeparationOfViews_def by (simp add: Int_commute)
        hence "\<alpha> \<upharpoonleft> V\<^bsub>\<V>\<^esub> \<upharpoonleft> E\<^bsub>ES2\<^esub> = \<alpha>2'' \<upharpoonleft> E\<^bsub>ES2\<^esub> \<upharpoonleft> V\<^bsub>\<V>\<^esub>"
          by (simp add: projection_def)
        with \<alpha>2''_in_E2star show ?thesis
          by (simp add: list_subset_iff_projection_neutral)
      qed
    moreover
    note \<alpha>1''Cv1_empty \<alpha>2''Cv2_empty generalized_zipping_lemma
    ultimately have "\<exists>\<alpha>'. (\<beta> @ [c]) @ \<alpha>' \<in> Tr\<^bsub>(ES1 \<parallel> ES2)\<^esub> \<and> \<alpha>' \<upharpoonleft> V\<^bsub>\<V>\<^esub> = \<alpha> \<upharpoonleft> V\<^bsub>\<V>\<^esub> \<and> \<alpha>' \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []"
      by blast
  }
  thus ?thesis
    unfolding BSIA_def
    by auto
qed

(* Theorem 6.4.1 case 4 *)
theorem compositionality_FCD: 
 "\<lbrakk> BSD \<V>1 Tr\<^bsub>ES1\<^esub>; BSD \<V>2 Tr\<^bsub>ES2\<^esub>; 
  \<nabla>\<^bsub>\<Gamma>\<^esub> \<inter> E\<^bsub>ES1\<^esub> \<subseteq> \<nabla>\<^bsub>\<Gamma>1\<^esub>; \<nabla>\<^bsub>\<Gamma>\<^esub> \<inter> E\<^bsub>ES2\<^esub> \<subseteq> \<nabla>\<^bsub>\<Gamma>2\<^esub>;
  \<Upsilon>\<^bsub>\<Gamma>\<^esub> \<inter> E\<^bsub>ES1\<^esub> \<subseteq> \<Upsilon>\<^bsub>\<Gamma>1\<^esub>; \<Upsilon>\<^bsub>\<Gamma>\<^esub> \<inter> E\<^bsub>ES2\<^esub> \<subseteq> \<Upsilon>\<^bsub>\<Gamma>2\<^esub>;
  ( \<Delta>\<^bsub>\<Gamma>1\<^esub> \<inter> N\<^bsub>\<V>1\<^esub> \<union> \<Delta>\<^bsub>\<Gamma>2\<^esub> \<inter> N\<^bsub>\<V>2\<^esub> ) \<subseteq> \<Delta>\<^bsub>\<Gamma>\<^esub>;
  N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub> \<inter> E\<^bsub>ES2\<^esub> = {}; N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub> \<inter> E\<^bsub>ES1\<^esub> = {};
  FCD \<Gamma>1 \<V>1 Tr\<^bsub>ES1\<^esub>; FCD \<Gamma>2 \<V>2 Tr\<^bsub>ES2\<^esub> \<rbrakk> 
  \<Longrightarrow> FCD \<Gamma> \<V> (Tr\<^bsub>(ES1 \<parallel> ES2)\<^esub>)"
proof -
  assume BSD1: "BSD \<V>1 Tr\<^bsub>ES1\<^esub>"
    and BSD2: "BSD \<V>2 Tr\<^bsub>ES2\<^esub>"
    and Nabla_inter_E1_subset_Nabla1: "\<nabla>\<^bsub>\<Gamma>\<^esub> \<inter> E\<^bsub>ES1\<^esub> \<subseteq> \<nabla>\<^bsub>\<Gamma>1\<^esub>"
    and Nabla_inter_E2_subset_Nabla2: "\<nabla>\<^bsub>\<Gamma>\<^esub> \<inter> E\<^bsub>ES2\<^esub> \<subseteq> \<nabla>\<^bsub>\<Gamma>2\<^esub>"
    and Upsilon_inter_E1_subset_Upsilon1: "\<Upsilon>\<^bsub>\<Gamma>\<^esub> \<inter> E\<^bsub>ES1\<^esub> \<subseteq> \<Upsilon>\<^bsub>\<Gamma>1\<^esub>"
    and Upsilon_inter_E2_subset_Upsilon2: "\<Upsilon>\<^bsub>\<Gamma>\<^esub> \<inter> E\<^bsub>ES2\<^esub> \<subseteq> \<Upsilon>\<^bsub>\<Gamma>2\<^esub>"
    and Delta1_N1_Delta2_N2_subset_Delta: "( \<Delta>\<^bsub>\<Gamma>1\<^esub> \<inter> N\<^bsub>\<V>1\<^esub> \<union> \<Delta>\<^bsub>\<Gamma>2\<^esub> \<inter> N\<^bsub>\<V>2\<^esub> ) \<subseteq> \<Delta>\<^bsub>\<Gamma>\<^esub>"
    and N1_Delta1_E2_disjoint: "N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub> \<inter> E\<^bsub>ES2\<^esub> = {}"
    and N2_Delta2_E1_disjoint: "N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub> \<inter> E\<^bsub>ES1\<^esub> = {}"
    and FCD1: "FCD \<Gamma>1 \<V>1 Tr\<^bsub>ES1\<^esub>"
    and FCD2: "FCD \<Gamma>2 \<V>2 Tr\<^bsub>ES2\<^esub>"

  {
    fix \<alpha> \<beta> c v'
    assume c_in_Cv_inter_Upsilon: "c \<in> (C\<^bsub>\<V>\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>\<^esub>)"
      and v'_in_Vv_inter_Nabla: "v' \<in> (V\<^bsub>\<V>\<^esub> \<inter> \<nabla>\<^bsub>\<Gamma>\<^esub>)"
      and \<beta>cv'\<alpha>_in_Tr: "(\<beta> @ [c,v'] @ \<alpha>) \<in> Tr\<^bsub>(ES1 \<parallel> ES2)\<^esub>" 
      and \<alpha>Cv_empty: "\<alpha> \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []"

    from  \<beta>cv'\<alpha>_in_Tr
    have  \<beta>cv'\<alpha>_E1_in_Tr1: "(((\<beta> @ [c,v']) @ \<alpha>) \<upharpoonleft> E\<^bsub>ES1\<^esub>) \<in> Tr\<^bsub>ES1\<^esub>"
      and \<beta>cv'\<alpha>_E2_in_Tr2: "(((\<beta> @ [c,v']) @ \<alpha>) \<upharpoonleft> E\<^bsub>ES2\<^esub>) \<in> Tr\<^bsub>ES2\<^esub>"
      by (simp add: composeES_def)+

    interpret CSES1: CompositionSupport "ES1" "\<V>" "\<V>1"
      using propSepViews unfolding properSeparationOfViews_def 
      by (simp add: CompositionSupport_def validES1 validV1)

    interpret CSES2: CompositionSupport "ES2" "\<V>" "\<V>2"
      using propSepViews unfolding properSeparationOfViews_def 
      by (simp add: CompositionSupport_def validES2 validV2)

    from CSES1.BSD_in_subsystem2[OF \<beta>cv'\<alpha>_E1_in_Tr1 BSD1] obtain \<alpha>1'
      where \<beta>cv'E1\<alpha>1'_in_Tr1: "(\<beta> @ [c,v']) \<upharpoonleft> E\<^bsub>ES1\<^esub> @ \<alpha>1' \<in> Tr\<^bsub>ES1\<^esub>"
      and \<alpha>1'Vv1_is_\<alpha>Vv1: "\<alpha>1' \<upharpoonleft> V\<^bsub>\<V>1\<^esub> = \<alpha> \<upharpoonleft> V\<^bsub>\<V>1\<^esub>"
      and \<alpha>1'Cv1_empty: "\<alpha>1' \<upharpoonleft> C\<^bsub>\<V>1\<^esub> = []"
      by auto

    from CSES2.BSD_in_subsystem2[OF \<beta>cv'\<alpha>_E2_in_Tr2 BSD2] obtain \<alpha>2'
      where \<beta>cv'E2\<alpha>2'_in_Tr2: "(\<beta> @ [c,v']) \<upharpoonleft> E\<^bsub>ES2\<^esub> @ \<alpha>2' \<in> Tr\<^bsub>ES2\<^esub>"
      and \<alpha>2'Vv2_is_\<alpha>Vv2: "\<alpha>2' \<upharpoonleft> V\<^bsub>\<V>2\<^esub> = \<alpha> \<upharpoonleft> V\<^bsub>\<V>2\<^esub>"
      and \<alpha>2'Cv2_empty: "\<alpha>2' \<upharpoonleft> C\<^bsub>\<V>2\<^esub> = []"
      by auto

    from c_in_Cv_inter_Upsilon v'_in_Vv_inter_Nabla validV1
    have "c \<notin> E\<^bsub>ES1\<^esub> \<or> (c \<in> E\<^bsub>ES1\<^esub> \<and> v' \<notin> E\<^bsub>ES1\<^esub>) \<or> (c \<in> E\<^bsub>ES1\<^esub> \<and> v' \<in> E\<^bsub>ES1\<^esub>)"
      by (simp add: isViewOn_def V_valid_def
        VC_disjoint_def VN_disjoint_def NC_disjoint_def)
    moreover {
      assume c_notin_E1: "c \<notin> E\<^bsub>ES1\<^esub>"
     
      have "set [] \<subseteq> (N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub>)"
        by auto
      moreover
      from \<beta>cv'E1\<alpha>1'_in_Tr1 c_notin_E1 have "(\<beta> \<upharpoonleft> E\<^bsub>ES1\<^esub>) @ [] @ ([v'] \<upharpoonleft> E\<^bsub>ES1\<^esub>) @ \<alpha>1' \<in> Tr\<^bsub>ES1\<^esub>"
        by (simp only: projection_concatenation_commute projection_def, auto)
      moreover
      have "\<alpha>1' \<upharpoonleft> V\<^bsub>\<V>1\<^esub> = \<alpha>1' \<upharpoonleft> V\<^bsub>\<V>1\<^esub>" ..
      moreover
      note \<alpha>1'Cv1_empty 
      ultimately have "\<exists> \<alpha>1'' \<delta>1''. set \<delta>1'' \<subseteq> (N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub>) 
        \<and> (\<beta> \<upharpoonleft> E\<^bsub>ES1\<^esub>) @ \<delta>1'' @ ([v'] \<upharpoonleft> E\<^bsub>ES1\<^esub>) @ \<alpha>1'' \<in> Tr\<^bsub>ES1\<^esub>        
        \<and> \<alpha>1'' \<upharpoonleft> V\<^bsub>\<V>1\<^esub> = \<alpha>1' \<upharpoonleft> V\<^bsub>\<V>1\<^esub> \<and> \<alpha>1'' \<upharpoonleft> C\<^bsub>\<V>1\<^esub> = []"
        by blast
    }
    moreover {
      assume c_in_E1: "c \<in> E\<^bsub>ES1\<^esub>"
      and v'_notin_E1: "v' \<notin> E\<^bsub>ES1\<^esub>"

      from c_in_E1 c_in_Cv_inter_Upsilon propSepViews
        Upsilon_inter_E1_subset_Upsilon1 
      have c_in_Cv1_Upsilon1: "c \<in> (C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub>)"
        unfolding properSeparationOfViews_def by auto
      hence c_in_Cv1: "c \<in> C\<^bsub>\<V>1\<^esub>"
        by auto
      moreover
      from \<beta>cv'E1\<alpha>1'_in_Tr1 c_in_E1 v'_notin_E1 have "(\<beta> \<upharpoonleft> E\<^bsub>ES1\<^esub>) @ [c] @ \<alpha>1' \<in> Tr\<^bsub>ES1\<^esub>"
        by (simp only: projection_concatenation_commute projection_def, auto)
      moreover
      note \<alpha>1'Cv1_empty BSD1
      ultimately obtain \<alpha>1''
        where first: "(\<beta> \<upharpoonleft> E\<^bsub>ES1\<^esub>) @ \<alpha>1'' \<in> Tr\<^bsub>ES1\<^esub>"
        and second: "\<alpha>1'' \<upharpoonleft> V\<^bsub>\<V>1\<^esub> = \<alpha>1' \<upharpoonleft> V\<^bsub>\<V>1\<^esub>"
        and third: "\<alpha>1'' \<upharpoonleft> C\<^bsub>\<V>1\<^esub> = []"
        unfolding BSD_def
        by blast
       
      have "set [] \<subseteq> (N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub>)"
        by auto
      moreover
      from first v'_notin_E1 have "(\<beta> \<upharpoonleft> E\<^bsub>ES1\<^esub>) @ [] @ ([v'] \<upharpoonleft> E\<^bsub>ES1\<^esub>) @ \<alpha>1'' \<in> Tr\<^bsub>ES1\<^esub>"
        by (simp add: projection_def)
      moreover
      note second third
      ultimately
      have "\<exists> \<alpha>1'' \<delta>1''. set \<delta>1'' \<subseteq> (N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub>) 
        \<and> (\<beta> \<upharpoonleft> E\<^bsub>ES1\<^esub>) @ \<delta>1'' @ ([v'] \<upharpoonleft> E\<^bsub>ES1\<^esub>) @ \<alpha>1'' \<in> Tr\<^bsub>ES1\<^esub>        
        \<and> \<alpha>1'' \<upharpoonleft> V\<^bsub>\<V>1\<^esub> = \<alpha>1' \<upharpoonleft> V\<^bsub>\<V>1\<^esub> \<and> \<alpha>1'' \<upharpoonleft> C\<^bsub>\<V>1\<^esub> = []"
        by blast
    }
    moreover {
      assume c_in_E1: "c \<in> E\<^bsub>ES1\<^esub>"
      and v'_in_E1: "v' \<in> E\<^bsub>ES1\<^esub>"
      
      from c_in_E1 c_in_Cv_inter_Upsilon propSepViews
        Upsilon_inter_E1_subset_Upsilon1 
      have c_in_Cv1_Upsilon1: "c \<in> (C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub>)"
        unfolding properSeparationOfViews_def by auto
      moreover
      from v'_in_E1 v'_in_Vv_inter_Nabla propSepViews Nabla_inter_E1_subset_Nabla1
      have v'_in_Vv1_inter_Nabla1: "v' \<in> (V\<^bsub>\<V>1\<^esub> \<inter> \<nabla>\<^bsub>\<Gamma>1\<^esub>)"
        unfolding properSeparationOfViews_def by auto
      moreover
      from \<beta>cv'E1\<alpha>1'_in_Tr1 c_in_E1 v'_in_E1 have "(\<beta> \<upharpoonleft> E\<^bsub>ES1\<^esub>) @ [c,v'] @ \<alpha>1' \<in> Tr\<^bsub>ES1\<^esub>"
        by (simp add: projection_def)
      moreover
      note \<alpha>1'Cv1_empty FCD1
      ultimately obtain \<alpha>1'' \<delta>1'' 
        where first: "set \<delta>1'' \<subseteq> (N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub>)"
        and second: "(\<beta> \<upharpoonleft> E\<^bsub>ES1\<^esub>) @ \<delta>1'' @ [v'] @ \<alpha>1'' \<in> Tr\<^bsub>ES1\<^esub>"
        and third: "\<alpha>1'' \<upharpoonleft> V\<^bsub>\<V>1\<^esub> = \<alpha>1' \<upharpoonleft> V\<^bsub>\<V>1\<^esub>"
        and fourth: "\<alpha>1'' \<upharpoonleft> C\<^bsub>\<V>1\<^esub> = []"
        unfolding FCD_def
        by blast

      from second v'_in_E1 have "(\<beta> \<upharpoonleft> E\<^bsub>ES1\<^esub>) @ \<delta>1'' @ ([v'] \<upharpoonleft> E\<^bsub>ES1\<^esub>) @ \<alpha>1'' \<in> Tr\<^bsub>ES1\<^esub>"
        by (simp add: projection_def)
      with first third fourth
      have "\<exists> \<alpha>1'' \<delta>1''. set \<delta>1'' \<subseteq> (N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub>) 
        \<and> (\<beta> \<upharpoonleft> E\<^bsub>ES1\<^esub>) @ \<delta>1'' @ ([v'] \<upharpoonleft> E\<^bsub>ES1\<^esub>) @ \<alpha>1'' \<in> Tr\<^bsub>ES1\<^esub>        
        \<and> \<alpha>1'' \<upharpoonleft> V\<^bsub>\<V>1\<^esub> = \<alpha>1' \<upharpoonleft> V\<^bsub>\<V>1\<^esub> \<and> \<alpha>1'' \<upharpoonleft> C\<^bsub>\<V>1\<^esub> = []"
        unfolding FCD_def
        by blast
    }
    ultimately obtain \<alpha>1'' \<delta>1'' 
      where \<delta>1''_in_Nv1_Delta1_star: "set \<delta>1'' \<subseteq> (N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub>)"
      and \<beta>E1\<delta>1''vE1\<alpha>1''_in_Tr1: "(\<beta> \<upharpoonleft> E\<^bsub>ES1\<^esub>) @ \<delta>1'' @ ([v'] \<upharpoonleft> E\<^bsub>ES1\<^esub>) @ \<alpha>1'' \<in> Tr\<^bsub>ES1\<^esub>"
      and \<alpha>1''Vv1_is_\<alpha>1'Vv1: "\<alpha>1'' \<upharpoonleft> V\<^bsub>\<V>1\<^esub> = \<alpha>1' \<upharpoonleft> V\<^bsub>\<V>1\<^esub>"
      and \<alpha>1''Cv1_empty: "\<alpha>1'' \<upharpoonleft> C\<^bsub>\<V>1\<^esub> = []"
      by blast
    with validV1 have \<delta>1''_in_E1_star: "set \<delta>1'' \<subseteq> E\<^bsub>ES1\<^esub>"
      by (simp add: isViewOn_def V_valid_def 
        VC_disjoint_def VN_disjoint_def NC_disjoint_def, auto)

    from c_in_Cv_inter_Upsilon v'_in_Vv_inter_Nabla validV2
    have "c \<notin> E\<^bsub>ES2\<^esub> \<or> (c \<in> E\<^bsub>ES2\<^esub> \<and> v' \<notin> E\<^bsub>ES2\<^esub>) \<or> (c \<in> E\<^bsub>ES2\<^esub> \<and> v' \<in> E\<^bsub>ES2\<^esub>)"
      by (simp add: isViewOn_def V_valid_def 
        VC_disjoint_def VN_disjoint_def NC_disjoint_def)
    moreover {
      assume c_notin_E2: "c \<notin> E\<^bsub>ES2\<^esub>"
     
      have "set [] \<subseteq> (N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub>)"
        by auto
      moreover
      from \<beta>cv'E2\<alpha>2'_in_Tr2 c_notin_E2 have "(\<beta> \<upharpoonleft> E\<^bsub>ES2\<^esub>) @ [] @ ([v'] \<upharpoonleft> E\<^bsub>ES2\<^esub>) @ \<alpha>2' \<in> Tr\<^bsub>ES2\<^esub>"
        by (simp only: projection_concatenation_commute projection_def, auto)
      moreover
      have "\<alpha>2' \<upharpoonleft> V\<^bsub>\<V>2\<^esub> = \<alpha>2' \<upharpoonleft> V\<^bsub>\<V>2\<^esub>" ..
      moreover
      note \<alpha>2'Cv2_empty 
      ultimately have "\<exists> \<alpha>2'' \<delta>2''. set \<delta>2'' \<subseteq> (N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub>) 
        \<and> (\<beta> \<upharpoonleft> E\<^bsub>ES2\<^esub>) @ \<delta>2'' @ ([v'] \<upharpoonleft> E\<^bsub>ES2\<^esub>) @ \<alpha>2'' \<in> Tr\<^bsub>ES2\<^esub>        
        \<and> \<alpha>2'' \<upharpoonleft> V\<^bsub>\<V>2\<^esub> = \<alpha>2' \<upharpoonleft> V\<^bsub>\<V>2\<^esub> \<and> \<alpha>2'' \<upharpoonleft> C\<^bsub>\<V>2\<^esub> = []"
        by blast
    }
    moreover {
      assume c_in_E2: "c \<in> E\<^bsub>ES2\<^esub>"
      and v'_notin_E2: "v' \<notin> E\<^bsub>ES2\<^esub>"

      from c_in_E2 c_in_Cv_inter_Upsilon propSepViews Upsilon_inter_E2_subset_Upsilon2 
      have c_in_Cv2_Upsilon2: "c \<in> (C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub>)"
        unfolding properSeparationOfViews_def by auto
      hence c_in_Cv2: "c \<in> C\<^bsub>\<V>2\<^esub>"
        by auto
      moreover
      from \<beta>cv'E2\<alpha>2'_in_Tr2 c_in_E2 v'_notin_E2 have "(\<beta> \<upharpoonleft> E\<^bsub>ES2\<^esub>) @ [c] @ \<alpha>2' \<in> Tr\<^bsub>ES2\<^esub>"
        by (simp only: projection_concatenation_commute projection_def, auto)
      moreover
      note \<alpha>2'Cv2_empty BSD2
      ultimately obtain \<alpha>2''
        where first: "(\<beta> \<upharpoonleft> E\<^bsub>ES2\<^esub>) @ \<alpha>2'' \<in> Tr\<^bsub>ES2\<^esub>"
        and second: "\<alpha>2'' \<upharpoonleft> V\<^bsub>\<V>2\<^esub> = \<alpha>2' \<upharpoonleft> V\<^bsub>\<V>2\<^esub>"
        and third: "\<alpha>2'' \<upharpoonleft> C\<^bsub>\<V>2\<^esub> = []"
        unfolding BSD_def
        by blast
       
      have "set [] \<subseteq> (N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub>)"
        by auto
      moreover
      from first v'_notin_E2 have "(\<beta> \<upharpoonleft> E\<^bsub>ES2\<^esub>) @ [] @ ([v'] \<upharpoonleft> E\<^bsub>ES2\<^esub>) @ \<alpha>2'' \<in> Tr\<^bsub>ES2\<^esub>"
        by (simp add: projection_def)
      moreover
      note second third
      ultimately
      have "\<exists> \<alpha>2'' \<delta>2''. set \<delta>2'' \<subseteq> (N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub>) 
        \<and> (\<beta> \<upharpoonleft> E\<^bsub>ES2\<^esub>) @ \<delta>2'' @ ([v'] \<upharpoonleft> E\<^bsub>ES2\<^esub>) @ \<alpha>2'' \<in> Tr\<^bsub>ES2\<^esub>        
        \<and> \<alpha>2'' \<upharpoonleft> V\<^bsub>\<V>2\<^esub> = \<alpha>2' \<upharpoonleft> V\<^bsub>\<V>2\<^esub> \<and> \<alpha>2'' \<upharpoonleft> C\<^bsub>\<V>2\<^esub> = []"
        by blast
    }
    moreover {
      assume c_in_E2: "c \<in> E\<^bsub>ES2\<^esub>"
      and v'_in_E2: "v' \<in> E\<^bsub>ES2\<^esub>"
      
      from c_in_E2 c_in_Cv_inter_Upsilon propSepViews
        Upsilon_inter_E2_subset_Upsilon2 
      have c_in_Cv2_Upsilon2: "c \<in> (C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub>)"
        unfolding properSeparationOfViews_def by auto
      moreover
      from v'_in_E2 v'_in_Vv_inter_Nabla propSepViews Nabla_inter_E2_subset_Nabla2
      have v'_in_Vv2_inter_Nabla2: "v' \<in> (V\<^bsub>\<V>2\<^esub> \<inter> \<nabla>\<^bsub>\<Gamma>2\<^esub>)"
        unfolding properSeparationOfViews_def by auto
      moreover
      from \<beta>cv'E2\<alpha>2'_in_Tr2 c_in_E2 v'_in_E2 have "(\<beta> \<upharpoonleft> E\<^bsub>ES2\<^esub>) @ [c,v'] @ \<alpha>2' \<in> Tr\<^bsub>ES2\<^esub>"
        by (simp add: projection_def)
      moreover
      note \<alpha>2'Cv2_empty FCD2
      ultimately obtain \<alpha>2'' \<delta>2'' 
        where first: "set \<delta>2'' \<subseteq> (N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub>)"
        and second: "(\<beta> \<upharpoonleft> E\<^bsub>ES2\<^esub>) @ \<delta>2'' @ [v'] @ \<alpha>2'' \<in> Tr\<^bsub>ES2\<^esub>"
        and third: "\<alpha>2'' \<upharpoonleft> V\<^bsub>\<V>2\<^esub> = \<alpha>2' \<upharpoonleft> V\<^bsub>\<V>2\<^esub>"
        and fourth: "\<alpha>2'' \<upharpoonleft> C\<^bsub>\<V>2\<^esub> = []"
        unfolding FCD_def
        by blast

      from second v'_in_E2 have "(\<beta> \<upharpoonleft> E\<^bsub>ES2\<^esub>) @ \<delta>2'' @ ([v'] \<upharpoonleft> E\<^bsub>ES2\<^esub>) @ \<alpha>2'' \<in> Tr\<^bsub>ES2\<^esub>"
        by (simp add: projection_def)
      with first third fourth
      have "\<exists> \<alpha>2'' \<delta>2''. set \<delta>2'' \<subseteq> (N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub>) 
        \<and> (\<beta> \<upharpoonleft> E\<^bsub>ES2\<^esub>) @ \<delta>2'' @ ([v'] \<upharpoonleft> E\<^bsub>ES2\<^esub>) @ \<alpha>2'' \<in> Tr\<^bsub>ES2\<^esub>        
        \<and> \<alpha>2'' \<upharpoonleft> V\<^bsub>\<V>2\<^esub> = \<alpha>2' \<upharpoonleft> V\<^bsub>\<V>2\<^esub> \<and> \<alpha>2'' \<upharpoonleft> C\<^bsub>\<V>2\<^esub> = []"
        unfolding FCD_def
        by blast
    }
    ultimately obtain \<alpha>2'' \<delta>2'' 
      where \<delta>2''_in_Nv2_Delta2_star: "set \<delta>2'' \<subseteq> (N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub>)"
      and \<beta>E2\<delta>2''vE2\<alpha>2''_in_Tr2: "(\<beta> \<upharpoonleft> E\<^bsub>ES2\<^esub>) @ \<delta>2'' @ ([v'] \<upharpoonleft> E\<^bsub>ES2\<^esub>) @ \<alpha>2'' \<in> Tr\<^bsub>ES2\<^esub>"
      and \<alpha>2''Vv2_is_\<alpha>2'Vv2: "\<alpha>2'' \<upharpoonleft> V\<^bsub>\<V>2\<^esub> = \<alpha>2' \<upharpoonleft> V\<^bsub>\<V>2\<^esub>"
      and \<alpha>2''Cv2_empty: "\<alpha>2'' \<upharpoonleft> C\<^bsub>\<V>2\<^esub> = []"
      by blast
    with validV2 have \<delta>2''_in_E2_star: "set \<delta>2'' \<subseteq> E\<^bsub>ES2\<^esub>"
      by (simp add: isViewOn_def V_valid_def  
        VC_disjoint_def VN_disjoint_def NC_disjoint_def, auto)
    
    from \<delta>1''_in_Nv1_Delta1_star N1_Delta1_E2_disjoint 
    have \<delta>1''E2_empty: "\<delta>1'' \<upharpoonleft> E\<^bsub>ES2\<^esub> = []"
      proof -
        from \<delta>1''_in_Nv1_Delta1_star have "\<delta>1'' = \<delta>1'' \<upharpoonleft> (N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub>)"
          by (simp only: list_subset_iff_projection_neutral)
        hence "\<delta>1'' \<upharpoonleft> E\<^bsub>ES2\<^esub> = \<delta>1'' \<upharpoonleft> (N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub>) \<upharpoonleft> E\<^bsub>ES2\<^esub>"
          by simp
        moreover
        have "\<delta>1'' \<upharpoonleft> (N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub>) \<upharpoonleft> E\<^bsub>ES2\<^esub> = \<delta>1'' \<upharpoonleft> (N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub> \<inter> E\<^bsub>ES2\<^esub>)"
          by (simp only: projection_def, auto)
        with N1_Delta1_E2_disjoint have "\<delta>1'' \<upharpoonleft> (N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub>) \<upharpoonleft> E\<^bsub>ES2\<^esub> = []"
          by (simp add: projection_def)
        ultimately show ?thesis
          by simp
      qed
    moreover
    from \<delta>2''_in_Nv2_Delta2_star N2_Delta2_E1_disjoint have \<delta>2''E1_empty: "\<delta>2'' \<upharpoonleft> E\<^bsub>ES1\<^esub> = []"
      proof -
        from \<delta>2''_in_Nv2_Delta2_star have "\<delta>2'' = \<delta>2'' \<upharpoonleft> (N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub>)"
          by (simp only: list_subset_iff_projection_neutral)
        hence "\<delta>2'' \<upharpoonleft> E\<^bsub>ES1\<^esub> = \<delta>2'' \<upharpoonleft> (N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub>) \<upharpoonleft> E\<^bsub>ES1\<^esub>"
          by simp
        moreover
        have "\<delta>2'' \<upharpoonleft> (N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub>) \<upharpoonleft> E\<^bsub>ES1\<^esub> = \<delta>2'' \<upharpoonleft> (N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub> \<inter> E\<^bsub>ES1\<^esub>)"
          by (simp only: projection_def, auto)
        with N2_Delta2_E1_disjoint have "\<delta>2'' \<upharpoonleft> (N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub>) \<upharpoonleft> E\<^bsub>ES1\<^esub> = []"
          by (simp add: projection_def)
        ultimately show ?thesis
          by simp
      qed
    moreover
    note \<beta>E1\<delta>1''vE1\<alpha>1''_in_Tr1 \<beta>E2\<delta>2''vE2\<alpha>2''_in_Tr2 \<delta>1''_in_E1_star \<delta>2''_in_E2_star
    ultimately have \<beta>\<delta>1''\<delta>2''v'E1\<alpha>1''_in_Tr1: "(\<beta> @ \<delta>1'' @ \<delta>2'' @ [v']) \<upharpoonleft> E\<^bsub>ES1\<^esub> @ \<alpha>1'' \<in> Tr\<^bsub>ES1\<^esub>"
      and \<beta>\<delta>1''\<delta>2''v'E2\<alpha>2''_in_Tr2: "(\<beta> @ \<delta>1'' @ \<delta>2'' @ [v']) \<upharpoonleft> E\<^bsub>ES2\<^esub> @ \<alpha>2'' \<in> Tr\<^bsub>ES2\<^esub>"
      by (simp only: projection_concatenation_commute list_subset_iff_projection_neutral, auto, 
          simp only: projection_concatenation_commute list_subset_iff_projection_neutral, auto)

    have "set (\<beta> @ \<delta>1'' @ \<delta>2'' @ [v']) \<subseteq> E\<^bsub>(ES1 \<parallel> ES2)\<^esub>"
      proof -
        from \<beta>cv'\<alpha>_in_Tr have "set \<beta> \<subseteq> E\<^bsub>(ES1 \<parallel> ES2)\<^esub>"
          by (simp add: composeES_def)
        moreover
        note \<delta>1''_in_E1_star \<delta>2''_in_E2_star
        moreover
        from v'_in_Vv_inter_Nabla VIsViewOnE
        have "v' \<in> E\<^bsub>(ES1 \<parallel> ES2)\<^esub>"
          by (simp add:isViewOn_def  V_valid_def
            VC_disjoint_def VN_disjoint_def NC_disjoint_def, auto)
        ultimately show ?thesis
          by (simp add: composeES_def, auto)
      qed
    moreover
    have "set (\<alpha> \<upharpoonleft> V\<^bsub>\<V>\<^esub>) \<subseteq> V\<^bsub>\<V>\<^esub>"
      by (simp add: projection_def, auto)
    moreover
    from \<beta>E1\<delta>1''vE1\<alpha>1''_in_Tr1 validES1 have \<alpha>1''_in_E1_star: "set \<alpha>1'' \<subseteq> E\<^bsub>ES1\<^esub>"
      by (simp add: ES_valid_def traces_contain_events_def, auto)
    moreover
    from \<beta>E2\<delta>2''vE2\<alpha>2''_in_Tr2 validES2 have \<alpha>2''_in_E2_star: "set \<alpha>2'' \<subseteq> E\<^bsub>ES2\<^esub>"
      by (simp add: ES_valid_def traces_contain_events_def, auto)
    moreover
    note \<beta>\<delta>1''\<delta>2''v'E1\<alpha>1''_in_Tr1 \<beta>\<delta>1''\<delta>2''v'E2\<alpha>2''_in_Tr2
    moreover 
    have "(\<alpha> \<upharpoonleft> V\<^bsub>\<V>\<^esub>) \<upharpoonleft> E\<^bsub>ES1\<^esub> = \<alpha>1'' \<upharpoonleft> V\<^bsub>\<V>\<^esub>"
      proof -
        from  \<alpha>1''Vv1_is_\<alpha>1'Vv1 \<alpha>1'Vv1_is_\<alpha>Vv1 propSepViews 
        have "\<alpha> \<upharpoonleft> (V\<^bsub>\<V>\<^esub> \<inter> E\<^bsub>ES1\<^esub>) = \<alpha>1'' \<upharpoonleft> (E\<^bsub>ES1\<^esub> \<inter> V\<^bsub>\<V>\<^esub>)"
          unfolding properSeparationOfViews_def by (simp add: Int_commute)
        hence "\<alpha> \<upharpoonleft> V\<^bsub>\<V>\<^esub> \<upharpoonleft> E\<^bsub>ES1\<^esub> = \<alpha>1'' \<upharpoonleft> E\<^bsub>ES1\<^esub> \<upharpoonleft> V\<^bsub>\<V>\<^esub>"
          by (simp add: projection_def)
        with \<alpha>1''_in_E1_star show ?thesis
          by (simp add: list_subset_iff_projection_neutral)
      qed
    moreover
    have "(\<alpha> \<upharpoonleft> V\<^bsub>\<V>\<^esub>) \<upharpoonleft> E\<^bsub>ES2\<^esub> = \<alpha>2'' \<upharpoonleft> V\<^bsub>\<V>\<^esub>"
      proof -
        from  \<alpha>2''Vv2_is_\<alpha>2'Vv2 \<alpha>2'Vv2_is_\<alpha>Vv2 propSepViews 
        have "\<alpha> \<upharpoonleft> (V\<^bsub>\<V>\<^esub> \<inter> E\<^bsub>ES2\<^esub>) = \<alpha>2'' \<upharpoonleft> (E\<^bsub>ES2\<^esub> \<inter> V\<^bsub>\<V>\<^esub>)"
          unfolding properSeparationOfViews_def by (simp add: Int_commute)
        hence "\<alpha> \<upharpoonleft> V\<^bsub>\<V>\<^esub> \<upharpoonleft> E\<^bsub>ES2\<^esub> = \<alpha>2'' \<upharpoonleft> E\<^bsub>ES2\<^esub> \<upharpoonleft> V\<^bsub>\<V>\<^esub>"
          by (simp add: projection_def)
        with \<alpha>2''_in_E2_star show ?thesis
          by (simp add: list_subset_iff_projection_neutral)
      qed
    moreover
    note \<alpha>1''Cv1_empty \<alpha>2''Cv2_empty generalized_zipping_lemma
    ultimately obtain t
      where first: "(\<beta> @ \<delta>1'' @ \<delta>2'' @ [v']) @ t \<in> Tr\<^bsub>(ES1 \<parallel> ES2)\<^esub>"
      and second: "t \<upharpoonleft> V\<^bsub>\<V>\<^esub> = \<alpha> \<upharpoonleft> V\<^bsub>\<V>\<^esub>"
      and third: "t \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []"
      by blast
    
    from \<delta>1''_in_Nv1_Delta1_star \<delta>2''_in_Nv2_Delta2_star 
    have "set (\<delta>1'' @ \<delta>2'') \<subseteq> (N\<^bsub>\<V>\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>\<^esub>)"
      proof -
        have "set (\<delta>1'' @ \<delta>2'') \<subseteq> \<Delta>\<^bsub>\<Gamma>\<^esub>"
          proof -
            from \<delta>1''_in_Nv1_Delta1_star \<delta>2''_in_Nv2_Delta2_star 
            have "set (\<delta>1'' @ \<delta>2'') \<subseteq> \<Delta>\<^bsub>\<Gamma>1\<^esub> \<inter> N\<^bsub>\<V>1\<^esub> \<union> \<Delta>\<^bsub>\<Gamma>2\<^esub> \<inter> N\<^bsub>\<V>2\<^esub>"
              by auto
            with Delta1_N1_Delta2_N2_subset_Delta show ?thesis
              by auto
          qed
        moreover
        have "set (\<delta>1'' @ \<delta>2'') \<subseteq> N\<^bsub>\<V>\<^esub>"
          proof -
            from \<delta>1''_in_Nv1_Delta1_star \<delta>2''_in_Nv2_Delta2_star 
            have "set (\<delta>1'' @ \<delta>2'') \<subseteq> (N\<^bsub>\<V>1\<^esub> \<union> N\<^bsub>\<V>2\<^esub>)"
              by auto
            with Nv1_union_Nv2_subsetof_Nv show ?thesis
              by auto
          qed
        ultimately show ?thesis
          by auto
      qed
    moreover
    from first have "\<beta> @ (\<delta>1'' @ \<delta>2'') @ [v'] @ t \<in> Tr\<^bsub>(ES1 \<parallel> ES2)\<^esub>"
      by auto
    moreover 
    note second third
    ultimately have "\<exists>\<alpha>'. \<exists>\<gamma>'. (set \<gamma>') \<subseteq> (N\<^bsub>\<V>\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>\<^esub>) 
      \<and> ((\<beta> @ \<gamma>' @ [v'] @ \<alpha>') \<in> Tr\<^bsub>(ES1 \<parallel> ES2)\<^esub>  
      \<and> (\<alpha>' \<upharpoonleft> V\<^bsub>\<V>\<^esub>) = (\<alpha> \<upharpoonleft> V\<^bsub>\<V>\<^esub>) 
      \<and> \<alpha>' \<upharpoonleft> C\<^bsub>\<V>\<^esub> = [])"
      by blast
  }
  thus ?thesis
    unfolding FCD_def
    by auto
qed

(* Theorem 6.4.1 case 5 *)
theorem compositionality_FCI: 
"\<lbrakk> BSD \<V>1 Tr\<^bsub>ES1\<^esub>; BSD \<V>2 Tr\<^bsub>ES2\<^esub>; BSIA \<rho>1 \<V>1 Tr\<^bsub>ES1\<^esub>; BSIA \<rho>2 \<V>2 Tr\<^bsub>ES2\<^esub>;
  total ES1 (C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub>); total ES2 (C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub>);
  \<nabla>\<^bsub>\<Gamma>\<^esub> \<inter> E\<^bsub>ES1\<^esub> \<subseteq> \<nabla>\<^bsub>\<Gamma>1\<^esub>; \<nabla>\<^bsub>\<Gamma>\<^esub> \<inter> E\<^bsub>ES2\<^esub> \<subseteq> \<nabla>\<^bsub>\<Gamma>2\<^esub>;
  \<Upsilon>\<^bsub>\<Gamma>\<^esub> \<inter> E\<^bsub>ES1\<^esub> \<subseteq> \<Upsilon>\<^bsub>\<Gamma>1\<^esub>; \<Upsilon>\<^bsub>\<Gamma>\<^esub> \<inter> E\<^bsub>ES2\<^esub> \<subseteq> \<Upsilon>\<^bsub>\<Gamma>2\<^esub>;
  ( \<Delta>\<^bsub>\<Gamma>1\<^esub> \<inter> N\<^bsub>\<V>1\<^esub> \<union> \<Delta>\<^bsub>\<Gamma>2\<^esub> \<inter> N\<^bsub>\<V>2\<^esub> ) \<subseteq> \<Delta>\<^bsub>\<Gamma>\<^esub>;
  (N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub> \<inter> E\<^bsub>ES2\<^esub> = {} \<and> N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub> \<inter> E\<^bsub>ES1\<^esub> \<subseteq> \<Upsilon>\<^bsub>\<Gamma>1\<^esub>)
  \<or> ( N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub> \<inter> E\<^bsub>ES1\<^esub> = {} \<and> N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub> \<inter> E\<^bsub>ES2\<^esub> \<subseteq> \<Upsilon>\<^bsub>\<Gamma>2\<^esub>)  ;
  FCI \<Gamma>1 \<V>1 Tr\<^bsub>ES1\<^esub>; FCI \<Gamma>2 \<V>2 Tr\<^bsub>ES2\<^esub> \<rbrakk> 
  \<Longrightarrow> FCI \<Gamma> \<V> (Tr\<^bsub>(ES1 \<parallel> ES2)\<^esub>)"
proof -
  assume BSD1: "BSD \<V>1 Tr\<^bsub>ES1\<^esub>" 
    and BSD2: "BSD \<V>2 Tr\<^bsub>ES2\<^esub>"
    and BSIA1: "BSIA \<rho>1 \<V>1 Tr\<^bsub>ES1\<^esub>"
    and BSIA2: "BSIA \<rho>2 \<V>2 Tr\<^bsub>ES2\<^esub>"
    and total_ES1_C1_inter_Upsilon1: "total ES1 (C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub>)"
    and total_ES2_C2_inter_Upsilon2: "total ES2 (C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub>)"
    and Nabla_inter_E1_subset_Nabla1: "\<nabla>\<^bsub>\<Gamma>\<^esub> \<inter> E\<^bsub>ES1\<^esub> \<subseteq> \<nabla>\<^bsub>\<Gamma>1\<^esub>"
    and Nabla_inter_E2_subset_Nabla2: "\<nabla>\<^bsub>\<Gamma>\<^esub> \<inter> E\<^bsub>ES2\<^esub> \<subseteq> \<nabla>\<^bsub>\<Gamma>2\<^esub>"
    and Upsilon_inter_E1_subset_Upsilon1: "\<Upsilon>\<^bsub>\<Gamma>\<^esub> \<inter> E\<^bsub>ES1\<^esub> \<subseteq> \<Upsilon>\<^bsub>\<Gamma>1\<^esub>"
    and Upsilon_inter_E2_subset_Upsilon2: "\<Upsilon>\<^bsub>\<Gamma>\<^esub> \<inter> E\<^bsub>ES2\<^esub> \<subseteq> \<Upsilon>\<^bsub>\<Gamma>2\<^esub>"
    and Delta1_N1_Delta2_N2_subset_Delta: "( \<Delta>\<^bsub>\<Gamma>1\<^esub> \<inter> N\<^bsub>\<V>1\<^esub> \<union> \<Delta>\<^bsub>\<Gamma>2\<^esub> \<inter> N\<^bsub>\<V>2\<^esub> ) \<subseteq> \<Delta>\<^bsub>\<Gamma>\<^esub>"
    and very_long_asm: "(N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub> \<inter> E\<^bsub>ES2\<^esub> = {} \<and> N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub> \<inter> E\<^bsub>ES1\<^esub> \<subseteq> \<Upsilon>\<^bsub>\<Gamma>1\<^esub>)
    \<or> ( N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub> \<inter> E\<^bsub>ES1\<^esub> = {} \<and> N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub> \<inter> E\<^bsub>ES2\<^esub> \<subseteq> \<Upsilon>\<^bsub>\<Gamma>2\<^esub>)"
    and FCI1: "FCI \<Gamma>1 \<V>1 Tr\<^bsub>ES1\<^esub>"
    and FCI2: "FCI \<Gamma>2 \<V>2 Tr\<^bsub>ES2\<^esub>"

  {
    fix \<alpha> \<beta> c v'
    assume c_in_Cv_inter_Upsilon: "c \<in> (C\<^bsub>\<V>\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>\<^esub>)"
      and v'_in_Vv_inter_Nabla: "v' \<in> (V\<^bsub>\<V>\<^esub> \<inter> \<nabla>\<^bsub>\<Gamma>\<^esub>)"
      and \<beta>v'\<alpha>_in_Tr: "(\<beta> @ [v'] @ \<alpha>) \<in> Tr\<^bsub>(ES1 \<parallel> ES2)\<^esub>" 
      and \<alpha>Cv_empty: "\<alpha> \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []"

    from  \<beta>v'\<alpha>_in_Tr
    have  \<beta>v'\<alpha>_E1_in_Tr1: "(((\<beta> @ [v']) @ \<alpha>) \<upharpoonleft> E\<^bsub>ES1\<^esub>) \<in> Tr\<^bsub>ES1\<^esub>"
      and \<beta>v'\<alpha>_E2_in_Tr2: "(((\<beta> @ [v']) @ \<alpha>) \<upharpoonleft> E\<^bsub>ES2\<^esub>) \<in> Tr\<^bsub>ES2\<^esub>"
      by (simp add: composeES_def)+

    interpret CSES1: CompositionSupport "ES1" "\<V>" "\<V>1"
      using propSepViews unfolding properSeparationOfViews_def 
      by (simp add: CompositionSupport_def validES1 validV1)

    interpret CSES2: CompositionSupport "ES2" "\<V>" "\<V>2"
      using propSepViews unfolding properSeparationOfViews_def 
      by (simp add: CompositionSupport_def validES2 validV2)

    from CSES1.BSD_in_subsystem2[OF \<beta>v'\<alpha>_E1_in_Tr1 BSD1] obtain \<alpha>1'
      where \<beta>v'E1\<alpha>1'_in_Tr1: "(\<beta> @ [v']) \<upharpoonleft> E\<^bsub>ES1\<^esub> @ \<alpha>1' \<in> Tr\<^bsub>ES1\<^esub>"
      and \<alpha>1'Vv1_is_\<alpha>Vv1: "\<alpha>1' \<upharpoonleft> V\<^bsub>\<V>1\<^esub> = \<alpha> \<upharpoonleft> V\<^bsub>\<V>1\<^esub>"
      and \<alpha>1'Cv1_empty: "\<alpha>1' \<upharpoonleft> C\<^bsub>\<V>1\<^esub> = []"
      by auto

    from CSES2.BSD_in_subsystem2[OF \<beta>v'\<alpha>_E2_in_Tr2 BSD2] obtain \<alpha>2'
      where \<beta>v'E2\<alpha>2'_in_Tr2: "(\<beta> @ [v']) \<upharpoonleft> E\<^bsub>ES2\<^esub> @ \<alpha>2' \<in> Tr\<^bsub>ES2\<^esub>"
      and \<alpha>2'Vv2_is_\<alpha>Vv2: "\<alpha>2' \<upharpoonleft> V\<^bsub>\<V>2\<^esub> = \<alpha> \<upharpoonleft> V\<^bsub>\<V>2\<^esub>"
      and \<alpha>2'Cv2_empty: "\<alpha>2' \<upharpoonleft> C\<^bsub>\<V>2\<^esub> = []"
      by auto

    note very_long_asm
    moreover {
      assume Nv1_inter_Delta1_inter_E2_empty: "N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub> \<inter> E\<^bsub>ES2\<^esub> = {}" 
        and  Nv2_inter_Delta2_inter_E1_subsetof_Upsilon1: "N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub> \<inter> E\<^bsub>ES1\<^esub> \<subseteq> \<Upsilon>\<^bsub>\<Gamma>1\<^esub>"

      let ?ALPHA2''_DELTA2'' = "\<exists> \<alpha>2'' \<delta>2''. (
        set \<alpha>2'' \<subseteq> E\<^bsub>ES2\<^esub> \<and> set \<delta>2'' \<subseteq> N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub> 
        \<and> \<beta> \<upharpoonleft> E\<^bsub>ES2\<^esub> @ [c] \<upharpoonleft> E\<^bsub>ES2\<^esub> @ \<delta>2'' @ [v'] \<upharpoonleft> E\<^bsub>ES2\<^esub> @ \<alpha>2'' \<in> Tr\<^bsub>ES2\<^esub>        
        \<and> \<alpha>2'' \<upharpoonleft> V\<^bsub>\<V>2\<^esub> = \<alpha>2' \<upharpoonleft> V\<^bsub>\<V>2\<^esub> \<and> \<alpha>2'' \<upharpoonleft> C\<^bsub>\<V>2\<^esub> = [])"

      from c_in_Cv_inter_Upsilon v'_in_Vv_inter_Nabla  validV2
      have "c \<notin> E\<^bsub>ES2\<^esub> \<or> (c \<in> E\<^bsub>ES2\<^esub> \<and> v' \<notin> E\<^bsub>ES2\<^esub>) \<or> (c \<in> E\<^bsub>ES2\<^esub> \<and> v' \<in> E\<^bsub>ES2\<^esub>)"
        by (simp add: isViewOn_def V_valid_def 
          VC_disjoint_def VN_disjoint_def NC_disjoint_def)
      moreover {
        assume c_notin_E2: "c \<notin> E\<^bsub>ES2\<^esub>"

        from validES2 \<beta>v'E2\<alpha>2'_in_Tr2 have "set \<alpha>2' \<subseteq> E\<^bsub>ES2\<^esub>"
          by (simp add: ES_valid_def traces_contain_events_def, auto)
        moreover 
        have "set [] \<subseteq> N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub>"
          by auto
        moreover 
        from \<beta>v'E2\<alpha>2'_in_Tr2 c_notin_E2 
        have "\<beta> \<upharpoonleft> E\<^bsub>ES2\<^esub> @ [c] \<upharpoonleft> E\<^bsub>ES2\<^esub> @ [] @ [v'] \<upharpoonleft> E\<^bsub>ES2\<^esub> @ \<alpha>2' \<in> Tr\<^bsub>ES2\<^esub>"
          by (simp add: projection_def)
        moreover
        have "\<alpha>2' \<upharpoonleft> V\<^bsub>\<V>2\<^esub> = \<alpha>2' \<upharpoonleft> V\<^bsub>\<V>2\<^esub>" ..
        moreover 
        note \<alpha>2'Cv2_empty
        ultimately have ?ALPHA2''_DELTA2''
          by blast
      }
      moreover {
        assume c_in_E2: "c \<in> E\<^bsub>ES2\<^esub>"
          and  v'_notin_E2: "v' \<notin> E\<^bsub>ES2\<^esub>"

        from c_in_E2 c_in_Cv_inter_Upsilon propSepViews 
          Upsilon_inter_E2_subset_Upsilon2
        have c_in_Cv2_inter_Upsilon2: "c \<in> C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub>"
          unfolding properSeparationOfViews_def by auto
        hence "c \<in> C\<^bsub>\<V>2\<^esub>"
          by auto
        moreover
        from \<beta>v'E2\<alpha>2'_in_Tr2 v'_notin_E2 have "\<beta> \<upharpoonleft> E\<^bsub>ES2\<^esub> @ \<alpha>2' \<in> Tr\<^bsub>ES2\<^esub>"
          by (simp add: projection_def)
        moreover
        note \<alpha>2'Cv2_empty
        moreover
        have "(Adm \<V>2 \<rho>2 Tr\<^bsub>ES2\<^esub> (\<beta> \<upharpoonleft> E\<^bsub>ES2\<^esub>) c)" 
          proof -
            from validES2 \<beta>v'E2\<alpha>2'_in_Tr2 v'_notin_E2 have "\<beta> \<upharpoonleft> E\<^bsub>ES2\<^esub> \<in> Tr\<^bsub>ES2\<^esub>"
              by (simp add: ES_valid_def traces_prefixclosed_def
                prefixclosed_def prefix_def projection_concatenation_commute)
            with total_ES2_C2_inter_Upsilon2 c_in_Cv2_inter_Upsilon2 
            have "\<beta> \<upharpoonleft> E\<^bsub>ES2\<^esub> @ [c] \<in> Tr\<^bsub>ES2\<^esub>"
              by (simp add: total_def)
            thus ?thesis
              unfolding Adm_def
              by blast
          qed
        moreover 
        note BSIA2
        ultimately obtain  \<alpha>2''
          where one: "\<beta> \<upharpoonleft> E\<^bsub>ES2\<^esub> @ [c] @ \<alpha>2'' \<in> Tr\<^bsub>ES2\<^esub>"
          and two:   "\<alpha>2'' \<upharpoonleft> V\<^bsub>\<V>2\<^esub> = \<alpha>2' \<upharpoonleft> V\<^bsub>\<V>2\<^esub>"
          and three: "\<alpha>2'' \<upharpoonleft> C\<^bsub>\<V>2\<^esub> = []"
          unfolding BSIA_def
          by blast

        from one validES2 have "set \<alpha>2'' \<subseteq> E\<^bsub>ES2\<^esub>"
          by (simp add: ES_valid_def traces_contain_events_def, auto)
        moreover
        have "set [] \<subseteq> N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub>"
          by auto
        moreover
        from one c_in_E2 v'_notin_E2 
        have "\<beta> \<upharpoonleft> E\<^bsub>ES2\<^esub> @ [c] \<upharpoonleft> E\<^bsub>ES2\<^esub> @ [] @ [v'] \<upharpoonleft> E\<^bsub>ES2\<^esub> @ \<alpha>2'' \<in> Tr\<^bsub>ES2\<^esub>"
          by (simp add: projection_def)
        moreover 
        note two three
        ultimately have ?ALPHA2''_DELTA2''
          by blast
      }
      moreover {
        assume c_in_E2: "c \<in> E\<^bsub>ES2\<^esub>"
          and  v'_in_E2: "v' \<in> E\<^bsub>ES2\<^esub>"

        from c_in_E2 c_in_Cv_inter_Upsilon propSepViews
          Upsilon_inter_E2_subset_Upsilon2
        have c_in_Cv2_inter_Upsilon2: "c \<in> C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub>"
          unfolding properSeparationOfViews_def by auto
        moreover
        from v'_in_E2 propSepViews v'_in_Vv_inter_Nabla Nabla_inter_E2_subset_Nabla2
        have "v' \<in> V\<^bsub>\<V>2\<^esub> \<inter> Nabla \<Gamma>2"
          unfolding properSeparationOfViews_def by auto
        moreover
        from v'_in_E2  \<beta>v'E2\<alpha>2'_in_Tr2 have "\<beta> \<upharpoonleft> E\<^bsub>ES2\<^esub> @ [v'] @ \<alpha>2' \<in> Tr\<^bsub>ES2\<^esub>"
          by (simp add: projection_def)
        moreover
        note \<alpha>2'Cv2_empty FCI2
        ultimately obtain \<alpha>2'' \<delta>2''
          where one: "set \<delta>2'' \<subseteq> N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub>"
          and two: "\<beta> \<upharpoonleft> E\<^bsub>ES2\<^esub> @ [c] @ \<delta>2'' @ [v'] @ \<alpha>2'' \<in> Tr\<^bsub>ES2\<^esub>"
          and three: "\<alpha>2'' \<upharpoonleft> V\<^bsub>\<V>2\<^esub> = \<alpha>2' \<upharpoonleft> V\<^bsub>\<V>2\<^esub>"
          and four: "\<alpha>2'' \<upharpoonleft> C\<^bsub>\<V>2\<^esub> = []"
          unfolding FCI_def
          by blast

        from two validES2 have "set \<alpha>2'' \<subseteq> E\<^bsub>ES2\<^esub>"
          by (simp add: ES_valid_def traces_contain_events_def, auto)
        moreover
        note one
        moreover
        from two c_in_E2 v'_in_E2 
        have "\<beta> \<upharpoonleft> E\<^bsub>ES2\<^esub> @ [c] \<upharpoonleft> E\<^bsub>ES2\<^esub> @ \<delta>2'' @ [v'] \<upharpoonleft> E\<^bsub>ES2\<^esub> @ \<alpha>2'' \<in> Tr\<^bsub>ES2\<^esub>"
          by (simp add: projection_def)
        moreover
        note three four
        ultimately have ?ALPHA2''_DELTA2''
          by blast
      }
      ultimately obtain \<alpha>2'' \<delta>2''
        where \<alpha>2''_in_E2star: "set \<alpha>2'' \<subseteq> E\<^bsub>ES2\<^esub>"
        and \<delta>2''_in_N2_inter_Delta2star:"set \<delta>2'' \<subseteq> N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub>"
        and \<beta>E2_cE2_\<delta>2''_v'E2_\<alpha>2''_in_Tr2:
              "\<beta> \<upharpoonleft> E\<^bsub>ES2\<^esub> @ [c] \<upharpoonleft> E\<^bsub>ES2\<^esub> @ \<delta>2'' @ [v'] \<upharpoonleft> E\<^bsub>ES2\<^esub> @ \<alpha>2'' \<in> Tr\<^bsub>ES2\<^esub>"
        and \<alpha>2''Vv2_is_\<alpha>2'Vv2: "\<alpha>2'' \<upharpoonleft> V\<^bsub>\<V>2\<^esub> = \<alpha>2' \<upharpoonleft> V\<^bsub>\<V>2\<^esub>"
        and \<alpha>2''Cv2_empty: "\<alpha>2'' \<upharpoonleft> C\<^bsub>\<V>2\<^esub> = []"
        by blast

      from c_in_Cv_inter_Upsilon Upsilon_inter_E1_subset_Upsilon1 
      propSepViews 
      have cE1_in_Cv1_inter_Upsilon1: "set ([c] \<upharpoonleft> E\<^bsub>ES1\<^esub>) \<subseteq> C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub>"
        unfolding properSeparationOfViews_def  by (simp add: projection_def, auto)
     
      from \<delta>2''_in_N2_inter_Delta2star Nv2_inter_Delta2_inter_E1_subsetof_Upsilon1 
        propSepViews disjoint_Nv2_Vv1 
      have \<delta>2''E1_in_Cv1_inter_Upsilon1star: "set (\<delta>2'' \<upharpoonleft> E\<^bsub>ES1\<^esub>) \<subseteq> C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub>"
        proof -
          from \<delta>2''_in_N2_inter_Delta2star 
          have eq: "\<delta>2'' \<upharpoonleft> E\<^bsub>ES1\<^esub> = \<delta>2'' \<upharpoonleft> (N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub> \<inter> E\<^bsub>ES1\<^esub>)"
            by (metis Int_commute Int_left_commute Int_lower1 Int_lower2 
              projection_intersection_neutral subset_trans)
          
          from validV1 Nv2_inter_Delta2_inter_E1_subsetof_Upsilon1 propSepViews
            disjoint_Nv2_Vv1  
          have "N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub> \<inter> E\<^bsub>ES1\<^esub> \<subseteq> C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub>"
            unfolding properSeparationOfViews_def
            by (simp add:isViewOn_def V_valid_def  VC_disjoint_def
              VN_disjoint_def NC_disjoint_def, auto)
          thus ?thesis
            by (subst eq, simp only: projection_def, auto)
        qed
      
      have c\<delta>2''E1_in_Cv1_inter_Upsilon1star: "set ((c # \<delta>2'') \<upharpoonleft> E\<^bsub>ES1\<^esub>) \<subseteq> C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub>"
        proof -
          from cE1_in_Cv1_inter_Upsilon1 \<delta>2''E1_in_Cv1_inter_Upsilon1star
          have "set (([c] @ \<delta>2'') \<upharpoonleft> E\<^bsub>ES1\<^esub>) \<subseteq> C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub>"
            by (simp only: projection_concatenation_commute, auto)
          thus ?thesis
            by auto
        qed


      have "\<exists> \<alpha>1'' \<delta>1''. set \<alpha>1'' \<subseteq> E\<^bsub>ES1\<^esub> 
        \<and> set \<delta>1'' \<subseteq> N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub> \<union> C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub> \<inter> N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2
\<^esub>        \<and> \<beta> \<upharpoonleft> E\<^bsub>ES1\<^esub> @ [c] \<upharpoonleft> E\<^bsub>ES1\<^esub> @ \<delta>1'' @ [v'] \<upharpoonleft> E\<^bsub>ES1\<^esub> @ \<alpha>1'' \<in> Tr\<^bsub>ES1\<^esub>        
        \<and> \<alpha>1'' \<upharpoonleft> V\<^bsub>\<V>1\<^esub> = \<alpha>1' \<upharpoonleft> V\<^bsub>\<V>1\<^esub> \<and> \<alpha>1'' \<upharpoonleft> C\<^bsub>\<V>1\<^esub> = []
        \<and> \<delta>1'' \<upharpoonleft> E\<^bsub>ES2\<^esub> = \<delta>2'' \<upharpoonleft> E\<^bsub>ES1\<^esub>"
        proof cases
          assume v'_in_E1: "v' \<in> E\<^bsub>ES1\<^esub>"
          with Nabla_inter_E1_subset_Nabla1 propSepViews v'_in_Vv_inter_Nabla
          have v'_in_Vv1_inter_Nabla1: "v' \<in> V\<^bsub>\<V>1\<^esub> \<inter> Nabla \<Gamma>1"
            unfolding properSeparationOfViews_def by auto

          have "\<lbrakk> (\<beta> @ [v']) \<upharpoonleft> E\<^bsub>ES1\<^esub> @ \<alpha>1' \<in> Tr\<^bsub>ES1\<^esub> ; 
            \<alpha>1' \<upharpoonleft> C\<^bsub>\<V>1\<^esub> = []; set ((c # \<delta>2'') \<upharpoonleft> E\<^bsub>ES1\<^esub>) \<subseteq> C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub> ; 
            c \<in> C\<^bsub>\<V>\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>\<^esub> ; set \<delta>2'' \<subseteq> N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub> \<rbrakk> 
            \<Longrightarrow> \<exists> \<alpha>1'' \<delta>1''. (set \<alpha>1'' \<subseteq> E\<^bsub>ES1\<^esub> \<and> set \<delta>1'' \<subseteq> N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub> 
              \<union> C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub> \<inter> N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub>
            \<and> \<beta> \<upharpoonleft> E\<^bsub>ES1\<^esub> @ [c] \<upharpoonleft> E\<^bsub>ES1\<^esub> @ \<delta>1'' @ [v'] \<upharpoonleft> E\<^bsub>ES1\<^esub> @ \<alpha>1'' \<in> Tr\<^bsub>ES1\<^esub>            
            \<and> \<alpha>1'' \<upharpoonleft> V\<^bsub>\<V>1\<^esub> = \<alpha>1' \<upharpoonleft> V\<^bsub>\<V>1\<^esub> \<and> \<alpha>1'' \<upharpoonleft> C\<^bsub>\<V>1\<^esub> = []
            \<and> \<delta>1'' \<upharpoonleft> (C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub>) = \<delta>2'' \<upharpoonleft> E\<^bsub>ES1\<^esub>)"
            proof (induct "length ((c # \<delta>2'') \<upharpoonleft> E\<^bsub>ES1\<^esub>)" arbitrary: \<beta> \<alpha>1' c \<delta>2'')
              case 0

              from 0(2) validES1 have "set \<alpha>1' \<subseteq> E\<^bsub>ES1\<^esub>"
                by (simp add: ES_valid_def traces_contain_events_def, auto)
              moreover
              have "set [] \<subseteq> N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub> \<union> C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub> \<inter> N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub>"
                by auto
              moreover
              have "\<beta> \<upharpoonleft> E\<^bsub>ES1\<^esub> @ [c] \<upharpoonleft> E\<^bsub>ES1\<^esub> @ [] @ [v'] \<upharpoonleft> E\<^bsub>ES1\<^esub> @ \<alpha>1' \<in> Tr\<^bsub>ES1\<^esub>"
                proof -
                  note 0(2)
                  moreover
                  from 0(1) have "c \<notin> E\<^bsub>ES1\<^esub>"
                    by (simp add: projection_def, auto)
                  ultimately show ?thesis
                    by (simp add: projection_concatenation_commute projection_def)
                qed
              moreover
              have "\<alpha>1' \<upharpoonleft> V\<^bsub>\<V>1\<^esub> = \<alpha>1' \<upharpoonleft> V\<^bsub>\<V>1\<^esub>" ..
              moreover
              note 0(3)
              moreover 
              from 0(1) have "[] \<upharpoonleft> (C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub>) = \<delta>2'' \<upharpoonleft> E\<^bsub>ES1\<^esub>"
                by (simp add: projection_def, split if_split_asm, auto)
              ultimately show ?case
                by blast
            next
              case (Suc n)

              from projection_split_last[OF Suc(2)] obtain \<mu> c' \<nu>
                where c'_in_E1: "c' \<in> E\<^bsub>ES1\<^esub>"
                and c\<delta>2''_is_\<mu>c'\<nu>: "c # \<delta>2'' = \<mu> @ [c'] @ \<nu>"
                and \<nu>E1_empty: "\<nu> \<upharpoonleft> E\<^bsub>ES1\<^esub> = []"
                and n_is_length_\<mu>\<nu>E1: "n = length ((\<mu> @ \<nu>) \<upharpoonleft> E\<^bsub>ES1\<^esub>)"
                by blast

              from Suc(5) c'_in_E1 c\<delta>2''_is_\<mu>c'\<nu> 
              have "set (\<mu> \<upharpoonleft> E\<^bsub>ES1\<^esub> @ [c']) \<subseteq> C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub>"
                by (simp only: c\<delta>2''_is_\<mu>c'\<nu> projection_concatenation_commute 
                  projection_def, auto)
              hence c'_in_Cv1_inter_Upsilon1: "c' \<in> C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub>"
                by auto
              hence c'_in_Cv1: "c' \<in> C\<^bsub>\<V>1\<^esub>" and c'_in_Upsilon1: "c' \<in> \<Upsilon>\<^bsub>\<Gamma>1\<^esub>"
                by auto
              with validV1 have c'_in_E1: "c' \<in> E\<^bsub>ES1\<^esub>"
                by (simp add: isViewOn_def V_valid_def  VC_disjoint_def 
                  VN_disjoint_def NC_disjoint_def, auto)

              show ?case
                proof (cases \<mu>)
                  case Nil (* we apply FCI in this case *)
                  with c\<delta>2''_is_\<mu>c'\<nu> have c_is_c': "c = c'" and \<delta>2''_is_\<nu>: "\<delta>2'' = \<nu>"
                    by auto
                  with c'_in_Cv1_inter_Upsilon1 have "c \<in> C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub>"
                    by simp
                  moreover
                  note v'_in_Vv1_inter_Nabla1
                  moreover
                  from v'_in_E1 Suc(3) have "(\<beta> \<upharpoonleft> E\<^bsub>ES1\<^esub>) @ [v'] @ \<alpha>1' \<in> Tr\<^bsub>ES1\<^esub>"
                    by (simp add: projection_concatenation_commute projection_def)
                  moreover
                  note Suc(4) FCI1
                  ultimately obtain \<alpha>1'' \<gamma>
                    where one: "set \<gamma> \<subseteq> N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub>"
                    and two: "\<beta> \<upharpoonleft> E\<^bsub>ES1\<^esub> @ [c] @ \<gamma> @ [v'] @ \<alpha>1'' \<in> Tr\<^bsub>ES1\<^esub>"
                    and three: "\<alpha>1'' \<upharpoonleft> V\<^bsub>\<V>1\<^esub> = \<alpha>1' \<upharpoonleft> V\<^bsub>\<V>1\<^esub>"
                    and four: "\<alpha>1'' \<upharpoonleft> C\<^bsub>\<V>1\<^esub> = []"
                    unfolding FCI_def
                    by blast

                  (* we choose \<delta>1'' = \<nu> \<upharpoonleft> E\<^bsub>ES1\<^esub> @ \<gamma> *)
                  let ?DELTA1'' = "\<nu> \<upharpoonleft> E\<^bsub>ES1\<^esub> @ \<gamma>"

                  from two validES1 have "set \<alpha>1'' \<subseteq> E\<^bsub>ES1\<^esub>"
                    by (simp add: ES_valid_def traces_contain_events_def, auto)
                  moreover
                  from one \<nu>E1_empty 
                  have "set ?DELTA1'' \<subseteq> N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub> \<union> C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub> \<inter> N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub>"
                    by auto
                  moreover
                  have "\<beta> \<upharpoonleft> E\<^bsub>ES1\<^esub> @ [c] \<upharpoonleft> E\<^bsub>ES1\<^esub> @ ?DELTA1'' @ [v'] \<upharpoonleft> E\<^bsub>ES1\<^esub> @ \<alpha>1'' \<in> Tr\<^bsub>ES1\<^esub>"
                    proof -
                      from c_is_c' c'_in_E1 have "[c] = [c] \<upharpoonleft> E\<^bsub>ES1\<^esub>"
                        by (simp add: projection_def)
                      moreover
                      from v'_in_E1 have "[v'] = [v'] \<upharpoonleft> E\<^bsub>ES1\<^esub>"
                        by (simp add: projection_def)
                      moreover
                      note \<nu>E1_empty two
                      ultimately show ?thesis
                        by auto
                    qed
                  moreover
                  note three four
                  moreover
                  have "?DELTA1'' \<upharpoonleft> (C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub>) = \<delta>2'' \<upharpoonleft> E\<^bsub>ES1\<^esub>"
                    proof -
                      have "\<gamma> \<upharpoonleft> (C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub>) = []"
                        proof -
                          from validV1 have "N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub> \<inter> (C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub>) = {}"
                            by (simp add: isViewOn_def V_valid_def 
                              VC_disjoint_def VN_disjoint_def NC_disjoint_def, auto)
                          with projection_intersection_neutral[OF one, of "C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub>"]
                          show ?thesis
                            by (simp add: projection_def)
                        qed
                      with \<delta>2''_is_\<nu> \<nu>E1_empty show ?thesis
                        by (simp add: projection_concatenation_commute)
                    qed
                  ultimately show ?thesis
                    by blast
                next
                  case (Cons x xs) (* we apply the inductive hypothesis in this case *)
                  with c\<delta>2''_is_\<mu>c'\<nu> have \<mu>_is_c_xs: "\<mu> = [c] @ xs" 
                    and \<delta>2''_is_xs_c'_\<nu>: "\<delta>2'' = xs @ [c'] @ \<nu>"
                    by auto
                  with n_is_length_\<mu>\<nu>E1 have "n = length ((c # (xs @ \<nu>)) \<upharpoonleft> E\<^bsub>ES1\<^esub>)"
                    by auto
                  moreover
                  note Suc(3,4)
                  moreover
                  have "set ((c # (xs @ \<nu>)) \<upharpoonleft> E\<^bsub>ES1\<^esub>) \<subseteq> C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub>"
                    proof -
                      have res: "c # (xs @ \<nu>) = [c] @ (xs @ \<nu>)" 
                        by auto

                      from Suc(5) c\<delta>2''_is_\<mu>c'\<nu> \<mu>_is_c_xs \<nu>E1_empty
                      show ?thesis
                        by (subst res, simp only: c\<delta>2''_is_\<mu>c'\<nu> projection_concatenation_commute 
                          set_append, auto)
                    qed
                  moreover
                  note Suc(6) 
                  moreover
                  from Suc(7) \<delta>2''_is_xs_c'_\<nu> have "set (xs @ \<nu>) \<subseteq> N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub>"
                    by auto
                  moreover note Suc(1)[of c "xs @ \<nu>" \<beta> \<alpha>1']
                  ultimately obtain \<delta> \<gamma>
                    where one: "set \<delta> \<subseteq> E\<^bsub>ES1\<^esub>"
                    and two: "set \<gamma> \<subseteq> N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub> \<union> C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub> \<inter> N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub>"
                    and three: "\<beta> \<upharpoonleft> E\<^bsub>ES1\<^esub> @ [c] \<upharpoonleft> E\<^bsub>ES1\<^esub> @ \<gamma> @ [v'] \<upharpoonleft> E\<^bsub>ES1\<^esub> @ \<delta> \<in> Tr\<^bsub>ES1\<^esub>"
                    and four: "\<delta> \<upharpoonleft> V\<^bsub>\<V>1\<^esub> = \<alpha>1' \<upharpoonleft> V\<^bsub>\<V>1\<^esub>"
                    and five: "\<delta> \<upharpoonleft> C\<^bsub>\<V>1\<^esub> = []"
                    and six: "\<gamma> \<upharpoonleft> (C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub>) = (xs @ \<nu>) \<upharpoonleft> E\<^bsub>ES1\<^esub>"
                    by blast

                  (* apply FCI to insert c' after \<gamma> *)
                  let ?BETA = "\<beta> \<upharpoonleft> E\<^bsub>ES1\<^esub> @ [c] \<upharpoonleft> E\<^bsub>ES1\<^esub> @ \<gamma>"

                  note c'_in_Cv1_inter_Upsilon1 v'_in_Vv1_inter_Nabla1
                  moreover
                  from three v'_in_E1 have "?BETA @ [v'] @ \<delta> \<in> Tr\<^bsub>ES1\<^esub>"
                    by (simp add: projection_def)
                  moreover
                  note five FCI1
                  ultimately obtain \<alpha>1'' \<delta>'
                    where fci_one: "set \<delta>' \<subseteq> N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub>"
                    and fci_two: "?BETA @ [c'] @ \<delta>' @ [v'] @ \<alpha>1'' \<in> Tr\<^bsub>ES1\<^esub>"
                    and fci_three: "\<alpha>1'' \<upharpoonleft> V\<^bsub>\<V>1\<^esub> = \<delta> \<upharpoonleft> V\<^bsub>\<V>1\<^esub>"
                    and fci_four:  "\<alpha>1'' \<upharpoonleft> C\<^bsub>\<V>1\<^esub> = []"
                    unfolding FCI_def
                    by blast
  
                  let ?DELTA1'' = "\<gamma> @ [c'] @ \<delta>'"

                  from fci_two validES1 have "set \<alpha>1'' \<subseteq> E\<^bsub>ES1\<^esub>"
                    by (simp add: ES_valid_def traces_contain_events_def, auto)
                  moreover
                  have "set ?DELTA1'' \<subseteq> N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub> \<union> C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub> \<inter> N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub>"
                    proof -
                      from Suc(7) c'_in_Cv1_inter_Upsilon1 \<delta>2''_is_xs_c'_\<nu> 
                      have "c' \<in>  C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub> \<inter> N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub>"
                        by auto
                      with two fci_one show ?thesis
                        by auto
                    qed
                  moreover
                  from fci_two v'_in_E1 
                  have "\<beta> \<upharpoonleft> E\<^bsub>ES1\<^esub> @ [c] \<upharpoonleft> E\<^bsub>ES1\<^esub> @ ?DELTA1'' @ [v'] \<upharpoonleft> E\<^bsub>ES1\<^esub> @ \<alpha>1'' \<in> Tr\<^bsub>ES1\<^esub>"
                    by (simp add: projection_def)
                  moreover
                  from fci_three four have "\<alpha>1'' \<upharpoonleft> V\<^bsub>\<V>1\<^esub> = \<alpha>1' \<upharpoonleft> V\<^bsub>\<V>1\<^esub>"
                    by simp
                  moreover
                  note fci_four
                  moreover             
                  have "?DELTA1'' \<upharpoonleft> (C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub>) = \<delta>2'' \<upharpoonleft> E\<^bsub>ES1\<^esub>"
                    proof -
                      have "\<delta>' \<upharpoonleft> (C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub>) = []"
                        proof -
                          from fci_one have "\<forall> e \<in> set \<delta>'. e \<in> N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub>"
                            by auto
                          with validV1 have "\<forall> e \<in> set \<delta>'. e \<notin> C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub>"
                            by (simp add: isViewOn_def V_valid_def
                              VC_disjoint_def VN_disjoint_def NC_disjoint_def, auto)
                          thus ?thesis
                            by (simp add: projection_def)
                        qed
                      with c'_in_E1 c'_in_Cv1_inter_Upsilon1 \<delta>2''_is_xs_c'_\<nu> \<nu>E1_empty six 
                      show ?thesis
                        by (simp only: projection_concatenation_commute projection_def, auto)
                    qed
                  ultimately show ?thesis 
                    by blast     
                qed
          qed
          from this[OF \<beta>v'E1\<alpha>1'_in_Tr1 \<alpha>1'Cv1_empty c\<delta>2''E1_in_Cv1_inter_Upsilon1star 
            c_in_Cv_inter_Upsilon \<delta>2''_in_N2_inter_Delta2star]
          obtain \<alpha>1'' \<delta>1''
            where one: "set \<alpha>1'' \<subseteq> E\<^bsub>ES1\<^esub>"
            and two: "set \<delta>1'' \<subseteq> N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub> \<union> C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub> \<inter> N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub>"
            and three: "\<beta> \<upharpoonleft> E\<^bsub>ES1\<^esub> @ [c] \<upharpoonleft> E\<^bsub>ES1\<^esub> @ \<delta>1'' @ [v'] \<upharpoonleft> E\<^bsub>ES1\<^esub> @ \<alpha>1'' \<in> Tr\<^bsub>ES1\<^esub>            
            \<and> \<alpha>1'' \<upharpoonleft> V\<^bsub>\<V>1\<^esub> = \<alpha>1' \<upharpoonleft> V\<^bsub>\<V>1\<^esub> \<and> \<alpha>1'' \<upharpoonleft> C\<^bsub>\<V>1\<^esub> = []"
            and four: "\<delta>1'' \<upharpoonleft> (C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub>) = \<delta>2'' \<upharpoonleft> E\<^bsub>ES1\<^esub>"
            by blast

          note one two three
          moreover
          have "\<delta>1'' \<upharpoonleft> E\<^bsub>ES2\<^esub> = \<delta>2'' \<upharpoonleft> E\<^bsub>ES1\<^esub>" 
            proof -
              from projection_intersection_neutral[OF two, of "E\<^bsub>ES2\<^esub>"] 
                Nv1_inter_Delta1_inter_E2_empty validV2 
              have "\<delta>1'' \<upharpoonleft> E\<^bsub>ES2\<^esub> = \<delta>1'' \<upharpoonleft> (C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub> \<inter> N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub> \<inter> E\<^bsub>ES2\<^esub>)"
                by (simp only: Int_Un_distrib2, auto)
              moreover
              from validV2 
              have "C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub> \<inter> N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub> \<inter> E\<^bsub>ES2\<^esub> = C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub> \<inter> N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub>"
                by (simp add: isViewOn_def V_valid_def 
                  VC_disjoint_def VN_disjoint_def NC_disjoint_def, auto)
              ultimately have "\<delta>1'' \<upharpoonleft> E\<^bsub>ES2\<^esub> = \<delta>1'' \<upharpoonleft> (C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub> \<inter> N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub>)"
                by simp
              hence "\<delta>1'' \<upharpoonleft> E\<^bsub>ES2\<^esub> = \<delta>1'' \<upharpoonleft> (C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub>) \<upharpoonleft> (N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub>)"
                by (simp add: projection_def)
              with four have "\<delta>1'' \<upharpoonleft> E\<^bsub>ES2\<^esub> = \<delta>2'' \<upharpoonleft> E\<^bsub>ES1\<^esub> \<upharpoonleft> (N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub>)"
                by simp
              hence "\<delta>1'' \<upharpoonleft> E\<^bsub>ES2\<^esub> = \<delta>2'' \<upharpoonleft> (N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub>) \<upharpoonleft> E\<^bsub>ES1\<^esub>"
                by (simp only: projection_commute)
              with \<delta>2''_in_N2_inter_Delta2star show ?thesis
                by (simp only: list_subset_iff_projection_neutral)
            qed
          ultimately show ?thesis
              by blast
        next
          assume v'_notin_E1: "v' \<notin> E\<^bsub>ES1\<^esub>"

           have "\<lbrakk> (\<beta> @ [v']) \<upharpoonleft> E\<^bsub>ES1\<^esub> @ \<alpha>1' \<in> Tr\<^bsub>ES1\<^esub> ; 
            \<alpha>1' \<upharpoonleft> C\<^bsub>\<V>1\<^esub> = []; set ((c # \<delta>2'') \<upharpoonleft> E\<^bsub>ES1\<^esub>) \<subseteq> C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub> ; 
             c \<in> C\<^bsub>\<V>\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>\<^esub> ; set \<delta>2'' \<subseteq> N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub> \<rbrakk> 
            \<Longrightarrow> \<exists> \<alpha>1'' \<delta>1''. (set \<alpha>1'' \<subseteq> E\<^bsub>ES1\<^esub> \<and> set \<delta>1'' \<subseteq> N\<^bsub>\<V>1\<^esub> 
                \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub> \<union> C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub> \<inter> N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2
\<^esub>            \<and> \<beta> \<upharpoonleft> E\<^bsub>ES1\<^esub> @ [c] \<upharpoonleft> E\<^bsub>ES1\<^esub> @ \<delta>1'' @ [v'] \<upharpoonleft> E\<^bsub>ES1\<^esub> @ \<alpha>1'' \<in> Tr\<^bsub>ES1\<^esub>            
             \<and> \<alpha>1'' \<upharpoonleft> V\<^bsub>\<V>1\<^esub> = \<alpha>1' \<upharpoonleft> V\<^bsub>\<V>1\<^esub> \<and> \<alpha>1'' \<upharpoonleft> C\<^bsub>\<V>1\<^esub> = []
            \<and> \<delta>1'' \<upharpoonleft> E\<^bsub>ES2\<^esub> = \<delta>2'' \<upharpoonleft> E\<^bsub>ES1\<^esub>)"
            proof (induct "length ((c # \<delta>2'') \<upharpoonleft> E\<^bsub>ES1\<^esub>)" arbitrary: \<beta> \<alpha>1' c \<delta>2'')
               case 0

              from 0(2) validES1 have "set \<alpha>1' \<subseteq> E\<^bsub>ES1\<^esub>"
                by (simp add: ES_valid_def traces_contain_events_def, auto)
              moreover
              have "set [] \<subseteq> N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub> \<union> C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub> \<inter> N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub>"
                by auto
              moreover
              have "\<beta> \<upharpoonleft> E\<^bsub>ES1\<^esub> @ [c] \<upharpoonleft> E\<^bsub>ES1\<^esub> @ [] @ [v'] \<upharpoonleft> E\<^bsub>ES1\<^esub> @ \<alpha>1' \<in> Tr\<^bsub>ES1\<^esub>"
                proof -
                  note 0(2)
                  moreover
                  from 0(1) have "c \<notin> E\<^bsub>ES1\<^esub>"
                    by (simp add: projection_def, auto)
                  ultimately show ?thesis
                    by (simp add: projection_concatenation_commute projection_def)
                qed
              moreover
              have "\<alpha>1' \<upharpoonleft> V\<^bsub>\<V>1\<^esub> = \<alpha>1' \<upharpoonleft> V\<^bsub>\<V>1\<^esub>" ..
              moreover
              note 0(3)
              moreover 
              from 0(1) have "[] \<upharpoonleft> E\<^bsub>ES2\<^esub> = \<delta>2'' \<upharpoonleft> E\<^bsub>ES1\<^esub>"
                by (simp add: projection_def, split if_split_asm, auto)
              ultimately show ?case
                by blast
            next
              case (Suc n)

              from projection_split_last[OF Suc(2)] obtain \<mu> c' \<nu>
                where c'_in_E1: "c' \<in> E\<^bsub>ES1\<^esub>"
                and c\<delta>2''_is_\<mu>c'\<nu>: "c # \<delta>2'' = \<mu> @ [c'] @ \<nu>"
                and \<nu>E1_empty: "\<nu> \<upharpoonleft> E\<^bsub>ES1\<^esub> = []"
                and n_is_length_\<mu>\<nu>E1: "n = length ((\<mu> @ \<nu>) \<upharpoonleft> E\<^bsub>ES1\<^esub>)"
                by blast

              from Suc(5) c'_in_E1 c\<delta>2''_is_\<mu>c'\<nu> 
              have "set (\<mu> \<upharpoonleft> E\<^bsub>ES1\<^esub> @ [c']) \<subseteq> C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub>"
                by (simp only: c\<delta>2''_is_\<mu>c'\<nu> projection_concatenation_commute 
                  projection_def, auto)
              hence c'_in_Cv1_inter_Upsilon1: "c' \<in> C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub>"
                by auto
              hence c'_in_Cv1: "c' \<in> C\<^bsub>\<V>1\<^esub>" and c'_in_Upsilon1: "c' \<in> \<Upsilon>\<^bsub>\<Gamma>1\<^esub>"
                by auto
              with validV1 have c'_in_E1: "c' \<in> E\<^bsub>ES1\<^esub>"
                by (simp add: isViewOn_def V_valid_def
                  VC_disjoint_def VN_disjoint_def NC_disjoint_def, auto)

              show ?case
                proof (cases \<mu>)
                  case Nil (* we just apply BSIA in this case *)
                  with c\<delta>2''_is_\<mu>c'\<nu> have c_is_c': "c = c'" 
                    and \<delta>2''_is_\<nu>: "\<delta>2'' = \<nu>"
                    by auto
                  with c'_in_Cv1_inter_Upsilon1 have "c \<in> C\<^bsub>\<V>1\<^esub>"
                    by simp
                  moreover
                  from v'_notin_E1 Suc(3) have "(\<beta> \<upharpoonleft> E\<^bsub>ES1\<^esub>) @ \<alpha>1' \<in> Tr\<^bsub>ES1\<^esub>"
                    by (simp add: projection_concatenation_commute projection_def)
                  moreover
                  note Suc(4)
                  moreover
                  have "Adm \<V>1 \<rho>1 Tr\<^bsub>ES1\<^esub> (\<beta> \<upharpoonleft> E\<^bsub>ES1\<^esub>) c"
                    proof -
                      have "\<beta> \<upharpoonleft> E\<^bsub>ES1\<^esub> @ [c] \<in> Tr\<^bsub>ES1\<^esub>"
                        proof -
                          from c_is_c' c'_in_Cv1_inter_Upsilon1 
                          have "c \<in> C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub>"
                            by simp
                          moreover
                          from validES1 Suc(3) 
                          have "(\<beta> \<upharpoonleft> E\<^bsub>ES1\<^esub>) \<in> Tr\<^bsub>ES1\<^esub>"
                            by (simp only: ES_valid_def traces_prefixclosed_def
                              projection_concatenation_commute 
                              prefixclosed_def prefix_def, auto)
                          moreover
                          note total_ES1_C1_inter_Upsilon1
                          ultimately show ?thesis
                            unfolding total_def
                            by blast
                        qed
                      thus ?thesis
                        unfolding Adm_def
                        by blast                        
                    qed
                  moreover
                  note BSIA1
                  ultimately obtain \<alpha>1''
                    where one: "(\<beta> \<upharpoonleft> E\<^bsub>ES1\<^esub>) @ [c] @ \<alpha>1'' \<in> Tr\<^bsub>ES1\<^esub>"
                    and two: "\<alpha>1'' \<upharpoonleft> V\<^bsub>\<V>1\<^esub> = \<alpha>1' \<upharpoonleft> V\<^bsub>\<V>1\<^esub>"
                    and three: "\<alpha>1'' \<upharpoonleft> C\<^bsub>\<V>1\<^esub> = []"
                    unfolding BSIA_def
                    by blast

                  let ?DELTA1'' = "\<nu> \<upharpoonleft> E\<^bsub>ES1\<^esub>"

                  from one validES1 have "set \<alpha>1'' \<subseteq> E\<^bsub>ES1\<^esub>"
                    by (simp add: ES_valid_def traces_contain_events_def, auto)
                  moreover
                  from \<nu>E1_empty
                  have "set ?DELTA1'' \<subseteq> N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub> \<union> C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub> \<inter> N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub>"
                    by simp
                  moreover
                  from c_is_c' c'_in_E1 one v'_notin_E1 \<nu>E1_empty
                  have "(\<beta> \<upharpoonleft> E\<^bsub>ES1\<^esub>) @ [c] \<upharpoonleft> E\<^bsub>ES1\<^esub> @ ?DELTA1'' @ [v'] \<upharpoonleft> E\<^bsub>ES1\<^esub> @ \<alpha>1'' \<in> Tr\<^bsub>ES1\<^esub>"
                    by (simp add: projection_def)
                  moreover
                  note two three
                  moreover
                  from \<nu>E1_empty \<delta>2''_is_\<nu> have "?DELTA1'' \<upharpoonleft> E\<^bsub>ES2\<^esub> = \<delta>2'' \<upharpoonleft> E\<^bsub>ES1\<^esub>"
                    by (simp add: projection_def)
                  ultimately show ?thesis
                    by blast
                next
                  case (Cons x xs) (* apply inductive hypothesis, then BSIA *)
                  with c\<delta>2''_is_\<mu>c'\<nu>
                  have \<mu>_is_c_xs: "\<mu> = [c] @ xs" and \<delta>2''_is_xs_c'_\<nu>: "\<delta>2'' = xs @ [c'] @ \<nu>"
                    by auto
                  with n_is_length_\<mu>\<nu>E1 have "n = length ((c # (xs @ \<nu>)) \<upharpoonleft> E\<^bsub>ES1\<^esub>)"
                    by auto
                  moreover
                  note Suc(3,4)
                  moreover
                  have "set ((c # (xs @ \<nu>)) \<upharpoonleft> E\<^bsub>ES1\<^esub>) \<subseteq> C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub>"
                    proof -
                      have res: "c # (xs @ \<nu>) = [c] @ (xs @ \<nu>)" 
                        by auto

                      from Suc(5) c\<delta>2''_is_\<mu>c'\<nu> \<mu>_is_c_xs \<nu>E1_empty
                      show ?thesis
                        by (subst res, simp only: c\<delta>2''_is_\<mu>c'\<nu> projection_concatenation_commute 
                          set_append, auto)
                    qed
                  moreover
                  note Suc(6) 
                  moreover
                  from Suc(7) \<delta>2''_is_xs_c'_\<nu> have "set (xs @ \<nu>) \<subseteq> N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub>"
                    by auto
                  moreover note Suc(1)[of c "xs @ \<nu>" \<beta> \<alpha>1']
                  ultimately obtain \<delta> \<gamma>
                    where one: "set \<delta> \<subseteq> E\<^bsub>ES1\<^esub>"
                    and two: "set \<gamma> \<subseteq> N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub> \<union> C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub> \<inter> N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub>"
                    and three: "\<beta> \<upharpoonleft> E\<^bsub>ES1\<^esub> @ [c] \<upharpoonleft> E\<^bsub>ES1\<^esub> @ \<gamma> @ [v'] \<upharpoonleft> E\<^bsub>ES1\<^esub> @ \<delta> \<in> Tr\<^bsub>ES1\<^esub>"
                    and four: "\<delta> \<upharpoonleft> V\<^bsub>\<V>1\<^esub> = \<alpha>1' \<upharpoonleft> V\<^bsub>\<V>1\<^esub>"
                    and five: "\<delta> \<upharpoonleft> C\<^bsub>\<V>1\<^esub> = []"
                    and six: "\<gamma> \<upharpoonleft> E\<^bsub>ES2\<^esub> = (xs @ \<nu>) \<upharpoonleft> E\<^bsub>ES1\<^esub>"
                    by blast
                  
                   (* apply BSIA to insert c' after \<gamma> *)
                  let ?BETA = "\<beta> \<upharpoonleft> E\<^bsub>ES1\<^esub> @ [c] \<upharpoonleft> E\<^bsub>ES1\<^esub> @ \<gamma>"

                  from c'_in_Cv1_inter_Upsilon1 have "c' \<in> C\<^bsub>\<V>1\<^esub>"
                    by auto
                  moreover
                  from three v'_notin_E1 have "?BETA @ \<delta> \<in> Tr\<^bsub>ES1\<^esub>"
                    by (simp add: projection_def)
                  moreover
                  note five 
                  moreover
                  have "Adm \<V>1 \<rho>1 Tr\<^bsub>ES1\<^esub> ?BETA c'"
                    proof -
                      have "?BETA @ [c'] \<in> Tr\<^bsub>ES1\<^esub>"
                        proof -
                          from validES1 three 
                          have "?BETA \<in> Tr\<^bsub>ES1\<^esub>"
                            by (simp only: ES_valid_def traces_prefixclosed_def
                              projection_concatenation_commute 
                              prefixclosed_def prefix_def, auto)
                          moreover
                          note c'_in_Cv1_inter_Upsilon1 total_ES1_C1_inter_Upsilon1
                          ultimately show ?thesis
                            unfolding total_def
                            by blast
                        qed
                      thus ?thesis
                        unfolding Adm_def
                        by blast                        
                    qed
                  moreover
                  note BSIA1
                  ultimately obtain \<alpha>1''
                    where bsia_one: "?BETA @ [c'] @ \<alpha>1'' \<in> Tr\<^bsub>ES1\<^esub>"
                    and bsia_two: "\<alpha>1'' \<upharpoonleft> V\<^bsub>\<V>1\<^esub> = \<delta> \<upharpoonleft> V\<^bsub>\<V>1\<^esub>"
                    and bsia_three:  "\<alpha>1'' \<upharpoonleft> C\<^bsub>\<V>1\<^esub> = []"
                    unfolding BSIA_def
                    by blast
  
                  let ?DELTA1'' = "\<gamma> @ [c']"

                  from bsia_one validES1 have "set \<alpha>1'' \<subseteq> E\<^bsub>ES1\<^esub>"
                    by (simp add:isViewOn_def ES_valid_def traces_contain_events_def, auto)
                  moreover
                  have "set ?DELTA1'' \<subseteq> N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub> \<union> C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub> \<inter> N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub>"
                    proof -
                      from Suc(7) c'_in_Cv1_inter_Upsilon1 \<delta>2''_is_xs_c'_\<nu> 
                      have "c' \<in>  C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub> \<inter> N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub>"
                        by auto
                      with two show ?thesis
                        by auto
                    qed
                  moreover
                  from bsia_one v'_notin_E1 
                  have "\<beta> \<upharpoonleft> E\<^bsub>ES1\<^esub> @ [c] \<upharpoonleft> E\<^bsub>ES1\<^esub> @ ?DELTA1'' @ [v'] \<upharpoonleft> E\<^bsub>ES1\<^esub> @ \<alpha>1'' \<in> Tr\<^bsub>ES1\<^esub>"
                    by (simp add: projection_def)
                  moreover
                  from bsia_two four have "\<alpha>1'' \<upharpoonleft> V\<^bsub>\<V>1\<^esub> = \<alpha>1' \<upharpoonleft> V\<^bsub>\<V>1\<^esub>"
                    by simp
                  moreover
                  note bsia_three
                  moreover             
                  have "?DELTA1'' \<upharpoonleft> E\<^bsub>ES2\<^esub> = \<delta>2'' \<upharpoonleft> E\<^bsub>ES1\<^esub>"
                    proof -
                      from validV2 Suc(7) \<delta>2''_is_xs_c'_\<nu> 
                      have "c' \<in> E\<^bsub>ES2\<^esub>"
                        by (simp add: isViewOn_def V_valid_def
                          VC_disjoint_def VN_disjoint_def NC_disjoint_def, auto)
                      with c'_in_E1 c'_in_Cv1_inter_Upsilon1 \<delta>2''_is_xs_c'_\<nu> \<nu>E1_empty six 
                      show ?thesis
                        by (simp only: projection_concatenation_commute projection_def, auto)
                    qed
                  ultimately show ?thesis 
                    by blast     
                qed
            qed
          from this[OF \<beta>v'E1\<alpha>1'_in_Tr1 \<alpha>1'Cv1_empty c\<delta>2''E1_in_Cv1_inter_Upsilon1star 
            c_in_Cv_inter_Upsilon \<delta>2''_in_N2_inter_Delta2star]
          show ?thesis 
            by blast
        qed
      then obtain \<alpha>1'' \<delta>1''
        where \<alpha>1''_in_E1star: "set \<alpha>1'' \<subseteq> E\<^bsub>ES1\<^esub>"
        and \<delta>1''_in_N1_inter_Delta1star:"set \<delta>1'' \<subseteq> N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub> \<union> C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub> \<inter> N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub>"
        and \<beta>E1_cE1_\<delta>1''_v'E1_\<alpha>1''_in_Tr1: 
        "\<beta> \<upharpoonleft> E\<^bsub>ES1\<^esub> @ [c] \<upharpoonleft> E\<^bsub>ES1\<^esub> @ \<delta>1'' @ [v'] \<upharpoonleft> E\<^bsub>ES1\<^esub> @ \<alpha>1'' \<in> Tr\<^bsub>ES1\<^esub>"
        and \<alpha>1''Vv1_is_\<alpha>1'Vv1: "\<alpha>1'' \<upharpoonleft> V\<^bsub>\<V>1\<^esub> = \<alpha>1' \<upharpoonleft> V\<^bsub>\<V>1\<^esub>"
        and \<alpha>1''Cv1_empty: "\<alpha>1'' \<upharpoonleft> C\<^bsub>\<V>1\<^esub> = []"
        and \<delta>1''E2_is_\<delta>2''E1: "\<delta>1'' \<upharpoonleft> E\<^bsub>ES2\<^esub> = \<delta>2'' \<upharpoonleft> E\<^bsub>ES1\<^esub>"
        by blast

      from \<beta>E1_cE1_\<delta>1''_v'E1_\<alpha>1''_in_Tr1 \<beta>E2_cE2_\<delta>2''_v'E2_\<alpha>2''_in_Tr2 
        validES1 validES2
      have \<delta>1''_in_E1star: "set \<delta>1'' \<subseteq> E\<^bsub>ES1\<^esub>" and \<delta>2''_in_E2star: "set \<delta>2'' \<subseteq> E\<^bsub>ES2\<^esub>"
        by (simp_all add: ES_valid_def traces_contain_events_def, auto)
      with \<delta>1''E2_is_\<delta>2''E1 merge_property[of \<delta>1'' "E\<^bsub>ES1\<^esub>" \<delta>2'' "E\<^bsub>ES2\<^esub>"] obtain \<delta>'
        where \<delta>'E1_is_\<delta>1'': "\<delta>' \<upharpoonleft> E\<^bsub>ES1\<^esub> = \<delta>1''"
        and \<delta>'E2_is_\<delta>2'': "\<delta>' \<upharpoonleft> E\<^bsub>ES2\<^esub> = \<delta>2''"
        and \<delta>'_contains_only_\<delta>1''_\<delta>2''_events: "set \<delta>' \<subseteq> set \<delta>1'' \<union> set \<delta>2''"
        unfolding Let_def
        by auto

      let ?TAU = "\<beta> @ [c] @ \<delta>' @ [v']"
      let ?LAMBDA = "\<alpha> \<upharpoonleft> V\<^bsub>\<V>\<^esub>"
      let ?T1 = \<alpha>1''
      let ?T2 = \<alpha>2''

     (* apply the generalized zipping lemma *)
     have "?TAU \<in> Tr\<^bsub>(ES1 \<parallel> ES2)\<^esub>"
        proof -
          from \<beta>E1_cE1_\<delta>1''_v'E1_\<alpha>1''_in_Tr1 \<delta>'E1_is_\<delta>1'' validES1 
          have "\<beta> \<upharpoonleft> E\<^bsub>ES1\<^esub> @ [c] \<upharpoonleft> E\<^bsub>ES1\<^esub> @ \<delta>' \<upharpoonleft> E\<^bsub>ES1\<^esub> @ [v'] \<upharpoonleft> E\<^bsub>ES1\<^esub> \<in> Tr\<^bsub>ES1\<^esub>"
            by (simp add: ES_valid_def traces_prefixclosed_def
              prefixclosed_def prefix_def)
          hence "(\<beta> @ [c] @ \<delta>' @ [v']) \<upharpoonleft> E\<^bsub>ES1\<^esub> \<in> Tr\<^bsub>ES1\<^esub>"
            by (simp add: projection_def, auto)
          moreover          
          from \<beta>E2_cE2_\<delta>2''_v'E2_\<alpha>2''_in_Tr2 \<delta>'E2_is_\<delta>2'' validES2 
          have "\<beta> \<upharpoonleft> E\<^bsub>ES2\<^esub> @ [c] \<upharpoonleft> E\<^bsub>ES2\<^esub> @ \<delta>' \<upharpoonleft> E\<^bsub>ES2\<^esub> @ [v'] \<upharpoonleft> E\<^bsub>ES2\<^esub> \<in> Tr\<^bsub>ES2\<^esub>"
            by (simp add: ES_valid_def traces_prefixclosed_def
              prefixclosed_def prefix_def)
          hence "(\<beta> @ [c] @ \<delta>' @ [v']) \<upharpoonleft> E\<^bsub>ES2\<^esub> \<in> Tr\<^bsub>ES2\<^esub>"
            by (simp add: projection_def, auto)
          moreover
          from \<beta>v'\<alpha>_in_Tr c_in_Cv_inter_Upsilon VIsViewOnE
            \<delta>'_contains_only_\<delta>1''_\<delta>2''_events \<delta>1''_in_E1star \<delta>2''_in_E2star
          have "set (\<beta> @ [c] @ \<delta>' @ [v']) \<subseteq> E\<^bsub>ES1\<^esub> \<union> E\<^bsub>ES2\<^esub>"
            unfolding composeES_def isViewOn_def V_valid_def 
              VC_disjoint_def VN_disjoint_def NC_disjoint_def
            by auto
          ultimately show ?thesis
            unfolding composeES_def
            by auto
        qed 
      hence "set ?TAU \<subseteq> E\<^bsub>(ES1 \<parallel> ES2)\<^esub>"
        unfolding composeES_def
        by auto
      moreover
      have "set ?LAMBDA \<subseteq> V\<^bsub>\<V>\<^esub>"
        by (simp add: projection_def, auto)
      moreover
      note \<alpha>1''_in_E1star \<alpha>2''_in_E2star
      moreover
      from \<beta>E1_cE1_\<delta>1''_v'E1_\<alpha>1''_in_Tr1 \<delta>'E1_is_\<delta>1'' 
      have "?TAU \<upharpoonleft> E\<^bsub>ES1\<^esub> @ ?T1 \<in> Tr\<^bsub>ES1\<^esub>"
        by (simp only: projection_concatenation_commute, auto)
      moreover
      from \<beta>E2_cE2_\<delta>2''_v'E2_\<alpha>2''_in_Tr2 \<delta>'E2_is_\<delta>2'' 
      have "?TAU \<upharpoonleft> E\<^bsub>ES2\<^esub> @ ?T2 \<in> Tr\<^bsub>ES2\<^esub>"
        by (simp only: projection_concatenation_commute, auto)
      moreover
      have "?LAMBDA \<upharpoonleft> E\<^bsub>ES1\<^esub> = ?T1 \<upharpoonleft> V\<^bsub>\<V>\<^esub>"
        proof -
          from propSepViews have "?LAMBDA \<upharpoonleft> E\<^bsub>ES1\<^esub> = \<alpha> \<upharpoonleft> V\<^bsub>\<V>1\<^esub>"
            unfolding properSeparationOfViews_def by (simp add: projection_sequence)
          moreover
          from \<alpha>1''_in_E1star propSepViews 
          have "?T1 \<upharpoonleft> V\<^bsub>\<V>\<^esub> = ?T1 \<upharpoonleft> V\<^bsub>\<V>1\<^esub>"
            unfolding properSeparationOfViews_def 
            by (metis Int_commute projection_intersection_neutral)
          moreover
          note \<alpha>1'Vv1_is_\<alpha>Vv1 \<alpha>1''Vv1_is_\<alpha>1'Vv1
          ultimately show ?thesis
            by simp
        qed
      moreover
      have "?LAMBDA \<upharpoonleft> E\<^bsub>ES2\<^esub> = ?T2 \<upharpoonleft> V\<^bsub>\<V>\<^esub>"
        proof -
          from propSepViews 
          have "?LAMBDA \<upharpoonleft> E\<^bsub>ES2\<^esub> = \<alpha> \<upharpoonleft> V\<^bsub>\<V>2\<^esub>"
            unfolding properSeparationOfViews_def  by (simp add: projection_sequence)
          moreover
          from \<alpha>2''_in_E2star propSepViews 
          have "?T2 \<upharpoonleft> V\<^bsub>\<V>\<^esub> = ?T2 \<upharpoonleft> V\<^bsub>\<V>2\<^esub>"
            unfolding properSeparationOfViews_def
            by (metis Int_commute projection_intersection_neutral)
          moreover
          note \<alpha>2'Vv2_is_\<alpha>Vv2 \<alpha>2''Vv2_is_\<alpha>2'Vv2
          ultimately show ?thesis
            by simp
        qed
      moreover
      note \<alpha>1''Cv1_empty \<alpha>2''Cv2_empty generalized_zipping_lemma
      ultimately obtain t (* show that the conclusion of FCI holds *)
        where "?TAU @ t \<in> Tr\<^bsub>(ES1 \<parallel> ES2)\<^esub>"
        and  "t \<upharpoonleft> V\<^bsub>\<V>\<^esub> = ?LAMBDA"
        and "t \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []"
        by blast
      moreover
      have "set \<delta>' \<subseteq> N\<^bsub>\<V>\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>\<^esub>"
        proof -
          from \<delta>'_contains_only_\<delta>1''_\<delta>2''_events 
            \<delta>1''_in_N1_inter_Delta1star \<delta>2''_in_N2_inter_Delta2star
          have "set \<delta>' \<subseteq> N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub> \<union> N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub>"
            by auto
          with Delta1_N1_Delta2_N2_subset_Delta Nv1_union_Nv2_subsetof_Nv 
          show ?thesis
            by auto
        qed
        ultimately
        have "\<exists>\<alpha>' \<gamma>'. (set \<gamma>' \<subseteq> N\<^bsub>\<V>\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>\<^esub> \<and> \<beta> @ [c] @ \<gamma>' @ [v'] @ \<alpha>' \<in> Tr\<^bsub>(ES1 \<parallel> ES2)\<^esub> 
                    \<and> \<alpha>' \<upharpoonleft> V\<^bsub>\<V>\<^esub> = \<alpha> \<upharpoonleft> V\<^bsub>\<V>\<^esub> \<and> \<alpha>' \<upharpoonleft> C\<^bsub>\<V>\<^esub> = [])"
        by (simp only: append_assoc, blast)
    }
    moreover {
      assume Nv2_inter_Delta2_inter_E1_empty: "N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub> \<inter> E\<^bsub>ES1\<^esub> = {}" 
        and  Nv1_inter_Delta1_inter_E2_subsetof_Upsilon2: "N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub> \<inter> E\<^bsub>ES2\<^esub> \<subseteq> \<Upsilon>\<^bsub>\<Gamma>2\<^esub>"

      let ?ALPHA1''_DELTA1'' = "\<exists> \<alpha>1'' \<delta>1''. (
        set \<alpha>1'' \<subseteq> E\<^bsub>ES1\<^esub> \<and> set \<delta>1'' \<subseteq> N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub> 
        \<and> \<beta> \<upharpoonleft> E\<^bsub>ES1\<^esub> @ [c] \<upharpoonleft> E\<^bsub>ES1\<^esub> @ \<delta>1'' @ [v'] \<upharpoonleft> E\<^bsub>ES1\<^esub> @ \<alpha>1'' \<in> Tr\<^bsub>ES1\<^esub>        
        \<and> \<alpha>1'' \<upharpoonleft> V\<^bsub>\<V>1\<^esub> = \<alpha>1' \<upharpoonleft> V\<^bsub>\<V>1\<^esub> \<and> \<alpha>1'' \<upharpoonleft> C\<^bsub>\<V>1\<^esub> = [])"

      from c_in_Cv_inter_Upsilon v'_in_Vv_inter_Nabla validV1
      have "c \<notin> E\<^bsub>ES1\<^esub> \<or> (c \<in> E\<^bsub>ES1\<^esub> \<and> v' \<notin> E\<^bsub>ES1\<^esub>) \<or> (c \<in> E\<^bsub>ES1\<^esub> \<and> v' \<in> E\<^bsub>ES1\<^esub>)"
        by (simp add: isViewOn_def V_valid_def 
          VC_disjoint_def VN_disjoint_def NC_disjoint_def)
      moreover {
        assume c_notin_E1: "c \<notin> E\<^bsub>ES1\<^esub>"

        from validES1 \<beta>v'E1\<alpha>1'_in_Tr1 have "set \<alpha>1' \<subseteq> E\<^bsub>ES1\<^esub>"
          by (simp add: ES_valid_def traces_contain_events_def, auto)
        moreover 
        have "set [] \<subseteq> N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub>"
          by auto
        moreover 
        from \<beta>v'E1\<alpha>1'_in_Tr1 c_notin_E1 
        have "\<beta> \<upharpoonleft> E\<^bsub>ES1\<^esub> @ [c] \<upharpoonleft> E\<^bsub>ES1\<^esub> @ [] @ [v'] \<upharpoonleft> E\<^bsub>ES1\<^esub> @ \<alpha>1' \<in> Tr\<^bsub>ES1\<^esub>"
          by (simp add: projection_def)
        moreover
        have "\<alpha>1' \<upharpoonleft> V\<^bsub>\<V>1\<^esub> = \<alpha>1' \<upharpoonleft> V\<^bsub>\<V>1\<^esub>" ..
        moreover 
        note \<alpha>1'Cv1_empty
        ultimately have ?ALPHA1''_DELTA1''
          by blast
      }
      moreover {
        assume c_in_E1: "c \<in> E\<^bsub>ES1\<^esub>"
          and  v'_notin_E1: "v' \<notin> E\<^bsub>ES1\<^esub>"

        from c_in_E1 c_in_Cv_inter_Upsilon propSepViews
          Upsilon_inter_E1_subset_Upsilon1
        have c_in_Cv1_inter_Upsilon1: "c \<in> C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub>"
          unfolding properSeparationOfViews_def by auto
        hence "c \<in> C\<^bsub>\<V>1\<^esub>"
          by auto
        moreover
        from \<beta>v'E1\<alpha>1'_in_Tr1 v'_notin_E1 have "\<beta> \<upharpoonleft> E\<^bsub>ES1\<^esub> @ \<alpha>1' \<in> Tr\<^bsub>ES1\<^esub>"
          by (simp add: projection_def)
        moreover
        note \<alpha>1'Cv1_empty
        moreover
        have "(Adm \<V>1 \<rho>1 Tr\<^bsub>ES1\<^esub> (\<beta> \<upharpoonleft> E\<^bsub>ES1\<^esub>) c)" 
          proof -
            from validES1 \<beta>v'E1\<alpha>1'_in_Tr1 v'_notin_E1 have "\<beta> \<upharpoonleft> E\<^bsub>ES1\<^esub> \<in> Tr\<^bsub>ES1\<^esub>"
              by (simp add: ES_valid_def traces_prefixclosed_def
                prefixclosed_def prefix_def projection_concatenation_commute)
            with total_ES1_C1_inter_Upsilon1 c_in_Cv1_inter_Upsilon1
            have "\<beta> \<upharpoonleft> E\<^bsub>ES1\<^esub> @ [c] \<in> Tr\<^bsub>ES1\<^esub>"
              by (simp add: total_def)
            thus ?thesis
              unfolding Adm_def
              by blast
          qed
        moreover 
        note BSIA1
        ultimately obtain  \<alpha>1''
          where one: "\<beta> \<upharpoonleft> E\<^bsub>ES1\<^esub> @ [c] @ \<alpha>1'' \<in> Tr\<^bsub>ES1\<^esub>"
          and two:   "\<alpha>1'' \<upharpoonleft> V\<^bsub>\<V>1\<^esub> = \<alpha>1' \<upharpoonleft> V\<^bsub>\<V>1\<^esub>"
          and three: "\<alpha>1'' \<upharpoonleft> C\<^bsub>\<V>1\<^esub> = []"
          unfolding BSIA_def
          by blast

        from one validES1 have "set \<alpha>1'' \<subseteq> E\<^bsub>ES1\<^esub>"
          by (simp add: ES_valid_def traces_contain_events_def, auto)
        moreover
        have "set [] \<subseteq> N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub>"
          by auto
        moreover
        from one c_in_E1 v'_notin_E1 
        have "\<beta> \<upharpoonleft> E\<^bsub>ES1\<^esub> @ [c] \<upharpoonleft> E\<^bsub>ES1\<^esub> @ [] @ [v'] \<upharpoonleft> E\<^bsub>ES1\<^esub> @ \<alpha>1'' \<in> Tr\<^bsub>ES1\<^esub>"
          by (simp add: projection_def)
        moreover 
        note two three
        ultimately have ?ALPHA1''_DELTA1''
          by blast
      }
      moreover {
        assume c_in_E1: "c \<in> E\<^bsub>ES1\<^esub>"
          and  v'_in_E1: "v' \<in> E\<^bsub>ES1\<^esub>"

        from c_in_E1 c_in_Cv_inter_Upsilon propSepViews
          Upsilon_inter_E1_subset_Upsilon1
        have c_in_Cv1_inter_Upsilon1: "c \<in> C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub>"
          unfolding properSeparationOfViews_def by auto
        moreover
        from v'_in_E1 propSepViews v'_in_Vv_inter_Nabla Nabla_inter_E1_subset_Nabla1
        have "v' \<in> V\<^bsub>\<V>1\<^esub> \<inter> Nabla \<Gamma>1"
         unfolding properSeparationOfViews_def by auto
        moreover
        from v'_in_E1  \<beta>v'E1\<alpha>1'_in_Tr1 have "\<beta> \<upharpoonleft> E\<^bsub>ES1\<^esub> @ [v'] @ \<alpha>1' \<in> Tr\<^bsub>ES1\<^esub>"
          by (simp add: projection_def)
        moreover
        note \<alpha>1'Cv1_empty FCI1
        ultimately obtain \<alpha>1'' \<delta>1''
          where one: "set \<delta>1'' \<subseteq> N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub>"
          and two: "\<beta> \<upharpoonleft> E\<^bsub>ES1\<^esub> @ [c] @ \<delta>1'' @ [v'] @ \<alpha>1'' \<in> Tr\<^bsub>ES1\<^esub>"
          and three: "\<alpha>1'' \<upharpoonleft> V\<^bsub>\<V>1\<^esub> = \<alpha>1' \<upharpoonleft> V\<^bsub>\<V>1\<^esub>"
          and four: "\<alpha>1'' \<upharpoonleft> C\<^bsub>\<V>1\<^esub> = []"
          unfolding FCI_def
          by blast

        from two validES1 have "set \<alpha>1'' \<subseteq> E\<^bsub>ES1\<^esub>"
          by (simp add: ES_valid_def traces_contain_events_def, auto)
        moreover
        note one
        moreover
        from two c_in_E1 v'_in_E1 
        have "\<beta> \<upharpoonleft> E\<^bsub>ES1\<^esub> @ [c] \<upharpoonleft> E\<^bsub>ES1\<^esub> @ \<delta>1'' @ [v'] \<upharpoonleft> E\<^bsub>ES1\<^esub> @ \<alpha>1'' \<in> Tr\<^bsub>ES1\<^esub>"
          by (simp add: projection_def)
        moreover
        note three four
        ultimately have ?ALPHA1''_DELTA1''
          by blast
      }
      ultimately obtain \<alpha>1'' \<delta>1''
        where \<alpha>1''_in_E1star: "set \<alpha>1'' \<subseteq> E\<^bsub>ES1\<^esub>"
        and \<delta>1''_in_N1_inter_Delta1star:"set \<delta>1'' \<subseteq> N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub>"
        and \<beta>E1_cE1_\<delta>1''_v'E1_\<alpha>1''_in_Tr1: 
        "\<beta> \<upharpoonleft> E\<^bsub>ES1\<^esub> @ [c] \<upharpoonleft> E\<^bsub>ES1\<^esub> @ \<delta>1'' @ [v'] \<upharpoonleft> E\<^bsub>ES1\<^esub> @ \<alpha>1'' \<in> Tr\<^bsub>ES1\<^esub>"
        and \<alpha>1''Vv1_is_\<alpha>1'Vv1: "\<alpha>1'' \<upharpoonleft> V\<^bsub>\<V>1\<^esub> = \<alpha>1' \<upharpoonleft> V\<^bsub>\<V>1\<^esub>"
        and \<alpha>1''Cv1_empty: "\<alpha>1'' \<upharpoonleft> C\<^bsub>\<V>1\<^esub> = []"
        by blast

      from c_in_Cv_inter_Upsilon Upsilon_inter_E2_subset_Upsilon2 propSepViews 
      have cE2_in_Cv2_inter_Upsilon2: "set ([c] \<upharpoonleft> E\<^bsub>ES2\<^esub>) \<subseteq> C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub>"
        unfolding properSeparationOfViews_def by (simp add: projection_def, auto)
     
      from \<delta>1''_in_N1_inter_Delta1star Nv1_inter_Delta1_inter_E2_subsetof_Upsilon2 
        propSepViews disjoint_Nv1_Vv2 
      have \<delta>1''E2_in_Cv2_inter_Upsilon2star: "set (\<delta>1'' \<upharpoonleft> E\<^bsub>ES2\<^esub>) \<subseteq> C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub>"
        proof -
          from \<delta>1''_in_N1_inter_Delta1star have eq: "\<delta>1'' \<upharpoonleft> E\<^bsub>ES2\<^esub> = \<delta>1'' \<upharpoonleft> (N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub> \<inter> E\<^bsub>ES2\<^esub>)"
            by (metis Int_commute Int_left_commute Int_lower2 Int_lower1 
              projection_intersection_neutral subset_trans)
          
          from validV2 Nv1_inter_Delta1_inter_E2_subsetof_Upsilon2 
           propSepViews disjoint_Nv1_Vv2  
          have "N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub> \<inter> E\<^bsub>ES2\<^esub> \<subseteq> C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub>"
            unfolding properSeparationOfViews_def
            by (simp add: isViewOn_def V_valid_def VC_disjoint_def 
              VN_disjoint_def NC_disjoint_def, auto)
          thus ?thesis
            by (subst eq, simp only: projection_def, auto)
        qed
      
      have c\<delta>1''E2_in_Cv2_inter_Upsilon2star: "set ((c # \<delta>1'') \<upharpoonleft> E\<^bsub>ES2\<^esub>) \<subseteq> C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub>"
        proof -
          from cE2_in_Cv2_inter_Upsilon2 \<delta>1''E2_in_Cv2_inter_Upsilon2star
          have "set (([c] @ \<delta>1'') \<upharpoonleft> E\<^bsub>ES2\<^esub>) \<subseteq> C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub>"
            by (simp only: projection_concatenation_commute, auto)
          thus ?thesis
            by auto
        qed


      have "\<exists> \<alpha>2'' \<delta>2''. set \<alpha>2'' \<subseteq> E\<^bsub>ES2\<^esub>        
        \<and> set \<delta>2'' \<subseteq> N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub> \<union> C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub> \<inter> N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub>        
        \<and> \<beta> \<upharpoonleft> E\<^bsub>ES2\<^esub> @ [c] \<upharpoonleft> E\<^bsub>ES2\<^esub> @ \<delta>2'' @ [v'] \<upharpoonleft> E\<^bsub>ES2\<^esub> @ \<alpha>2'' \<in> Tr\<^bsub>ES2\<^esub>        
        \<and> \<alpha>2'' \<upharpoonleft> V\<^bsub>\<V>2\<^esub> = \<alpha>2' \<upharpoonleft> V\<^bsub>\<V>2\<^esub> \<and> \<alpha>2'' \<upharpoonleft> C\<^bsub>\<V>2\<^esub> = []
        \<and> \<delta>2'' \<upharpoonleft> E\<^bsub>ES1\<^esub> = \<delta>1'' \<upharpoonleft> E\<^bsub>ES2\<^esub>"
        proof cases
          assume v'_in_E2: "v' \<in> E\<^bsub>ES2\<^esub>"
          with Nabla_inter_E2_subset_Nabla2 
            propSepViews v'_in_Vv_inter_Nabla
          have v'_in_Vv2_inter_Nabla2: "v' \<in> V\<^bsub>\<V>2\<^esub> \<inter> Nabla \<Gamma>2"
            unfolding properSeparationOfViews_def by auto

          have "\<lbrakk> (\<beta> @ [v']) \<upharpoonleft> E\<^bsub>ES2\<^esub> @ \<alpha>2' \<in> Tr\<^bsub>ES2\<^esub> ; 
            \<alpha>2' \<upharpoonleft> C\<^bsub>\<V>2\<^esub> = []; set ((c # \<delta>1'') \<upharpoonleft> E\<^bsub>ES2\<^esub>) \<subseteq> C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub> ; 
            c \<in> C\<^bsub>\<V>\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>\<^esub> ; set \<delta>1'' \<subseteq> N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub> \<rbrakk> 
            \<Longrightarrow> \<exists> \<alpha>2'' \<delta>2''. (set \<alpha>2'' \<subseteq> E\<^bsub>ES2\<^esub> \<and> set \<delta>2'' \<subseteq> N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub> \<union> C\<^bsub>\<V>2\<^esub> 
              \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub> \<inter> N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub>            
            \<and> \<beta> \<upharpoonleft> E\<^bsub>ES2\<^esub> @ [c] \<upharpoonleft> E\<^bsub>ES2\<^esub> @ \<delta>2'' @ [v'] \<upharpoonleft> E\<^bsub>ES2\<^esub> @ \<alpha>2'' \<in> Tr\<^bsub>ES2\<^esub>            
            \<and> \<alpha>2'' \<upharpoonleft> V\<^bsub>\<V>2\<^esub> = \<alpha>2' \<upharpoonleft> V\<^bsub>\<V>2\<^esub> \<and> \<alpha>2'' \<upharpoonleft> C\<^bsub>\<V>2\<^esub> = []
            \<and> \<delta>2'' \<upharpoonleft> (C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub>) = \<delta>1'' \<upharpoonleft> E\<^bsub>ES2\<^esub>)"
            proof (induct "length ((c # \<delta>1'') \<upharpoonleft> E\<^bsub>ES2\<^esub>)" arbitrary: \<beta> \<alpha>2' c \<delta>1'')
              case 0

              from 0(2) validES2 have "set \<alpha>2' \<subseteq> E\<^bsub>ES2\<^esub>"
                by (simp add: ES_valid_def traces_contain_events_def, auto)
              moreover
              have "set [] \<subseteq> N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub> \<union> C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub> \<inter> N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub>"
                by auto
              moreover
              have "\<beta> \<upharpoonleft> E\<^bsub>ES2\<^esub> @ [c] \<upharpoonleft> E\<^bsub>ES2\<^esub> @ [] @ [v'] \<upharpoonleft> E\<^bsub>ES2\<^esub> @ \<alpha>2' \<in> Tr\<^bsub>ES2\<^esub>"
                proof -
                  note 0(2)
                  moreover
                  from 0(1) have "c \<notin> E\<^bsub>ES2\<^esub>"
                    by (simp add: projection_def, auto)
                  ultimately show ?thesis
                    by (simp add: projection_concatenation_commute projection_def)
                qed
              moreover
              have "\<alpha>2' \<upharpoonleft> V\<^bsub>\<V>2\<^esub> = \<alpha>2' \<upharpoonleft> V\<^bsub>\<V>2\<^esub>" ..
              moreover
              note 0(3)
              moreover 
              from 0(1) have "[] \<upharpoonleft> (C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub>) = \<delta>1'' \<upharpoonleft> E\<^bsub>ES2\<^esub>"
                by (simp add: projection_def, split if_split_asm, auto)
              ultimately show ?case
                by blast
            next
              case (Suc n)

              from projection_split_last[OF Suc(2)] obtain \<mu> c' \<nu>
                where c'_in_E2: "c' \<in> E\<^bsub>ES2\<^esub>"
                and c\<delta>1''_is_\<mu>c'\<nu>: "c # \<delta>1'' = \<mu> @ [c'] @ \<nu>"
                and \<nu>E2_empty: "\<nu> \<upharpoonleft> E\<^bsub>ES2\<^esub> = []"
                and n_is_length_\<mu>\<nu>E2: "n = length ((\<mu> @ \<nu>) \<upharpoonleft> E\<^bsub>ES2\<^esub>)"
                by blast

              from Suc(5) c'_in_E2 c\<delta>1''_is_\<mu>c'\<nu> 
              have "set (\<mu> \<upharpoonleft> E\<^bsub>ES2\<^esub> @ [c']) \<subseteq> C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub>"
                by (simp only: c\<delta>1''_is_\<mu>c'\<nu> projection_concatenation_commute 
                  projection_def, auto)
              hence c'_in_Cv2_inter_Upsilon2: "c' \<in> C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub>"
                by auto
              hence c'_in_Cv2: "c' \<in> C\<^bsub>\<V>2\<^esub>" and c'_in_Upsilon2: "c' \<in> \<Upsilon>\<^bsub>\<Gamma>2\<^esub>"
                by auto
              with validV2 have c'_in_E2: "c' \<in> E\<^bsub>ES2\<^esub>"
                by (simp add: isViewOn_def V_valid_def VC_disjoint_def 
                  VN_disjoint_def NC_disjoint_def, auto)

              show ?case
                proof (cases \<mu>)
                  case Nil (* we apply FCI in this case *)
                  with c\<delta>1''_is_\<mu>c'\<nu> have c_is_c': "c = c'" and \<delta>1''_is_\<nu>: "\<delta>1'' = \<nu>"
                    by auto
                  with c'_in_Cv2_inter_Upsilon2 have "c \<in> C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub>"
                    by simp
                  moreover
                  note v'_in_Vv2_inter_Nabla2
                  moreover
                  from v'_in_E2 Suc(3) have "(\<beta> \<upharpoonleft> E\<^bsub>ES2\<^esub>) @ [v'] @ \<alpha>2' \<in> Tr\<^bsub>ES2\<^esub>"
                    by (simp add: projection_concatenation_commute projection_def)
                  moreover
                  note Suc(4) FCI2
                  ultimately obtain \<alpha>2'' \<gamma>
                    where one: "set \<gamma> \<subseteq> N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub>"
                    and two: "\<beta> \<upharpoonleft> E\<^bsub>ES2\<^esub> @ [c] @ \<gamma> @ [v'] @ \<alpha>2'' \<in> Tr\<^bsub>ES2\<^esub>"
                    and three: "\<alpha>2'' \<upharpoonleft> V\<^bsub>\<V>2\<^esub> = \<alpha>2' \<upharpoonleft> V\<^bsub>\<V>2\<^esub>"
                    and four: "\<alpha>2'' \<upharpoonleft> C\<^bsub>\<V>2\<^esub> = []"
                    unfolding FCI_def
                    by blast

                  (* we choose \<delta>2'' = \<nu> \<upharpoonleft> E\<^bsub>ES2\<^esub> @ \<gamma> *)
                  let ?DELTA2'' = "\<nu> \<upharpoonleft> E\<^bsub>ES2\<^esub> @ \<gamma>"

                  from two validES2 have "set \<alpha>2'' \<subseteq> E\<^bsub>ES2\<^esub>"
                    by (simp add: ES_valid_def traces_contain_events_def, auto)
                  moreover
                  from one \<nu>E2_empty
                  have "set ?DELTA2'' \<subseteq> N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub> \<union> C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub> \<inter> N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub>"
                    by auto
                  moreover
                  have "\<beta> \<upharpoonleft> E\<^bsub>ES2\<^esub> @ [c] \<upharpoonleft> E\<^bsub>ES2\<^esub> @ ?DELTA2'' @ [v'] \<upharpoonleft> E\<^bsub>ES2\<^esub> @ \<alpha>2'' \<in> Tr\<^bsub>ES2\<^esub>"
                    proof -
                      from c_is_c' c'_in_E2 have "[c] = [c] \<upharpoonleft> E\<^bsub>ES2\<^esub>"
                        by (simp add: projection_def)
                      moreover
                      from v'_in_E2 have "[v'] = [v'] \<upharpoonleft> E\<^bsub>ES2\<^esub>"
                        by (simp add: projection_def)
                      moreover
                      note \<nu>E2_empty two
                      ultimately show ?thesis
                        by auto
                    qed
                  moreover
                  note three four
                  moreover
                  have "?DELTA2'' \<upharpoonleft> (C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub>) = \<delta>1'' \<upharpoonleft> E\<^bsub>ES2\<^esub>"
                    proof -
                      have "\<gamma> \<upharpoonleft> (C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub>) = []"
                        proof -
                          from validV2 have "N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub> \<inter> (C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub>) = {}"
                            by (simp add: isViewOn_def V_valid_def
                              VC_disjoint_def VN_disjoint_def NC_disjoint_def, auto)
                          with projection_intersection_neutral[OF one, of "C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub>"]
                          show ?thesis
                            by (simp add: projection_def)
                        qed
                      with \<delta>1''_is_\<nu> \<nu>E2_empty show ?thesis
                        by (simp add: projection_concatenation_commute)
                    qed
                  ultimately show ?thesis
                    by blast
                next
                  case (Cons x xs) (* we apply the inductive hypothesis in this case *)
                  with c\<delta>1''_is_\<mu>c'\<nu> have \<mu>_is_c_xs: "\<mu> = [c] @ xs" 
                    and \<delta>1''_is_xs_c'_\<nu>: "\<delta>1'' = xs @ [c'] @ \<nu>"
                    by auto
                  with n_is_length_\<mu>\<nu>E2 have "n = length ((c # (xs @ \<nu>)) \<upharpoonleft> E\<^bsub>ES2\<^esub>)"
                    by auto
                  moreover
                  note Suc(3,4)
                  moreover
                  have "set ((c # (xs @ \<nu>)) \<upharpoonleft> E\<^bsub>ES2\<^esub>) \<subseteq> C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub>"
                    proof -
                      have res: "c # (xs @ \<nu>) = [c] @ (xs @ \<nu>)" 
                        by auto

                      from Suc(5) c\<delta>1''_is_\<mu>c'\<nu> \<mu>_is_c_xs \<nu>E2_empty
                      show ?thesis
                        by (subst res, simp only: c\<delta>1''_is_\<mu>c'\<nu> 
                          projection_concatenation_commute set_append, auto)
                    qed
                  moreover
                  note Suc(6) 
                  moreover
                  from Suc(7) \<delta>1''_is_xs_c'_\<nu> have "set (xs @ \<nu>) \<subseteq> N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub>"
                    by auto
                  moreover note Suc(1)[of c "xs @ \<nu>" \<beta> \<alpha>2']
                  ultimately obtain \<delta> \<gamma>
                    where one: "set \<delta> \<subseteq> E\<^bsub>ES2\<^esub>"
                    and two: "set \<gamma> \<subseteq> N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub> \<union> C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub> \<inter> N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub>"
                    and three: "\<beta> \<upharpoonleft> E\<^bsub>ES2\<^esub> @ [c] \<upharpoonleft> E\<^bsub>ES2\<^esub> @ \<gamma> @ [v'] \<upharpoonleft> E\<^bsub>ES2\<^esub> @ \<delta> \<in> Tr\<^bsub>ES2\<^esub>"
                    and four: "\<delta> \<upharpoonleft> V\<^bsub>\<V>2\<^esub> = \<alpha>2' \<upharpoonleft> V\<^bsub>\<V>2\<^esub>"
                    and five: "\<delta> \<upharpoonleft> C\<^bsub>\<V>2\<^esub> = []"
                    and six: "\<gamma> \<upharpoonleft> (C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub>) = (xs @ \<nu>) \<upharpoonleft> E\<^bsub>ES2\<^esub>"
                    by blast

                  (* apply FCI to insert c' after \<gamma> *)
                  let ?BETA = "\<beta> \<upharpoonleft> E\<^bsub>ES2\<^esub> @ [c] \<upharpoonleft> E\<^bsub>ES2\<^esub> @ \<gamma>"

                  note c'_in_Cv2_inter_Upsilon2 v'_in_Vv2_inter_Nabla2
                  moreover
                  from three v'_in_E2 have "?BETA @ [v'] @ \<delta> \<in> Tr\<^bsub>ES2\<^esub>"
                    by (simp add: projection_def)
                  moreover
                  note five FCI2
                  ultimately obtain \<alpha>2'' \<delta>'
                    where fci_one: "set \<delta>' \<subseteq> N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub>"
                    and fci_two: "?BETA @ [c'] @ \<delta>' @ [v'] @ \<alpha>2'' \<in> Tr\<^bsub>ES2\<^esub>"
                    and fci_three: "\<alpha>2'' \<upharpoonleft> V\<^bsub>\<V>2\<^esub> = \<delta> \<upharpoonleft> V\<^bsub>\<V>2\<^esub>"
                    and fci_four:  "\<alpha>2'' \<upharpoonleft> C\<^bsub>\<V>2\<^esub> = []"
                    unfolding FCI_def
                    by blast
  
                  let ?DELTA2'' = "\<gamma> @ [c'] @ \<delta>'"

                  from fci_two validES2 have "set \<alpha>2'' \<subseteq> E\<^bsub>ES2\<^esub>"
                    by (simp add: ES_valid_def traces_contain_events_def, auto)
                  moreover
                  have "set ?DELTA2'' \<subseteq> N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub> \<union> C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub> \<inter> N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub>"
                    proof -
                      from Suc(7) c'_in_Cv2_inter_Upsilon2 \<delta>1''_is_xs_c'_\<nu> 
                      have "c' \<in>  C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub> \<inter> N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub>"
                        by auto
                      with two fci_one show ?thesis
                        by auto
                    qed
                  moreover
                  from fci_two v'_in_E2 
                  have "\<beta> \<upharpoonleft> E\<^bsub>ES2\<^esub> @ [c] \<upharpoonleft> E\<^bsub>ES2\<^esub> @ ?DELTA2'' @ [v'] \<upharpoonleft> E\<^bsub>ES2\<^esub> @ \<alpha>2'' \<in> Tr\<^bsub>ES2\<^esub>"
                    by (simp add: projection_def)
                  moreover
                  from fci_three four have "\<alpha>2'' \<upharpoonleft> V\<^bsub>\<V>2\<^esub> = \<alpha>2' \<upharpoonleft> V\<^bsub>\<V>2\<^esub>"
                    by simp
                  moreover
                  note fci_four
                  moreover             
                  have "?DELTA2'' \<upharpoonleft> (C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub>) = \<delta>1'' \<upharpoonleft> E\<^bsub>ES2\<^esub>"
                    proof -
                      have "\<delta>' \<upharpoonleft> (C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub>) = []"
                        proof -
                          from fci_one have "\<forall> e \<in> set \<delta>'. e \<in> N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub>"
                            by auto
                          with validV2 have "\<forall> e \<in> set \<delta>'. e \<notin> C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub>"
                            by (simp add: isViewOn_def V_valid_def
                              VC_disjoint_def VN_disjoint_def NC_disjoint_def, auto)
                          thus ?thesis
                            by (simp add: projection_def)
                        qed
                      with c'_in_E2 c'_in_Cv2_inter_Upsilon2 \<delta>1''_is_xs_c'_\<nu> \<nu>E2_empty six 
                      show ?thesis
                        by (simp only: projection_concatenation_commute projection_def, auto)
                    qed
                  ultimately show ?thesis 
                    by blast     
                qed
          qed
          from this[OF \<beta>v'E2\<alpha>2'_in_Tr2 \<alpha>2'Cv2_empty c\<delta>1''E2_in_Cv2_inter_Upsilon2star 
            c_in_Cv_inter_Upsilon \<delta>1''_in_N1_inter_Delta1star]
          obtain \<alpha>2'' \<delta>2''
            where one: "set \<alpha>2'' \<subseteq> E\<^bsub>ES2\<^esub>"
            and two: "set \<delta>2'' \<subseteq> N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub> \<union> C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub> \<inter> N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub>"
            and three: "\<beta> \<upharpoonleft> E\<^bsub>ES2\<^esub> @ [c] \<upharpoonleft> E\<^bsub>ES2\<^esub> @ \<delta>2'' @ [v'] \<upharpoonleft> E\<^bsub>ES2\<^esub> @ \<alpha>2'' \<in> Tr\<^bsub>ES2\<^esub>            
            \<and> \<alpha>2'' \<upharpoonleft> V\<^bsub>\<V>2\<^esub> = \<alpha>2' \<upharpoonleft> V\<^bsub>\<V>2\<^esub> \<and> \<alpha>2'' \<upharpoonleft> C\<^bsub>\<V>2\<^esub> = []"
            and four: "\<delta>2'' \<upharpoonleft> (C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub>) = \<delta>1'' \<upharpoonleft> E\<^bsub>ES2\<^esub>"
            by blast

          note one two three
          moreover
          have "\<delta>2'' \<upharpoonleft> E\<^bsub>ES1\<^esub> = \<delta>1'' \<upharpoonleft> E\<^bsub>ES2\<^esub>" 
            proof -
              from projection_intersection_neutral[OF two, of "E\<^bsub>ES1\<^esub>"] 
                Nv2_inter_Delta2_inter_E1_empty validV1 
              have "\<delta>2'' \<upharpoonleft> E\<^bsub>ES1\<^esub> = \<delta>2'' \<upharpoonleft> (C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub> \<inter> N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub> \<inter> E\<^bsub>ES1\<^esub>)"
                by (simp only: Int_Un_distrib2, auto)
              moreover
              from validV1 
              have "C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub> \<inter> N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub> \<inter> E\<^bsub>ES1\<^esub> = C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub> \<inter> N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub>"
                by (simp add: isViewOn_def V_valid_def VC_disjoint_def 
                  VN_disjoint_def NC_disjoint_def, auto)
              ultimately have "\<delta>2'' \<upharpoonleft> E\<^bsub>ES1\<^esub> = \<delta>2'' \<upharpoonleft> (C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub> \<inter> N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub>)"
                by simp
              hence "\<delta>2'' \<upharpoonleft> E\<^bsub>ES1\<^esub> = \<delta>2'' \<upharpoonleft> (C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub>) \<upharpoonleft> (N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub>)"
                by (simp add: projection_def)
              with four have "\<delta>2'' \<upharpoonleft> E\<^bsub>ES1\<^esub> = \<delta>1'' \<upharpoonleft> E\<^bsub>ES2\<^esub> \<upharpoonleft> (N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub>)"
                by simp
              hence "\<delta>2'' \<upharpoonleft> E\<^bsub>ES1\<^esub> = \<delta>1'' \<upharpoonleft> (N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub>) \<upharpoonleft> E\<^bsub>ES2\<^esub>"
                by (simp only: projection_commute)
              with \<delta>1''_in_N1_inter_Delta1star show ?thesis
                by (simp only: list_subset_iff_projection_neutral)
            qed
          ultimately show ?thesis
              by blast
        next
          assume v'_notin_E2: "v' \<notin> E\<^bsub>ES2\<^esub>"

          have 
            "\<lbrakk> (\<beta> @ [v']) \<upharpoonleft> E\<^bsub>ES2\<^esub> @ \<alpha>2' \<in> Tr\<^bsub>ES2\<^esub> ; \<alpha>2' \<upharpoonleft> C\<^bsub>\<V>2\<^esub> = []; 
                set ((c # \<delta>1'') \<upharpoonleft> E\<^bsub>ES2\<^esub>) \<subseteq> C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub> ; c \<in> C\<^bsub>\<V>\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>\<^esub> ;
                set \<delta>1'' \<subseteq> N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub> \<rbrakk> 
            \<Longrightarrow> \<exists> \<alpha>2'' \<delta>2''.
             (set \<alpha>2'' \<subseteq> E\<^bsub>ES2\<^esub> \<and> set \<delta>2'' \<subseteq> N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub> \<union> C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub> \<inter> N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub>            
             \<and> \<beta> \<upharpoonleft> E\<^bsub>ES2\<^esub> @ [c] \<upharpoonleft> E\<^bsub>ES2\<^esub> @ \<delta>2'' @ [v'] \<upharpoonleft> E\<^bsub>ES2\<^esub> @ \<alpha>2'' \<in> Tr\<^bsub>ES2 \<^esub>            
             \<and> \<alpha>2'' \<upharpoonleft> V\<^bsub>\<V>2\<^esub> = \<alpha>2' \<upharpoonleft> V\<^bsub>\<V>2\<^esub> \<and> \<alpha>2'' \<upharpoonleft> C\<^bsub>\<V>2\<^esub> = []
            \<and> \<delta>2'' \<upharpoonleft> E\<^bsub>ES1\<^esub> = \<delta>1'' \<upharpoonleft> E\<^bsub>ES2\<^esub>)"
            proof (induct "length ((c # \<delta>1'') \<upharpoonleft> E\<^bsub>ES2\<^esub>)" arbitrary: \<beta> \<alpha>2' c \<delta>1'')
               case 0

              from 0(2) validES2 have "set \<alpha>2' \<subseteq> E\<^bsub>ES2\<^esub>"
                by (simp add: ES_valid_def traces_contain_events_def, auto)
              moreover
              have "set [] \<subseteq> N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub> \<union> C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub> \<inter> N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub>"
                by auto
              moreover
              have "\<beta> \<upharpoonleft> E\<^bsub>ES2\<^esub> @ [c] \<upharpoonleft> E\<^bsub>ES2\<^esub> @ [] @ [v'] \<upharpoonleft> E\<^bsub>ES2\<^esub> @ \<alpha>2' \<in> Tr\<^bsub>ES2\<^esub>"
                proof -
                  note 0(2)
                  moreover
                  from 0(1) have "c \<notin> E\<^bsub>ES2\<^esub>"
                    by (simp add: projection_def, auto)
                  ultimately show ?thesis
                    by (simp add: projection_concatenation_commute projection_def)
                qed
              moreover
              have "\<alpha>2' \<upharpoonleft> V\<^bsub>\<V>2\<^esub> = \<alpha>2' \<upharpoonleft> V\<^bsub>\<V>2\<^esub>" ..
              moreover
              note 0(3)
              moreover 
              from 0(1) have "[] \<upharpoonleft> E\<^bsub>ES1\<^esub> = \<delta>1'' \<upharpoonleft> E\<^bsub>ES2\<^esub>"
                by (simp add: projection_def, split if_split_asm, auto)
              ultimately show ?case
                by blast
            next
              case (Suc n)

              from projection_split_last[OF Suc(2)] obtain \<mu> c' \<nu>
                where c'_in_E2: "c' \<in> E\<^bsub>ES2\<^esub>"
                and c\<delta>1''_is_\<mu>c'\<nu>: "c # \<delta>1'' = \<mu> @ [c'] @ \<nu>"
                and \<nu>E2_empty: "\<nu> \<upharpoonleft> E\<^bsub>ES2\<^esub> = []"
                and n_is_length_\<mu>\<nu>E2: "n = length ((\<mu> @ \<nu>) \<upharpoonleft> E\<^bsub>ES2\<^esub>)"
                by blast

              from Suc(5) c'_in_E2 c\<delta>1''_is_\<mu>c'\<nu> have "set (\<mu> \<upharpoonleft> E\<^bsub>ES2\<^esub> @ [c']) \<subseteq> C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub>"
                by (simp only: c\<delta>1''_is_\<mu>c'\<nu> projection_concatenation_commute projection_def, auto)
              hence c'_in_Cv2_inter_Upsilon2: "c' \<in> C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub>"
                by auto
              hence c'_in_Cv2: "c' \<in> C\<^bsub>\<V>2\<^esub>" and c'_in_Upsilon2: "c' \<in> \<Upsilon>\<^bsub>\<Gamma>2\<^esub>"
                by auto
              with validV2 have c'_in_E2: "c' \<in> E\<^bsub>ES2\<^esub>"
                by (simp add: isViewOn_def V_valid_def VC_disjoint_def
                  VN_disjoint_def NC_disjoint_def, auto)

              show ?case
                proof (cases \<mu>)
                  case Nil (* we just apply BSIA in this case *)
                  with c\<delta>1''_is_\<mu>c'\<nu> have c_is_c': "c = c'" and \<delta>1''_is_\<nu>: "\<delta>1'' = \<nu>"
                    by auto
                  with c'_in_Cv2_inter_Upsilon2 have "c \<in> C\<^bsub>\<V>2\<^esub>"
                    by simp
                  moreover
                  from v'_notin_E2 Suc(3) have "(\<beta> \<upharpoonleft> E\<^bsub>ES2\<^esub>) @ \<alpha>2' \<in> Tr\<^bsub>ES2\<^esub>"
                    by (simp add: projection_concatenation_commute projection_def)
                  moreover
                  note Suc(4)
                  moreover
                  have "Adm \<V>2 \<rho>2 Tr\<^bsub>ES2\<^esub> (\<beta> \<upharpoonleft> E\<^bsub>ES2\<^esub>) c"
                    proof -
                      have "\<beta> \<upharpoonleft> E\<^bsub>ES2\<^esub> @ [c] \<in> Tr\<^bsub>ES2\<^esub>"
                        proof -
                          from c_is_c' c'_in_Cv2_inter_Upsilon2 have "c \<in> C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub>"
                            by simp
                          moreover
                          from validES2 Suc(3) have "(\<beta> \<upharpoonleft> E\<^bsub>ES2\<^esub>) \<in> Tr\<^bsub>ES2\<^esub>"
                            by (simp only: ES_valid_def traces_prefixclosed_def
                              projection_concatenation_commute 
                              prefixclosed_def prefix_def, auto)
                          moreover
                          note total_ES2_C2_inter_Upsilon2
                          ultimately show ?thesis
                            unfolding total_def
                            by blast
                        qed
                      thus ?thesis
                        unfolding Adm_def
                        by blast                        
                    qed
                  moreover
                  note BSIA2
                  ultimately obtain \<alpha>2''
                    where one: "(\<beta> \<upharpoonleft> E\<^bsub>ES2\<^esub>) @ [c] @ \<alpha>2'' \<in> Tr\<^bsub>ES2\<^esub>"
                    and two: "\<alpha>2'' \<upharpoonleft> V\<^bsub>\<V>2\<^esub> = \<alpha>2' \<upharpoonleft> V\<^bsub>\<V>2\<^esub>"
                    and three: "\<alpha>2'' \<upharpoonleft> C\<^bsub>\<V>2\<^esub> = []"
                    unfolding BSIA_def
                    by blast

                  let ?DELTA2'' = "\<nu> \<upharpoonleft> E\<^bsub>ES2\<^esub>"

                  from one validES2 have "set \<alpha>2'' \<subseteq> E\<^bsub>ES2\<^esub>"
                    by (simp add: ES_valid_def traces_contain_events_def, auto)
                  moreover
                  from \<nu>E2_empty
                  have "set ?DELTA2'' \<subseteq> N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub> \<union> C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub> \<inter> N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub>"
                    by simp
                  moreover
                  from c_is_c' c'_in_E2 one v'_notin_E2 \<nu>E2_empty
                  have "(\<beta> \<upharpoonleft> E\<^bsub>ES2\<^esub>) @ [c] \<upharpoonleft> E\<^bsub>ES2\<^esub> @ ?DELTA2'' @ [v'] \<upharpoonleft> E\<^bsub>ES2\<^esub> @ \<alpha>2'' \<in> Tr\<^bsub>ES2\<^esub>"
                    by (simp add: projection_def)
                  moreover
                  note two three
                  moreover
                  from \<nu>E2_empty \<delta>1''_is_\<nu> have "?DELTA2'' \<upharpoonleft> E\<^bsub>ES1\<^esub> = \<delta>1'' \<upharpoonleft> E\<^bsub>ES2\<^esub>"
                    by (simp add: projection_def)
                  ultimately show ?thesis
                    by blast
                next
                  case (Cons x xs) (* apply inductive hypothesis, then BSIA *)
                   with c\<delta>1''_is_\<mu>c'\<nu> have \<mu>_is_c_xs: "\<mu> = [c] @ xs" 
                     and \<delta>1''_is_xs_c'_\<nu>: "\<delta>1'' = xs @ [c'] @ \<nu>"
                    by auto
                  with n_is_length_\<mu>\<nu>E2 have "n = length ((c # (xs @ \<nu>)) \<upharpoonleft> E\<^bsub>ES2\<^esub>)"
                    by auto
                  moreover
                  note Suc(3,4)
                  moreover
                  have "set ((c # (xs @ \<nu>)) \<upharpoonleft> E\<^bsub>ES2\<^esub>) \<subseteq> C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub>"
                    proof -
                      have res: "c # (xs @ \<nu>) = [c] @ (xs @ \<nu>)" 
                        by auto

                      from Suc(5) c\<delta>1''_is_\<mu>c'\<nu> \<mu>_is_c_xs \<nu>E2_empty
                      show ?thesis
                        by (subst res, simp only: c\<delta>1''_is_\<mu>c'\<nu> projection_concatenation_commute 
                          set_append, auto)
                    qed
                  moreover
                  note Suc(6) 
                  moreover
                  from Suc(7) \<delta>1''_is_xs_c'_\<nu> have "set (xs @ \<nu>) \<subseteq> N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub>"
                    by auto
                  moreover note Suc(1)[of c "xs @ \<nu>" \<beta> \<alpha>2']
                  ultimately obtain \<delta> \<gamma>
                    where one: "set \<delta> \<subseteq> E\<^bsub>ES2\<^esub>"
                    and two: "set \<gamma> \<subseteq> N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub> \<union> C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub> \<inter> N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub>"
                    and three: "\<beta> \<upharpoonleft> E\<^bsub>ES2\<^esub> @ [c] \<upharpoonleft> E\<^bsub>ES2\<^esub> @ \<gamma> @ [v'] \<upharpoonleft> E\<^bsub>ES2\<^esub> @ \<delta> \<in> Tr\<^bsub>ES2\<^esub>"
                    and four: "\<delta> \<upharpoonleft> V\<^bsub>\<V>2\<^esub> = \<alpha>2' \<upharpoonleft> V\<^bsub>\<V>2\<^esub>"
                    and five: "\<delta> \<upharpoonleft> C\<^bsub>\<V>2\<^esub> = []"
                    and six: "\<gamma> \<upharpoonleft> E\<^bsub>ES1\<^esub> = (xs @ \<nu>) \<upharpoonleft> E\<^bsub>ES2\<^esub>"
                    by blast
                  
                   (* apply BSIA to insert c' after \<gamma> *)
                  let ?BETA = "\<beta> \<upharpoonleft> E\<^bsub>ES2\<^esub> @ [c] \<upharpoonleft> E\<^bsub>ES2\<^esub> @ \<gamma>"

                  from c'_in_Cv2_inter_Upsilon2 have "c' \<in> C\<^bsub>\<V>2\<^esub>"
                    by auto
                  moreover
                  from three v'_notin_E2 have "?BETA @ \<delta> \<in> Tr\<^bsub>ES2\<^esub>"
                    by (simp add: projection_def)
                  moreover
                  note five 
                  moreover
                  have "Adm \<V>2 \<rho>2 Tr\<^bsub>ES2\<^esub> ?BETA c'"
                    proof -
                      have "?BETA @ [c'] \<in> Tr\<^bsub>ES2\<^esub>"
                        proof -
                          from validES2 three have "?BETA \<in> Tr\<^bsub>ES2\<^esub>"
                            by (simp only: ES_valid_def traces_prefixclosed_def
                              projection_concatenation_commute prefixclosed_def prefix_def, auto)
                          moreover
                          note c'_in_Cv2_inter_Upsilon2 total_ES2_C2_inter_Upsilon2
                          ultimately show ?thesis
                            unfolding total_def
                            by blast
                        qed
                      thus ?thesis
                        unfolding Adm_def
                        by blast                        
                    qed
                  moreover
                  note BSIA2
                  ultimately obtain \<alpha>2''
                    where bsia_one: "?BETA @ [c'] @ \<alpha>2'' \<in> Tr\<^bsub>ES2\<^esub>"
                    and bsia_two: "\<alpha>2'' \<upharpoonleft> V\<^bsub>\<V>2\<^esub> = \<delta> \<upharpoonleft> V\<^bsub>\<V>2\<^esub>"
                    and bsia_three:  "\<alpha>2'' \<upharpoonleft> C\<^bsub>\<V>2\<^esub> = []"
                    unfolding BSIA_def
                    by blast
  
                  let ?DELTA2'' = "\<gamma> @ [c']"

                  from bsia_one validES2 have "set \<alpha>2'' \<subseteq> E\<^bsub>ES2\<^esub>"
                    by (simp add: ES_valid_def traces_contain_events_def, auto)
                  moreover
                  have "set ?DELTA2'' \<subseteq> N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub> \<union> C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub> \<inter> N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub>"
                    proof -
                      from Suc(7) c'_in_Cv2_inter_Upsilon2 \<delta>1''_is_xs_c'_\<nu> 
                      have "c' \<in>  C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub> \<inter> N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub>"
                        by auto
                      with two show ?thesis
                        by auto
                    qed
                  moreover
                  from bsia_one v'_notin_E2 
                  have "\<beta> \<upharpoonleft> E\<^bsub>ES2\<^esub> @ [c] \<upharpoonleft> E\<^bsub>ES2\<^esub> @ ?DELTA2'' @ [v'] \<upharpoonleft> E\<^bsub>ES2\<^esub> @ \<alpha>2'' \<in> Tr\<^bsub>ES2\<^esub>"
                    by (simp add: projection_def)
                  moreover
                  from bsia_two four have "\<alpha>2'' \<upharpoonleft> V\<^bsub>\<V>2\<^esub> = \<alpha>2' \<upharpoonleft> V\<^bsub>\<V>2\<^esub>"
                    by simp
                  moreover
                  note bsia_three
                  moreover             
                  have "?DELTA2'' \<upharpoonleft> E\<^bsub>ES1\<^esub> = \<delta>1'' \<upharpoonleft> E\<^bsub>ES2\<^esub>"
                    proof -
                      from validV1 Suc(7) \<delta>1''_is_xs_c'_\<nu> have "c' \<in> E\<^bsub>ES1\<^esub>"
                        by (simp add: isViewOn_def V_valid_def
                          VC_disjoint_def VN_disjoint_def NC_disjoint_def, auto)
                      with c'_in_E2 c'_in_Cv2_inter_Upsilon2 \<delta>1''_is_xs_c'_\<nu> \<nu>E2_empty six 
                      show ?thesis
                        by (simp only: projection_concatenation_commute 
                          projection_def, auto)
                    qed
                  ultimately show ?thesis 
                    by blast     
                qed
            qed
          from this[OF \<beta>v'E2\<alpha>2'_in_Tr2 \<alpha>2'Cv2_empty c\<delta>1''E2_in_Cv2_inter_Upsilon2star 
            c_in_Cv_inter_Upsilon \<delta>1''_in_N1_inter_Delta1star]
          show ?thesis 
            by blast
        qed
      then obtain \<alpha>2'' \<delta>2''
        where \<alpha>2''_in_E2star: "set \<alpha>2'' \<subseteq> E\<^bsub>ES2\<^esub>"
        and \<delta>2''_in_N2_inter_Delta2star:"set \<delta>2'' \<subseteq> N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub> \<union> C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub> \<inter> N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub>"
        and \<beta>E2_cE2_\<delta>2''_v'E2_\<alpha>2''_in_Tr2: 
        "\<beta> \<upharpoonleft> E\<^bsub>ES2\<^esub> @ [c] \<upharpoonleft> E\<^bsub>ES2\<^esub> @ \<delta>2'' @ [v'] \<upharpoonleft> E\<^bsub>ES2\<^esub> @ \<alpha>2'' \<in> Tr\<^bsub>ES2\<^esub>"
        and \<alpha>2''Vv2_is_\<alpha>2'Vv2: "\<alpha>2'' \<upharpoonleft> V\<^bsub>\<V>2\<^esub> = \<alpha>2' \<upharpoonleft> V\<^bsub>\<V>2\<^esub>"
        and \<alpha>2''Cv2_empty: "\<alpha>2'' \<upharpoonleft> C\<^bsub>\<V>2\<^esub> = []"
        and \<delta>2''E1_is_\<delta>1''E2: "\<delta>2'' \<upharpoonleft> E\<^bsub>ES1\<^esub> = \<delta>1'' \<upharpoonleft> E\<^bsub>ES2\<^esub>"
        by blast

      from \<beta>E2_cE2_\<delta>2''_v'E2_\<alpha>2''_in_Tr2 \<beta>E1_cE1_\<delta>1''_v'E1_\<alpha>1''_in_Tr1 
        validES2 validES1
      have \<delta>2''_in_E2star: "set \<delta>2'' \<subseteq> E\<^bsub>ES2\<^esub>" and \<delta>1''_in_E1star: "set \<delta>1'' \<subseteq> E\<^bsub>ES1\<^esub>"
        by (simp_all add: ES_valid_def traces_contain_events_def, auto)
      with \<delta>2''E1_is_\<delta>1''E2 merge_property[of \<delta>2'' "E\<^bsub>ES2\<^esub>" \<delta>1'' "E\<^bsub>ES1\<^esub>"] obtain \<delta>'
        where \<delta>'E2_is_\<delta>2'': "\<delta>' \<upharpoonleft> E\<^bsub>ES2\<^esub> = \<delta>2''"
        and \<delta>'E1_is_\<delta>1'': "\<delta>' \<upharpoonleft> E\<^bsub>ES1\<^esub> = \<delta>1''"
        and \<delta>'_contains_only_\<delta>2''_\<delta>1''_events: "set \<delta>' \<subseteq> set \<delta>2'' \<union> set \<delta>1''"
        unfolding Let_def
        by auto

      let ?TAU = "\<beta> @ [c] @ \<delta>' @ [v']"
      let ?LAMBDA = "\<alpha> \<upharpoonleft> V\<^bsub>\<V>\<^esub>"
      let ?T2 = \<alpha>2''
      let ?T1 = \<alpha>1''

     (* apply the generalized zipping lemma *)
     have "?TAU \<in> Tr\<^bsub>(ES1 \<parallel> ES2)\<^esub>"
        proof -
          from \<beta>E2_cE2_\<delta>2''_v'E2_\<alpha>2''_in_Tr2 \<delta>'E2_is_\<delta>2'' validES2 
          have "\<beta> \<upharpoonleft> E\<^bsub>ES2\<^esub> @ [c] \<upharpoonleft> E\<^bsub>ES2\<^esub> @ \<delta>' \<upharpoonleft> E\<^bsub>ES2\<^esub> @ [v'] \<upharpoonleft> E\<^bsub>ES2\<^esub> \<in> Tr\<^bsub>ES2\<^esub>"
            by (simp add: ES_valid_def traces_prefixclosed_def
              prefixclosed_def prefix_def)
          hence "(\<beta> @ [c] @ \<delta>' @ [v']) \<upharpoonleft> E\<^bsub>ES2\<^esub> \<in> Tr\<^bsub>ES2\<^esub>"
            by (simp add: projection_def, auto)
          moreover          
          from \<beta>E1_cE1_\<delta>1''_v'E1_\<alpha>1''_in_Tr1 \<delta>'E1_is_\<delta>1'' validES1 
          have "\<beta> \<upharpoonleft> E\<^bsub>ES1\<^esub> @ [c] \<upharpoonleft> E\<^bsub>ES1\<^esub> @ \<delta>' \<upharpoonleft> E\<^bsub>ES1\<^esub> @ [v'] \<upharpoonleft> E\<^bsub>ES1\<^esub> \<in> Tr\<^bsub>ES1\<^esub>"
            by (simp add: ES_valid_def traces_prefixclosed_def
              prefixclosed_def prefix_def)
          hence "(\<beta> @ [c] @ \<delta>' @ [v']) \<upharpoonleft> E\<^bsub>ES1\<^esub> \<in> Tr\<^bsub>ES1\<^esub>"
            by (simp add: projection_def, auto)
          moreover
          from \<beta>v'\<alpha>_in_Tr c_in_Cv_inter_Upsilon VIsViewOnE \<delta>'_contains_only_\<delta>2''_\<delta>1''_events 
            \<delta>2''_in_E2star \<delta>1''_in_E1star
          have "set (\<beta> @ [c] @ \<delta>' @ [v']) \<subseteq> E\<^bsub>ES2\<^esub> \<union> E\<^bsub>ES1\<^esub>"
            unfolding composeES_def isViewOn_def V_valid_def VC_disjoint_def 
              VN_disjoint_def NC_disjoint_def
            by auto
          ultimately show ?thesis
            unfolding composeES_def
            by auto
        qed 
      hence "set ?TAU \<subseteq> E\<^bsub>(ES1 \<parallel> ES2)\<^esub>"
        unfolding composeES_def
        by auto
      moreover
      have "set ?LAMBDA \<subseteq> V\<^bsub>\<V>\<^esub>"
        by (simp add: projection_def, auto)
      moreover
      note \<alpha>2''_in_E2star \<alpha>1''_in_E1star
      moreover
      from \<beta>E2_cE2_\<delta>2''_v'E2_\<alpha>2''_in_Tr2 \<delta>'E2_is_\<delta>2'' 
      have "?TAU \<upharpoonleft> E\<^bsub>ES2\<^esub> @ ?T2 \<in> Tr\<^bsub>ES2\<^esub>"
        by (simp only: projection_concatenation_commute, auto)
      moreover
      from \<beta>E1_cE1_\<delta>1''_v'E1_\<alpha>1''_in_Tr1 \<delta>'E1_is_\<delta>1'' 
      have "?TAU \<upharpoonleft> E\<^bsub>ES1\<^esub> @ ?T1 \<in> Tr\<^bsub>ES1\<^esub>"
        by (simp only: projection_concatenation_commute, auto)
      moreover
      have "?LAMBDA \<upharpoonleft> E\<^bsub>ES2\<^esub> = ?T2 \<upharpoonleft> V\<^bsub>\<V>\<^esub>"
        proof -
          from propSepViews 
          have "?LAMBDA \<upharpoonleft> E\<^bsub>ES2\<^esub> = \<alpha> \<upharpoonleft> V\<^bsub>\<V>2\<^esub>"
            unfolding properSeparationOfViews_def  by (simp only: projection_sequence)
          moreover
          from \<alpha>2''_in_E2star propSepViews
          have "?T2 \<upharpoonleft> V\<^bsub>\<V>\<^esub> = ?T2 \<upharpoonleft> V\<^bsub>\<V>2\<^esub>"
            unfolding properSeparationOfViews_def
            by (metis Int_commute projection_intersection_neutral)
          moreover
          note \<alpha>2'Vv2_is_\<alpha>Vv2 \<alpha>2''Vv2_is_\<alpha>2'Vv2
          ultimately show ?thesis
            by simp
        qed
      moreover
      have "?LAMBDA \<upharpoonleft> E\<^bsub>ES1\<^esub> = ?T1 \<upharpoonleft> V\<^bsub>\<V>\<^esub>"
        proof -
          from propSepViews
          have "?LAMBDA \<upharpoonleft> E\<^bsub>ES1\<^esub> = \<alpha> \<upharpoonleft> V\<^bsub>\<V>1\<^esub>"
            unfolding properSeparationOfViews_def  by (simp add: projection_sequence)
          moreover
          from \<alpha>1''_in_E1star propSepViews
          have "?T1 \<upharpoonleft> V\<^bsub>\<V>\<^esub> = ?T1 \<upharpoonleft> V\<^bsub>\<V>1\<^esub>"
            unfolding properSeparationOfViews_def 
            by (metis Int_commute projection_intersection_neutral)
          moreover
          note \<alpha>1'Vv1_is_\<alpha>Vv1 \<alpha>1''Vv1_is_\<alpha>1'Vv1
          ultimately show ?thesis
            by simp
        qed
      moreover
      note \<alpha>2''Cv2_empty \<alpha>1''Cv1_empty generalized_zipping_lemma
      ultimately obtain t (* show that the conclusion of FCI holds *)
        where "?TAU @ t \<in> Tr\<^bsub>(ES1 \<parallel> ES2)\<^esub>"
        and  "t \<upharpoonleft> V\<^bsub>\<V>\<^esub> = ?LAMBDA"
        and "t \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []"
        by blast
      moreover
      have "set \<delta>' \<subseteq> N\<^bsub>\<V>\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>\<^esub>"
        proof -
          from \<delta>'_contains_only_\<delta>2''_\<delta>1''_events \<delta>2''_in_N2_inter_Delta2star
               \<delta>1''_in_N1_inter_Delta1star
          have "set \<delta>' \<subseteq> N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub> \<union> N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub>"
            by auto
          with Delta1_N1_Delta2_N2_subset_Delta Nv1_union_Nv2_subsetof_Nv show ?thesis
            by auto
        qed
      ultimately have "\<exists>\<alpha>' \<gamma>'. (set \<gamma>' \<subseteq> N\<^bsub>\<V>\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>\<^esub> \<and> \<beta> @ [c] @ \<gamma>' @ [v'] @ \<alpha>' \<in> Tr\<^bsub>(ES1 \<parallel> ES2)\<^esub> 
        \<and> \<alpha>' \<upharpoonleft> V\<^bsub>\<V>\<^esub> = \<alpha> \<upharpoonleft> V\<^bsub>\<V>\<^esub> \<and> \<alpha>' \<upharpoonleft> C\<^bsub>\<V>\<^esub> = [])"
        by (simp only: append_assoc, blast)
    }
    ultimately have "\<exists>\<alpha>' \<gamma>'. (set \<gamma>' \<subseteq> N\<^bsub>\<V>\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>\<^esub> \<and> \<beta> @ [c] @ \<gamma>' @ [v'] @ \<alpha>' \<in> Tr\<^bsub>(ES1 \<parallel> ES2)\<^esub> 
      \<and> \<alpha>' \<upharpoonleft> V\<^bsub>\<V>\<^esub> = \<alpha> \<upharpoonleft> V\<^bsub>\<V>\<^esub> \<and> \<alpha>' \<upharpoonleft> C\<^bsub>\<V>\<^esub> = [])"
      by blast
  }
  thus ?thesis
    unfolding FCI_def
    by blast
qed


(* Theorem 6.4.1 case 6 *)
theorem compositionality_FCIA: 
  "\<lbrakk> BSD \<V>1 Tr\<^bsub>ES1\<^esub>; BSD \<V>2 Tr\<^bsub>ES2\<^esub>; BSIA \<rho>1 \<V>1 Tr\<^bsub>ES1\<^esub>; BSIA \<rho>2 \<V>2 Tr\<^bsub>ES2\<^esub>;
  (\<rho>1 \<V>1) \<subseteq> (\<rho> \<V>) \<inter> E\<^bsub>ES1\<^esub>; (\<rho>2 \<V>2) \<subseteq> (\<rho> \<V>) \<inter> E\<^bsub>ES2\<^esub>;
  total ES1 (C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub> \<inter> N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub>); total ES2 (C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub> \<inter> N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub>);
  \<nabla>\<^bsub>\<Gamma>\<^esub> \<inter> E\<^bsub>ES1\<^esub> \<subseteq> \<nabla>\<^bsub>\<Gamma>1\<^esub>; \<nabla>\<^bsub>\<Gamma>\<^esub> \<inter> E\<^bsub>ES2\<^esub> \<subseteq> \<nabla>\<^bsub>\<Gamma>2\<^esub>;
  \<Upsilon>\<^bsub>\<Gamma>\<^esub> \<inter> E\<^bsub>ES1\<^esub> \<subseteq> \<Upsilon>\<^bsub>\<Gamma>1\<^esub>; \<Upsilon>\<^bsub>\<Gamma>\<^esub> \<inter> E\<^bsub>ES2\<^esub> \<subseteq> \<Upsilon>\<^bsub>\<Gamma>2\<^esub>;
  ( \<Delta>\<^bsub>\<Gamma>1\<^esub> \<inter> N\<^bsub>\<V>1\<^esub> \<union> \<Delta>\<^bsub>\<Gamma>2\<^esub> \<inter> N\<^bsub>\<V>2\<^esub> ) \<subseteq> \<Delta>\<^bsub>\<Gamma>\<^esub>;
  (N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub> \<inter> E\<^bsub>ES2\<^esub> = {} \<and> N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub> \<inter> E\<^bsub>ES1\<^esub> \<subseteq> \<Upsilon>\<^bsub>\<Gamma>1\<^esub>)
  \<or> ( N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub> \<inter> E\<^bsub>ES1\<^esub> = {} \<and> N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub> \<inter> E\<^bsub>ES2\<^esub> \<subseteq> \<Upsilon>\<^bsub>\<Gamma>2\<^esub>)  ;
  FCIA \<rho>1 \<Gamma>1 \<V>1 Tr\<^bsub>ES1\<^esub>; FCIA \<rho>2 \<Gamma>2 \<V>2 Tr\<^bsub>ES2\<^esub> \<rbrakk> 
  \<Longrightarrow> FCIA \<rho> \<Gamma> \<V> (Tr\<^bsub>(ES1 \<parallel> ES2)\<^esub>)"
proof -
 assume BSD1: "BSD \<V>1 Tr\<^bsub>ES1\<^esub>" 
    and BSD2: "BSD \<V>2 Tr\<^bsub>ES2\<^esub>"
    and BSIA1: "BSIA \<rho>1 \<V>1 Tr\<^bsub>ES1\<^esub>"
    and BSIA2: "BSIA \<rho>2 \<V>2 Tr\<^bsub>ES2\<^esub>"
    and \<rho>1v1_subset_\<rho>v_inter_E1: "(\<rho>1 \<V>1) \<subseteq> (\<rho> \<V>) \<inter> E\<^bsub>ES1\<^esub>"
    and \<rho>2v2_subset_\<rho>v_inter_E2: "(\<rho>2 \<V>2) \<subseteq> (\<rho> \<V>) \<inter> E\<^bsub>ES2\<^esub>"
    and total_ES1_C1_inter_Upsilon1_inter_N2_inter_Delta2: 
     "total ES1 (C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub> \<inter> N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub>)"
    and total_ES2_C2_inter_Upsilon2_inter_N1_inter_Delta1: 
     "total ES2 (C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub> \<inter> N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub>)"
    and Nabla_inter_E1_subset_Nabla1: "\<nabla>\<^bsub>\<Gamma>\<^esub> \<inter> E\<^bsub>ES1\<^esub> \<subseteq> \<nabla>\<^bsub>\<Gamma>1\<^esub>"
    and Nabla_inter_E2_subset_Nabla2: "\<nabla>\<^bsub>\<Gamma>\<^esub> \<inter> E\<^bsub>ES2\<^esub> \<subseteq> \<nabla>\<^bsub>\<Gamma>2\<^esub>"
    and Upsilon_inter_E1_subset_Upsilon1: "\<Upsilon>\<^bsub>\<Gamma>\<^esub> \<inter> E\<^bsub>ES1\<^esub> \<subseteq> \<Upsilon>\<^bsub>\<Gamma>1\<^esub>"
    and Upsilon_inter_E2_subset_Upsilon2: "\<Upsilon>\<^bsub>\<Gamma>\<^esub> \<inter> E\<^bsub>ES2\<^esub> \<subseteq> \<Upsilon>\<^bsub>\<Gamma>2\<^esub>"
    and Delta1_N1_Delta2_N2_subset_Delta: "( \<Delta>\<^bsub>\<Gamma>1\<^esub> \<inter> N\<^bsub>\<V>1\<^esub> \<union> \<Delta>\<^bsub>\<Gamma>2\<^esub> \<inter> N\<^bsub>\<V>2\<^esub> ) \<subseteq> \<Delta>\<^bsub>\<Gamma>\<^esub>"
    and very_long_asm: "(N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub> \<inter> E\<^bsub>ES2\<^esub> = {} \<and> N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub> \<inter> E\<^bsub>ES1\<^esub> \<subseteq> \<Upsilon>\<^bsub>\<Gamma>1\<^esub>)
    \<or> ( N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub> \<inter> E\<^bsub>ES1\<^esub> = {} \<and> N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub> \<inter> E\<^bsub>ES2\<^esub> \<subseteq> \<Upsilon>\<^bsub>\<Gamma>2\<^esub>)"
    and FCIA1: "FCIA \<rho>1 \<Gamma>1 \<V>1 Tr\<^bsub>ES1\<^esub>"
    and FCIA2: "FCIA \<rho>2 \<Gamma>2 \<V>2 Tr\<^bsub>ES2\<^esub>"

  {
    fix \<alpha> \<beta> c v'
    assume c_in_Cv_inter_Upsilon: "c \<in> (C\<^bsub>\<V>\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>\<^esub>)"
      and v'_in_Vv_inter_Nabla: "v' \<in> (V\<^bsub>\<V>\<^esub> \<inter> \<nabla>\<^bsub>\<Gamma>\<^esub>)"
      and \<beta>v'\<alpha>_in_Tr: "(\<beta> @ [v'] @ \<alpha>) \<in> Tr\<^bsub>(ES1 \<parallel> ES2)\<^esub>" 
      and \<alpha>Cv_empty: "\<alpha> \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []"
      and Adm: "Adm \<V> \<rho> (Tr\<^bsub>(ES1 \<parallel> ES2)\<^esub>) \<beta> c"

    interpret CSES1: CompositionSupport "ES1" "\<V>" "\<V>1"
      using propSepViews unfolding properSeparationOfViews_def 
      by (simp add: CompositionSupport_def validES1 validV1)

    interpret CSES2: CompositionSupport "ES2" "\<V>" "\<V>2"
      using propSepViews unfolding properSeparationOfViews_def 
      by (simp add: CompositionSupport_def validES2 validV2)

    from  \<beta>v'\<alpha>_in_Tr
    have  \<beta>v'\<alpha>_E1_in_Tr1: "(((\<beta> @ [v']) @ \<alpha>) \<upharpoonleft> E\<^bsub>ES1\<^esub>) \<in> Tr\<^bsub>ES1\<^esub>"
      and \<beta>v'\<alpha>_E2_in_Tr2: "(((\<beta> @ [v']) @ \<alpha>) \<upharpoonleft> E\<^bsub>ES2\<^esub>) \<in> Tr\<^bsub>ES2\<^esub>"
      by (simp add: composeES_def)+    

    from CSES1.BSD_in_subsystem2[OF \<beta>v'\<alpha>_E1_in_Tr1 BSD1] obtain \<alpha>1'
      where \<beta>v'E1\<alpha>1'_in_Tr1: "(\<beta> @ [v']) \<upharpoonleft> E\<^bsub>ES1\<^esub> @ \<alpha>1' \<in> Tr\<^bsub>ES1\<^esub>"
      and \<alpha>1'Vv1_is_\<alpha>Vv1: "\<alpha>1' \<upharpoonleft> V\<^bsub>\<V>1\<^esub> = \<alpha> \<upharpoonleft> V\<^bsub>\<V>1\<^esub>"
      and \<alpha>1'Cv1_empty: "\<alpha>1' \<upharpoonleft> C\<^bsub>\<V>1\<^esub> = []"
      by auto

    from CSES2.BSD_in_subsystem2[OF \<beta>v'\<alpha>_E2_in_Tr2 BSD2] obtain \<alpha>2'
      where \<beta>v'E2\<alpha>2'_in_Tr2: "(\<beta> @ [v']) \<upharpoonleft> E\<^bsub>ES2\<^esub> @ \<alpha>2' \<in> Tr\<^bsub>ES2\<^esub>"
      and \<alpha>2'Vv2_is_\<alpha>Vv2: "\<alpha>2' \<upharpoonleft> V\<^bsub>\<V>2\<^esub> = \<alpha> \<upharpoonleft> V\<^bsub>\<V>2\<^esub>"
      and \<alpha>2'Cv2_empty: "\<alpha>2' \<upharpoonleft> C\<^bsub>\<V>2\<^esub> = []"
      by auto

    note very_long_asm
    moreover {
      assume Nv1_inter_Delta1_inter_E2_empty: "N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub> \<inter> E\<^bsub>ES2\<^esub> = {}" 
        and  Nv2_inter_Delta2_inter_E1_subsetof_Upsilon1: "N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub> \<inter> E\<^bsub>ES1\<^esub> \<subseteq> \<Upsilon>\<^bsub>\<Gamma>1\<^esub>"

      let ?ALPHA2''_DELTA2'' = "\<exists> \<alpha>2'' \<delta>2''. (
        set \<alpha>2'' \<subseteq> E\<^bsub>ES2\<^esub> \<and> set \<delta>2'' \<subseteq> N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub> 
        \<and> \<beta> \<upharpoonleft> E\<^bsub>ES2\<^esub> @ [c] \<upharpoonleft> E\<^bsub>ES2\<^esub> @ \<delta>2'' @ [v'] \<upharpoonleft> E\<^bsub>ES2\<^esub> @ \<alpha>2'' \<in> Tr\<^bsub>ES2\<^esub>        
        \<and> \<alpha>2'' \<upharpoonleft> V\<^bsub>\<V>2\<^esub> = \<alpha>2' \<upharpoonleft> V\<^bsub>\<V>2\<^esub> \<and> \<alpha>2'' \<upharpoonleft> C\<^bsub>\<V>2\<^esub> = [])"

      from c_in_Cv_inter_Upsilon v'_in_Vv_inter_Nabla validV2
      have "c \<notin> E\<^bsub>ES2\<^esub> \<or> (c \<in> E\<^bsub>ES2\<^esub> \<and> v' \<notin> E\<^bsub>ES2\<^esub>) \<or> (c \<in> E\<^bsub>ES2\<^esub> \<and> v' \<in> E\<^bsub>ES2\<^esub>)"
        by (simp add: V_valid_def isViewOn_def 
          VC_disjoint_def VN_disjoint_def NC_disjoint_def)
      moreover {
        assume c_notin_E2: "c \<notin> E\<^bsub>ES2\<^esub>"

        from validES2 \<beta>v'E2\<alpha>2'_in_Tr2 have "set \<alpha>2' \<subseteq> E\<^bsub>ES2\<^esub>"
          by (simp add: ES_valid_def traces_contain_events_def, auto)
        moreover 
        have "set [] \<subseteq> N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub>"
          by auto
        moreover 
        from \<beta>v'E2\<alpha>2'_in_Tr2 c_notin_E2 
        have "\<beta> \<upharpoonleft> E\<^bsub>ES2\<^esub> @ [c] \<upharpoonleft> E\<^bsub>ES2\<^esub> @ [] @ [v'] \<upharpoonleft> E\<^bsub>ES2\<^esub> @ \<alpha>2' \<in> Tr\<^bsub>ES2\<^esub>"
          by (simp add: projection_def)
        moreover
        have "\<alpha>2' \<upharpoonleft> V\<^bsub>\<V>2\<^esub> = \<alpha>2' \<upharpoonleft> V\<^bsub>\<V>2\<^esub>" ..
        moreover 
        note \<alpha>2'Cv2_empty
        ultimately have ?ALPHA2''_DELTA2''
          by blast
      }
      moreover {
        assume c_in_E2: "c \<in> E\<^bsub>ES2\<^esub>"
          and  v'_notin_E2: "v' \<notin> E\<^bsub>ES2\<^esub>"

        from c_in_E2 c_in_Cv_inter_Upsilon propSepViews
          Upsilon_inter_E2_subset_Upsilon2
        have c_in_Cv2_inter_Upsilon2: "c \<in> C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub>"
          unfolding properSeparationOfViews_def by auto
        hence "c \<in> C\<^bsub>\<V>2\<^esub>"
          by auto
        moreover
        from \<beta>v'E2\<alpha>2'_in_Tr2 v'_notin_E2 have "\<beta> \<upharpoonleft> E\<^bsub>ES2\<^esub> @ \<alpha>2' \<in> Tr\<^bsub>ES2\<^esub>"
          by (simp add: projection_def)
        moreover
        note \<alpha>2'Cv2_empty
        moreover
        have "Adm \<V>2 \<rho>2 Tr\<^bsub>ES2\<^esub> (\<beta> \<upharpoonleft> E\<^bsub>ES2\<^esub>) c"
        proof -
          from Adm obtain \<gamma>
            where \<gamma>\<rho>v_is_\<beta>\<rho>v: "\<gamma> \<upharpoonleft> (\<rho> \<V>) = \<beta> \<upharpoonleft> (\<rho> \<V>)"
            and \<gamma>c_in_Tr: "(\<gamma> @ [c]) \<in> Tr\<^bsub>(ES1 \<parallel> ES2)\<^esub>"
            unfolding Adm_def
            by auto

          from c_in_E2 \<gamma>c_in_Tr have "(\<gamma> \<upharpoonleft> E\<^bsub>ES2\<^esub>) @ [c] \<in> Tr\<^bsub>ES2\<^esub>"
            by (simp add: projection_def composeES_def)
          moreover
          have "\<gamma> \<upharpoonleft> E\<^bsub>ES2\<^esub> \<upharpoonleft> (\<rho>2 \<V>2) = \<beta> \<upharpoonleft> E\<^bsub>ES2\<^esub> \<upharpoonleft> (\<rho>2 \<V>2)"
          proof -
            from \<gamma>\<rho>v_is_\<beta>\<rho>v have "\<gamma> \<upharpoonleft> E\<^bsub>ES2\<^esub> \<upharpoonleft> (\<rho> \<V>) = \<beta> \<upharpoonleft> E\<^bsub>ES2\<^esub> \<upharpoonleft> (\<rho> \<V>)"
              by (metis projection_commute)
            with \<rho>2v2_subset_\<rho>v_inter_E2 have "\<gamma> \<upharpoonleft> (\<rho>2 \<V>2) = \<beta> \<upharpoonleft> (\<rho>2 \<V>2)"
              by (metis Int_subset_iff \<gamma>\<rho>v_is_\<beta>\<rho>v projection_subset_elim)
            thus ?thesis
              by (metis projection_commute)
          qed
          ultimately show ?thesis unfolding Adm_def
            by auto
        qed  
        moreover 
        note BSIA2
        ultimately obtain  \<alpha>2''
          where one: "\<beta> \<upharpoonleft> E\<^bsub>ES2\<^esub> @ [c] @ \<alpha>2'' \<in> Tr\<^bsub>ES2\<^esub>"
          and two:   "\<alpha>2'' \<upharpoonleft> V\<^bsub>\<V>2\<^esub> = \<alpha>2' \<upharpoonleft> V\<^bsub>\<V>2\<^esub>"
          and three: "\<alpha>2'' \<upharpoonleft> C\<^bsub>\<V>2\<^esub> = []"
          unfolding BSIA_def
          by blast

        from one validES2 have "set \<alpha>2'' \<subseteq> E\<^bsub>ES2\<^esub>"
          by (simp add: ES_valid_def traces_contain_events_def, auto)
        moreover
        have "set [] \<subseteq> N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub>"
          by auto
        moreover
        from one c_in_E2 v'_notin_E2 
        have "\<beta> \<upharpoonleft> E\<^bsub>ES2\<^esub> @ [c] \<upharpoonleft> E\<^bsub>ES2\<^esub> @ [] @ [v'] \<upharpoonleft> E\<^bsub>ES2\<^esub> @ \<alpha>2'' \<in> Tr\<^bsub>ES2\<^esub>"
          by (simp add: projection_def)
        moreover 
        note two three
        ultimately have ?ALPHA2''_DELTA2''
          by blast
      }
      moreover {
        assume c_in_E2: "c \<in> E\<^bsub>ES2\<^esub>"
          and  v'_in_E2: "v' \<in> E\<^bsub>ES2\<^esub>"

        from c_in_E2 c_in_Cv_inter_Upsilon propSepViews
          Upsilon_inter_E2_subset_Upsilon2
        have c_in_Cv2_inter_Upsilon2: "c \<in> C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub>"
          unfolding properSeparationOfViews_def by auto
        moreover
        from v'_in_E2 propSepViews v'_in_Vv_inter_Nabla Nabla_inter_E2_subset_Nabla2
        have "v' \<in> V\<^bsub>\<V>2\<^esub> \<inter> Nabla \<Gamma>2"
          unfolding properSeparationOfViews_def by auto
        moreover
        from v'_in_E2  \<beta>v'E2\<alpha>2'_in_Tr2 have "\<beta> \<upharpoonleft> E\<^bsub>ES2\<^esub> @ [v'] @ \<alpha>2' \<in> Tr\<^bsub>ES2\<^esub>"
          by (simp add: projection_def)
        moreover
        note \<alpha>2'Cv2_empty 
        moreover
        have "Adm \<V>2 \<rho>2 Tr\<^bsub>ES2\<^esub> (\<beta> \<upharpoonleft> E\<^bsub>ES2\<^esub>) c"
        proof -
          from Adm obtain \<gamma>
            where \<gamma>\<rho>v_is_\<beta>\<rho>v: "\<gamma> \<upharpoonleft> (\<rho> \<V>) = \<beta> \<upharpoonleft> (\<rho> \<V>)"
            and \<gamma>c_in_Tr: "(\<gamma> @ [c]) \<in> Tr\<^bsub>(ES1 \<parallel> ES2)\<^esub>"
            unfolding Adm_def
            by auto

          from c_in_E2 \<gamma>c_in_Tr have "(\<gamma> \<upharpoonleft> E\<^bsub>ES2\<^esub>) @ [c] \<in> Tr\<^bsub>ES2\<^esub>"
            by (simp add: projection_def composeES_def)
          moreover
          have "\<gamma> \<upharpoonleft> E\<^bsub>ES2\<^esub> \<upharpoonleft> (\<rho>2 \<V>2) = \<beta> \<upharpoonleft> E\<^bsub>ES2\<^esub> \<upharpoonleft> (\<rho>2 \<V>2)"
          proof -
            from \<gamma>\<rho>v_is_\<beta>\<rho>v have "\<gamma> \<upharpoonleft> E\<^bsub>ES2\<^esub> \<upharpoonleft> (\<rho> \<V>) = \<beta> \<upharpoonleft> E\<^bsub>ES2\<^esub> \<upharpoonleft> (\<rho> \<V>)"
              by (metis projection_commute)
            with \<rho>2v2_subset_\<rho>v_inter_E2 have "\<gamma> \<upharpoonleft> (\<rho>2 \<V>2) = \<beta> \<upharpoonleft> (\<rho>2 \<V>2)"
              by (metis Int_subset_iff \<gamma>\<rho>v_is_\<beta>\<rho>v projection_subset_elim)
            thus ?thesis
              by (metis projection_commute)
          qed
          ultimately show ?thesis unfolding Adm_def
            by auto
        qed  
        moreover
        note FCIA2
        ultimately obtain \<alpha>2'' \<delta>2''
          where one: "set \<delta>2'' \<subseteq> N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub>"
          and two: "\<beta> \<upharpoonleft> E\<^bsub>ES2\<^esub> @ [c] @ \<delta>2'' @ [v'] @ \<alpha>2'' \<in> Tr\<^bsub>ES2\<^esub>"
          and three: "\<alpha>2'' \<upharpoonleft> V\<^bsub>\<V>2\<^esub> = \<alpha>2' \<upharpoonleft> V\<^bsub>\<V>2\<^esub>"
          and four: "\<alpha>2'' \<upharpoonleft> C\<^bsub>\<V>2\<^esub> = []"
          unfolding FCIA_def
          by blast

        from two validES2 have "set \<alpha>2'' \<subseteq> E\<^bsub>ES2\<^esub>"
          by (simp add: ES_valid_def traces_contain_events_def, auto)
        moreover
        note one
        moreover
        from two c_in_E2 v'_in_E2 
        have "\<beta> \<upharpoonleft> E\<^bsub>ES2\<^esub> @ [c] \<upharpoonleft> E\<^bsub>ES2\<^esub> @ \<delta>2'' @ [v'] \<upharpoonleft> E\<^bsub>ES2\<^esub> @ \<alpha>2'' \<in> Tr\<^bsub>ES2\<^esub>"
          by (simp add: projection_def)
        moreover
        note three four
        ultimately have ?ALPHA2''_DELTA2''
          by blast
      }
      ultimately obtain \<alpha>2'' \<delta>2''
        where \<alpha>2''_in_E2star: "set \<alpha>2'' \<subseteq> E\<^bsub>ES2\<^esub>"
        and \<delta>2''_in_N2_inter_Delta2star:"set \<delta>2'' \<subseteq> N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub>"
        and \<beta>E2_cE2_\<delta>2''_v'E2_\<alpha>2''_in_Tr2:
              "\<beta> \<upharpoonleft> E\<^bsub>ES2\<^esub> @ [c] \<upharpoonleft> E\<^bsub>ES2\<^esub> @ \<delta>2'' @ [v'] \<upharpoonleft> E\<^bsub>ES2\<^esub> @ \<alpha>2'' \<in> Tr\<^bsub>ES2\<^esub>"
        and \<alpha>2''Vv2_is_\<alpha>2'Vv2: "\<alpha>2'' \<upharpoonleft> V\<^bsub>\<V>2\<^esub> = \<alpha>2' \<upharpoonleft> V\<^bsub>\<V>2\<^esub>"
        and \<alpha>2''Cv2_empty: "\<alpha>2'' \<upharpoonleft> C\<^bsub>\<V>2\<^esub> = []"
        by blast

      from c_in_Cv_inter_Upsilon Upsilon_inter_E1_subset_Upsilon1 propSepViews
      have cE1_in_Cv1_inter_Upsilon1: "set ([c] \<upharpoonleft> E\<^bsub>ES1\<^esub>) \<subseteq> C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub>"
        unfolding properSeparationOfViews_def by (simp add: projection_def, auto)
     
      from \<delta>2''_in_N2_inter_Delta2star Nv2_inter_Delta2_inter_E1_subsetof_Upsilon1 
       propSepViews disjoint_Nv2_Vv1 
      have \<delta>2''E1_in_Cv1_inter_Upsilon1star: "set (\<delta>2'' \<upharpoonleft> E\<^bsub>ES1\<^esub>) \<subseteq> C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub>"
        proof -
          from \<delta>2''_in_N2_inter_Delta2star
          have eq: "\<delta>2'' \<upharpoonleft> E\<^bsub>ES1\<^esub> = \<delta>2'' \<upharpoonleft> (N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub> \<inter> E\<^bsub>ES1\<^esub>)"
            by (metis Int_commute Int_left_commute Int_lower1 Int_lower2 
              projection_intersection_neutral subset_trans)
          
          from validV1 Nv2_inter_Delta2_inter_E1_subsetof_Upsilon1 
            propSepViews disjoint_Nv2_Vv1  
          have "N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub> \<inter> E\<^bsub>ES1\<^esub> \<subseteq> C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub>"
            unfolding properSeparationOfViews_def 
            by (simp add: isViewOn_def V_valid_def 
              VC_disjoint_def VN_disjoint_def NC_disjoint_def, auto)
          thus ?thesis
            by (subst eq, simp only: projection_def, auto)
        qed
      
      have c\<delta>2''E1_in_Cv1_inter_Upsilon1star: "set ((c # \<delta>2'') \<upharpoonleft> E\<^bsub>ES1\<^esub>) \<subseteq> C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub>"
        proof -
          from cE1_in_Cv1_inter_Upsilon1 \<delta>2''E1_in_Cv1_inter_Upsilon1star
          have "set (([c] @ \<delta>2'') \<upharpoonleft> E\<^bsub>ES1\<^esub>) \<subseteq> C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub>"
            by (simp only: projection_concatenation_commute, auto)
          thus ?thesis
            by auto
        qed


        have 
        "\<exists> \<alpha>1'' \<delta>1''. set \<alpha>1'' \<subseteq> E\<^bsub>ES1\<^esub> \<and> set \<delta>1'' \<subseteq> N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub> \<union> C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub> \<inter> N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub>        
        \<and> \<beta> \<upharpoonleft> E\<^bsub>ES1\<^esub> @ [c] \<upharpoonleft> E\<^bsub>ES1\<^esub> @ \<delta>1'' @ [v'] \<upharpoonleft> E\<^bsub>ES1\<^esub> @ \<alpha>1'' \<in> Tr\<^bsub>ES1\<^esub>        
        \<and> \<alpha>1'' \<upharpoonleft> V\<^bsub>\<V>1\<^esub> = \<alpha>1' \<upharpoonleft> V\<^bsub>\<V>1\<^esub> \<and> \<alpha>1'' \<upharpoonleft> C\<^bsub>\<V>1\<^esub> = []
        \<and> \<delta>1'' \<upharpoonleft> E\<^bsub>ES2\<^esub> = \<delta>2'' \<upharpoonleft> E\<^bsub>ES1\<^esub>"
        proof cases
          assume v'_in_E1: "v' \<in> E\<^bsub>ES1\<^esub>"
          with Nabla_inter_E1_subset_Nabla1 propSepViews v'_in_Vv_inter_Nabla
          have v'_in_Vv1_inter_Nabla1: "v' \<in> V\<^bsub>\<V>1\<^esub> \<inter> Nabla \<Gamma>1"
            unfolding properSeparationOfViews_def by auto

          have "\<lbrakk> (\<beta> @ [v']) \<upharpoonleft> E\<^bsub>ES1\<^esub> @ \<alpha>1' \<in> Tr\<^bsub>ES1\<^esub> ; 
            \<alpha>1' \<upharpoonleft> C\<^bsub>\<V>1\<^esub> = []; set ((c # \<delta>2'') \<upharpoonleft> E\<^bsub>ES1\<^esub>) \<subseteq> C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub> ; 
            c \<in> C\<^bsub>\<V>\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>\<^esub> ; set \<delta>2'' \<subseteq> N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub>;
            Adm \<V> \<rho> (Tr\<^bsub>(ES1 \<parallel> ES2)\<^esub>) \<beta> c \<rbrakk> 
            \<Longrightarrow> \<exists> \<alpha>1'' \<delta>1''.
            (set \<alpha>1'' \<subseteq> E\<^bsub>ES1\<^esub> \<and> set \<delta>1'' \<subseteq> N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub> \<union> C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub> \<inter> N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub>            
            \<and> \<beta> \<upharpoonleft> E\<^bsub>ES1\<^esub> @ [c] \<upharpoonleft> E\<^bsub>ES1\<^esub> @ \<delta>1'' @ [v'] \<upharpoonleft> E\<^bsub>ES1\<^esub> @ \<alpha>1'' \<in> Tr\<^bsub>ES1\<^esub>            
            \<and> \<alpha>1'' \<upharpoonleft> V\<^bsub>\<V>1\<^esub> = \<alpha>1' \<upharpoonleft> V\<^bsub>\<V>1\<^esub> \<and> \<alpha>1'' \<upharpoonleft> C\<^bsub>\<V>1\<^esub> = []
            \<and> \<delta>1'' \<upharpoonleft> (C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub>) = \<delta>2'' \<upharpoonleft> E\<^bsub>ES1\<^esub>)"
            proof (induct "length ((c # \<delta>2'') \<upharpoonleft> E\<^bsub>ES1\<^esub>)" arbitrary: \<beta> \<alpha>1' c \<delta>2'')
              case 0

              from 0(2) validES1 have "set \<alpha>1' \<subseteq> E\<^bsub>ES1\<^esub>"
                by (simp add: ES_valid_def traces_contain_events_def, auto)
              moreover
              have "set [] \<subseteq> N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub> \<union> C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub> \<inter> N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub>"
                by auto
              moreover
              have "\<beta> \<upharpoonleft> E\<^bsub>ES1\<^esub> @ [c] \<upharpoonleft> E\<^bsub>ES1\<^esub> @ [] @ [v'] \<upharpoonleft> E\<^bsub>ES1\<^esub> @ \<alpha>1' \<in> Tr\<^bsub>ES1\<^esub>"
                proof -
                  note 0(2)
                  moreover
                  from 0(1) have "c \<notin> E\<^bsub>ES1\<^esub>"
                    by (simp add: projection_def, auto)
                  ultimately show ?thesis
                    by (simp add: projection_concatenation_commute projection_def)
                qed
              moreover
              have "\<alpha>1' \<upharpoonleft> V\<^bsub>\<V>1\<^esub> = \<alpha>1' \<upharpoonleft> V\<^bsub>\<V>1\<^esub>" ..
              moreover
              note 0(3)
              moreover 
              from 0(1) have "[] \<upharpoonleft> (C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub>) = \<delta>2'' \<upharpoonleft> E\<^bsub>ES1\<^esub>"
                by (simp add: projection_def, split if_split_asm, auto)
              ultimately show ?case
                by blast
            next
              case (Suc n)

              from projection_split_last[OF Suc(2)] obtain \<mu> c' \<nu>
                where c'_in_E1: "c' \<in> E\<^bsub>ES1\<^esub>"
                and c\<delta>2''_is_\<mu>c'\<nu>: "c # \<delta>2'' = \<mu> @ [c'] @ \<nu>"
                and \<nu>E1_empty: "\<nu> \<upharpoonleft> E\<^bsub>ES1\<^esub> = []"
                and n_is_length_\<mu>\<nu>E1: "n = length ((\<mu> @ \<nu>) \<upharpoonleft> E\<^bsub>ES1\<^esub>)"
                by blast

              from Suc(5) c'_in_E1 c\<delta>2''_is_\<mu>c'\<nu> have "set (\<mu> \<upharpoonleft> E\<^bsub>ES1\<^esub> @ [c']) \<subseteq> C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub>"
                by (simp only: c\<delta>2''_is_\<mu>c'\<nu> projection_concatenation_commute 
                  projection_def, auto)
              hence c'_in_Cv1_inter_Upsilon1: "c' \<in> C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub>"
                by auto
              hence c'_in_Cv1: "c' \<in> C\<^bsub>\<V>1\<^esub>" and c'_in_Upsilon1: "c' \<in> \<Upsilon>\<^bsub>\<Gamma>1\<^esub>"
                by auto
              with validV1 have c'_in_E1: "c' \<in> E\<^bsub>ES1\<^esub>"
                by (simp add: isViewOn_def V_valid_def VC_disjoint_def 
                  VN_disjoint_def NC_disjoint_def, auto)

              show ?case
                proof (cases \<mu>)
                  case Nil (* we apply FCIA in this case *)
                  with c\<delta>2''_is_\<mu>c'\<nu> have c_is_c': "c = c'" and \<delta>2''_is_\<nu>: "\<delta>2'' = \<nu>"
                    by auto
                  with c'_in_Cv1_inter_Upsilon1 have "c \<in> C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub>"
                    by simp
                  moreover
                  note v'_in_Vv1_inter_Nabla1
                  moreover
                  from v'_in_E1 Suc(3) have "(\<beta> \<upharpoonleft> E\<^bsub>ES1\<^esub>) @ [v'] @ \<alpha>1' \<in> Tr\<^bsub>ES1\<^esub>"
                    by (simp add: projection_concatenation_commute projection_def)
                  moreover
                  note Suc(4)
                  moreover
                  have "Adm \<V>1 \<rho>1 Tr\<^bsub>ES1\<^esub> (\<beta> \<upharpoonleft> E\<^bsub>ES1\<^esub>) c"
                    proof -
                      from Suc(8) obtain \<gamma>
                        where \<gamma>\<rho>v_is_\<beta>\<rho>v: "\<gamma> \<upharpoonleft> (\<rho> \<V>) = \<beta> \<upharpoonleft> (\<rho> \<V>)"
                        and \<gamma>c_in_Tr: "(\<gamma> @ [c]) \<in> Tr\<^bsub>(ES1 \<parallel> ES2)\<^esub>"
                        unfolding Adm_def
                        by auto

                      from c_is_c' c'_in_E1 \<gamma>c_in_Tr have "(\<gamma> \<upharpoonleft> E\<^bsub>ES1\<^esub>) @ [c] \<in> Tr\<^bsub>ES1\<^esub>"
                        by (simp add: projection_def composeES_def)
                      moreover
                      have "\<gamma> \<upharpoonleft> E\<^bsub>ES1\<^esub> \<upharpoonleft> (\<rho>1 \<V>1) = \<beta> \<upharpoonleft> E\<^bsub>ES1\<^esub> \<upharpoonleft> (\<rho>1 \<V>1)"
                      proof -
                        from \<gamma>\<rho>v_is_\<beta>\<rho>v have "\<gamma> \<upharpoonleft> E\<^bsub>ES1\<^esub> \<upharpoonleft> (\<rho> \<V>) = \<beta> \<upharpoonleft> E\<^bsub>ES1\<^esub> \<upharpoonleft> (\<rho> \<V>)"
                          by (metis projection_commute)
                        with \<rho>1v1_subset_\<rho>v_inter_E1 have "\<gamma> \<upharpoonleft> (\<rho>1 \<V>1) = \<beta> \<upharpoonleft> (\<rho>1 \<V>1)"
                          by (metis Int_subset_iff \<gamma>\<rho>v_is_\<beta>\<rho>v projection_subset_elim)
                        thus ?thesis
                          by (metis projection_commute)
                      qed
                      ultimately show ?thesis unfolding Adm_def
                        by auto
                    qed  
                  moreover
                  note FCIA1
                  ultimately obtain \<alpha>1'' \<gamma>
                    where one: "set \<gamma> \<subseteq> N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub>"
                    and two: "\<beta> \<upharpoonleft> E\<^bsub>ES1\<^esub> @ [c] @ \<gamma> @ [v'] @ \<alpha>1'' \<in> Tr\<^bsub>ES1\<^esub>"
                    and three: "\<alpha>1'' \<upharpoonleft> V\<^bsub>\<V>1\<^esub> = \<alpha>1' \<upharpoonleft> V\<^bsub>\<V>1\<^esub>"
                    and four: "\<alpha>1'' \<upharpoonleft> C\<^bsub>\<V>1\<^esub> = []"
                    unfolding FCIA_def
                    by blast

                  (* we choose \<delta>1'' = \<nu> \<upharpoonleft> E\<^bsub>ES1\<^esub> @ \<gamma> *)
                  let ?DELTA1'' = "\<nu> \<upharpoonleft> E\<^bsub>ES1\<^esub> @ \<gamma>" 
                    
                  from two validES1 have "set \<alpha>1'' \<subseteq> E\<^bsub>ES1\<^esub>"
                    by (simp add: ES_valid_def traces_contain_events_def, auto)
                  moreover
                  from one \<nu>E1_empty
                  have "set ?DELTA1'' \<subseteq> N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub> \<union> C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub> \<inter> N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub>"
                    by auto
                  moreover
                  have "\<beta> \<upharpoonleft> E\<^bsub>ES1\<^esub> @ [c] \<upharpoonleft> E\<^bsub>ES1\<^esub> @ ?DELTA1'' @ [v'] \<upharpoonleft> E\<^bsub>ES1\<^esub> @ \<alpha>1'' \<in> Tr\<^bsub>ES1\<^esub>"
                    proof -
                      from c_is_c' c'_in_E1 have "[c] = [c] \<upharpoonleft> E\<^bsub>ES1\<^esub>"
                        by (simp add: projection_def)
                      moreover
                      from v'_in_E1 have "[v'] = [v'] \<upharpoonleft> E\<^bsub>ES1\<^esub>"
                        by (simp add: projection_def)
                      moreover
                      note \<nu>E1_empty two
                      ultimately show ?thesis
                        by auto
                    qed
                  moreover
                  note three four
                  moreover
                  have "?DELTA1'' \<upharpoonleft> (C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub>) = \<delta>2'' \<upharpoonleft> E\<^bsub>ES1\<^esub>"
                    proof -
                      have "\<gamma> \<upharpoonleft> (C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub>) = []"
                        proof -
                          from validV1 have "N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub> \<inter> (C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub>) = {}"
                            by (simp add: isViewOn_def V_valid_def
                              VC_disjoint_def VN_disjoint_def NC_disjoint_def, auto)
                          with projection_intersection_neutral[OF one, of "C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub>"]
                          show ?thesis
                            by (simp add: projection_def)
                        qed
                      with \<delta>2''_is_\<nu> \<nu>E1_empty show ?thesis
                        by (simp add: projection_concatenation_commute)
                    qed
                  ultimately show ?thesis
                    by blast
                next
                  case (Cons x xs) (* we apply the inductive hypothesis in this case *)
                  with c\<delta>2''_is_\<mu>c'\<nu>
                  have \<mu>_is_c_xs: "\<mu> = [c] @ xs" and \<delta>2''_is_xs_c'_\<nu>: "\<delta>2'' = xs @ [c'] @ \<nu>"
                    by auto
                  with n_is_length_\<mu>\<nu>E1 have "n = length ((c # (xs @ \<nu>)) \<upharpoonleft> E\<^bsub>ES1\<^esub>)"
                    by auto
                  moreover
                  note Suc(3,4)
                  moreover
                  have "set ((c # (xs @ \<nu>)) \<upharpoonleft> E\<^bsub>ES1\<^esub>) \<subseteq> C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub>"
                    proof -
                      have res: "c # (xs @ \<nu>) = [c] @ (xs @ \<nu>)" 
                        by auto

                      from Suc(5) c\<delta>2''_is_\<mu>c'\<nu> \<mu>_is_c_xs \<nu>E1_empty
                      show ?thesis
                        by (subst res, simp only: c\<delta>2''_is_\<mu>c'\<nu> 
                          projection_concatenation_commute set_append, auto)
                    qed
                  moreover
                  note Suc(6) 
                  moreover
                  from Suc(7) \<delta>2''_is_xs_c'_\<nu> have "set (xs @ \<nu>) \<subseteq> N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub>"
                    by auto
                  moreover note Suc(8) Suc(1)[of c "xs @ \<nu>" \<beta> \<alpha>1']
                  ultimately obtain \<delta> \<gamma>
                    where one: "set \<delta> \<subseteq> E\<^bsub>ES1\<^esub>"
                    and two: "set \<gamma> \<subseteq> N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub> \<union> C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub> \<inter> N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub>"
                    and three: "\<beta> \<upharpoonleft> E\<^bsub>ES1\<^esub> @ [c] \<upharpoonleft> E\<^bsub>ES1\<^esub> @ \<gamma> @ [v'] \<upharpoonleft> E\<^bsub>ES1\<^esub> @ \<delta> \<in> Tr\<^bsub>ES1\<^esub>"
                    and four: "\<delta> \<upharpoonleft> V\<^bsub>\<V>1\<^esub> = \<alpha>1' \<upharpoonleft> V\<^bsub>\<V>1\<^esub>"
                    and five: "\<delta> \<upharpoonleft> C\<^bsub>\<V>1\<^esub> = []"
                    and six: "\<gamma> \<upharpoonleft> (C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub>) = (xs @ \<nu>) \<upharpoonleft> E\<^bsub>ES1\<^esub>"
                    by blast

                  (* apply FCIA to insert c' after \<gamma> *)
                  let ?BETA = "\<beta> \<upharpoonleft> E\<^bsub>ES1\<^esub> @ [c] \<upharpoonleft> E\<^bsub>ES1\<^esub> @ \<gamma>"

                  note c'_in_Cv1_inter_Upsilon1 v'_in_Vv1_inter_Nabla1
                  moreover
                  from three v'_in_E1 have "?BETA @ [v'] @ \<delta> \<in> Tr\<^bsub>ES1\<^esub>"
                    by (simp add: projection_def)
                  moreover
                  note five 
                  moreover
                  have "Adm \<V>1 \<rho>1 Tr\<^bsub>ES1\<^esub> ?BETA c'"
                    proof -
                      have "?BETA @ [c'] \<in> Tr\<^bsub>ES1\<^esub>"
                        proof -
                          from Suc(7) c'_in_Cv1_inter_Upsilon1 \<delta>2''_is_xs_c'_\<nu>
                          have "c' \<in> C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub> \<inter> N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub>"
                            by auto
                          moreover
                          from validES1 three have "?BETA \<in> Tr\<^bsub>ES1\<^esub>"
                            by (unfold ES_valid_def traces_prefixclosed_def
                              prefixclosed_def prefix_def, auto)
                          moreover
                          note total_ES1_C1_inter_Upsilon1_inter_N2_inter_Delta2
                          ultimately show ?thesis
                            unfolding total_def
                            by blast
                        qed
                      thus ?thesis
                        unfolding Adm_def
                        by blast                        
                    qed
                  moreover
                  note FCIA1
                  ultimately obtain \<alpha>1'' \<delta>'
                    where fcia_one: "set \<delta>' \<subseteq> N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub>"
                    and fcia_two: "?BETA @ [c'] @ \<delta>' @ [v'] @ \<alpha>1'' \<in> Tr\<^bsub>ES1\<^esub>"
                    and fcia_three: "\<alpha>1'' \<upharpoonleft> V\<^bsub>\<V>1\<^esub> = \<delta> \<upharpoonleft> V\<^bsub>\<V>1\<^esub>"
                    and fcia_four:  "\<alpha>1'' \<upharpoonleft> C\<^bsub>\<V>1\<^esub> = []"
                    unfolding FCIA_def
                    by blast
  
                  let ?DELTA1'' = "\<gamma> @ [c'] @ \<delta>'"

                  from fcia_two validES1 have "set \<alpha>1'' \<subseteq> E\<^bsub>ES1\<^esub>"
                    by (simp add: ES_valid_def traces_contain_events_def, auto)
                  moreover
                  have "set ?DELTA1'' \<subseteq> N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub> \<union> C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub> \<inter> N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub>"
                    proof -
                      from Suc(7) c'_in_Cv1_inter_Upsilon1 \<delta>2''_is_xs_c'_\<nu> 
                      have "c' \<in>  C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub> \<inter> N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub>"
                        by auto
                      with two fcia_one show ?thesis
                        by auto
                    qed
                  moreover
                  from fcia_two v'_in_E1 
                  have "\<beta> \<upharpoonleft> E\<^bsub>ES1\<^esub> @ [c] \<upharpoonleft> E\<^bsub>ES1\<^esub> @ ?DELTA1'' @ [v'] \<upharpoonleft> E\<^bsub>ES1\<^esub> @ \<alpha>1'' \<in> Tr\<^bsub>ES1\<^esub>"
                    by (simp add: projection_def)
                  moreover
                  from fcia_three four have "\<alpha>1'' \<upharpoonleft> V\<^bsub>\<V>1\<^esub> = \<alpha>1' \<upharpoonleft> V\<^bsub>\<V>1\<^esub>"
                    by simp
                  moreover
                  note fcia_four
                  moreover             
                  have "?DELTA1'' \<upharpoonleft> (C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub>) = \<delta>2'' \<upharpoonleft> E\<^bsub>ES1\<^esub>"
                    proof -
                      have "\<delta>' \<upharpoonleft> (C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub>) = []"
                        proof -
                          from fcia_one have "\<forall> e \<in> set \<delta>'. e \<in> N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub>"
                            by auto
                          with validV1 have "\<forall> e \<in> set \<delta>'. e \<notin> C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub>"
                            by (simp add: isViewOn_def V_valid_def 
                              VC_disjoint_def VN_disjoint_def NC_disjoint_def, auto)
                          thus ?thesis
                            by (simp add: projection_def)
                        qed
                      with c'_in_E1 c'_in_Cv1_inter_Upsilon1 \<delta>2''_is_xs_c'_\<nu> \<nu>E1_empty six 
                      show ?thesis
                        by (simp only: projection_concatenation_commute projection_def, auto)
                    qed
                  ultimately show ?thesis 
                    by blast     
                qed
          qed
          from this[OF \<beta>v'E1\<alpha>1'_in_Tr1 \<alpha>1'Cv1_empty c\<delta>2''E1_in_Cv1_inter_Upsilon1star 
            c_in_Cv_inter_Upsilon \<delta>2''_in_N2_inter_Delta2star Adm]
          obtain \<alpha>1'' \<delta>1''
            where one: "set \<alpha>1'' \<subseteq> E\<^bsub>ES1\<^esub>"
            and two: "set \<delta>1'' \<subseteq> N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub> \<union> C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub> \<inter> N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub>"
            and three: "\<beta> \<upharpoonleft> E\<^bsub>ES1\<^esub> @ [c] \<upharpoonleft> E\<^bsub>ES1\<^esub> @ \<delta>1'' @ [v'] \<upharpoonleft> E\<^bsub>ES1\<^esub> @ \<alpha>1'' \<in> Tr\<^bsub>ES1\<^esub>            
            \<and> \<alpha>1'' \<upharpoonleft> V\<^bsub>\<V>1\<^esub> = \<alpha>1' \<upharpoonleft> V\<^bsub>\<V>1\<^esub> \<and> \<alpha>1'' \<upharpoonleft> C\<^bsub>\<V>1\<^esub> = []"
            and four: "\<delta>1'' \<upharpoonleft> (C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub>) = \<delta>2'' \<upharpoonleft> E\<^bsub>ES1\<^esub>"
            by blast

          note one two three
          moreover
          have "\<delta>1'' \<upharpoonleft> E\<^bsub>ES2\<^esub> = \<delta>2'' \<upharpoonleft> E\<^bsub>ES1\<^esub>" 
            proof -
              from projection_intersection_neutral[OF two, of "E\<^bsub>ES2\<^esub>"] 
                Nv1_inter_Delta1_inter_E2_empty validV2 
              have "\<delta>1'' \<upharpoonleft> E\<^bsub>ES2\<^esub> = \<delta>1'' \<upharpoonleft> (C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub> \<inter> N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub> \<inter> E\<^bsub>ES2\<^esub>)"
                by (simp only: Int_Un_distrib2, auto)
              moreover
              from validV2 
              have "C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub> \<inter> N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub> \<inter> E\<^bsub>ES2\<^esub> = C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub> \<inter> N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub>"
                by (simp add:isViewOn_def  V_valid_def  VC_disjoint_def 
                  VN_disjoint_def NC_disjoint_def, auto)
              ultimately have "\<delta>1'' \<upharpoonleft> E\<^bsub>ES2\<^esub> = \<delta>1'' \<upharpoonleft> (C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub> \<inter> N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub>)"
                by simp
              hence "\<delta>1'' \<upharpoonleft> E\<^bsub>ES2\<^esub> = \<delta>1'' \<upharpoonleft> (C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub>) \<upharpoonleft> (N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub>)"
                by (simp add: projection_def)
              with four have "\<delta>1'' \<upharpoonleft> E\<^bsub>ES2\<^esub> = \<delta>2'' \<upharpoonleft> E\<^bsub>ES1\<^esub> \<upharpoonleft> (N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub>)"
                by simp
              hence "\<delta>1'' \<upharpoonleft> E\<^bsub>ES2\<^esub> = \<delta>2'' \<upharpoonleft> (N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub>) \<upharpoonleft> E\<^bsub>ES1\<^esub>"
                by (simp only: projection_commute)
              with \<delta>2''_in_N2_inter_Delta2star show ?thesis
                by (simp only: list_subset_iff_projection_neutral)
            qed
          ultimately show ?thesis
              by blast
        next
          assume v'_notin_E1: "v' \<notin> E\<^bsub>ES1\<^esub>"

           have "\<lbrakk> (\<beta> @ [v']) \<upharpoonleft> E\<^bsub>ES1\<^esub> @ \<alpha>1' \<in> Tr\<^bsub>ES1\<^esub> ; 
            \<alpha>1' \<upharpoonleft> C\<^bsub>\<V>1\<^esub> = []; set ((c # \<delta>2'') \<upharpoonleft> E\<^bsub>ES1\<^esub>) \<subseteq> C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub> ; 
             c \<in> C\<^bsub>\<V>\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>\<^esub> ; set \<delta>2'' \<subseteq> N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub>;
            Adm \<V> \<rho> (Tr\<^bsub>(ES1 \<parallel> ES2)\<^esub>) \<beta> c \<rbrakk> 
            \<Longrightarrow> \<exists> \<alpha>1'' \<delta>1''. (set \<alpha>1'' \<subseteq> E\<^bsub>ES1\<^esub> \<and> set \<delta>1'' \<subseteq> N\<^bsub>\<V>1\<^esub> 
             \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub> \<union> C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub> \<inter> N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub>            
             \<and> \<beta> \<upharpoonleft> E\<^bsub>ES1\<^esub> @ [c] \<upharpoonleft> E\<^bsub>ES1\<^esub> @ \<delta>1'' @ [v'] \<upharpoonleft> E\<^bsub>ES1\<^esub> @ \<alpha>1'' \<in> Tr\<^bsub>ES1\<^esub>            
             \<and> \<alpha>1'' \<upharpoonleft> V\<^bsub>\<V>1\<^esub> = \<alpha>1' \<upharpoonleft> V\<^bsub>\<V>1\<^esub> \<and> \<alpha>1'' \<upharpoonleft> C\<^bsub>\<V>1\<^esub> = []
            \<and> \<delta>1'' \<upharpoonleft> E\<^bsub>ES2\<^esub> = \<delta>2'' \<upharpoonleft> E\<^bsub>ES1\<^esub>)"
            proof (induct "length ((c # \<delta>2'') \<upharpoonleft> E\<^bsub>ES1\<^esub>)" arbitrary: \<beta> \<alpha>1' c \<delta>2'')
               case 0

              from 0(2) validES1 have "set \<alpha>1' \<subseteq> E\<^bsub>ES1\<^esub>"
                by (simp add: ES_valid_def traces_contain_events_def, auto)
              moreover
              have "set [] \<subseteq> N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub> \<union> C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub> \<inter> N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub>"
                by auto
              moreover
              have "\<beta> \<upharpoonleft> E\<^bsub>ES1\<^esub> @ [c] \<upharpoonleft> E\<^bsub>ES1\<^esub> @ [] @ [v'] \<upharpoonleft> E\<^bsub>ES1\<^esub> @ \<alpha>1' \<in> Tr\<^bsub>ES1\<^esub>"
                proof -
                  note 0(2)
                  moreover
                  from 0(1) have "c \<notin> E\<^bsub>ES1\<^esub>"
                    by (simp add: projection_def, auto)
                  ultimately show ?thesis
                    by (simp add: projection_concatenation_commute projection_def)
                qed
              moreover
              have "\<alpha>1' \<upharpoonleft> V\<^bsub>\<V>1\<^esub> = \<alpha>1' \<upharpoonleft> V\<^bsub>\<V>1\<^esub>" ..
              moreover
              note 0(3)
              moreover 
              from 0(1) have "[] \<upharpoonleft> E\<^bsub>ES2\<^esub> = \<delta>2'' \<upharpoonleft> E\<^bsub>ES1\<^esub>"
                by (simp add: projection_def, split if_split_asm, auto)
              ultimately show ?case
                by blast
            next
              case (Suc n)

              from projection_split_last[OF Suc(2)] obtain \<mu> c' \<nu>
                where c'_in_E1: "c' \<in> E\<^bsub>ES1\<^esub>"
                and c\<delta>2''_is_\<mu>c'\<nu>: "c # \<delta>2'' = \<mu> @ [c'] @ \<nu>"
                and \<nu>E1_empty: "\<nu> \<upharpoonleft> E\<^bsub>ES1\<^esub> = []"
                and n_is_length_\<mu>\<nu>E1: "n = length ((\<mu> @ \<nu>) \<upharpoonleft> E\<^bsub>ES1\<^esub>)"
                by blast

              from Suc(5) c'_in_E1 c\<delta>2''_is_\<mu>c'\<nu> have "set (\<mu> \<upharpoonleft> E\<^bsub>ES1\<^esub> @ [c']) \<subseteq> C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub>"
                by (simp only: c\<delta>2''_is_\<mu>c'\<nu> projection_concatenation_commute projection_def, auto)
              hence c'_in_Cv1_inter_Upsilon1: "c' \<in> C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub>"
                by auto
              hence c'_in_Cv1: "c' \<in> C\<^bsub>\<V>1\<^esub>" and c'_in_Upsilon1: "c' \<in> \<Upsilon>\<^bsub>\<Gamma>1\<^esub>"
                by auto
              with validV1 have c'_in_E1: "c' \<in> E\<^bsub>ES1\<^esub>"
                by (simp add:isViewOn_def V_valid_def VC_disjoint_def 
                  VN_disjoint_def NC_disjoint_def, auto)

              show ?case
                proof (cases \<mu>)
                  case Nil (* we just apply BSIA in this case *)
                  with c\<delta>2''_is_\<mu>c'\<nu> have c_is_c': "c = c'" and \<delta>2''_is_\<nu>: "\<delta>2'' = \<nu>"
                    by auto
                  with c'_in_Cv1_inter_Upsilon1 have "c \<in> C\<^bsub>\<V>1\<^esub>"
                    by simp
                  moreover
                  from v'_notin_E1 Suc(3) have "(\<beta> \<upharpoonleft> E\<^bsub>ES1\<^esub>) @ \<alpha>1' \<in> Tr\<^bsub>ES1\<^esub>"
                    by (simp add: projection_concatenation_commute projection_def)
                  moreover
                  note Suc(4)
                  moreover
                  have "Adm \<V>1 \<rho>1 Tr\<^bsub>ES1\<^esub> (\<beta> \<upharpoonleft> E\<^bsub>ES1\<^esub>) c"
                     proof -
                      from Suc(8) obtain \<gamma>
                        where \<gamma>\<rho>v_is_\<beta>\<rho>v: "\<gamma> \<upharpoonleft> (\<rho> \<V>) = \<beta> \<upharpoonleft> (\<rho> \<V>)"
                        and \<gamma>c_in_Tr: "(\<gamma> @ [c]) \<in> Tr\<^bsub>(ES1 \<parallel> ES2)\<^esub>"
                        unfolding Adm_def
                        by auto

                      from c_is_c' c'_in_E1 \<gamma>c_in_Tr have "(\<gamma> \<upharpoonleft> E\<^bsub>ES1\<^esub>) @ [c] \<in> Tr\<^bsub>ES1\<^esub>"
                        by (simp add: projection_def composeES_def)
                      moreover
                      have "\<gamma> \<upharpoonleft> E\<^bsub>ES1\<^esub> \<upharpoonleft> (\<rho>1 \<V>1) = \<beta> \<upharpoonleft> E\<^bsub>ES1\<^esub> \<upharpoonleft> (\<rho>1 \<V>1)"
                      proof -
                        from \<gamma>\<rho>v_is_\<beta>\<rho>v have "\<gamma> \<upharpoonleft> E\<^bsub>ES1\<^esub> \<upharpoonleft> (\<rho> \<V>) = \<beta> \<upharpoonleft> E\<^bsub>ES1\<^esub> \<upharpoonleft> (\<rho> \<V>)"
                          by (metis projection_commute)
                        with \<rho>1v1_subset_\<rho>v_inter_E1 have "\<gamma> \<upharpoonleft> (\<rho>1 \<V>1) = \<beta> \<upharpoonleft> (\<rho>1 \<V>1)"
                          by (metis Int_subset_iff \<gamma>\<rho>v_is_\<beta>\<rho>v projection_subset_elim)
                        thus ?thesis
                          by (metis projection_commute)
                      qed
                      ultimately show ?thesis unfolding Adm_def
                        by auto
                    qed  
                  moreover
                  note BSIA1
                  ultimately obtain \<alpha>1''
                    where one: "(\<beta> \<upharpoonleft> E\<^bsub>ES1\<^esub>) @ [c] @ \<alpha>1'' \<in> Tr\<^bsub>ES1\<^esub>"
                    and two: "\<alpha>1'' \<upharpoonleft> V\<^bsub>\<V>1\<^esub> = \<alpha>1' \<upharpoonleft> V\<^bsub>\<V>1\<^esub>"
                    and three: "\<alpha>1'' \<upharpoonleft> C\<^bsub>\<V>1\<^esub> = []"
                    unfolding BSIA_def
                    by blast

                  let ?DELTA1'' = "\<nu> \<upharpoonleft> E\<^bsub>ES1\<^esub>"

                  from one validES1 have "set \<alpha>1'' \<subseteq> E\<^bsub>ES1\<^esub>"
                    by (simp add: ES_valid_def traces_contain_events_def, auto)
                  moreover
                  from \<nu>E1_empty
                  have "set ?DELTA1'' \<subseteq> N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub> \<union> C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub> \<inter> N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub>"
                    by simp
                  moreover
                  from c_is_c' c'_in_E1 one v'_notin_E1 \<nu>E1_empty
                  have "(\<beta> \<upharpoonleft> E\<^bsub>ES1\<^esub>) @ [c] \<upharpoonleft> E\<^bsub>ES1\<^esub> @ ?DELTA1'' @ [v'] \<upharpoonleft> E\<^bsub>ES1\<^esub> @ \<alpha>1'' \<in> Tr\<^bsub>ES1\<^esub>"
                    by (simp add: projection_def)
                  moreover
                  note two three
                  moreover
                  from \<nu>E1_empty \<delta>2''_is_\<nu> have "?DELTA1'' \<upharpoonleft> E\<^bsub>ES2\<^esub> = \<delta>2'' \<upharpoonleft> E\<^bsub>ES1\<^esub>"
                    by (simp add: projection_def)
                  ultimately show ?thesis
                    by blast
                next
                  case (Cons x xs) (* apply inductive hypothesis, then BSIA *)
                  with c\<delta>2''_is_\<mu>c'\<nu>
                  have \<mu>_is_c_xs: "\<mu> = [c] @ xs" and \<delta>2''_is_xs_c'_\<nu>: "\<delta>2'' = xs @ [c'] @ \<nu>"
                    by auto
                  with n_is_length_\<mu>\<nu>E1 have "n = length ((c # (xs @ \<nu>)) \<upharpoonleft> E\<^bsub>ES1\<^esub>)"
                    by auto
                  moreover
                  note Suc(3,4)
                  moreover
                  have "set ((c # (xs @ \<nu>)) \<upharpoonleft> E\<^bsub>ES1\<^esub>) \<subseteq> C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub>"
                    proof -
                      have res: "c # (xs @ \<nu>) = [c] @ (xs @ \<nu>)" 
                        by auto

                      from Suc(5) c\<delta>2''_is_\<mu>c'\<nu> \<mu>_is_c_xs \<nu>E1_empty
                      show ?thesis
                        by (subst res, simp only: c\<delta>2''_is_\<mu>c'\<nu> projection_concatenation_commute 
                          set_append, auto)
                    qed
                  moreover
                  note Suc(6) 
                  moreover
                  from Suc(7) \<delta>2''_is_xs_c'_\<nu> have "set (xs @ \<nu>) \<subseteq> N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub>"
                    by auto
                  moreover note Suc(8) Suc(1)[of c "xs @ \<nu>" \<beta> \<alpha>1']
                  ultimately obtain \<delta> \<gamma>
                    where one: "set \<delta> \<subseteq> E\<^bsub>ES1\<^esub>"
                    and two: "set \<gamma> \<subseteq> N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub> \<union> C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub> \<inter> N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub>"
                    and three: "\<beta> \<upharpoonleft> E\<^bsub>ES1\<^esub> @ [c] \<upharpoonleft> E\<^bsub>ES1\<^esub> @ \<gamma> @ [v'] \<upharpoonleft> E\<^bsub>ES1\<^esub> @ \<delta> \<in> Tr\<^bsub>ES1\<^esub>"
                    and four: "\<delta> \<upharpoonleft> V\<^bsub>\<V>1\<^esub> = \<alpha>1' \<upharpoonleft> V\<^bsub>\<V>1\<^esub>"
                    and five: "\<delta> \<upharpoonleft> C\<^bsub>\<V>1\<^esub> = []"
                    and six: "\<gamma> \<upharpoonleft> E\<^bsub>ES2\<^esub> = (xs @ \<nu>) \<upharpoonleft> E\<^bsub>ES1\<^esub>"
                    by blast
                  
                   (* apply BSIA to insert c' after \<gamma> *)
                  let ?BETA = "\<beta> \<upharpoonleft> E\<^bsub>ES1\<^esub> @ [c] \<upharpoonleft> E\<^bsub>ES1\<^esub> @ \<gamma>"

                  from c'_in_Cv1_inter_Upsilon1 have "c' \<in> C\<^bsub>\<V>1\<^esub>"
                    by auto
                  moreover
                  from three v'_notin_E1 have "?BETA @ \<delta> \<in> Tr\<^bsub>ES1\<^esub>"
                    by (simp add: projection_def)
                  moreover
                  note five 
                  moreover
                  have "Adm \<V>1 \<rho>1 Tr\<^bsub>ES1\<^esub> ?BETA c'"
                    proof -
                      have "?BETA @ [c'] \<in> Tr\<^bsub>ES1\<^esub>"
                        proof -
                          from Suc(7) c'_in_Cv1_inter_Upsilon1 \<delta>2''_is_xs_c'_\<nu>
                          have "c' \<in> C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub> \<inter> N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub>"
                            by auto
                          moreover
                          from validES1 three have "?BETA \<in> Tr\<^bsub>ES1\<^esub>"
                            by (unfold ES_valid_def traces_prefixclosed_def
                              prefixclosed_def prefix_def, auto)
                          moreover
                          note total_ES1_C1_inter_Upsilon1_inter_N2_inter_Delta2
                          ultimately show ?thesis
                            unfolding total_def
                            by blast
                        qed
                      thus ?thesis
                        unfolding Adm_def
                        by blast                      
                    qed
                  moreover
                  note BSIA1
                  ultimately obtain \<alpha>1''
                    where bsia_one: "?BETA @ [c'] @ \<alpha>1'' \<in> Tr\<^bsub>ES1\<^esub>"
                    and bsia_two: "\<alpha>1'' \<upharpoonleft> V\<^bsub>\<V>1\<^esub> = \<delta> \<upharpoonleft> V\<^bsub>\<V>1\<^esub>"
                    and bsia_three:  "\<alpha>1'' \<upharpoonleft> C\<^bsub>\<V>1\<^esub> = []"
                    unfolding BSIA_def
                    by blast
  
                  let ?DELTA1'' = "\<gamma> @ [c']"

                  from bsia_one validES1 have "set \<alpha>1'' \<subseteq> E\<^bsub>ES1\<^esub>"
                    by (simp add: ES_valid_def traces_contain_events_def, auto)
                  moreover
                  have "set ?DELTA1'' \<subseteq> N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub> \<union> C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub> \<inter> N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub>"
                    proof -
                      from Suc(7) c'_in_Cv1_inter_Upsilon1 \<delta>2''_is_xs_c'_\<nu> 
                      have "c' \<in>  C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub> \<inter> N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub>"
                        by auto
                      with two show ?thesis
                        by auto
                    qed
                  moreover
                  from bsia_one v'_notin_E1 
                  have "\<beta> \<upharpoonleft> E\<^bsub>ES1\<^esub> @ [c] \<upharpoonleft> E\<^bsub>ES1\<^esub> @ ?DELTA1'' @ [v'] \<upharpoonleft> E\<^bsub>ES1\<^esub> @ \<alpha>1'' \<in> Tr\<^bsub>ES1\<^esub>"
                    by (simp add: projection_def)
                  moreover
                  from bsia_two four have "\<alpha>1'' \<upharpoonleft> V\<^bsub>\<V>1\<^esub> = \<alpha>1' \<upharpoonleft> V\<^bsub>\<V>1\<^esub>"
                    by simp
                  moreover
                  note bsia_three
                  moreover             
                  have "?DELTA1'' \<upharpoonleft> E\<^bsub>ES2\<^esub> = \<delta>2'' \<upharpoonleft> E\<^bsub>ES1\<^esub>"
                    proof -
                      from validV2 Suc(7) \<delta>2''_is_xs_c'_\<nu> have "c' \<in> E\<^bsub>ES2\<^esub>"
                        by (simp add: isViewOn_def V_valid_def
                          VC_disjoint_def VN_disjoint_def NC_disjoint_def, auto)
                      with c'_in_E1 c'_in_Cv1_inter_Upsilon1 \<delta>2''_is_xs_c'_\<nu> \<nu>E1_empty six 
                      show ?thesis
                        by (simp only: projection_concatenation_commute projection_def, auto)
                    qed
                  ultimately show ?thesis 
                    by blast     
                qed
            qed
          from this[OF \<beta>v'E1\<alpha>1'_in_Tr1 \<alpha>1'Cv1_empty c\<delta>2''E1_in_Cv1_inter_Upsilon1star 
            c_in_Cv_inter_Upsilon \<delta>2''_in_N2_inter_Delta2star Adm]
          show ?thesis 
            by blast
        qed
      then obtain \<alpha>1'' \<delta>1''
        where \<alpha>1''_in_E1star: "set \<alpha>1'' \<subseteq> E\<^bsub>ES1\<^esub>"
        and \<delta>1''_in_N1_inter_Delta1star:"set \<delta>1'' \<subseteq> N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub> \<union> C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub> \<inter> N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub>"
        and \<beta>E1_cE1_\<delta>1''_v'E1_\<alpha>1''_in_Tr1: 
          "\<beta> \<upharpoonleft> E\<^bsub>ES1\<^esub> @ [c] \<upharpoonleft> E\<^bsub>ES1\<^esub> @ \<delta>1'' @ [v'] \<upharpoonleft> E\<^bsub>ES1\<^esub> @ \<alpha>1'' \<in> Tr\<^bsub>ES1\<^esub>"
        and \<alpha>1''Vv1_is_\<alpha>1'Vv1: "\<alpha>1'' \<upharpoonleft> V\<^bsub>\<V>1\<^esub> = \<alpha>1' \<upharpoonleft> V\<^bsub>\<V>1\<^esub>"
        and \<alpha>1''Cv1_empty: "\<alpha>1'' \<upharpoonleft> C\<^bsub>\<V>1\<^esub> = []"
        and \<delta>1''E2_is_\<delta>2''E1: "\<delta>1'' \<upharpoonleft> E\<^bsub>ES2\<^esub> = \<delta>2'' \<upharpoonleft> E\<^bsub>ES1\<^esub>"
        by blast

      from \<beta>E1_cE1_\<delta>1''_v'E1_\<alpha>1''_in_Tr1 \<beta>E2_cE2_\<delta>2''_v'E2_\<alpha>2''_in_Tr2 validES1 
        validES2
      have \<delta>1''_in_E1star: "set \<delta>1'' \<subseteq> E\<^bsub>ES1\<^esub>" and \<delta>2''_in_E2star: "set \<delta>2'' \<subseteq> E\<^bsub>ES2\<^esub>"
        by (simp_all add: ES_valid_def traces_contain_events_def, auto)
      with \<delta>1''E2_is_\<delta>2''E1 merge_property[of \<delta>1'' "E\<^bsub>ES1\<^esub>" \<delta>2'' "E\<^bsub>ES2\<^esub>"] obtain \<delta>'
        where \<delta>'E1_is_\<delta>1'': "\<delta>' \<upharpoonleft> E\<^bsub>ES1\<^esub> = \<delta>1''"
        and \<delta>'E2_is_\<delta>2'': "\<delta>' \<upharpoonleft> E\<^bsub>ES2\<^esub> = \<delta>2''"
        and \<delta>'_contains_only_\<delta>1''_\<delta>2''_events: "set \<delta>' \<subseteq> set \<delta>1'' \<union> set \<delta>2''"
        unfolding Let_def
        by auto

      let ?TAU = "\<beta> @ [c] @ \<delta>' @ [v']"
      let ?LAMBDA = "\<alpha> \<upharpoonleft> V\<^bsub>\<V>\<^esub>"
      let ?T1 = \<alpha>1''
      let ?T2 = \<alpha>2''

     (* apply the generalized zipping lemma *)
     have "?TAU \<in> Tr\<^bsub>(ES1 \<parallel> ES2)\<^esub>"
        proof -
          from \<beta>E1_cE1_\<delta>1''_v'E1_\<alpha>1''_in_Tr1 \<delta>'E1_is_\<delta>1'' validES1
          have "\<beta> \<upharpoonleft> E\<^bsub>ES1\<^esub> @ [c] \<upharpoonleft> E\<^bsub>ES1\<^esub> @ \<delta>' \<upharpoonleft> E\<^bsub>ES1\<^esub> @ [v'] \<upharpoonleft> E\<^bsub>ES1\<^esub> \<in> Tr\<^bsub>ES1\<^esub>"
            by (simp add: ES_valid_def traces_prefixclosed_def
              prefixclosed_def prefix_def)
          hence "(\<beta> @ [c] @ \<delta>' @ [v']) \<upharpoonleft> E\<^bsub>ES1\<^esub> \<in> Tr\<^bsub>ES1\<^esub>"
            by (simp add: projection_def, auto)
          moreover          
          from \<beta>E2_cE2_\<delta>2''_v'E2_\<alpha>2''_in_Tr2 \<delta>'E2_is_\<delta>2'' validES2 
          have "\<beta> \<upharpoonleft> E\<^bsub>ES2\<^esub> @ [c] \<upharpoonleft> E\<^bsub>ES2\<^esub> @ \<delta>' \<upharpoonleft> E\<^bsub>ES2\<^esub> @ [v'] \<upharpoonleft> E\<^bsub>ES2\<^esub> \<in> Tr\<^bsub>ES2\<^esub>"
            by (simp add: ES_valid_def traces_prefixclosed_def
              prefixclosed_def prefix_def)
          hence "(\<beta> @ [c] @ \<delta>' @ [v']) \<upharpoonleft> E\<^bsub>ES2\<^esub> \<in> Tr\<^bsub>ES2\<^esub>"
            by (simp add: projection_def, auto)
          moreover
          from \<beta>v'\<alpha>_in_Tr c_in_Cv_inter_Upsilon VIsViewOnE \<delta>'_contains_only_\<delta>1''_\<delta>2''_events 
            \<delta>1''_in_E1star \<delta>2''_in_E2star
          have "set (\<beta> @ [c] @ \<delta>' @ [v']) \<subseteq> E\<^bsub>ES1\<^esub> \<union> E\<^bsub>ES2\<^esub>"
            unfolding composeES_def isViewOn_def V_valid_def 
              VC_disjoint_def VN_disjoint_def NC_disjoint_def
            by auto
          ultimately show ?thesis
            unfolding composeES_def
            by auto
        qed 
      hence "set ?TAU \<subseteq> E\<^bsub>(ES1 \<parallel> ES2)\<^esub>"
        unfolding composeES_def
        by auto
      moreover
      have "set ?LAMBDA \<subseteq> V\<^bsub>\<V>\<^esub>"
        by (simp add: projection_def, auto)
      moreover
      note \<alpha>1''_in_E1star \<alpha>2''_in_E2star
      moreover
      from \<beta>E1_cE1_\<delta>1''_v'E1_\<alpha>1''_in_Tr1 \<delta>'E1_is_\<delta>1'' 
      have "?TAU \<upharpoonleft> E\<^bsub>ES1\<^esub> @ ?T1 \<in> Tr\<^bsub>ES1\<^esub>"
        by (simp only: projection_concatenation_commute, auto)
      moreover
      from \<beta>E2_cE2_\<delta>2''_v'E2_\<alpha>2''_in_Tr2 \<delta>'E2_is_\<delta>2'' 
      have "?TAU \<upharpoonleft> E\<^bsub>ES2\<^esub> @ ?T2 \<in> Tr\<^bsub>ES2\<^esub>"
        by (simp only: projection_concatenation_commute, auto)
      moreover
      have "?LAMBDA \<upharpoonleft> E\<^bsub>ES1\<^esub> = ?T1 \<upharpoonleft> V\<^bsub>\<V>\<^esub>"
        proof -
          from propSepViews have "?LAMBDA \<upharpoonleft> E\<^bsub>ES1\<^esub> = \<alpha> \<upharpoonleft> V\<^bsub>\<V>1\<^esub>"
            unfolding properSeparationOfViews_def by (simp only: projection_sequence)
          moreover
          from \<alpha>1''_in_E1star propSepViews 
          have "?T1 \<upharpoonleft> V\<^bsub>\<V>\<^esub> = ?T1 \<upharpoonleft> V\<^bsub>\<V>1\<^esub>"
            unfolding properSeparationOfViews_def
            by (metis Int_commute projection_intersection_neutral)
          moreover
          note \<alpha>1'Vv1_is_\<alpha>Vv1 \<alpha>1''Vv1_is_\<alpha>1'Vv1
          ultimately show ?thesis
            by simp
        qed
      moreover
      have "?LAMBDA \<upharpoonleft> E\<^bsub>ES2\<^esub> = ?T2 \<upharpoonleft> V\<^bsub>\<V>\<^esub>"
        proof -
          from propSepViews have "?LAMBDA \<upharpoonleft> E\<^bsub>ES2\<^esub> = \<alpha> \<upharpoonleft> V\<^bsub>\<V>2\<^esub>"
            unfolding properSeparationOfViews_def by (simp only: projection_sequence)
          moreover
          from \<alpha>2''_in_E2star propSepViews have "?T2 \<upharpoonleft> V\<^bsub>\<V>\<^esub> = ?T2 \<upharpoonleft> V\<^bsub>\<V>2\<^esub>"
            unfolding properSeparationOfViews_def
            by (metis Int_commute projection_intersection_neutral)
          moreover
          note \<alpha>2'Vv2_is_\<alpha>Vv2 \<alpha>2''Vv2_is_\<alpha>2'Vv2
          ultimately show ?thesis
            by simp
        qed
      moreover
      note \<alpha>1''Cv1_empty \<alpha>2''Cv2_empty generalized_zipping_lemma
      ultimately obtain t (* show that the conclusion of FCIA holds *)
        where "?TAU @ t \<in> Tr\<^bsub>(ES1 \<parallel> ES2)\<^esub>"
        and  "t \<upharpoonleft> V\<^bsub>\<V>\<^esub> = ?LAMBDA"
        and "t \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []"
        by blast
      moreover
      have "set \<delta>' \<subseteq> N\<^bsub>\<V>\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>\<^esub>"
        proof -
          from \<delta>'_contains_only_\<delta>1''_\<delta>2''_events \<delta>1''_in_N1_inter_Delta1star 
            \<delta>2''_in_N2_inter_Delta2star
          have "set \<delta>' \<subseteq> N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub> \<union> N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub>"
            by auto
          with Delta1_N1_Delta2_N2_subset_Delta Nv1_union_Nv2_subsetof_Nv 
          show ?thesis
            by auto
        qed
      ultimately have "\<exists>\<alpha>' \<gamma>'. (set \<gamma>' \<subseteq> N\<^bsub>\<V>\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>\<^esub> \<and> \<beta> @ [c] @ \<gamma>' @ [v'] @ \<alpha>' \<in> Tr\<^bsub>(ES1 \<parallel> ES2)\<^esub> 
        \<and> \<alpha>' \<upharpoonleft> V\<^bsub>\<V>\<^esub> = \<alpha> \<upharpoonleft> V\<^bsub>\<V>\<^esub> \<and> \<alpha>' \<upharpoonleft> C\<^bsub>\<V>\<^esub> = [])"
        by (simp only: append_assoc, blast)
    }
    moreover {
      assume Nv2_inter_Delta2_inter_E1_empty: "N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub> \<inter> E\<^bsub>ES1\<^esub> = {}" 
        and  Nv1_inter_Delta1_inter_E2_subsetof_Upsilon2: "N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub> \<inter> E\<^bsub>ES2\<^esub> \<subseteq> \<Upsilon>\<^bsub>\<Gamma>2\<^esub>"

      let ?ALPHA1''_DELTA1'' = "\<exists> \<alpha>1'' \<delta>1''. (
        set \<alpha>1'' \<subseteq> E\<^bsub>ES1\<^esub> \<and> set \<delta>1'' \<subseteq> N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub> 
        \<and> \<beta> \<upharpoonleft> E\<^bsub>ES1\<^esub> @ [c] \<upharpoonleft> E\<^bsub>ES1\<^esub> @ \<delta>1'' @ [v'] \<upharpoonleft> E\<^bsub>ES1\<^esub> @ \<alpha>1'' \<in> Tr\<^bsub>ES1\<^esub> 
        \<and> \<alpha>1'' \<upharpoonleft> V\<^bsub>\<V>1\<^esub> = \<alpha>1' \<upharpoonleft> V\<^bsub>\<V>1\<^esub> \<and> \<alpha>1'' \<upharpoonleft> C\<^bsub>\<V>1\<^esub> = [])"

      from c_in_Cv_inter_Upsilon v'_in_Vv_inter_Nabla validV1
      have "c \<notin> E\<^bsub>ES1\<^esub> \<or> (c \<in> E\<^bsub>ES1\<^esub> \<and> v' \<notin> E\<^bsub>ES1\<^esub>) \<or> (c \<in> E\<^bsub>ES1\<^esub> \<and> v' \<in> E\<^bsub>ES1\<^esub>)"
        by (simp add: isViewOn_def V_valid_def VC_disjoint_def 
          VN_disjoint_def NC_disjoint_def)
      moreover {
        assume c_notin_E1: "c \<notin> E\<^bsub>ES1\<^esub>"

        from validES1 \<beta>v'E1\<alpha>1'_in_Tr1 have "set \<alpha>1' \<subseteq> E\<^bsub>ES1\<^esub>"
          by (simp add: ES_valid_def traces_contain_events_def, auto)
        moreover 
        have "set [] \<subseteq> N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub>"
          by auto
        moreover 
        from \<beta>v'E1\<alpha>1'_in_Tr1 c_notin_E1 
        have "\<beta> \<upharpoonleft> E\<^bsub>ES1\<^esub> @ [c] \<upharpoonleft> E\<^bsub>ES1\<^esub> @ [] @ [v'] \<upharpoonleft> E\<^bsub>ES1\<^esub> @ \<alpha>1' \<in> Tr\<^bsub>ES1\<^esub>"
          by (simp add: projection_def)
        moreover
        have "\<alpha>1' \<upharpoonleft> V\<^bsub>\<V>1\<^esub> = \<alpha>1' \<upharpoonleft> V\<^bsub>\<V>1\<^esub>" ..
        moreover 
        note \<alpha>1'Cv1_empty
        ultimately have ?ALPHA1''_DELTA1''
          by blast
      }
      moreover {
        assume c_in_E1: "c \<in> E\<^bsub>ES1\<^esub>"
          and  v'_notin_E1: "v' \<notin> E\<^bsub>ES1\<^esub>"

        from c_in_E1 c_in_Cv_inter_Upsilon propSepViews
          Upsilon_inter_E1_subset_Upsilon1
        have c_in_Cv1_inter_Upsilon1: "c \<in> C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub>"
          unfolding properSeparationOfViews_def by auto
        hence "c \<in> C\<^bsub>\<V>1\<^esub>"
          by auto
        moreover
        from \<beta>v'E1\<alpha>1'_in_Tr1 v'_notin_E1 have "\<beta> \<upharpoonleft> E\<^bsub>ES1\<^esub> @ \<alpha>1' \<in> Tr\<^bsub>ES1\<^esub>"
          by (simp add: projection_def)
        moreover
        note \<alpha>1'Cv1_empty
        moreover
        have "Adm \<V>1 \<rho>1 Tr\<^bsub>ES1\<^esub> (\<beta> \<upharpoonleft> E\<^bsub>ES1\<^esub>) c"
        proof -
          from Adm obtain \<gamma>
            where \<gamma>\<rho>v_is_\<beta>\<rho>v: "\<gamma> \<upharpoonleft> (\<rho> \<V>) = \<beta> \<upharpoonleft> (\<rho> \<V>)"
            and \<gamma>c_in_Tr: "(\<gamma> @ [c]) \<in> Tr\<^bsub>(ES1 \<parallel> ES2)\<^esub>"
            unfolding Adm_def
            by auto

          from c_in_E1 \<gamma>c_in_Tr have "(\<gamma> \<upharpoonleft> E\<^bsub>ES1\<^esub>) @ [c] \<in> Tr\<^bsub>ES1\<^esub>"
            by (simp add: projection_def composeES_def)
          moreover
          have "\<gamma> \<upharpoonleft> E\<^bsub>ES1\<^esub> \<upharpoonleft> (\<rho>1 \<V>1) = \<beta> \<upharpoonleft> E\<^bsub>ES1\<^esub> \<upharpoonleft> (\<rho>1 \<V>1)"
          proof -
            from \<gamma>\<rho>v_is_\<beta>\<rho>v have "\<gamma> \<upharpoonleft> E\<^bsub>ES1\<^esub> \<upharpoonleft> (\<rho> \<V>) = \<beta> \<upharpoonleft> E\<^bsub>ES1\<^esub> \<upharpoonleft> (\<rho> \<V>)"
              by (metis projection_commute)
            with \<rho>1v1_subset_\<rho>v_inter_E1 have "\<gamma> \<upharpoonleft> (\<rho>1 \<V>1) = \<beta> \<upharpoonleft> (\<rho>1 \<V>1)"
              by (metis Int_subset_iff \<gamma>\<rho>v_is_\<beta>\<rho>v projection_subset_elim)
            thus ?thesis
              by (metis projection_commute)
          qed
          ultimately show ?thesis unfolding Adm_def
            by auto
        qed  
        moreover 
        note BSIA1
        ultimately obtain  \<alpha>1''
          where one: "\<beta> \<upharpoonleft> E\<^bsub>ES1\<^esub> @ [c] @ \<alpha>1'' \<in> Tr\<^bsub>ES1\<^esub>"
          and two:   "\<alpha>1'' \<upharpoonleft> V\<^bsub>\<V>1\<^esub> = \<alpha>1' \<upharpoonleft> V\<^bsub>\<V>1\<^esub>"
          and three: "\<alpha>1'' \<upharpoonleft> C\<^bsub>\<V>1\<^esub> = []"
          unfolding BSIA_def
          by blast

        from one validES1 have "set \<alpha>1'' \<subseteq> E\<^bsub>ES1\<^esub>"
          by (simp add: ES_valid_def traces_contain_events_def, auto)
        moreover
        have "set [] \<subseteq> N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub>"
          by auto
        moreover
        from one c_in_E1 v'_notin_E1 
        have "\<beta> \<upharpoonleft> E\<^bsub>ES1\<^esub> @ [c] \<upharpoonleft> E\<^bsub>ES1\<^esub> @ [] @ [v'] \<upharpoonleft> E\<^bsub>ES1\<^esub> @ \<alpha>1'' \<in> Tr\<^bsub>ES1\<^esub>"
          by (simp add: projection_def)
        moreover 
        note two three
        ultimately have ?ALPHA1''_DELTA1''
          by blast
      }
      moreover {
        assume c_in_E1: "c \<in> E\<^bsub>ES1\<^esub>"
          and  v'_in_E1: "v' \<in> E\<^bsub>ES1\<^esub>"

        from c_in_E1 c_in_Cv_inter_Upsilon propSepViews
          Upsilon_inter_E1_subset_Upsilon1
        have c_in_Cv1_inter_Upsilon1: "c \<in> C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub>"
          unfolding properSeparationOfViews_def by auto
        moreover
        from v'_in_E1 propSepViews v'_in_Vv_inter_Nabla 
          Nabla_inter_E1_subset_Nabla1
        have "v' \<in> V\<^bsub>\<V>1\<^esub> \<inter> Nabla \<Gamma>1"
          unfolding properSeparationOfViews_def by auto
        moreover
        from v'_in_E1  \<beta>v'E1\<alpha>1'_in_Tr1 have "\<beta> \<upharpoonleft> E\<^bsub>ES1\<^esub> @ [v'] @ \<alpha>1' \<in> Tr\<^bsub>ES1\<^esub>"
          by (simp add: projection_def)
        moreover
        note \<alpha>1'Cv1_empty 
        moreover
        have "Adm \<V>1 \<rho>1 Tr\<^bsub>ES1\<^esub> (\<beta> \<upharpoonleft> E\<^bsub>ES1\<^esub>) c"
        proof -
          from Adm obtain \<gamma>
            where \<gamma>\<rho>v_is_\<beta>\<rho>v: "\<gamma> \<upharpoonleft> (\<rho> \<V>) = \<beta> \<upharpoonleft> (\<rho> \<V>)"
            and \<gamma>c_in_Tr: "(\<gamma> @ [c]) \<in> Tr\<^bsub>(ES1 \<parallel> ES2)\<^esub>"
            unfolding Adm_def
            by auto

          from c_in_E1 \<gamma>c_in_Tr have "(\<gamma> \<upharpoonleft> E\<^bsub>ES1\<^esub>) @ [c] \<in> Tr\<^bsub>ES1\<^esub>"
            by (simp add: projection_def composeES_def)
          moreover
          have "\<gamma> \<upharpoonleft> E\<^bsub>ES1\<^esub> \<upharpoonleft> (\<rho>1 \<V>1) = \<beta> \<upharpoonleft> E\<^bsub>ES1\<^esub> \<upharpoonleft> (\<rho>1 \<V>1)"
          proof -
            from \<gamma>\<rho>v_is_\<beta>\<rho>v have "\<gamma> \<upharpoonleft> E\<^bsub>ES1\<^esub> \<upharpoonleft> (\<rho> \<V>) = \<beta> \<upharpoonleft> E\<^bsub>ES1\<^esub> \<upharpoonleft> (\<rho> \<V>)"
              by (metis projection_commute)
            with \<rho>1v1_subset_\<rho>v_inter_E1 have "\<gamma> \<upharpoonleft> (\<rho>1 \<V>1) = \<beta> \<upharpoonleft> (\<rho>1 \<V>1)"
              by (metis Int_subset_iff \<gamma>\<rho>v_is_\<beta>\<rho>v projection_subset_elim)
            thus ?thesis
              by (metis projection_commute)
          qed
          ultimately show ?thesis unfolding Adm_def
            by auto
        qed  
        moreover
        note FCIA1
        ultimately obtain \<alpha>1'' \<delta>1''
          where one: "set \<delta>1'' \<subseteq> N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub>"
          and two: "\<beta> \<upharpoonleft> E\<^bsub>ES1\<^esub> @ [c] @ \<delta>1'' @ [v'] @ \<alpha>1'' \<in> Tr\<^bsub>ES1\<^esub>"
          and three: "\<alpha>1'' \<upharpoonleft> V\<^bsub>\<V>1\<^esub> = \<alpha>1' \<upharpoonleft> V\<^bsub>\<V>1\<^esub>"
          and four: "\<alpha>1'' \<upharpoonleft> C\<^bsub>\<V>1\<^esub> = []"
          unfolding FCIA_def
          by blast

        from two validES1 have "set \<alpha>1'' \<subseteq> E\<^bsub>ES1\<^esub>"
          by (simp add: ES_valid_def traces_contain_events_def, auto)
        moreover
        note one
        moreover
        from two c_in_E1 v'_in_E1 
        have "\<beta> \<upharpoonleft> E\<^bsub>ES1\<^esub> @ [c] \<upharpoonleft> E\<^bsub>ES1\<^esub> @ \<delta>1'' @ [v'] \<upharpoonleft> E\<^bsub>ES1\<^esub> @ \<alpha>1'' \<in> Tr\<^bsub>ES1\<^esub>"
          by (simp add: projection_def)
        moreover
        note three four
        ultimately have ?ALPHA1''_DELTA1''
          by blast
      }
      ultimately obtain \<alpha>1'' \<delta>1''
        where \<alpha>1''_in_E1star: "set \<alpha>1'' \<subseteq> E\<^bsub>ES1\<^esub>"
        and \<delta>1''_in_N1_inter_Delta1star:"set \<delta>1'' \<subseteq> N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub>"
        and \<beta>E1_cE1_\<delta>1''_v'E1_\<alpha>1''_in_Tr1: 
          "\<beta> \<upharpoonleft> E\<^bsub>ES1\<^esub> @ [c] \<upharpoonleft> E\<^bsub>ES1\<^esub> @ \<delta>1'' @ [v'] \<upharpoonleft> E\<^bsub>ES1\<^esub> @ \<alpha>1'' \<in> Tr\<^bsub>ES1\<^esub>"
        and \<alpha>1''Vv1_is_\<alpha>1'Vv1: "\<alpha>1'' \<upharpoonleft> V\<^bsub>\<V>1\<^esub> = \<alpha>1' \<upharpoonleft> V\<^bsub>\<V>1\<^esub>"
        and \<alpha>1''Cv1_empty: "\<alpha>1'' \<upharpoonleft> C\<^bsub>\<V>1\<^esub> = []"
        by blast

      from c_in_Cv_inter_Upsilon Upsilon_inter_E2_subset_Upsilon2 propSepViews
      have cE2_in_Cv2_inter_Upsilon2: "set ([c] \<upharpoonleft> E\<^bsub>ES2\<^esub>) \<subseteq> C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub>"
        unfolding properSeparationOfViews_def by (simp add: projection_def, auto)
     
      from \<delta>1''_in_N1_inter_Delta1star Nv1_inter_Delta1_inter_E2_subsetof_Upsilon2 
       propSepViews disjoint_Nv1_Vv2 
      have \<delta>1''E2_in_Cv2_inter_Upsilon2star: "set (\<delta>1'' \<upharpoonleft> E\<^bsub>ES2\<^esub>) \<subseteq> C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub>"
        proof -
          from \<delta>1''_in_N1_inter_Delta1star 
          have eq: "\<delta>1'' \<upharpoonleft> E\<^bsub>ES2\<^esub> = \<delta>1'' \<upharpoonleft> (N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub> \<inter> E\<^bsub>ES2\<^esub>)"
            by (metis Int_commute Int_left_commute Int_lower2 Int_lower1 
              projection_intersection_neutral subset_trans)
          
          from validV2 Nv1_inter_Delta1_inter_E2_subsetof_Upsilon2 
            propSepViews disjoint_Nv1_Vv2  
          have "N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub> \<inter> E\<^bsub>ES2\<^esub> \<subseteq> C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub>"
            unfolding properSeparationOfViews_def 
            by (simp add: isViewOn_def V_valid_def VC_disjoint_def 
              VN_disjoint_def NC_disjoint_def, auto)
          thus ?thesis
            by (subst eq, simp only: projection_def, auto)
        qed
      
      have c\<delta>1''E2_in_Cv2_inter_Upsilon2star: "set ((c # \<delta>1'') \<upharpoonleft> E\<^bsub>ES2\<^esub>) \<subseteq> C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub>"
        proof -
          from cE2_in_Cv2_inter_Upsilon2 \<delta>1''E2_in_Cv2_inter_Upsilon2star
          have "set (([c] @ \<delta>1'') \<upharpoonleft> E\<^bsub>ES2\<^esub>) \<subseteq> C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub>"
            by (simp only: projection_concatenation_commute, auto)
          thus ?thesis
            by auto
        qed


      have "\<exists> \<alpha>2'' \<delta>2''. set \<alpha>2'' \<subseteq> E\<^bsub>ES2\<^esub>        
        \<and> set \<delta>2'' \<subseteq> N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub> \<union> C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub> \<inter> N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub>        
        \<and> \<beta> \<upharpoonleft> E\<^bsub>ES2\<^esub> @ [c] \<upharpoonleft> E\<^bsub>ES2\<^esub> @ \<delta>2'' @ [v'] \<upharpoonleft> E\<^bsub>ES2\<^esub> @ \<alpha>2'' \<in> Tr\<^bsub>ES2\<^esub>        
        \<and> \<alpha>2'' \<upharpoonleft> V\<^bsub>\<V>2\<^esub> = \<alpha>2' \<upharpoonleft> V\<^bsub>\<V>2\<^esub> \<and> \<alpha>2'' \<upharpoonleft> C\<^bsub>\<V>2\<^esub> = []
        \<and> \<delta>2'' \<upharpoonleft> E\<^bsub>ES1\<^esub> = \<delta>1'' \<upharpoonleft> E\<^bsub>ES2\<^esub>"
        proof cases
          assume v'_in_E2: "v' \<in> E\<^bsub>ES2\<^esub>"
          with Nabla_inter_E2_subset_Nabla2 propSepViews v'_in_Vv_inter_Nabla
          have v'_in_Vv2_inter_Nabla2: "v' \<in> V\<^bsub>\<V>2\<^esub> \<inter> Nabla \<Gamma>2"
            unfolding properSeparationOfViews_def by auto

          have "\<lbrakk> (\<beta> @ [v']) \<upharpoonleft> E\<^bsub>ES2\<^esub> @ \<alpha>2' \<in> Tr\<^bsub>ES2\<^esub> ; 
            \<alpha>2' \<upharpoonleft> C\<^bsub>\<V>2\<^esub> = []; set ((c # \<delta>1'') \<upharpoonleft> E\<^bsub>ES2\<^esub>) \<subseteq> C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub> ; 
            c \<in> C\<^bsub>\<V>\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>\<^esub> ; set \<delta>1'' \<subseteq> N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub>;
            Adm \<V> \<rho> (Tr\<^bsub>(ES1 \<parallel> ES2)\<^esub>) \<beta> c \<rbrakk> 
            \<Longrightarrow> \<exists> \<alpha>2'' \<delta>2''.
           (set \<alpha>2'' \<subseteq> E\<^bsub>ES2\<^esub> \<and> set \<delta>2'' \<subseteq> N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub> \<union> C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub> \<inter> N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub>            
            \<and> \<beta> \<upharpoonleft> E\<^bsub>ES2\<^esub> @ [c] \<upharpoonleft> E\<^bsub>ES2\<^esub> @ \<delta>2'' @ [v'] \<upharpoonleft> E\<^bsub>ES2\<^esub> @ \<alpha>2'' \<in> Tr\<^bsub>ES2\<^esub>            
            \<and> \<alpha>2'' \<upharpoonleft> V\<^bsub>\<V>2\<^esub> = \<alpha>2' \<upharpoonleft> V\<^bsub>\<V>2\<^esub> \<and> \<alpha>2'' \<upharpoonleft> C\<^bsub>\<V>2\<^esub> = []
            \<and> \<delta>2'' \<upharpoonleft> (C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub>) = \<delta>1'' \<upharpoonleft> E\<^bsub>ES2\<^esub>)"
            proof (induct "length ((c # \<delta>1'') \<upharpoonleft> E\<^bsub>ES2\<^esub>)" arbitrary: \<beta> \<alpha>2' c \<delta>1'')
              case 0

              from 0(2) validES2 have "set \<alpha>2' \<subseteq> E\<^bsub>ES2\<^esub>"
                by (simp add: ES_valid_def traces_contain_events_def, auto)
              moreover
              have "set [] \<subseteq> N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub> \<union> C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub> \<inter> N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub>"
                by auto
              moreover
              have "\<beta> \<upharpoonleft> E\<^bsub>ES2\<^esub> @ [c] \<upharpoonleft> E\<^bsub>ES2\<^esub> @ [] @ [v'] \<upharpoonleft> E\<^bsub>ES2\<^esub> @ \<alpha>2' \<in> Tr\<^bsub>ES2\<^esub>"
                proof -
                  note 0(2)
                  moreover
                  from 0(1) have "c \<notin> E\<^bsub>ES2\<^esub>"
                    by (simp add: projection_def, auto)
                  ultimately show ?thesis
                    by (simp add: projection_concatenation_commute projection_def)
                qed
              moreover
              have "\<alpha>2' \<upharpoonleft> V\<^bsub>\<V>2\<^esub> = \<alpha>2' \<upharpoonleft> V\<^bsub>\<V>2\<^esub>" ..
              moreover
              note 0(3)
              moreover 
              from 0(1) have "[] \<upharpoonleft> (C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub>) = \<delta>1'' \<upharpoonleft> E\<^bsub>ES2\<^esub>"
                by (simp add: projection_def, split if_split_asm, auto)
              ultimately show ?case
                by blast
            next
              case (Suc n)

              from projection_split_last[OF Suc(2)] obtain \<mu> c' \<nu>
                where c'_in_E2: "c' \<in> E\<^bsub>ES2\<^esub>"
                and c\<delta>1''_is_\<mu>c'\<nu>: "c # \<delta>1'' = \<mu> @ [c'] @ \<nu>"
                and \<nu>E2_empty: "\<nu> \<upharpoonleft> E\<^bsub>ES2\<^esub> = []"
                and n_is_length_\<mu>\<nu>E2: "n = length ((\<mu> @ \<nu>) \<upharpoonleft> E\<^bsub>ES2\<^esub>)"
                by blast

              from Suc(5) c'_in_E2 c\<delta>1''_is_\<mu>c'\<nu> have "set (\<mu> \<upharpoonleft> E\<^bsub>ES2\<^esub> @ [c']) \<subseteq> C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub>"
                by (simp only: c\<delta>1''_is_\<mu>c'\<nu> projection_concatenation_commute 
                  projection_def, auto)
              hence c'_in_Cv2_inter_Upsilon2: "c' \<in> C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub>"
                by auto
              hence c'_in_Cv2: "c' \<in> C\<^bsub>\<V>2\<^esub>" and c'_in_Upsilon2: "c' \<in> \<Upsilon>\<^bsub>\<Gamma>2\<^esub>"
                by auto
              with validV2 have c'_in_E2: "c' \<in> E\<^bsub>ES2\<^esub>"
                by (simp add: isViewOn_def V_valid_def
                  VC_disjoint_def VN_disjoint_def NC_disjoint_def, auto)

              show ?case
                proof (cases \<mu>)
                  case Nil (* we apply FCIA in this case *)
                  with c\<delta>1''_is_\<mu>c'\<nu> have c_is_c': "c = c'" and \<delta>1''_is_\<nu>: "\<delta>1'' = \<nu>"
                    by auto
                  with c'_in_Cv2_inter_Upsilon2 have "c \<in> C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub>"
                    by simp
                  moreover
                  note v'_in_Vv2_inter_Nabla2
                  moreover
                  from v'_in_E2 Suc(3) have "(\<beta> \<upharpoonleft> E\<^bsub>ES2\<^esub>) @ [v'] @ \<alpha>2' \<in> Tr\<^bsub>ES2\<^esub>"
                    by (simp add: projection_concatenation_commute projection_def)
                  moreover
                  note Suc(4)
                  moreover
                  have "Adm \<V>2 \<rho>2 Tr\<^bsub>ES2\<^esub> (\<beta> \<upharpoonleft> E\<^bsub>ES2\<^esub>) c"
                    proof -
                      from Suc(8) obtain \<gamma>
                        where \<gamma>\<rho>v_is_\<beta>\<rho>v: "\<gamma> \<upharpoonleft> (\<rho> \<V>) = \<beta> \<upharpoonleft> (\<rho> \<V>)"
                        and \<gamma>c_in_Tr: "(\<gamma> @ [c]) \<in> Tr\<^bsub>(ES1 \<parallel> ES2)\<^esub>"
                        unfolding Adm_def
                        by auto

                      from c_is_c' c'_in_E2 \<gamma>c_in_Tr have "(\<gamma> \<upharpoonleft> E\<^bsub>ES2\<^esub>) @ [c] \<in> Tr\<^bsub>ES2\<^esub>"
                        by (simp add: projection_def composeES_def)
                      moreover
                      have "\<gamma> \<upharpoonleft> E\<^bsub>ES2\<^esub> \<upharpoonleft> (\<rho>2 \<V>2) = \<beta> \<upharpoonleft> E\<^bsub>ES2\<^esub> \<upharpoonleft> (\<rho>2 \<V>2)"
                      proof -
                        from \<gamma>\<rho>v_is_\<beta>\<rho>v have "\<gamma> \<upharpoonleft> E\<^bsub>ES2\<^esub> \<upharpoonleft> (\<rho> \<V>) = \<beta> \<upharpoonleft> E\<^bsub>ES2\<^esub> \<upharpoonleft> (\<rho> \<V>)"
                          by (metis projection_commute)
                        with \<rho>2v2_subset_\<rho>v_inter_E2 have "\<gamma> \<upharpoonleft> (\<rho>2 \<V>2) = \<beta> \<upharpoonleft> (\<rho>2 \<V>2)"
                          by (metis Int_subset_iff \<gamma>\<rho>v_is_\<beta>\<rho>v projection_subset_elim)
                        thus ?thesis
                          by (metis projection_commute)
                      qed
                      ultimately show ?thesis unfolding Adm_def
                        by auto
                    qed  
                  moreover
                  note FCIA2
                  ultimately obtain \<alpha>2'' \<gamma>
                    where one: "set \<gamma> \<subseteq> N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub>"
                    and two: "\<beta> \<upharpoonleft> E\<^bsub>ES2\<^esub> @ [c] @ \<gamma> @ [v'] @ \<alpha>2'' \<in> Tr\<^bsub>ES2\<^esub>"
                    and three: "\<alpha>2'' \<upharpoonleft> V\<^bsub>\<V>2\<^esub> = \<alpha>2' \<upharpoonleft> V\<^bsub>\<V>2\<^esub>"
                    and four: "\<alpha>2'' \<upharpoonleft> C\<^bsub>\<V>2\<^esub> = []"
                    unfolding FCIA_def
                    by blast

                  (* we choose \<delta>2'' = \<nu> \<upharpoonleft> E\<^bsub>ES2\<^esub> @ \<gamma> *)
                  let ?DELTA2'' = "\<nu> \<upharpoonleft> E\<^bsub>ES2\<^esub> @ \<gamma>" 
                    
                  from two validES2 have "set \<alpha>2'' \<subseteq> E\<^bsub>ES2\<^esub>"
                    by (simp add: ES_valid_def traces_contain_events_def, auto)
                  moreover
                  from one \<nu>E2_empty
                  have "set ?DELTA2'' \<subseteq> N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub> \<union> C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub> \<inter> N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub>"
                    by auto
                  moreover
                  have "\<beta> \<upharpoonleft> E\<^bsub>ES2\<^esub> @ [c] \<upharpoonleft> E\<^bsub>ES2\<^esub> @ ?DELTA2'' @ [v'] \<upharpoonleft> E\<^bsub>ES2\<^esub> @ \<alpha>2'' \<in> Tr\<^bsub>ES2\<^esub>"
                    proof -
                      from c_is_c' c'_in_E2 have "[c] = [c] \<upharpoonleft> E\<^bsub>ES2\<^esub>"
                        by (simp add: projection_def)
                      moreover
                      from v'_in_E2 have "[v'] = [v'] \<upharpoonleft> E\<^bsub>ES2\<^esub>"
                        by (simp add: projection_def)
                      moreover
                      note \<nu>E2_empty two
                      ultimately show ?thesis
                        by auto
                    qed
                  moreover
                  note three four
                  moreover
                  have "?DELTA2'' \<upharpoonleft> (C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub>) = \<delta>1'' \<upharpoonleft> E\<^bsub>ES2\<^esub>"
                    proof -
                      have "\<gamma> \<upharpoonleft> (C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub>) = []"
                        proof -
                          from validV2 have "N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub> \<inter> (C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub>) = {}"
                            by (simp add: isViewOn_def V_valid_def
                              VC_disjoint_def VN_disjoint_def NC_disjoint_def, auto)
                          with projection_intersection_neutral[OF one, of "C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub>"]
                          show ?thesis
                            by (simp add: projection_def)
                        qed
                      with \<delta>1''_is_\<nu> \<nu>E2_empty show ?thesis
                        by (simp add: projection_concatenation_commute)
                    qed
                  ultimately show ?thesis
                    by blast
                next
                  case (Cons x xs) (* we apply the inductive hypothesis in this case *)
                  with c\<delta>1''_is_\<mu>c'\<nu>
                  have \<mu>_is_c_xs: "\<mu> = [c] @ xs" and \<delta>1''_is_xs_c'_\<nu>: "\<delta>1'' = xs @ [c'] @ \<nu>"
                    by auto
                  with n_is_length_\<mu>\<nu>E2 have "n = length ((c # (xs @ \<nu>)) \<upharpoonleft> E\<^bsub>ES2\<^esub>)"
                    by auto
                  moreover
                  note Suc(3,4)
                  moreover
                  have "set ((c # (xs @ \<nu>)) \<upharpoonleft> E\<^bsub>ES2\<^esub>) \<subseteq> C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub>"
                    proof -
                      have res: "c # (xs @ \<nu>) = [c] @ (xs @ \<nu>)" 
                        by auto

                      from Suc(5) c\<delta>1''_is_\<mu>c'\<nu> \<mu>_is_c_xs \<nu>E2_empty
                      show ?thesis
                        by (subst res, simp only: c\<delta>1''_is_\<mu>c'\<nu> 
                          projection_concatenation_commute set_append, auto)
                    qed
                  moreover
                  note Suc(6) 
                  moreover
                  from Suc(7) \<delta>1''_is_xs_c'_\<nu> have "set (xs @ \<nu>) \<subseteq> N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub>"
                    by auto
                  moreover note Suc(8) Suc(1)[of c "xs @ \<nu>" \<beta> \<alpha>2']
                  ultimately obtain \<delta> \<gamma>
                    where one: "set \<delta> \<subseteq> E\<^bsub>ES2\<^esub>"
                    and two: "set \<gamma> \<subseteq> N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub> \<union> C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub> \<inter> N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub>"
                    and three: "\<beta> \<upharpoonleft> E\<^bsub>ES2\<^esub> @ [c] \<upharpoonleft> E\<^bsub>ES2\<^esub> @ \<gamma> @ [v'] \<upharpoonleft> E\<^bsub>ES2\<^esub> @ \<delta> \<in> Tr\<^bsub>ES2\<^esub>"
                    and four: "\<delta> \<upharpoonleft> V\<^bsub>\<V>2\<^esub> = \<alpha>2' \<upharpoonleft> V\<^bsub>\<V>2\<^esub>"
                    and five: "\<delta> \<upharpoonleft> C\<^bsub>\<V>2\<^esub> = []"
                    and six: "\<gamma> \<upharpoonleft> (C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub>) = (xs @ \<nu>) \<upharpoonleft> E\<^bsub>ES2\<^esub>"
                    by blast

                  (* apply FCIA to insert c' after \<gamma> *)
                  let ?BETA = "\<beta> \<upharpoonleft> E\<^bsub>ES2\<^esub> @ [c] \<upharpoonleft> E\<^bsub>ES2\<^esub> @ \<gamma>"

                  note c'_in_Cv2_inter_Upsilon2 v'_in_Vv2_inter_Nabla2
                  moreover
                  from three v'_in_E2 have "?BETA @ [v'] @ \<delta> \<in> Tr\<^bsub>ES2\<^esub>"
                    by (simp add: projection_def)
                  moreover
                  note five 
                  moreover
                  have "Adm \<V>2 \<rho>2 Tr\<^bsub>ES2\<^esub> ?BETA c'"
                    proof -
                      have "?BETA @ [c'] \<in> Tr\<^bsub>ES2\<^esub>"
                        proof -
                          from Suc(7) c'_in_Cv2_inter_Upsilon2 \<delta>1''_is_xs_c'_\<nu>
                          have "c' \<in> C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub> \<inter> N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub>"
                            by auto
                          moreover
                          from validES2 three have "?BETA \<in> Tr\<^bsub>ES2\<^esub>"
                            by (unfold ES_valid_def traces_prefixclosed_def
                              prefixclosed_def prefix_def, auto)
                          moreover
                          note total_ES2_C2_inter_Upsilon2_inter_N1_inter_Delta1
                          ultimately show ?thesis
                            unfolding total_def
                            by blast
                        qed
                      thus ?thesis
                        unfolding Adm_def
                        by blast                        
                    qed
                  moreover
                  note FCIA2
                  ultimately obtain \<alpha>2'' \<delta>'
                    where fcia_one: "set \<delta>' \<subseteq> N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub>"
                    and fcia_two: "?BETA @ [c'] @ \<delta>' @ [v'] @ \<alpha>2'' \<in> Tr\<^bsub>ES2\<^esub>"
                    and fcia_three: "\<alpha>2'' \<upharpoonleft> V\<^bsub>\<V>2\<^esub> = \<delta> \<upharpoonleft> V\<^bsub>\<V>2\<^esub>"
                    and fcia_four:  "\<alpha>2'' \<upharpoonleft> C\<^bsub>\<V>2\<^esub> = []"
                    unfolding FCIA_def
                    by blast
  
                  let ?DELTA2'' = "\<gamma> @ [c'] @ \<delta>'"

                  from fcia_two validES2 have "set \<alpha>2'' \<subseteq> E\<^bsub>ES2\<^esub>"
                    by (simp add: ES_valid_def traces_contain_events_def, auto)
                  moreover
                  have "set ?DELTA2'' \<subseteq> N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub> \<union> C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub> \<inter> N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub>"
                    proof -
                      from Suc(7) c'_in_Cv2_inter_Upsilon2 \<delta>1''_is_xs_c'_\<nu> 
                      have "c' \<in>  C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub> \<inter> N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub>"
                        by auto
                      with two fcia_one show ?thesis
                        by auto
                    qed
                  moreover
                  from fcia_two v'_in_E2 
                  have "\<beta> \<upharpoonleft> E\<^bsub>ES2\<^esub> @ [c] \<upharpoonleft> E\<^bsub>ES2\<^esub> @ ?DELTA2'' @ [v'] \<upharpoonleft> E\<^bsub>ES2\<^esub> @ \<alpha>2'' \<in> Tr\<^bsub>ES2\<^esub>"
                    by (simp add: projection_def)
                  moreover
                  from fcia_three four have "\<alpha>2'' \<upharpoonleft> V\<^bsub>\<V>2\<^esub> = \<alpha>2' \<upharpoonleft> V\<^bsub>\<V>2\<^esub>"
                    by simp
                  moreover
                  note fcia_four
                  moreover             
                  have "?DELTA2'' \<upharpoonleft> (C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub>) = \<delta>1'' \<upharpoonleft> E\<^bsub>ES2\<^esub>"
                    proof -
                      have "\<delta>' \<upharpoonleft> (C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub>) = []"
                        proof -
                          from fcia_one have "\<forall> e \<in> set \<delta>'. e \<in> N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub>"
                            by auto
                          with validV2 have "\<forall> e \<in> set \<delta>'. e \<notin> C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub>"
                            by (simp add:isViewOn_def V_valid_def 
                              VC_disjoint_def VN_disjoint_def NC_disjoint_def, auto)
                          thus ?thesis
                            by (simp add: projection_def)
                        qed
                      with c'_in_E2 c'_in_Cv2_inter_Upsilon2 \<delta>1''_is_xs_c'_\<nu> \<nu>E2_empty six 
                      show ?thesis
                        by (simp only: projection_concatenation_commute projection_def, auto)
                    qed
                  ultimately show ?thesis 
                    by blast     
                qed
          qed
          from this[OF \<beta>v'E2\<alpha>2'_in_Tr2 \<alpha>2'Cv2_empty 
            c\<delta>1''E2_in_Cv2_inter_Upsilon2star c_in_Cv_inter_Upsilon \<delta>1''_in_N1_inter_Delta1star Adm]
          obtain \<alpha>2'' \<delta>2''
            where one: "set \<alpha>2'' \<subseteq> E\<^bsub>ES2\<^esub>"
            and two: "set \<delta>2'' \<subseteq> N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub> \<union> C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub> \<inter> N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub>"
            and three: "\<beta> \<upharpoonleft> E\<^bsub>ES2\<^esub> @ [c] \<upharpoonleft> E\<^bsub>ES2\<^esub> @ \<delta>2'' @ [v'] \<upharpoonleft> E\<^bsub>ES2\<^esub> @ \<alpha>2'' \<in> Tr\<^bsub>ES2\<^esub>            
            \<and> \<alpha>2'' \<upharpoonleft> V\<^bsub>\<V>2\<^esub> = \<alpha>2' \<upharpoonleft> V\<^bsub>\<V>2\<^esub> \<and> \<alpha>2'' \<upharpoonleft> C\<^bsub>\<V>2\<^esub> = []"
            and four: "\<delta>2'' \<upharpoonleft> (C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub>) = \<delta>1'' \<upharpoonleft> E\<^bsub>ES2\<^esub>"
            by blast

          note one two three
          moreover
          have "\<delta>2'' \<upharpoonleft> E\<^bsub>ES1\<^esub> = \<delta>1'' \<upharpoonleft> E\<^bsub>ES2\<^esub>" 
            proof -
              from projection_intersection_neutral[OF two, of "E\<^bsub>ES1\<^esub>"] 
                Nv2_inter_Delta2_inter_E1_empty validV1 
              have "\<delta>2'' \<upharpoonleft> E\<^bsub>ES1\<^esub> = \<delta>2'' \<upharpoonleft> (C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub> \<inter> N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub> \<inter> E\<^bsub>ES1\<^esub>)"
                by (simp only: Int_Un_distrib2, auto)
              moreover
              from validV1
              have "C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub> \<inter> N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub> \<inter> E\<^bsub>ES1\<^esub> = C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub> \<inter> N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub>"
                by (simp add: isViewOn_def V_valid_def VC_disjoint_def 
                  VN_disjoint_def NC_disjoint_def, auto)
              ultimately have "\<delta>2'' \<upharpoonleft> E\<^bsub>ES1\<^esub> = \<delta>2'' \<upharpoonleft> (C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub> \<inter> N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub>)"
                by simp
              hence "\<delta>2'' \<upharpoonleft> E\<^bsub>ES1\<^esub> = \<delta>2'' \<upharpoonleft> (C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub>) \<upharpoonleft> (N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub>)"
                by (simp add: projection_def)
              with four have "\<delta>2'' \<upharpoonleft> E\<^bsub>ES1\<^esub> = \<delta>1'' \<upharpoonleft> E\<^bsub>ES2\<^esub> \<upharpoonleft> (N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub>)"
                by simp
              hence "\<delta>2'' \<upharpoonleft> E\<^bsub>ES1\<^esub> = \<delta>1'' \<upharpoonleft> (N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub>) \<upharpoonleft> E\<^bsub>ES2\<^esub>"
                by (simp only: projection_commute)
              with \<delta>1''_in_N1_inter_Delta1star show ?thesis
                by (simp only: list_subset_iff_projection_neutral)
            qed
          ultimately show ?thesis
              by blast
        next
          assume v'_notin_E2: "v' \<notin> E\<^bsub>ES2\<^esub>"

           have "\<lbrakk> (\<beta> @ [v']) \<upharpoonleft> E\<^bsub>ES2\<^esub> @ \<alpha>2' \<in> Tr\<^bsub>ES2\<^esub> ; 
            \<alpha>2' \<upharpoonleft> C\<^bsub>\<V>2\<^esub> = []; set ((c # \<delta>1'') \<upharpoonleft> E\<^bsub>ES2\<^esub>) \<subseteq> C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub> ; 
             c \<in> C\<^bsub>\<V>\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>\<^esub> ; set \<delta>1'' \<subseteq> N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub>;
            Adm \<V> \<rho> (Tr\<^bsub>(ES1 \<parallel> ES2)\<^esub>) \<beta> c \<rbrakk> 
            \<Longrightarrow> \<exists> \<alpha>2'' \<delta>2''.
             (set \<alpha>2'' \<subseteq> E\<^bsub>ES2\<^esub> \<and> set \<delta>2'' \<subseteq> N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub> \<union> C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub> \<inter> N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub>            
             \<and> \<beta> \<upharpoonleft> E\<^bsub>ES2\<^esub> @ [c] \<upharpoonleft> E\<^bsub>ES2\<^esub> @ \<delta>2'' @ [v'] \<upharpoonleft> E\<^bsub>ES2\<^esub> @ \<alpha>2'' \<in> Tr\<^bsub>ES2\<^esub>            
             \<and> \<alpha>2'' \<upharpoonleft> V\<^bsub>\<V>2\<^esub> = \<alpha>2' \<upharpoonleft> V\<^bsub>\<V>2\<^esub> \<and> \<alpha>2'' \<upharpoonleft> C\<^bsub>\<V>2\<^esub> = []
            \<and> \<delta>2'' \<upharpoonleft> E\<^bsub>ES1\<^esub> = \<delta>1'' \<upharpoonleft> E\<^bsub>ES2\<^esub>)"
            proof (induct "length ((c # \<delta>1'') \<upharpoonleft> E\<^bsub>ES2\<^esub>)" arbitrary: \<beta> \<alpha>2' c \<delta>1'')
               case 0

              from 0(2) validES2 have "set \<alpha>2' \<subseteq> E\<^bsub>ES2\<^esub>"
                by (simp add: ES_valid_def traces_contain_events_def, auto)
              moreover
              have "set [] \<subseteq> N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub> \<union> C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub> \<inter> N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub>"
                by auto
              moreover
              have "\<beta> \<upharpoonleft> E\<^bsub>ES2\<^esub> @ [c] \<upharpoonleft> E\<^bsub>ES2\<^esub> @ [] @ [v'] \<upharpoonleft> E\<^bsub>ES2\<^esub> @ \<alpha>2' \<in> Tr\<^bsub>ES2\<^esub>"
                proof -
                  note 0(2)
                  moreover
                  from 0(1) have "c \<notin> E\<^bsub>ES2\<^esub>"
                    by (simp add: projection_def, auto)
                  ultimately show ?thesis
                    by (simp add: projection_concatenation_commute projection_def)
                qed
              moreover
              have "\<alpha>2' \<upharpoonleft> V\<^bsub>\<V>2\<^esub> = \<alpha>2' \<upharpoonleft> V\<^bsub>\<V>2\<^esub>" ..
              moreover
              note 0(3)
              moreover 
              from 0(1) have "[] \<upharpoonleft> E\<^bsub>ES1\<^esub> = \<delta>1'' \<upharpoonleft> E\<^bsub>ES2\<^esub>"
                by (simp add: projection_def, split if_split_asm, auto)
              ultimately show ?case
                by blast
            next
              case (Suc n)

              from projection_split_last[OF Suc(2)] obtain \<mu> c' \<nu>
                where c'_in_E2: "c' \<in> E\<^bsub>ES2\<^esub>"
                and c\<delta>1''_is_\<mu>c'\<nu>: "c # \<delta>1'' = \<mu> @ [c'] @ \<nu>"
                and \<nu>E2_empty: "\<nu> \<upharpoonleft> E\<^bsub>ES2\<^esub> = []"
                and n_is_length_\<mu>\<nu>E2: "n = length ((\<mu> @ \<nu>) \<upharpoonleft> E\<^bsub>ES2\<^esub>)"
                by blast

              from Suc(5) c'_in_E2 c\<delta>1''_is_\<mu>c'\<nu> have "set (\<mu> \<upharpoonleft> E\<^bsub>ES2\<^esub> @ [c']) \<subseteq> C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub>"
                by (simp only: c\<delta>1''_is_\<mu>c'\<nu> projection_concatenation_commute projection_def, auto)
              hence c'_in_Cv2_inter_Upsilon2: "c' \<in> C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub>"
                by auto
              hence c'_in_Cv2: "c' \<in> C\<^bsub>\<V>2\<^esub>" and c'_in_Upsilon2: "c' \<in> \<Upsilon>\<^bsub>\<Gamma>2\<^esub>"
                by auto
              with validV2 have c'_in_E2: "c' \<in> E\<^bsub>ES2\<^esub>"
                by (simp add:isViewOn_def V_valid_def 
                  VC_disjoint_def VN_disjoint_def NC_disjoint_def, auto)

              show ?case
                proof (cases \<mu>)
                  case Nil (* we just apply BSIA in this case *)
                  with c\<delta>1''_is_\<mu>c'\<nu> have c_is_c': "c = c'" and \<delta>1''_is_\<nu>: "\<delta>1'' = \<nu>"
                    by auto
                  with c'_in_Cv2_inter_Upsilon2 have "c \<in> C\<^bsub>\<V>2\<^esub>"
                    by simp
                  moreover
                  from v'_notin_E2 Suc(3) have "(\<beta> \<upharpoonleft> E\<^bsub>ES2\<^esub>) @ \<alpha>2' \<in> Tr\<^bsub>ES2\<^esub>"
                    by (simp add: projection_concatenation_commute projection_def)
                  moreover
                  note Suc(4)
                  moreover
                  have "Adm \<V>2 \<rho>2 Tr\<^bsub>ES2\<^esub> (\<beta> \<upharpoonleft> E\<^bsub>ES2\<^esub>) c"
                     proof -
                      from Suc(8) obtain \<gamma>
                        where \<gamma>\<rho>v_is_\<beta>\<rho>v: "\<gamma> \<upharpoonleft> (\<rho> \<V>) = \<beta> \<upharpoonleft> (\<rho> \<V>)"
                        and \<gamma>c_in_Tr: "(\<gamma> @ [c]) \<in> Tr\<^bsub>(ES1 \<parallel> ES2)\<^esub>"
                        unfolding Adm_def
                        by auto

                      from c_is_c' c'_in_E2 \<gamma>c_in_Tr have "(\<gamma> \<upharpoonleft> E\<^bsub>ES2\<^esub>) @ [c] \<in> Tr\<^bsub>ES2\<^esub>"
                        by (simp add: projection_def composeES_def)
                      moreover
                      have "\<gamma> \<upharpoonleft> E\<^bsub>ES2\<^esub> \<upharpoonleft> (\<rho>2 \<V>2) = \<beta> \<upharpoonleft> E\<^bsub>ES2\<^esub> \<upharpoonleft> (\<rho>2 \<V>2)"
                      proof -
                        from \<gamma>\<rho>v_is_\<beta>\<rho>v have "\<gamma> \<upharpoonleft> E\<^bsub>ES2\<^esub> \<upharpoonleft> (\<rho> \<V>) = \<beta> \<upharpoonleft> E\<^bsub>ES2\<^esub> \<upharpoonleft> (\<rho> \<V>)"
                          by (metis projection_commute)
                        with \<rho>2v2_subset_\<rho>v_inter_E2 
                        have "\<gamma> \<upharpoonleft> (\<rho>2 \<V>2) = \<beta> \<upharpoonleft> (\<rho>2 \<V>2)"
                          by (metis Int_subset_iff \<gamma>\<rho>v_is_\<beta>\<rho>v projection_subset_elim)
                        thus ?thesis
                          by (metis projection_commute)
                      qed
                      ultimately show ?thesis unfolding Adm_def
                        by auto
                    qed  
                  moreover
                  note BSIA2
                  ultimately obtain \<alpha>2''
                    where one: "(\<beta> \<upharpoonleft> E\<^bsub>ES2\<^esub>) @ [c] @ \<alpha>2'' \<in> Tr\<^bsub>ES2\<^esub>"
                    and two: "\<alpha>2'' \<upharpoonleft> V\<^bsub>\<V>2\<^esub> = \<alpha>2' \<upharpoonleft> V\<^bsub>\<V>2\<^esub>"
                    and three: "\<alpha>2'' \<upharpoonleft> C\<^bsub>\<V>2\<^esub> = []"
                    unfolding BSIA_def
                    by blast

                  let ?DELTA2'' = "\<nu> \<upharpoonleft> E\<^bsub>ES2\<^esub>"

                  from one validES2 have "set \<alpha>2'' \<subseteq> E\<^bsub>ES2\<^esub>"
                    by (simp add: ES_valid_def traces_contain_events_def, auto)
                  moreover
                  from \<nu>E2_empty
                  have "set ?DELTA2'' \<subseteq> N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub> \<union> C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub> \<inter> N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub>"
                    by simp
                  moreover
                  from c_is_c' c'_in_E2 one v'_notin_E2 \<nu>E2_empty
                  have "(\<beta> \<upharpoonleft> E\<^bsub>ES2\<^esub>) @ [c] \<upharpoonleft> E\<^bsub>ES2\<^esub> @ ?DELTA2'' @ [v'] \<upharpoonleft> E\<^bsub>ES2\<^esub> @ \<alpha>2'' \<in> Tr\<^bsub>ES2\<^esub>"
                    by (simp add: projection_def)
                  moreover
                  note two three
                  moreover
                  from \<nu>E2_empty \<delta>1''_is_\<nu> have "?DELTA2'' \<upharpoonleft> E\<^bsub>ES1\<^esub> = \<delta>1'' \<upharpoonleft> E\<^bsub>ES2\<^esub>"
                    by (simp add: projection_def)
                  ultimately show ?thesis
                    by blast
                next
                  case (Cons x xs) (* apply inductive hypothesis, then BSIA *)
                   with c\<delta>1''_is_\<mu>c'\<nu> have \<mu>_is_c_xs: "\<mu> = [c] @ xs" 
                     and \<delta>1''_is_xs_c'_\<nu>: "\<delta>1'' = xs @ [c'] @ \<nu>"
                    by auto
                  with n_is_length_\<mu>\<nu>E2 have "n = length ((c # (xs @ \<nu>)) \<upharpoonleft> E\<^bsub>ES2\<^esub>)"
                    by auto
                  moreover
                  note Suc(3,4)
                  moreover
                  have "set ((c # (xs @ \<nu>)) \<upharpoonleft> E\<^bsub>ES2\<^esub>) \<subseteq> C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub>"
                    proof -
                      have res: "c # (xs @ \<nu>) = [c] @ (xs @ \<nu>)" 
                        by auto

                      from Suc(5) c\<delta>1''_is_\<mu>c'\<nu> \<mu>_is_c_xs \<nu>E2_empty
                      show ?thesis
                        by (subst res, simp only: c\<delta>1''_is_\<mu>c'\<nu> 
                          projection_concatenation_commute set_append, auto)
                    qed
                  moreover
                  note Suc(6) 
                  moreover
                  from Suc(7) \<delta>1''_is_xs_c'_\<nu> have "set (xs @ \<nu>) \<subseteq> N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub>"
                    by auto
                  moreover note Suc(8) Suc(1)[of c "xs @ \<nu>" \<beta> \<alpha>2']
                  ultimately obtain \<delta> \<gamma>
                    where one: "set \<delta> \<subseteq> E\<^bsub>ES2\<^esub>"
                    and two: "set \<gamma> \<subseteq> N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub> \<union> C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub> \<inter> N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub>"
                    and three: "\<beta> \<upharpoonleft> E\<^bsub>ES2\<^esub> @ [c] \<upharpoonleft> E\<^bsub>ES2\<^esub> @ \<gamma> @ [v'] \<upharpoonleft> E\<^bsub>ES2\<^esub> @ \<delta> \<in> Tr\<^bsub>ES2\<^esub>"
                    and four: "\<delta> \<upharpoonleft> V\<^bsub>\<V>2\<^esub> = \<alpha>2' \<upharpoonleft> V\<^bsub>\<V>2\<^esub>"
                    and five: "\<delta> \<upharpoonleft> C\<^bsub>\<V>2\<^esub> = []"
                    and six: "\<gamma> \<upharpoonleft> E\<^bsub>ES1\<^esub> = (xs @ \<nu>) \<upharpoonleft> E\<^bsub>ES2\<^esub>"
                    by blast
                  
                   (* apply BSIA to insert c' after \<gamma> *)
                  let ?BETA = "\<beta> \<upharpoonleft> E\<^bsub>ES2\<^esub> @ [c] \<upharpoonleft> E\<^bsub>ES2\<^esub> @ \<gamma>"

                  from c'_in_Cv2_inter_Upsilon2 have "c' \<in> C\<^bsub>\<V>2\<^esub>"
                    by auto
                  moreover
                  from three v'_notin_E2 have "?BETA @ \<delta> \<in> Tr\<^bsub>ES2\<^esub>"
                    by (simp add: projection_def)
                  moreover
                  note five 
                  moreover
                  have "Adm \<V>2 \<rho>2 Tr\<^bsub>ES2\<^esub> ?BETA c'"
                    proof -
                      have "?BETA @ [c'] \<in> Tr\<^bsub>ES2\<^esub>"
                        proof -
                          from Suc(7) c'_in_Cv2_inter_Upsilon2 \<delta>1''_is_xs_c'_\<nu>
                          have "c' \<in> C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub> \<inter> N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub>"
                            by auto
                          moreover
                          from validES2 three have "?BETA \<in> Tr\<^bsub>ES2\<^esub>"
                            by (unfold ES_valid_def traces_prefixclosed_def
                              prefixclosed_def prefix_def, auto)
                          moreover
                          note total_ES2_C2_inter_Upsilon2_inter_N1_inter_Delta1
                          ultimately show ?thesis
                            unfolding total_def
                            by blast
                        qed
                      thus ?thesis
                        unfolding Adm_def
                        by blast                      
                    qed
                  moreover
                  note BSIA2
                  ultimately obtain \<alpha>2''
                    where bsia_one: "?BETA @ [c'] @ \<alpha>2'' \<in> Tr\<^bsub>ES2\<^esub>"
                    and bsia_two: "\<alpha>2'' \<upharpoonleft> V\<^bsub>\<V>2\<^esub> = \<delta> \<upharpoonleft> V\<^bsub>\<V>2\<^esub>"
                    and bsia_three:  "\<alpha>2'' \<upharpoonleft> C\<^bsub>\<V>2\<^esub> = []"
                    unfolding BSIA_def
                    by blast
  
                  let ?DELTA2'' = "\<gamma> @ [c']"

                  from bsia_one validES2 have "set \<alpha>2'' \<subseteq> E\<^bsub>ES2\<^esub>"
                    by (simp add: ES_valid_def traces_contain_events_def, auto)
                  moreover
                  have "set ?DELTA2'' \<subseteq> N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub> \<union> C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub> \<inter> N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub>"
                    proof -
                      from Suc(7) c'_in_Cv2_inter_Upsilon2 \<delta>1''_is_xs_c'_\<nu> 
                      have "c' \<in>  C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub> \<inter> N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub>"
                        by auto
                      with two show ?thesis
                        by auto
                    qed
                  moreover
                  from bsia_one v'_notin_E2 
                  have "\<beta> \<upharpoonleft> E\<^bsub>ES2\<^esub> @ [c] \<upharpoonleft> E\<^bsub>ES2\<^esub> @ ?DELTA2'' @ [v'] \<upharpoonleft> E\<^bsub>ES2\<^esub> @ \<alpha>2'' \<in> Tr\<^bsub>ES2\<^esub>"
                    by (simp add: projection_def)
                  moreover
                  from bsia_two four have "\<alpha>2'' \<upharpoonleft> V\<^bsub>\<V>2\<^esub> = \<alpha>2' \<upharpoonleft> V\<^bsub>\<V>2\<^esub>"
                    by simp
                  moreover
                  note bsia_three
                  moreover             
                  have "?DELTA2'' \<upharpoonleft> E\<^bsub>ES1\<^esub> = \<delta>1'' \<upharpoonleft> E\<^bsub>ES2\<^esub>"
                    proof -
                      from validV1 Suc(7) \<delta>1''_is_xs_c'_\<nu> have "c' \<in> E\<^bsub>ES1\<^esub>"
                        by (simp add: isViewOn_def V_valid_def 
                          VC_disjoint_def VN_disjoint_def NC_disjoint_def, auto)
                      with c'_in_E2 c'_in_Cv2_inter_Upsilon2 \<delta>1''_is_xs_c'_\<nu> \<nu>E2_empty six 
                      show ?thesis
                        by (simp only: projection_concatenation_commute projection_def, auto)
                    qed
                  ultimately show ?thesis 
                    by blast     
                qed
            qed
          from this[OF \<beta>v'E2\<alpha>2'_in_Tr2 \<alpha>2'Cv2_empty c\<delta>1''E2_in_Cv2_inter_Upsilon2star 
            c_in_Cv_inter_Upsilon \<delta>1''_in_N1_inter_Delta1star Adm]
          show ?thesis 
            by blast
        qed
      then obtain \<alpha>2'' \<delta>2''
        where \<alpha>2''_in_E2star: "set \<alpha>2'' \<subseteq> E\<^bsub>ES2\<^esub>"
        and \<delta>2''_in_N2_inter_Delta2star:"set \<delta>2'' \<subseteq> N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub> \<union> C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub> \<inter> N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub>"
        and \<beta>E2_cE2_\<delta>2''_v'E2_\<alpha>2''_in_Tr2: 
        "\<beta> \<upharpoonleft> E\<^bsub>ES2\<^esub> @ [c] \<upharpoonleft> E\<^bsub>ES2\<^esub> @ \<delta>2'' @ [v'] \<upharpoonleft> E\<^bsub>ES2\<^esub> @ \<alpha>2'' \<in> Tr\<^bsub>ES2\<^esub>"
        and \<alpha>2''Vv2_is_\<alpha>2'Vv2: "\<alpha>2'' \<upharpoonleft> V\<^bsub>\<V>2\<^esub> = \<alpha>2' \<upharpoonleft> V\<^bsub>\<V>2\<^esub>"
        and \<alpha>2''Cv2_empty: "\<alpha>2'' \<upharpoonleft> C\<^bsub>\<V>2\<^esub> = []"
        and \<delta>2''E1_is_\<delta>1''E2: "\<delta>2'' \<upharpoonleft> E\<^bsub>ES1\<^esub> = \<delta>1'' \<upharpoonleft> E\<^bsub>ES2\<^esub>"
        by blast

      from \<beta>E2_cE2_\<delta>2''_v'E2_\<alpha>2''_in_Tr2 \<beta>E1_cE1_\<delta>1''_v'E1_\<alpha>1''_in_Tr1 
        validES2 validES1
      have \<delta>2''_in_E2star: "set \<delta>2'' \<subseteq> E\<^bsub>ES2\<^esub>" and \<delta>1''_in_E1star: "set \<delta>1'' \<subseteq> E\<^bsub>ES1\<^esub>"
        by (simp_all add: ES_valid_def traces_contain_events_def, auto)
      with \<delta>2''E1_is_\<delta>1''E2 merge_property[of \<delta>2'' "E\<^bsub>ES2\<^esub>" \<delta>1'' "E\<^bsub>ES1\<^esub>"] obtain \<delta>'
        where \<delta>'E2_is_\<delta>2'': "\<delta>' \<upharpoonleft> E\<^bsub>ES2\<^esub> = \<delta>2''"
        and \<delta>'E1_is_\<delta>1'': "\<delta>' \<upharpoonleft> E\<^bsub>ES1\<^esub> = \<delta>1''"
        and \<delta>'_contains_only_\<delta>2''_\<delta>1''_events: "set \<delta>' \<subseteq> set \<delta>2'' \<union> set \<delta>1''"
        unfolding Let_def
        by auto

      let ?TAU = "\<beta> @ [c] @ \<delta>' @ [v']"
      let ?LAMBDA = "\<alpha> \<upharpoonleft> V\<^bsub>\<V>\<^esub>"
      let ?T2 = \<alpha>2''
      let ?T1 = \<alpha>1''

     (* apply the generalized zipping lemma *)
     have "?TAU \<in> Tr\<^bsub>(ES1 \<parallel> ES2)\<^esub>"
        proof -
          from \<beta>E2_cE2_\<delta>2''_v'E2_\<alpha>2''_in_Tr2 \<delta>'E2_is_\<delta>2'' validES2
          have "\<beta> \<upharpoonleft> E\<^bsub>ES2\<^esub> @ [c] \<upharpoonleft> E\<^bsub>ES2\<^esub> @ \<delta>' \<upharpoonleft> E\<^bsub>ES2\<^esub> @ [v'] \<upharpoonleft> E\<^bsub>ES2\<^esub> \<in> Tr\<^bsub>ES2\<^esub>"
            by (simp add: ES_valid_def traces_prefixclosed_def
              prefixclosed_def prefix_def)
          hence "(\<beta> @ [c] @ \<delta>' @ [v']) \<upharpoonleft> E\<^bsub>ES2\<^esub> \<in> Tr\<^bsub>ES2\<^esub>"
            by (simp add: projection_def, auto)
          moreover          
          from \<beta>E1_cE1_\<delta>1''_v'E1_\<alpha>1''_in_Tr1 \<delta>'E1_is_\<delta>1'' validES1 
          have "\<beta> \<upharpoonleft> E\<^bsub>ES1\<^esub> @ [c] \<upharpoonleft> E\<^bsub>ES1\<^esub> @ \<delta>' \<upharpoonleft> E\<^bsub>ES1\<^esub> @ [v'] \<upharpoonleft> E\<^bsub>ES1\<^esub> \<in> Tr\<^bsub>ES1\<^esub>"
            by (simp add: ES_valid_def traces_prefixclosed_def
              prefixclosed_def prefix_def)
          hence "(\<beta> @ [c] @ \<delta>' @ [v']) \<upharpoonleft> E\<^bsub>ES1\<^esub> \<in> Tr\<^bsub>ES1\<^esub>"
            by (simp add: projection_def, auto)
          moreover
          from \<beta>v'\<alpha>_in_Tr c_in_Cv_inter_Upsilon VIsViewOnE
            \<delta>'_contains_only_\<delta>2''_\<delta>1''_events \<delta>2''_in_E2star \<delta>1''_in_E1star
          have "set (\<beta> @ [c] @ \<delta>' @ [v']) \<subseteq> E\<^bsub>ES2\<^esub> \<union> E\<^bsub>ES1\<^esub>"
            unfolding composeES_def isViewOn_def V_valid_def 
              VC_disjoint_def VN_disjoint_def NC_disjoint_def
            by auto
          ultimately show ?thesis
            unfolding composeES_def
            by auto
        qed 
      hence "set ?TAU \<subseteq> E\<^bsub>(ES1 \<parallel> ES2)\<^esub>"
        unfolding composeES_def
        by auto
      moreover
      have "set ?LAMBDA \<subseteq> V\<^bsub>\<V>\<^esub>"
        by (simp add: projection_def, auto)
      moreover
      note \<alpha>2''_in_E2star \<alpha>1''_in_E1star
      moreover
      from \<beta>E2_cE2_\<delta>2''_v'E2_\<alpha>2''_in_Tr2 \<delta>'E2_is_\<delta>2'' 
      have "?TAU \<upharpoonleft> E\<^bsub>ES2\<^esub> @ ?T2 \<in> Tr\<^bsub>ES2\<^esub>"
        by (simp only: projection_concatenation_commute, auto)
      moreover
      from \<beta>E1_cE1_\<delta>1''_v'E1_\<alpha>1''_in_Tr1 \<delta>'E1_is_\<delta>1'' 
      have "?TAU \<upharpoonleft> E\<^bsub>ES1\<^esub> @ ?T1 \<in> Tr\<^bsub>ES1\<^esub>"
        by (simp only: projection_concatenation_commute, auto)
      moreover
      have "?LAMBDA \<upharpoonleft> E\<^bsub>ES2\<^esub> = ?T2 \<upharpoonleft> V\<^bsub>\<V>\<^esub>"
        proof -
          from propSepViews have "?LAMBDA \<upharpoonleft> E\<^bsub>ES2\<^esub> = \<alpha> \<upharpoonleft> V\<^bsub>\<V>2\<^esub>"
            unfolding properSeparationOfViews_def by (simp only: projection_sequence)
          moreover
          from \<alpha>2''_in_E2star propSepViews have "?T2 \<upharpoonleft> V\<^bsub>\<V>\<^esub> = ?T2 \<upharpoonleft> V\<^bsub>\<V>2\<^esub>"
            unfolding properSeparationOfViews_def
            by (metis Int_commute projection_intersection_neutral)
          moreover
          note \<alpha>2'Vv2_is_\<alpha>Vv2 \<alpha>2''Vv2_is_\<alpha>2'Vv2
          ultimately show ?thesis
            by simp
        qed
      moreover
      have "?LAMBDA \<upharpoonleft> E\<^bsub>ES1\<^esub> = ?T1 \<upharpoonleft> V\<^bsub>\<V>\<^esub>"
        proof -
          from propSepViews have "?LAMBDA \<upharpoonleft> E\<^bsub>ES1\<^esub> = \<alpha> \<upharpoonleft> V\<^bsub>\<V>1\<^esub>"
            unfolding properSeparationOfViews_def by (simp only: projection_sequence)
          moreover
          from \<alpha>1''_in_E1star propSepViews have "?T1 \<upharpoonleft> V\<^bsub>\<V>\<^esub> = ?T1 \<upharpoonleft> V\<^bsub>\<V>1\<^esub>"
            unfolding properSeparationOfViews_def
            by (metis Int_commute projection_intersection_neutral)
          moreover
          note \<alpha>1'Vv1_is_\<alpha>Vv1 \<alpha>1''Vv1_is_\<alpha>1'Vv1
          ultimately show ?thesis
            by simp
        qed
      moreover
      note \<alpha>2''Cv2_empty \<alpha>1''Cv1_empty generalized_zipping_lemma
      ultimately obtain t (* show that the conclusion of FCIA holds *)
        where "?TAU @ t \<in> Tr\<^bsub>(ES1 \<parallel> ES2)\<^esub>"
        and  "t \<upharpoonleft> V\<^bsub>\<V>\<^esub> = ?LAMBDA"
        and "t \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []"
        by blast
      moreover
      have "set \<delta>' \<subseteq> N\<^bsub>\<V>\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>\<^esub>"
        proof -
          from \<delta>'_contains_only_\<delta>2''_\<delta>1''_events 
            \<delta>2''_in_N2_inter_Delta2star \<delta>1''_in_N1_inter_Delta1star
          have "set \<delta>' \<subseteq> N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub> \<union> N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub>"
            by auto
          with Delta1_N1_Delta2_N2_subset_Delta Nv1_union_Nv2_subsetof_Nv show ?thesis
            by auto
        qed
      ultimately have "\<exists>\<alpha>' \<gamma>'. (set \<gamma>' \<subseteq> N\<^bsub>\<V>\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>\<^esub> \<and> \<beta> @ [c] @ \<gamma>' @ [v'] @ \<alpha>' \<in> Tr\<^bsub>(ES1 \<parallel> ES2)\<^esub> 
        \<and> \<alpha>' \<upharpoonleft> V\<^bsub>\<V>\<^esub> = \<alpha> \<upharpoonleft> V\<^bsub>\<V>\<^esub> \<and> \<alpha>' \<upharpoonleft> C\<^bsub>\<V>\<^esub> = [])"
        by (simp only: append_assoc, blast)
    }
    ultimately have "\<exists>\<alpha>' \<gamma>'. (set \<gamma>' \<subseteq> N\<^bsub>\<V>\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>\<^esub> \<and> \<beta> @ [c] @ \<gamma>' @ [v'] @ \<alpha>' \<in> Tr\<^bsub>(ES1 \<parallel> ES2)\<^esub> 
      \<and> \<alpha>' \<upharpoonleft> V\<^bsub>\<V>\<^esub> = \<alpha> \<upharpoonleft> V\<^bsub>\<V>\<^esub> \<and> \<alpha>' \<upharpoonleft> C\<^bsub>\<V>\<^esub> = [])"
      by blast
  }
  thus ?thesis
    unfolding FCIA_def
    by blast
qed

(* Theorem 6.4.2 *)
theorem compositionality_R: 
"\<lbrakk> R \<V>1 Tr\<^bsub>ES1\<^esub>; R \<V>2 Tr\<^bsub>ES2\<^esub> \<rbrakk> \<Longrightarrow> R \<V> (Tr\<^bsub>(ES1 \<parallel> ES2)\<^esub>)"
  proof -
    assume R1: "R \<V>1 Tr\<^bsub>ES1\<^esub>"
    and R2: "R \<V>2 Tr\<^bsub>ES2\<^esub>"

    {
      fix \<tau>'
      assume \<tau>'_in_Tr: "\<tau>' \<in> Tr\<^bsub>(ES1 \<parallel> ES2)\<^esub>"
      hence \<tau>'E1_in_Tr1: "\<tau>' \<upharpoonleft> E\<^bsub>ES1\<^esub> \<in> Tr\<^bsub>ES1\<^esub>"
        and \<tau>'E2_in_Tr2: "\<tau>' \<upharpoonleft> E\<^bsub>ES2\<^esub> \<in> Tr\<^bsub>ES2\<^esub>"
        unfolding composeES_def
        by auto
      with R1 R2 obtain \<tau>1' \<tau>2'
        where \<tau>1'_in_Tr1: "\<tau>1' \<in> Tr\<^bsub>ES1\<^esub>"
        and \<tau>1'Cv1_empty: "\<tau>1' \<upharpoonleft> C\<^bsub>\<V>1\<^esub> = []"
        and \<tau>1'Vv1_is_\<tau>'_E1_Vv1: "\<tau>1' \<upharpoonleft> V\<^bsub>\<V>1\<^esub> = \<tau>' \<upharpoonleft> E\<^bsub>ES1\<^esub> \<upharpoonleft> V\<^bsub>\<V>1\<^esub>"
        and \<tau>2'_in_Tr2: "\<tau>2' \<in> Tr\<^bsub>ES2\<^esub>"
        and \<tau>2'Cv2_empty: "\<tau>2' \<upharpoonleft> C\<^bsub>\<V>2\<^esub> = []"
        and \<tau>2'Vv2_is_\<tau>'_E2_Vv2: "\<tau>2' \<upharpoonleft> V\<^bsub>\<V>2\<^esub> = \<tau>' \<upharpoonleft> E\<^bsub>ES2\<^esub> \<upharpoonleft> V\<^bsub>\<V>2\<^esub>"
        unfolding R_def
        by blast

      have "set [] \<subseteq> E\<^bsub>(ES1 \<parallel> ES2)\<^esub>"
        by auto
      moreover
      have "set (\<tau>' \<upharpoonleft> V\<^bsub>\<V>\<^esub>) \<subseteq> V\<^bsub>\<V>\<^esub>"
        by (simp add: projection_def, auto)
      moreover
      from validES1 \<tau>1'_in_Tr1 have \<tau>1'_in_E1: "set \<tau>1' \<subseteq> E\<^bsub>ES1\<^esub>"
        by (simp add: ES_valid_def traces_contain_events_def, auto)
      moreover
      from validES2 \<tau>2'_in_Tr2 have \<tau>2'_in_E2: "set \<tau>2' \<subseteq> E\<^bsub>ES2\<^esub>"
        by (simp add: ES_valid_def traces_contain_events_def, auto)
      moreover
      from \<tau>1'_in_Tr1 have "[] \<upharpoonleft> E\<^bsub>ES1\<^esub> @ \<tau>1' \<in> Tr\<^bsub>ES1\<^esub>"
        by (simp add: projection_def)
      moreover
      from \<tau>2'_in_Tr2 have "[] \<upharpoonleft> E\<^bsub>ES2\<^esub> @ \<tau>2' \<in> Tr\<^bsub>ES2\<^esub>"
        by (simp add: projection_def)
      moreover
      have "\<tau>' \<upharpoonleft> V\<^bsub>\<V>\<^esub> \<upharpoonleft> E\<^bsub>ES1\<^esub> = \<tau>1' \<upharpoonleft> V\<^bsub>\<V>\<^esub>"
        proof -
          from projection_intersection_neutral[OF \<tau>1'_in_E1, of "V\<^bsub>\<V>\<^esub>"] propSepViews 
          have "\<tau>1' \<upharpoonleft> V\<^bsub>\<V>\<^esub> = \<tau>1' \<upharpoonleft> V\<^bsub>\<V>1\<^esub>"
            unfolding properSeparationOfViews_def
            by (simp add: Int_commute)
          moreover
          from  propSepViews have "\<tau>' \<upharpoonleft> V\<^bsub>\<V>\<^esub> \<upharpoonleft> E\<^bsub>ES1\<^esub> = \<tau>' \<upharpoonleft> V\<^bsub>\<V>1\<^esub>"
            unfolding properSeparationOfViews_def
            by (simp add: projection_sequence)
          moreover {
            have " \<tau>' \<upharpoonleft> E\<^bsub>ES1\<^esub> \<upharpoonleft> V\<^bsub>\<V>1\<^esub> = \<tau>' \<upharpoonleft> (E\<^bsub>ES1\<^esub> \<inter> V\<^bsub>\<V>1\<^esub>)"
              by (simp add: projection_def)
            moreover
            from validV1 have "E\<^bsub>ES1\<^esub> \<inter> V\<^bsub>\<V>1\<^esub> = V\<^bsub>\<V>1\<^esub>"
              by (simp add: isViewOn_def V_valid_def 
                VC_disjoint_def VN_disjoint_def NC_disjoint_def, auto)
            ultimately have "\<tau>' \<upharpoonleft> E\<^bsub>ES1\<^esub> \<upharpoonleft> V\<^bsub>\<V>1\<^esub> = \<tau>' \<upharpoonleft> V\<^bsub>\<V>1\<^esub>"
              by simp
            }
          moreover
          note \<tau>1'Vv1_is_\<tau>'_E1_Vv1
          ultimately show ?thesis
            by simp
        qed
      moreover
      have "\<tau>' \<upharpoonleft> V\<^bsub>\<V>\<^esub> \<upharpoonleft> E\<^bsub>ES2\<^esub> = \<tau>2' \<upharpoonleft> V\<^bsub>\<V>\<^esub>"
        proof -
          from projection_intersection_neutral[OF \<tau>2'_in_E2, of "V\<^bsub>\<V>\<^esub>"] propSepViews
          have "\<tau>2' \<upharpoonleft> V\<^bsub>\<V>\<^esub> = \<tau>2' \<upharpoonleft> V\<^bsub>\<V>2\<^esub>"
            unfolding properSeparationOfViews_def
            by (simp add: Int_commute)
          moreover
          from  propSepViews have "\<tau>' \<upharpoonleft> V\<^bsub>\<V>\<^esub> \<upharpoonleft> E\<^bsub>ES2\<^esub> = \<tau>' \<upharpoonleft> V\<^bsub>\<V>2\<^esub>"
            unfolding properSeparationOfViews_def
            by (simp add: projection_sequence)
          moreover {
            have " \<tau>' \<upharpoonleft> E\<^bsub>ES2\<^esub> \<upharpoonleft> V\<^bsub>\<V>2\<^esub> = \<tau>' \<upharpoonleft> (E\<^bsub>ES2\<^esub> \<inter> V\<^bsub>\<V>2\<^esub>)"
              by (simp add: projection_def)
            moreover
            from validV2 have "E\<^bsub>ES2\<^esub> \<inter> V\<^bsub>\<V>2\<^esub> = V\<^bsub>\<V>2\<^esub>"
              by (simp add:isViewOn_def V_valid_def VC_disjoint_def 
                VN_disjoint_def NC_disjoint_def, auto)
            ultimately have "\<tau>' \<upharpoonleft> E\<^bsub>ES2\<^esub> \<upharpoonleft> V\<^bsub>\<V>2\<^esub> = \<tau>' \<upharpoonleft> V\<^bsub>\<V>2\<^esub>"
              by simp
            }
          moreover
          note \<tau>2'Vv2_is_\<tau>'_E2_Vv2
          ultimately show ?thesis
            by simp
        qed
      moreover
      note \<tau>1'Cv1_empty \<tau>2'Cv2_empty generalized_zipping_lemma
      ultimately have "\<exists>t. [] @ t \<in> Tr\<^bsub>(ES1 \<parallel> ES2)\<^esub> \<and> t \<upharpoonleft> V\<^bsub>\<V>\<^esub> = \<tau>' \<upharpoonleft> V\<^bsub>\<V>\<^esub> \<and> t \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []"
        by blast
    }
    thus ?thesis
      unfolding R_def
      by auto
  qed

end

locale CompositionalityStrictBSPs = Compositionality +
(*adds the additional assumptions of theorem 6.4.3 in Heiko Mantel's phd thesis*)
assumes N\<V>_inter_E1_is_N\<V>1: "N\<^bsub>\<V>\<^esub> \<inter> E\<^bsub>ES1\<^esub> = N\<^bsub>\<V>1\<^esub>"
    and N\<V>_inter_E2_is_N\<V>2: "N\<^bsub>\<V>\<^esub> \<inter> E\<^bsub>ES2\<^esub> = N\<^bsub>\<V>2\<^esub>"

(* sublocale relationship to other compositionality assumptions*)
sublocale CompositionalityStrictBSPs \<subseteq> Compositionality
by (unfold_locales)

context CompositionalityStrictBSPs
begin
(*Theorem 6.4.3 Case 1 in Heiko Mantel's pdh thesis*)
theorem compositionality_SR: 
"\<lbrakk> SR \<V>1 Tr\<^bsub>ES1\<^esub>; SR \<V>2 Tr\<^bsub>ES2\<^esub> \<rbrakk> \<Longrightarrow> SR \<V> (Tr\<^bsub>(ES1 \<parallel> ES2)\<^esub>)" 
proof -
  assume "SR \<V>1 Tr\<^bsub>ES1\<^esub>"
     and "SR \<V>2 Tr\<^bsub>ES2\<^esub>"
  { 
    let ?\<V>\<^sub>1'="\<lparr>V = V\<^bsub>\<V>1\<^esub> \<union> N\<^bsub>\<V>1\<^esub>, N = {}, C = C\<^bsub>\<V>1\<^esub>\<rparr>"
    let ?\<V>\<^sub>2'="\<lparr>V = V\<^bsub>\<V>2\<^esub> \<union> N\<^bsub>\<V>2\<^esub>, N = {}, C = C\<^bsub>\<V>2\<^esub> \<rparr>"
    let ?\<V>' ="\<lparr>V=V\<^bsub>\<V>\<^esub> \<union> N\<^bsub>\<V>\<^esub>, N={}, C=C\<^bsub>\<V>\<^esub> \<rparr>" 
    (*Show ?\<V>\<^sub>1' ?\<V>\<^sub>2' ?\<V>' are views on the respective set of events*)
    from validV1 have \<V>\<^sub>1'IsViewOnE\<^sub>1: "isViewOn ?\<V>\<^sub>1' E\<^bsub>ES1\<^esub> " 
      unfolding isViewOn_def V_valid_def  VN_disjoint_def NC_disjoint_def VC_disjoint_def by auto
    from validV2 have \<V>\<^sub>2'IsViewOnE\<^sub>2: "isViewOn ?\<V>\<^sub>2' E\<^bsub>ES2\<^esub> " 
      unfolding isViewOn_def V_valid_def  VN_disjoint_def NC_disjoint_def VC_disjoint_def by auto
    from VIsViewOnE have \<V>'IsViewOnE: "isViewOn  ?\<V>' E\<^bsub>(ES1\<parallel>ES2)\<^esub>" 
      unfolding isViewOn_def V_valid_def  VN_disjoint_def NC_disjoint_def VC_disjoint_def by auto
    
    (*Show ?\<V>\<^sub>1' and ?\<V>\<^sub>2' are proper separation of \<lparr> V=\<^bsub>\<V>\<^esub>, N={}, C=\<^bsub>\<V>\<^esub> \<rparr> *)
     from propSepViews  N\<V>_inter_E1_is_N\<V>1
     have "V\<^bsub>?\<V>'\<^esub> \<inter> E\<^bsub>ES1\<^esub> = V\<^bsub>?\<V>\<^sub>1'\<^esub>"
       unfolding properSeparationOfViews_def by auto
     from propSepViews   N\<V>_inter_E2_is_N\<V>2
     have "V\<^bsub>?\<V>'\<^esub> \<inter> E\<^bsub>ES2\<^esub> = V\<^bsub>?\<V>\<^sub>2'\<^esub>"
       unfolding properSeparationOfViews_def by auto
     from propSepViews 
     have  "C\<^bsub>?\<V>'\<^esub> \<inter> E\<^bsub>ES1\<^esub> \<subseteq> C\<^bsub>?\<V>\<^sub>1'\<^esub>"
       unfolding properSeparationOfViews_def by auto      
     from propSepViews
     have  "C\<^bsub>?\<V>'\<^esub> \<inter> E\<^bsub>ES2\<^esub> \<subseteq> C\<^bsub>?\<V>\<^sub>2'\<^esub>"
       unfolding properSeparationOfViews_def by auto
     have "N\<^bsub>?\<V>\<^sub>1'\<^esub> \<inter> N\<^bsub>?\<V>\<^sub>2'\<^esub> ={}"
       by auto
     
     note properSeparation_\<V>\<^sub>1\<V>\<^sub>2=\<open>V\<^bsub>?\<V>'\<^esub> \<inter> E\<^bsub>ES1\<^esub> = V\<^bsub>?\<V>\<^sub>1'\<^esub>\<close> \<open>V\<^bsub>?\<V>'\<^esub> \<inter> E\<^bsub>ES2\<^esub> = V\<^bsub>?\<V>\<^sub>2'\<^esub>\<close> 
              \<open>C\<^bsub>?\<V>'\<^esub> \<inter> E\<^bsub>ES1\<^esub> \<subseteq> C\<^bsub>?\<V>\<^sub>1'\<^esub>\<close> \<open>C\<^bsub>?\<V>'\<^esub> \<inter> E\<^bsub>ES2\<^esub> \<subseteq> C\<^bsub>?\<V>\<^sub>2'\<^esub>\<close> \<open>N\<^bsub>?\<V>\<^sub>1'\<^esub> \<inter> N\<^bsub>?\<V>\<^sub>2'\<^esub> ={}\<close>
    
    (*Show ES1\<parallel>ES2 is a well behaved composition w.r.t.  ?\<V>\<^sub>1' and ?\<V>\<^sub>2' *)
     have wbc1: "N\<^bsub>?\<V>\<^sub>1'\<^esub> \<inter> E\<^bsub>ES1\<^esub>={} \<and> N\<^bsub>?\<V>\<^sub>2'\<^esub> \<inter> E\<^bsub>ES2\<^esub>={}"
       by auto
     
     
    from \<open>SR \<V>1 Tr\<^bsub>ES1\<^esub>\<close>  have "R ?\<V>\<^sub>1' Tr\<^bsub>ES1\<^esub>"      
      using validES1 validV1 BSPTaxonomyDifferentCorrections.SR_implies_R_for_modified_view  
      unfolding  BSPTaxonomyDifferentCorrections_def by auto
    from \<open>SR \<V>2 Tr\<^bsub>ES2\<^esub>\<close>  have "R ?\<V>\<^sub>2' Tr\<^bsub>ES2\<^esub>"     
      using validES2 validV2  BSPTaxonomyDifferentCorrections.SR_implies_R_for_modified_view 
      unfolding BSPTaxonomyDifferentCorrections_def by auto   
 
    from validES1 validES2 composableES1ES2  \<V>'IsViewOnE \<V>\<^sub>1'IsViewOnE\<^sub>1 \<V>\<^sub>2'IsViewOnE\<^sub>2
         properSeparation_\<V>\<^sub>1\<V>\<^sub>2  wbc1
    have "Compositionality ES1 ES2 ?\<V>' ?\<V>\<^sub>1' ?\<V>\<^sub>2'" unfolding Compositionality_def 
      by (simp add: properSeparationOfViews_def wellBehavedComposition_def)
    with \<open>R ?\<V>\<^sub>1' Tr\<^bsub>ES1\<^esub>\<close> \<open>R ?\<V>\<^sub>2' Tr\<^bsub>ES2\<^esub>\<close> have "R ?\<V>' Tr\<^bsub>(ES1\<parallel>ES2)\<^esub>" 
     using Compositionality.compositionality_R by blast
     
   from  validES1 validES2 composeES_yields_ES validVC
   have "BSPTaxonomyDifferentCorrections (ES1\<parallel>ES2) \<V>"
      unfolding BSPTaxonomyDifferentCorrections_def by auto 
    with \<open>R ?\<V>' Tr\<^bsub>(ES1\<parallel>ES2)\<^esub>\<close> have "SR \<V> Tr\<^bsub>(ES1\<parallel>ES2)\<^esub>" 
      using BSPTaxonomyDifferentCorrections.R_implies_SR_for_modified_view  by auto 
  }
  thus ?thesis by auto  
qed

(*Theorem 6.4.3 Case 2 in Heiko Mantel's pdh thesis*)
theorem compositionality_SD: 
"\<lbrakk> SD \<V>1 Tr\<^bsub>ES1\<^esub>; SD \<V>2 Tr\<^bsub>ES2\<^esub> \<rbrakk> \<Longrightarrow> SD \<V> (Tr\<^bsub>(ES1 \<parallel> ES2)\<^esub>)" 
proof -
  assume "SD \<V>1 Tr\<^bsub>ES1\<^esub>"
     and "SD \<V>2 Tr\<^bsub>ES2\<^esub>"
  { 
    let ?\<V>\<^sub>1'="\<lparr>V = V\<^bsub>\<V>1\<^esub> \<union> N\<^bsub>\<V>1\<^esub>, N = {}, C = C\<^bsub>\<V>1\<^esub>\<rparr>"
    let ?\<V>\<^sub>2'="\<lparr>V = V\<^bsub>\<V>2\<^esub> \<union> N\<^bsub>\<V>2\<^esub>, N = {}, C = C\<^bsub>\<V>2\<^esub> \<rparr>"
    let ?\<V>' ="\<lparr>V=V\<^bsub>\<V>\<^esub> \<union> N\<^bsub>\<V>\<^esub>, N={}, C=C\<^bsub>\<V>\<^esub> \<rparr>" 
    (*Show ?\<V>\<^sub>1' ?\<V>\<^sub>2' ?\<V>' are views on the respective set of events*)
    from validV1 have \<V>\<^sub>1'IsViewOnE\<^sub>1: "isViewOn ?\<V>\<^sub>1' E\<^bsub>ES1\<^esub> " 
      unfolding isViewOn_def V_valid_def  VN_disjoint_def NC_disjoint_def VC_disjoint_def by auto
    from validV2 have \<V>\<^sub>2'IsViewOnE\<^sub>2: "isViewOn ?\<V>\<^sub>2' E\<^bsub>ES2\<^esub> " 
      unfolding isViewOn_def V_valid_def  VN_disjoint_def NC_disjoint_def VC_disjoint_def by auto
    from VIsViewOnE have \<V>'IsViewOnE: "isViewOn  ?\<V>' E\<^bsub>(ES1\<parallel>ES2)\<^esub>" 
      unfolding isViewOn_def V_valid_def  VN_disjoint_def NC_disjoint_def VC_disjoint_def by auto
    
    (*Show ?\<V>\<^sub>1' and ?\<V>\<^sub>2' are proper separation of \<lparr> V=\<^bsub>\<V>\<^esub>, N={}, C=\<^bsub>\<V>\<^esub> \<rparr> *)
     from propSepViews  N\<V>_inter_E1_is_N\<V>1
     have "V\<^bsub>?\<V>'\<^esub> \<inter> E\<^bsub>ES1\<^esub> = V\<^bsub>?\<V>\<^sub>1'\<^esub>" 
       unfolding properSeparationOfViews_def by auto
     from propSepViews   N\<V>_inter_E2_is_N\<V>2
     have "V\<^bsub>?\<V>'\<^esub> \<inter> E\<^bsub>ES2\<^esub> = V\<^bsub>?\<V>\<^sub>2'\<^esub>"
       unfolding properSeparationOfViews_def by auto
     from propSepViews 
     have  "C\<^bsub>?\<V>'\<^esub> \<inter> E\<^bsub>ES1\<^esub> \<subseteq> C\<^bsub>?\<V>\<^sub>1'\<^esub>"
       unfolding properSeparationOfViews_def by auto      
     from propSepViews
     have  "C\<^bsub>?\<V>'\<^esub> \<inter> E\<^bsub>ES2\<^esub> \<subseteq> C\<^bsub>?\<V>\<^sub>2'\<^esub>"
       unfolding properSeparationOfViews_def by auto
     have "N\<^bsub>?\<V>\<^sub>1'\<^esub> \<inter> N\<^bsub>?\<V>\<^sub>2'\<^esub> ={}"
       by auto
     
     note properSeparation_\<V>\<^sub>1\<V>\<^sub>2=\<open>V\<^bsub>?\<V>'\<^esub> \<inter> E\<^bsub>ES1\<^esub> = V\<^bsub>?\<V>\<^sub>1'\<^esub>\<close> \<open>V\<^bsub>?\<V>'\<^esub> \<inter> E\<^bsub>ES2\<^esub> = V\<^bsub>?\<V>\<^sub>2'\<^esub>\<close> 
              \<open>C\<^bsub>?\<V>'\<^esub> \<inter> E\<^bsub>ES1\<^esub> \<subseteq> C\<^bsub>?\<V>\<^sub>1'\<^esub>\<close> \<open>C\<^bsub>?\<V>'\<^esub> \<inter> E\<^bsub>ES2\<^esub> \<subseteq> C\<^bsub>?\<V>\<^sub>2'\<^esub>\<close> \<open>N\<^bsub>?\<V>\<^sub>1'\<^esub> \<inter> N\<^bsub>?\<V>\<^sub>2'\<^esub> ={}\<close>
    
    (*Show ES1\<parallel>ES2 is a well behaved composition w.r.t.  ?\<V>\<^sub>1' and ?\<V>\<^sub>2' *)
     have wbc1: "N\<^bsub>?\<V>\<^sub>1'\<^esub> \<inter> E\<^bsub>ES1\<^esub>={} \<and> N\<^bsub>?\<V>\<^sub>2'\<^esub> \<inter> E\<^bsub>ES2\<^esub>={}"
       by auto
     
     
    from \<open>SD \<V>1 Tr\<^bsub>ES1\<^esub>\<close>  have "BSD ?\<V>\<^sub>1' Tr\<^bsub>ES1\<^esub>"      
      using validES1 validV1 BSPTaxonomyDifferentCorrections.SD_implies_BSD_for_modified_view
      unfolding  BSPTaxonomyDifferentCorrections_def by auto
    from \<open>SD \<V>2 Tr\<^bsub>ES2\<^esub>\<close>  have "BSD ?\<V>\<^sub>2' Tr\<^bsub>ES2\<^esub>"     
      using validES2 validV2 BSPTaxonomyDifferentCorrections.SD_implies_BSD_for_modified_view
      unfolding BSPTaxonomyDifferentCorrections_def by auto   
 
    from validES1 validES2 composableES1ES2   \<V>'IsViewOnE \<V>\<^sub>1'IsViewOnE\<^sub>1 \<V>\<^sub>2'IsViewOnE\<^sub>2
         properSeparation_\<V>\<^sub>1\<V>\<^sub>2  wbc1
    have "Compositionality ES1 ES2 ?\<V>' ?\<V>\<^sub>1' ?\<V>\<^sub>2'"
      unfolding Compositionality_def
      by (simp add: properSeparationOfViews_def wellBehavedComposition_def)
    with \<open>BSD ?\<V>\<^sub>1' Tr\<^bsub>ES1\<^esub>\<close> \<open>BSD ?\<V>\<^sub>2' Tr\<^bsub>ES2\<^esub>\<close> have "BSD ?\<V>' Tr\<^bsub>(ES1\<parallel>ES2)\<^esub>" 
     using Compositionality.compositionality_BSD by blast
     
   from  validES1 validES2 composeES_yields_ES validVC
   have "BSPTaxonomyDifferentCorrections (ES1\<parallel>ES2) \<V>"
      unfolding BSPTaxonomyDifferentCorrections_def by auto 
    with \<open>BSD ?\<V>' Tr\<^bsub>(ES1\<parallel>ES2)\<^esub>\<close> have "SD \<V> Tr\<^bsub>(ES1\<parallel>ES2)\<^esub>" 
      using BSPTaxonomyDifferentCorrections.BSD_implies_SD_for_modified_view  by auto 
  }
  thus ?thesis by auto  
qed

(*Theorem 6.4.3 Case 3 in Heiko Mantel's pdh thesis*)
theorem compositionality_SI: 
"\<lbrakk>SD \<V>1 Tr\<^bsub>ES1\<^esub>; SD \<V>2 Tr\<^bsub>ES2\<^esub>; SI \<V>1 Tr\<^bsub>ES1\<^esub>; SI \<V>2 Tr\<^bsub>ES2\<^esub> \<rbrakk> 
   \<Longrightarrow> SI \<V> (Tr\<^bsub>(ES1 \<parallel> ES2)\<^esub>)" 
proof -
  assume "SD \<V>1 Tr\<^bsub>ES1\<^esub>"
     and "SD \<V>2 Tr\<^bsub>ES2\<^esub>"
     and "SI \<V>1 Tr\<^bsub>ES1\<^esub>"
     and "SI \<V>2 Tr\<^bsub>ES2\<^esub>"
  { 
    let ?\<V>\<^sub>1'="\<lparr>V = V\<^bsub>\<V>1\<^esub> \<union> N\<^bsub>\<V>1\<^esub>, N = {}, C = C\<^bsub>\<V>1\<^esub>\<rparr>"
    let ?\<V>\<^sub>2'="\<lparr>V = V\<^bsub>\<V>2\<^esub> \<union> N\<^bsub>\<V>2\<^esub>, N = {}, C = C\<^bsub>\<V>2\<^esub> \<rparr>"
    let ?\<V>' ="\<lparr>V=V\<^bsub>\<V>\<^esub> \<union> N\<^bsub>\<V>\<^esub>, N={}, C=C\<^bsub>\<V>\<^esub> \<rparr>" 
    (*Show ?\<V>\<^sub>1' ?\<V>\<^sub>2' ?\<V>' are views on the respective set of events*)
    from validV1 have \<V>\<^sub>1'IsViewOnE\<^sub>1: "isViewOn ?\<V>\<^sub>1' E\<^bsub>ES1\<^esub> " 
      unfolding isViewOn_def V_valid_def  VN_disjoint_def NC_disjoint_def VC_disjoint_def by auto
    from validV2 have \<V>\<^sub>2'IsViewOnE\<^sub>2: "isViewOn ?\<V>\<^sub>2' E\<^bsub>ES2\<^esub> " 
      unfolding isViewOn_def V_valid_def  VN_disjoint_def NC_disjoint_def VC_disjoint_def by auto
    from VIsViewOnE have \<V>'IsViewOnE: "isViewOn  ?\<V>' E\<^bsub>(ES1\<parallel>ES2)\<^esub>" 
      unfolding isViewOn_def V_valid_def  VN_disjoint_def NC_disjoint_def VC_disjoint_def by auto
    
    (*Show ?\<V>\<^sub>1' and ?\<V>\<^sub>2' are proper separation of \<lparr> V=\<^bsub>\<V>\<^esub>, N={}, C=\<^bsub>\<V>\<^esub> \<rparr> *)
     from propSepViews  N\<V>_inter_E1_is_N\<V>1
     have "V\<^bsub>?\<V>'\<^esub> \<inter> E\<^bsub>ES1\<^esub> = V\<^bsub>?\<V>\<^sub>1'\<^esub>" 
       unfolding properSeparationOfViews_def by auto
     from propSepViews   N\<V>_inter_E2_is_N\<V>2
     have "V\<^bsub>?\<V>'\<^esub> \<inter> E\<^bsub>ES2\<^esub> = V\<^bsub>?\<V>\<^sub>2'\<^esub>" 
       unfolding properSeparationOfViews_def by auto
     from propSepViews 
     have  "C\<^bsub>?\<V>'\<^esub> \<inter> E\<^bsub>ES1\<^esub> \<subseteq> C\<^bsub>?\<V>\<^sub>1'\<^esub>" 
       unfolding properSeparationOfViews_def by auto      
     from propSepViews
     have  "C\<^bsub>?\<V>'\<^esub> \<inter> E\<^bsub>ES2\<^esub> \<subseteq> C\<^bsub>?\<V>\<^sub>2'\<^esub>" 
       unfolding properSeparationOfViews_def by auto
     have "N\<^bsub>?\<V>\<^sub>1'\<^esub> \<inter> N\<^bsub>?\<V>\<^sub>2'\<^esub> ={}"
       by auto
     
     note properSeparation_\<V>\<^sub>1\<V>\<^sub>2=\<open>V\<^bsub>?\<V>'\<^esub> \<inter> E\<^bsub>ES1\<^esub> = V\<^bsub>?\<V>\<^sub>1'\<^esub>\<close> \<open>V\<^bsub>?\<V>'\<^esub> \<inter> E\<^bsub>ES2\<^esub> = V\<^bsub>?\<V>\<^sub>2'\<^esub>\<close> 
              \<open>C\<^bsub>?\<V>'\<^esub> \<inter> E\<^bsub>ES1\<^esub> \<subseteq> C\<^bsub>?\<V>\<^sub>1'\<^esub>\<close> \<open>C\<^bsub>?\<V>'\<^esub> \<inter> E\<^bsub>ES2\<^esub> \<subseteq> C\<^bsub>?\<V>\<^sub>2'\<^esub>\<close> \<open>N\<^bsub>?\<V>\<^sub>1'\<^esub> \<inter> N\<^bsub>?\<V>\<^sub>2'\<^esub> ={}\<close>
    
    (*Show ES1\<parallel>ES2 is a well behaved composition w.r.t.  ?\<V>\<^sub>1' and ?\<V>\<^sub>2' *)
     have wbc1: "N\<^bsub>?\<V>\<^sub>1'\<^esub> \<inter> E\<^bsub>ES1\<^esub>={} \<and> N\<^bsub>?\<V>\<^sub>2'\<^esub> \<inter> E\<^bsub>ES2\<^esub>={}"
       by auto
     
    from \<open>SD \<V>1 Tr\<^bsub>ES1\<^esub>\<close>  have "BSD ?\<V>\<^sub>1' Tr\<^bsub>ES1\<^esub>"      
      using validES1 validV1 BSPTaxonomyDifferentCorrections.SD_implies_BSD_for_modified_view 
      unfolding  BSPTaxonomyDifferentCorrections_def by auto
    from \<open>SD \<V>2 Tr\<^bsub>ES2\<^esub>\<close>  have "BSD ?\<V>\<^sub>2' Tr\<^bsub>ES2\<^esub>"     
      using validES2 validV2 BSPTaxonomyDifferentCorrections.SD_implies_BSD_for_modified_view 
      unfolding BSPTaxonomyDifferentCorrections_def by auto  
    from \<open>SI \<V>1 Tr\<^bsub>ES1\<^esub>\<close>  have "BSI ?\<V>\<^sub>1' Tr\<^bsub>ES1\<^esub>"      
      using validES1 validV1 BSPTaxonomyDifferentCorrections.SI_implies_BSI_for_modified_view 
      unfolding  BSPTaxonomyDifferentCorrections_def by auto
    from \<open>SI \<V>2 Tr\<^bsub>ES2\<^esub>\<close>  have "BSI ?\<V>\<^sub>2' Tr\<^bsub>ES2\<^esub>"     
      using validES2 validV2 BSPTaxonomyDifferentCorrections.SI_implies_BSI_for_modified_view 
      unfolding BSPTaxonomyDifferentCorrections_def by auto   

    from validES1 validES2 composableES1ES2  \<V>'IsViewOnE \<V>\<^sub>1'IsViewOnE\<^sub>1 \<V>\<^sub>2'IsViewOnE\<^sub>2
         properSeparation_\<V>\<^sub>1\<V>\<^sub>2  wbc1
    have "Compositionality ES1 ES2 ?\<V>' ?\<V>\<^sub>1' ?\<V>\<^sub>2'" unfolding Compositionality_def 
      by (simp add: properSeparationOfViews_def wellBehavedComposition_def)
    with \<open>BSD ?\<V>\<^sub>1' Tr\<^bsub>ES1\<^esub>\<close> \<open>BSD ?\<V>\<^sub>2' Tr\<^bsub>ES2\<^esub>\<close> \<open>BSI  ?\<V>\<^sub>1' Tr\<^bsub>ES1\<^esub>\<close> \<open>BSI ?\<V>\<^sub>2' Tr\<^bsub>ES2\<^esub>\<close>
    have "BSI ?\<V>' Tr\<^bsub>(ES1\<parallel>ES2)\<^esub>" 
     using Compositionality.compositionality_BSI by blast
     
   from  validES1 validES2 composeES_yields_ES validVC
   have "BSPTaxonomyDifferentCorrections (ES1\<parallel>ES2) \<V>"
      unfolding BSPTaxonomyDifferentCorrections_def by auto 
    with \<open>BSI ?\<V>' Tr\<^bsub>(ES1\<parallel>ES2)\<^esub>\<close> have "SI \<V> Tr\<^bsub>(ES1\<parallel>ES2)\<^esub>" 
      using BSPTaxonomyDifferentCorrections.BSI_implies_SI_for_modified_view  by auto 
  }
  thus ?thesis by auto  
qed


(*Theorem 6.4.3 Case 4 in Heiko Mantel's pdh thesis*)
theorem compositionality_SIA: 
"\<lbrakk>SD \<V>1 Tr\<^bsub>ES1\<^esub>; SD \<V>2 Tr\<^bsub>ES2\<^esub>; SIA \<rho>1 \<V>1 Tr\<^bsub>ES1\<^esub>; SIA \<rho>2 \<V>2 Tr\<^bsub>ES2\<^esub>; 
  (\<rho>1 \<V>1) \<subseteq> (\<rho> \<V>) \<inter> E\<^bsub>ES1\<^esub>; (\<rho>2 \<V>2) \<subseteq> (\<rho> \<V>) \<inter> E\<^bsub>ES2\<^esub> \<rbrakk>
   \<Longrightarrow> SIA \<rho> \<V> (Tr\<^bsub>(ES1 \<parallel> ES2)\<^esub>)"
proof -
  assume "SD \<V>1 Tr\<^bsub>ES1\<^esub>"
     and "SD \<V>2 Tr\<^bsub>ES2\<^esub>"
     and "SIA \<rho>1 \<V>1 Tr\<^bsub>ES1\<^esub>"
     and "SIA \<rho>2 \<V>2 Tr\<^bsub>ES2\<^esub>"
     and "(\<rho>1 \<V>1) \<subseteq> (\<rho> \<V>) \<inter> E\<^bsub>ES1\<^esub>"
     and "(\<rho>2 \<V>2) \<subseteq> (\<rho> \<V>) \<inter> E\<^bsub>ES2\<^esub>"
  { 
    let ?\<V>\<^sub>1' ="\<lparr>V = V\<^bsub>\<V>1\<^esub> \<union> N\<^bsub>\<V>1\<^esub>, N = {}, C = C\<^bsub>\<V>1\<^esub>\<rparr>"
    let ?\<V>\<^sub>2'="\<lparr>V = V\<^bsub>\<V>2\<^esub> \<union> N\<^bsub>\<V>2\<^esub>, N = {}, C = C\<^bsub>\<V>2\<^esub> \<rparr>"
    let ?\<V>' ="\<lparr>V=V\<^bsub>\<V>\<^esub> \<union> N\<^bsub>\<V>\<^esub>, N={}, C=C\<^bsub>\<V>\<^esub> \<rparr>" 
    
    (*Fix some intermediate rho's such that (\<rho>1' ?\<V>\<^sub>1') = (\<rho>1 \<V>1), (\<rho>2' ?\<V>\<^sub>2') = (\<rho>2 \<V>2)  and
      (\<rho>' ?\<V>') = (\<rho> \<V>) hold.*)
    let "?\<rho>1'::'a Rho" ="\<lambda>\<V>. if \<V>=?\<V>\<^sub>1' then \<rho>1 \<V>1  else {}"
    let "?\<rho>2'::'a Rho" ="\<lambda>\<V>. if \<V>=?\<V>\<^sub>2' then \<rho>2 \<V>2  else {}"
    let "?\<rho>'::'a Rho" ="\<lambda>\<V>'. if \<V>'=?\<V>' then \<rho> \<V>  else {}"
    
    have "(?\<rho>1' ?\<V>\<^sub>1') = (\<rho>1 \<V>1)" by simp 
    have "(?\<rho>2' ?\<V>\<^sub>2') = (\<rho>2 \<V>2)" by simp
    have "(?\<rho>' ?\<V>') = (\<rho> \<V>)" by simp

    (*Show ?\<V>\<^sub>1' ?\<V>\<^sub>2' ?\<V>' are views on the respective set of events*)
    from validV1 have \<V>\<^sub>1'IsViewOnE\<^sub>1: "isViewOn ?\<V>\<^sub>1' E\<^bsub>ES1\<^esub> " 
      unfolding isViewOn_def V_valid_def  VN_disjoint_def NC_disjoint_def VC_disjoint_def by auto
    from validV2 have \<V>\<^sub>2'IsViewOnE\<^sub>2: "isViewOn ?\<V>\<^sub>2' E\<^bsub>ES2\<^esub> " 
      unfolding isViewOn_def V_valid_def  VN_disjoint_def NC_disjoint_def VC_disjoint_def by auto
    from VIsViewOnE have \<V>'IsViewOnE: "isViewOn  ?\<V>' E\<^bsub>(ES1\<parallel>ES2)\<^esub>" 
      unfolding isViewOn_def V_valid_def  VN_disjoint_def NC_disjoint_def VC_disjoint_def by auto
    
    (*Show ?\<V>\<^sub>1' and ?\<V>\<^sub>2' are proper separation of \<lparr> V=\<^bsub>\<V>\<^esub>, N={}, C=\<^bsub>\<V>\<^esub> \<rparr> *)
     from propSepViews  N\<V>_inter_E1_is_N\<V>1
     have "V\<^bsub>?\<V>'\<^esub> \<inter> E\<^bsub>ES1\<^esub> = V\<^bsub>?\<V>\<^sub>1'\<^esub>"
       unfolding properSeparationOfViews_def by auto
     from propSepViews   N\<V>_inter_E2_is_N\<V>2
     have "V\<^bsub>?\<V>'\<^esub> \<inter> E\<^bsub>ES2\<^esub> = V\<^bsub>?\<V>\<^sub>2'\<^esub>"
       unfolding properSeparationOfViews_def by auto
     from propSepViews 
     have  "C\<^bsub>?\<V>'\<^esub> \<inter> E\<^bsub>ES1\<^esub> \<subseteq> C\<^bsub>?\<V>\<^sub>1'\<^esub>"
       unfolding properSeparationOfViews_def by auto      
     from propSepViews
     have  "C\<^bsub>?\<V>'\<^esub> \<inter> E\<^bsub>ES2\<^esub> \<subseteq> C\<^bsub>?\<V>\<^sub>2'\<^esub>"
       unfolding properSeparationOfViews_def by auto
     have "N\<^bsub>?\<V>\<^sub>1'\<^esub> \<inter> N\<^bsub>?\<V>\<^sub>2'\<^esub> ={}"
       by auto
     
     note properSeparation_\<V>\<^sub>1\<V>\<^sub>2=\<open>V\<^bsub>?\<V>'\<^esub> \<inter> E\<^bsub>ES1\<^esub> = V\<^bsub>?\<V>\<^sub>1'\<^esub>\<close> \<open>V\<^bsub>?\<V>'\<^esub> \<inter> E\<^bsub>ES2\<^esub> = V\<^bsub>?\<V>\<^sub>2'\<^esub>\<close> 
              \<open>C\<^bsub>?\<V>'\<^esub> \<inter> E\<^bsub>ES1\<^esub> \<subseteq> C\<^bsub>?\<V>\<^sub>1'\<^esub>\<close> \<open>C\<^bsub>?\<V>'\<^esub> \<inter> E\<^bsub>ES2\<^esub> \<subseteq> C\<^bsub>?\<V>\<^sub>2'\<^esub>\<close> \<open>N\<^bsub>?\<V>\<^sub>1'\<^esub> \<inter> N\<^bsub>?\<V>\<^sub>2'\<^esub> ={}\<close>
    
    (*Show ES1\<parallel>ES2 is a well behaved composition w.r.t.  ?\<V>\<^sub>1' and ?\<V>\<^sub>2' *)
     have wbc1: "N\<^bsub>?\<V>\<^sub>1'\<^esub> \<inter> E\<^bsub>ES1\<^esub>={} \<and> N\<^bsub>?\<V>\<^sub>2'\<^esub> \<inter> E\<^bsub>ES2\<^esub>={}" 
       by auto
    
      
    from \<open>SD \<V>1 Tr\<^bsub>ES1\<^esub>\<close>  have "BSD ?\<V>\<^sub>1' Tr\<^bsub>ES1\<^esub>"      
      using validES1 validV1 BSPTaxonomyDifferentCorrections.SD_implies_BSD_for_modified_view 
      unfolding  BSPTaxonomyDifferentCorrections_def by auto
    from \<open>SD \<V>2 Tr\<^bsub>ES2\<^esub>\<close>  have "BSD ?\<V>\<^sub>2' Tr\<^bsub>ES2\<^esub>"     
      using validES2 validV2 BSPTaxonomyDifferentCorrections.SD_implies_BSD_for_modified_view 
      unfolding BSPTaxonomyDifferentCorrections_def by auto 

    from \<open>SIA \<rho>1 \<V>1 Tr\<^bsub>ES1\<^esub>\<close> \<open>(?\<rho>1' ?\<V>\<^sub>1') = (\<rho>1 \<V>1)\<close>  have "BSIA ?\<rho>1' ?\<V>\<^sub>1' Tr\<^bsub>ES1\<^esub>"      
      using validES1 validV1 BSPTaxonomyDifferentCorrections.SIA_implies_BSIA_for_modified_view 
      unfolding  BSPTaxonomyDifferentCorrections_def by fastforce
    from \<open>SIA \<rho>2 \<V>2 Tr\<^bsub>ES2\<^esub>\<close> \<open>(?\<rho>2' ?\<V>\<^sub>2') = (\<rho>2 \<V>2)\<close>  have "BSIA ?\<rho>2' ?\<V>\<^sub>2' Tr\<^bsub>ES2\<^esub>"     
      using validES2 validV2 BSPTaxonomyDifferentCorrections.SIA_implies_BSIA_for_modified_view 
      unfolding BSPTaxonomyDifferentCorrections_def by fastforce   

    from validES1 validES2 composableES1ES2  \<V>'IsViewOnE \<V>\<^sub>1'IsViewOnE\<^sub>1 \<V>\<^sub>2'IsViewOnE\<^sub>2
         properSeparation_\<V>\<^sub>1\<V>\<^sub>2  wbc1
    have "Compositionality ES1 ES2 ?\<V>' ?\<V>\<^sub>1' ?\<V>\<^sub>2'" 
      unfolding Compositionality_def 
      by (simp add: properSeparationOfViews_def wellBehavedComposition_def)
    from \<open>(\<rho>1 \<V>1) \<subseteq> (\<rho> \<V>) \<inter> E\<^bsub>ES1\<^esub>\<close> \<open>(?\<rho>1' ?\<V>\<^sub>1') = (\<rho>1 \<V>1)\<close> \<open>(?\<rho>' ?\<V>') = (\<rho> \<V>)\<close>
    have "?\<rho>1' ?\<V>\<^sub>1'  \<subseteq>  ?\<rho>'  ?\<V>' \<inter> E\<^bsub>ES1\<^esub>"
      by auto 
    from \<open>(\<rho>2 \<V>2) \<subseteq> (\<rho> \<V>) \<inter> E\<^bsub>ES2\<^esub>\<close> \<open>(?\<rho>2' ?\<V>\<^sub>2') = (\<rho>2 \<V>2)\<close> \<open>(?\<rho>' ?\<V>') = (\<rho> \<V>)\<close>
    have "?\<rho>2' ?\<V>\<^sub>2'  \<subseteq>  ?\<rho>'  ?\<V>' \<inter> E\<^bsub>ES2\<^esub>"
      by auto   

    from \<open>Compositionality ES1 ES2 ?\<V>' ?\<V>\<^sub>1' ?\<V>\<^sub>2'\<close> \<open>BSD ?\<V>\<^sub>1' Tr\<^bsub>ES1\<^esub>\<close> \<open>BSD ?\<V>\<^sub>2' Tr\<^bsub>ES2\<^esub>\<close> 
          \<open>BSIA ?\<rho>1' ?\<V>\<^sub>1' Tr\<^bsub>ES1\<^esub>\<close> \<open>BSIA ?\<rho>2' ?\<V>\<^sub>2' Tr\<^bsub>ES2\<^esub>\<close> 
          \<open>?\<rho>1' ?\<V>\<^sub>1'  \<subseteq>  ?\<rho>'  ?\<V>' \<inter> E\<^bsub>ES1\<^esub>\<close> \<open>?\<rho>2' ?\<V>\<^sub>2'  \<subseteq>  ?\<rho>'  ?\<V>' \<inter> E\<^bsub>ES2\<^esub>\<close>
    have "BSIA ?\<rho>' ?\<V>' Tr\<^bsub>(ES1\<parallel>ES2)\<^esub>"
      using Compositionality.compositionality_BSIA by fastforce
      
    from  validES1 validES2 composeES_yields_ES validVC 
    have "BSPTaxonomyDifferentCorrections (ES1\<parallel>ES2) \<V>" 
      unfolding BSPTaxonomyDifferentCorrections_def by auto 
    with \<open>BSIA ?\<rho>' ?\<V>' Tr\<^bsub>(ES1\<parallel>ES2)\<^esub>\<close> \<open>(?\<rho>' ?\<V>') = (\<rho> \<V>)\<close> have "SIA \<rho> \<V> Tr\<^bsub>(ES1\<parallel>ES2)\<^esub>" 
      using BSPTaxonomyDifferentCorrections.BSIA_implies_SIA_for_modified_view  by fastforce
  }
  thus ?thesis
    by auto  
qed
end

end
