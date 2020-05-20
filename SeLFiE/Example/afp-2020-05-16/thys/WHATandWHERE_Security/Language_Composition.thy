(*
Title: WHATandWHERE-Security
Authors: Sylvia Grewe, Alexander Lux, Heiko Mantel, Jens Sauer
*)
theory Language_Composition
imports WHATWHERE_Secure_Skip_Assign
begin

context WHATWHERE_Secure_Programs
begin

theorem Compositionality_Seq: 
  assumes WWs_part1: "WHATWHERE_Secure [c1]" 
  assumes WWs_part2: "WHATWHERE_Secure [c2]"
  assumes uniPPc1c2: "unique_PPc (c1;c2)"
  shows "WHATWHERE_Secure [c1;c2]"
proof (simp add: WHATWHERE_Secure_def, auto)
  fix d PP

  from uniPPc1c2 have nocommonPP: "set (PPc c1) \<inter> set (PPc c2) = {}"
    by (simp add: unique_PPV_def unique_PPc_def)
    
  from WWs_part1 obtain R1' where R1'assump: 
    "SdlHPPB d PP R1' \<and> ([c1],[c1]) \<in> R1'"
    by (simp add: WHATWHERE_Secure_def, auto)

  define R1 where "R1 = {(V,V'). (V,V') \<in> R1' \<and> set (PPV V) \<subseteq> set (PPc c1) 
    \<and> set (PPV V') \<subseteq> set (PPc c1)}"

  from R1'assump R1_def SdlHPPB_restricted_on_PP_is_SdlHPPB
  have SdlHPPR1: "SdlHPPB d PP R1"
    by force
    
  from WWs_part2 obtain R2' where R2'assump: 
    "SdlHPPB d PP R2' \<and> ([c2],[c2]) \<in> R2'"
    by (simp add: WHATWHERE_Secure_def, auto)

  define R2 where "R2 = {(V,V'). (V,V') \<in> R2' \<and> set (PPV V) \<subseteq> set (PPc c2) 
    \<and> set (PPV V') \<subseteq> set (PPc c2)}"

  from R2'assump R2_def SdlHPPB_restricted_on_PP_is_SdlHPPB
  have SdlHPPR2: "SdlHPPB d PP R2"
    by force

  from nocommonPP have nocommonDomain: "Domain R1 \<inter> Domain R2 \<subseteq> {[]}"
    by (simp add: R1_def R2_def, auto,
      metis inf_greatest inf_idem le_bot unique_V_uneq)

  with commonArefl_subset_commonDomain
  have Areflassump1: "Arefl R1 \<inter> Arefl R2 \<subseteq> {[]}"
    by force
     
  define R0 where "R0 = {(s1,s2). \<exists>c1 c1' c2 c2'. s1 = [c1;c2] \<and> s2 = [c1';c2'] \<and> 
    ([c1],[c1']) \<in> R1 \<and> ([c2],[c2']) \<in> R2}"

  with R1_def R1'assump R2_def R2'assump 
  have inR0: "([c1;c2],[c1;c2]) \<in> R0"
    by auto
  
  have "Domain R0 \<inter> Domain (R1 \<union> R2) = {}"
    by (simp add: R0_def R1_def R2_def, auto, metis Int_absorb1 Int_assoc Int_empty_left 
      nocommonPP unique_c_uneq, metis Int_absorb Int_absorb1 
      Int_assoc Int_empty_left nocommonPP unique_c_uneq)
    
  with commonArefl_subset_commonDomain
  have Areflassump2: "Arefl R0 \<inter> Arefl (R1 \<union> R2) \<subseteq> {[]}"
    by force

  have disjuptoR0: 
    "disj_dlHPP_Bisimulation_Up_To_R' d PP (R1 \<union> R2) R0"
    proof (simp add: disj_dlHPP_Bisimulation_Up_To_R'_def, auto)
        from Areflassump1 SdlHPPR1 SdlHPPR2 Union_Strong_dlHPP_Bisim
        show "SdlHPPB d PP (R1 \<union> R2)"
          by metis
      next
        from SdlHPPR1 have symR1: "sym R1" 
          by (simp add: Strong_dlHPP_Bisimulation_def)
        from SdlHPPR2 have symR2: "sym R2" 
          by (simp add: Strong_dlHPP_Bisimulation_def)
        with symR1 R0_def show "sym R0"
          by (simp add: sym_def, auto)
      next
        from SdlHPPR1 have transR1: "trans R1" 
          by (simp add: Strong_dlHPP_Bisimulation_def)
        from SdlHPPR2 have transR2: "trans R2" 
          by (simp add: Strong_dlHPP_Bisimulation_def)
        show "trans R0"
          proof -
            {
            fix V V' V''
            assume p1: "(V,V') \<in> R0"
            assume p2: "(V',V'') \<in> R0"
            have "(V,V'') \<in> R0"
              proof -
                from p1 R0_def obtain c1 c2 c1' c2' where p1assump:
                  "V = [c1;c2] \<and> V' = [c1';c2'] \<and>
                  ([c1],[c1']) \<in> R1 \<and> ([c2],[c2']) \<in> R2"
                  by auto
                with p2 R0_def obtain c1'' c2'' where p2assump:
                  "V'' = [c1'';c2''] \<and>
                  ([c1'],[c1'']) \<in> R1 \<and> ([c2'],[c2'']) \<in> R2"
                  by auto
                with p1assump transR1 transR2 have 
                  trans_assump: "([c1],[c1'']) \<in> R1 \<and> ([c2],[c2'']) \<in> R2"
                  by (simp add: trans_def, blast)
                with p1assump p2assump R0_def show ?thesis
                  by auto
              qed
             }
            thus ?thesis unfolding trans_def by blast
          qed
      next
        fix V V'
        assume "(V,V') \<in> R0"
        with R0_def show "length V = length V'"
          by auto
      next
        fix V V' i
        assume inR0: "(V,V') \<in> R0"
        assume irange: "i < length V"
        assume notIDC: "\<not> IDC d (V!i) (htchLoc (pp (V!i)))"
        from inR0 R0_def obtain c1 c2 c1' c2' where VV'assump:
          "V = [c1;c2] \<and> V' = [c1';c2'] \<and>
          ([c1],[c1']) \<in> R1 \<and> ([c2],[c2']) \<in> R2"
          by auto
        have eqnextmem: "\<And>m. \<lbrakk>c1;c2\<rbrakk>(m) = \<lbrakk>c1\<rbrakk>(m)"
          proof -
            fix m
            from nextmem_exists_and_unique obtain m' where c1nextmem:
              "\<exists>p \<alpha>. \<langle>c1,m\<rangle> \<rightarrow>\<lhd>\<alpha>\<rhd> \<langle>p,m'\<rangle> 
              \<and> (\<forall>m''. (\<exists>p \<alpha>. \<langle>c1,m\<rangle> \<rightarrow>\<lhd>\<alpha>\<rhd> \<langle>p,m''\<rangle>) \<longrightarrow> m'' = m')"
              by force

            hence eqdir1: "\<lbrakk>c1\<rbrakk>(m) = m'"
              by (simp add: NextMem_def, auto)
            
            from c1nextmem obtain p \<alpha> where "\<langle>c1,m\<rangle> \<rightarrow>\<lhd>\<alpha>\<rhd> \<langle>p,m'\<rangle>"
              by auto

            with c1nextmem have "\<exists>p \<alpha>. \<langle>c1;c2,m\<rangle> \<rightarrow>\<lhd>\<alpha>\<rhd> \<langle>p,m'\<rangle>
              \<and> (\<forall>m''. (\<exists>p \<alpha>. \<langle>c1;c2,m\<rangle> \<rightarrow>\<lhd>\<alpha>\<rhd> \<langle>p,m''\<rangle>) \<longrightarrow> m'' = m')"
              by (auto, metis MWLsSteps_det.seq1 MWLsSteps_det.seq2 
                option.exhaust, metis MWLsSteps_det_cases(3))
                            
            hence eqdir2: "\<lbrakk>c1;c2\<rbrakk>(m) = m'"
              by (simp add: NextMem_def, auto)

            with eqdir1 show "\<lbrakk>c1;c2\<rbrakk>(m) = \<lbrakk>c1\<rbrakk>(m)" 
              by auto
          qed
            
        have eqpp: "pp (c1;c2) = pp c1"
          by simp
        from VV'assump SdlHPPR1 have "IDC d c1 (htchLoc (pp c1)) 
          \<or> NDC d c1"
          by (simp add: Strong_dlHPP_Bisimulation_def, auto)
        with eqnextmem eqpp have "IDC d (c1;c2)
          (htchLoc (pp (c1;c2))) \<or> NDC d (c1;c2)"
          by (simp add: IDC_def NDC_def)
        with inR0 irange notIDC VV'assump
        show "NDC d (V!i)"
          by (simp add: IDC_def, auto)
      next
        fix V V' m1 m1' m2 \<alpha> p i
        assume inR0: "(V,V') \<in> R0"
        assume irange: "i < length V"
        assume step: "\<langle>V!i,m1\<rangle> \<rightarrow>\<lhd>\<alpha>\<rhd> \<langle>p,m2\<rangle>"
        assume dhequal: "m1 \<sim>\<^bsub>d,htchLocSet PP\<^esub> m1'"

        from inR0 R0_def obtain c1 c1' c2 c2' where R0pair:
          "V = [c1;c2] \<and> V' = [c1';c2'] \<and> ([c1],[c1']) \<in> R1
          \<and> ([c2],[c2']) \<in> R2"
          by auto
 
       from R0pair irange have i0: "i = 0" by simp

       have eqpp: "pp (c1;c2) = pp c1"
         by simp

        \<comment> \<open>get the two different cases:\<close>
        from R0pair step i0 obtain c3 where case_distinction:
          "(p = Some c2 \<and> \<langle>c1,m1\<rangle> \<rightarrow>\<lhd>\<alpha>\<rhd> \<langle>None,m2\<rangle>)
          \<or> (p = Some (c3;c2) \<and> \<langle>c1,m1\<rangle> \<rightarrow>\<lhd>\<alpha>\<rhd> \<langle>Some c3,m2\<rangle>)"
          by (simp, insert MWLsSteps_det.simps[of "c1;c2" "m1"],
            auto)
        moreover
        \<comment> \<open>Case 1: first command terminates\<close>
        {
          assume passump: "p = Some c2"
          assume StepAssump: "\<langle>c1,m1\<rangle> \<rightarrow>\<lhd>\<alpha>\<rhd> \<langle>None,m2\<rangle>"
          hence Vstep_case1:
            "\<langle>c1;c2,m1\<rangle> \<rightarrow>\<lhd>\<alpha>\<rhd> \<langle>Some c2,m2\<rangle>"
            by (simp add: MWLsSteps_det.seq1)
          
          from SdlHPPR1 StepAssump R0pair dhequal
            strongdlHPPB_aux[of "d" "PP"
            "R1" "0" "[c1]" "[c1']" "m1" "\<alpha>" "None" "m2" "m1'"]
          obtain p' \<alpha>' m2' where c1c1'reason: 
            "p' = None \<and> \<langle>c1',m1'\<rangle> \<rightarrow>\<lhd>\<alpha>'\<rhd> \<langle>p',m2'\<rangle> \<and> (\<alpha>,\<alpha>') \<in> R1 \<and> 
            dhequality_alternative d PP (pp c1) m2 m2'"
            by (simp add: stepResultsinR_def, fastforce)
 
          with eqpp c1c1'reason have conclpart:
            "\<langle>c1';c2',m1'\<rangle> \<rightarrow>\<lhd>\<alpha>'\<rhd> \<langle>Some c2',m2'\<rangle> \<and> 
            dhequality_alternative d PP (pp (c1;c2)) m2 m2'"
            by (auto, simp add: MWLsSteps_det.seq1)

          with passump R0pair c1c1'reason i0
          have case1_concl: 
          "\<exists>p' \<alpha>' m2'.
             \<langle>V'!i,m1'\<rangle> \<rightarrow>\<lhd>\<alpha>'\<rhd> \<langle>p',m2'\<rangle> \<and>
             stepResultsinR p p' (R0 \<union> (R1 \<union> R2)) \<and>
             ((\<alpha>,\<alpha>') \<in> R0 \<or> (\<alpha>,\<alpha>') \<in> R1 \<or> (\<alpha>,\<alpha>') \<in> R2) \<and>
             dhequality_alternative d PP (pp (V!i)) m2 m2'"
          by (simp add: stepResultsinR_def, auto)
        }
        moreover
        \<comment> \<open>Case 2: first command does not terminate\<close>
        {
          assume passump: "p = Some (c3;c2)"
          assume StepAssump: "\<langle>c1,m1\<rangle> \<rightarrow>\<lhd>\<alpha>\<rhd> \<langle>Some c3,m2\<rangle>"

          hence Vstep_case2:  "\<langle>c1;c2,m1\<rangle> \<rightarrow>\<lhd>\<alpha>\<rhd> \<langle>Some (c3;c2),m2\<rangle>"
            by (simp add: MWLsSteps_det.seq2)

          from SdlHPPR1 StepAssump R0pair dhequal
            strongdlHPPB_aux[of "d" "PP"
            "R1" "0" "[c1]" "[c1']" "m1" "\<alpha>" "Some c3" "m2" "m1'"]
          obtain p' c3' \<alpha>' m2' where c1c1'reason: 
            "p' = Some c3' \<and> \<langle>c1',m1'\<rangle> \<rightarrow>\<lhd>\<alpha>'\<rhd> \<langle>p',m2'\<rangle> \<and> 
            ([c3],[c3']) \<in> R1 \<and> (\<alpha>,\<alpha>') \<in> R1 \<and>
            dhequality_alternative d PP (pp c1) m2 m2'"
            by (simp add: stepResultsinR_def, fastforce)

          with eqpp c1c1'reason have conclpart:
            "\<langle>c1';c2',m1'\<rangle> \<rightarrow>\<lhd>\<alpha>'\<rhd> \<langle>Some (c3';c2'),m2'\<rangle> \<and> 
            dhequality_alternative d PP (pp (c1;c2)) m2 m2'"
            by (auto, simp add: MWLsSteps_det.seq2)

          from c1c1'reason R0pair R0_def have 
            "([c3;c2],[c3';c2']) \<in> R0"
            by auto
          
          with R0pair conclpart passump c1c1'reason i0
          have case1_concl: 
            "\<exists>p' \<alpha>' m2'. \<langle>V'!i,m1'\<rangle> \<rightarrow>\<lhd>\<alpha>'\<rhd> \<langle>p',m2'\<rangle> \<and>
            stepResultsinR p p' (R0 \<union> (R1 \<union> R2)) \<and>
            ((\<alpha>,\<alpha>') \<in> R0 \<or> (\<alpha>,\<alpha>') \<in> R1 \<or> (\<alpha>,\<alpha>') \<in> R2) \<and>
            dhequality_alternative d PP (pp (V!i)) m2 m2'"
            by (simp add: stepResultsinR_def, auto)
        }
        ultimately
        show "\<exists>p' \<alpha>' m2'. \<langle>V'!i,m1'\<rangle> \<rightarrow>\<lhd>\<alpha>'\<rhd> \<langle>p',m2'\<rangle> \<and>
             stepResultsinR p p' (R0 \<union> (R1 \<union> R2)) \<and>
             ((\<alpha>,\<alpha>') \<in> R0 \<or> (\<alpha>,\<alpha>') \<in> R1 \<or> (\<alpha>,\<alpha>') \<in> R2) \<and>
             dhequality_alternative d PP (pp (V!i)) m2 m2'"
          by blast
      qed
        
  with inR0 Areflassump2 Up_To_Technique
  have "SdlHPPB d PP (R0 \<union> (R1 \<union> R2))"
    by auto 

  with inR0 show "\<exists>R. SdlHPPB d PP R \<and> ([c1;c2],[c1;c2]) \<in> R"
    by auto

qed


theorem Compositionality_Spawn:
  assumes WWs_threads: "WHATWHERE_Secure V"
  assumes uniPPspawn: "unique_PPc (spawn\<^bsub>\<iota>\<^esub> V)"
  shows "WHATWHERE_Secure [spawn\<^bsub>\<iota>\<^esub> V]"
proof (simp add: WHATWHERE_Secure_def, auto)
  fix d PP
    
  from uniPPspawn have pp_difference: "\<iota> \<notin> set (PPV V)"
    by (simp add: unique_PPc_def)
  
  \<comment> \<open>Step 1\<close>
  from WWs_threads obtain R' where R'assump:
    "SdlHPPB d PP R' \<and> (V,V) \<in> R'"
    by (simp add: WHATWHERE_Secure_def, auto)

  define R where "R = {(V',V''). (V',V'') \<in> R' \<and> set (PPV V') \<subseteq> set (PPV V)
    \<and> set (PPV V'') \<subseteq> set (PPV V)}"

  from R'assump R_def SdlHPPB_restricted_on_PP_is_SdlHPPB
  have SdlHPPR: "SdlHPPB d PP R"
    by force

  \<comment> \<open>Step 2\<close>
  define R0 where "R0 = {(sp1,sp2). \<exists>\<iota>' \<iota>'' V' V''. 
    sp1 = [spawn\<^bsub>\<iota>'\<^esub> V'] \<and> sp2 = [spawn\<^bsub>\<iota>''\<^esub> V'']
    \<and> \<iota>' \<notin> set (PPV V) \<and> \<iota>'' \<notin> set (PPV V) \<and> (V',V'') \<in> R}"

  with R_def R'assump pp_difference have inR0: 
    "([spawn\<^bsub>\<iota>\<^esub> V],[spawn\<^bsub>\<iota>\<^esub> V]) \<in> R0"
    by auto
    
  \<comment> \<open>Step 3\<close>
  from R0_def R_def R'assump have "Domain R0 \<inter> Domain R = {}"
    by auto

  with commonArefl_subset_commonDomain
  have Areflassump: "Arefl R0 \<inter> Arefl R \<subseteq> {[]}"
    by force
  
  \<comment> \<open>Step 4\<close>
  have disjuptoR0:
    "disj_dlHPP_Bisimulation_Up_To_R' d PP R R0"
    proof (simp add: disj_dlHPP_Bisimulation_Up_To_R'_def, auto)
      from SdlHPPR show "SdlHPPB d PP R"
        by auto
    next
      from SdlHPPR have symR: "sym R" 
        by (simp add: Strong_dlHPP_Bisimulation_def)
      with R0_def show "sym R0" 
        by (simp add: sym_def, auto)
    next  
      from SdlHPPR have transR: "trans R"
        by (simp add: Strong_dlHPP_Bisimulation_def)
      with R0_def show "trans R0"
        proof -
          {
          fix V1 V2 V3
          assume inR1: "(V1,V2) \<in> R0"
          assume inR2: "(V2,V3) \<in> R0"
          from inR1 R0_def obtain W W' \<iota> \<iota>' where p1: "V1 = [spawn\<^bsub>\<iota>\<^esub> W] 
            \<and> V2 = [spawn\<^bsub>\<iota>'\<^esub> W'] \<and> \<iota> \<notin> set (PPV V) \<and> \<iota>' \<notin> set (PPV V)
            \<and> (W,W') \<in> R"
            by auto
          with inR2 R0_def obtain W'' \<iota>'' where p2: "V3 = [spawn\<^bsub>\<iota>''\<^esub> W'']
            \<and> \<iota>'' \<notin> set (PPV V) \<and> (W',W'') \<in> R"
            by auto
          from p1 p2 transR have "(W,W'') \<in> R" 
            by (simp add: trans_def, auto)
          with p1 p2 R0_def have "(V1,V3) \<in> R0"
            by auto
          }
          thus ?thesis unfolding trans_def by blast
        qed
    next
      fix V' V''
      from SdlHPPR have eqlenR: "(V',V'') \<in> R \<Longrightarrow> length V' = length V''"
        by (simp add: Strong_dlHPP_Bisimulation_def, auto)
      with R0_def show "(V',V'') \<in> R0 \<Longrightarrow> length V' = length V''"
        by auto
    next
      fix V' V'' i
      assume inR0: "(V',V'') \<in> R0"
      assume irange: "i < length V'"
      from inR0 R0_def obtain \<iota>' \<iota>'' W' W'' 
        where R0pair: "V' = [spawn\<^bsub>\<iota>'\<^esub> W'] \<and> V'' = [spawn\<^bsub>\<iota>''\<^esub> W'']"
        by auto
      {
        fix m
        from nextmem_exists_and_unique obtain m' where spawnnextmem:
          "\<exists>p \<alpha>. \<langle>spawn\<^bsub>\<iota>'\<^esub> W',m\<rangle> \<rightarrow>\<lhd>\<alpha>\<rhd> \<langle>p,m'\<rangle> 
          \<and> (\<forall>m''. (\<exists>p \<alpha>. \<langle>spawn\<^bsub>\<iota>'\<^esub> W',m\<rangle> \<rightarrow>\<lhd>\<alpha>\<rhd> \<langle>p,m''\<rangle>) \<longrightarrow> m'' = m')"
          by force
      
        hence "m = m'"
          by (metis MWLsSteps_det.spawn)

        with spawnnextmem have eqnextmem: 
          "\<lbrakk>spawn\<^bsub>\<iota>'\<^esub> W'\<rbrakk>(m) = m"
          by (simp add: NextMem_def, auto)
      }

      with R0pair irange show "NDC d (V'!i)"
        by (simp add: NDC_def)
    next
      fix V' V'' i m1 m1' m2 \<alpha> p
      assume inR0: "(V',V'') \<in> R0"
      assume irange: "i < length V'"
      assume step: "\<langle>V'!i,m1\<rangle> \<rightarrow>\<lhd>\<alpha>\<rhd> \<langle>p,m2\<rangle>"
      assume dhequal: "m1 \<sim>\<^bsub>d,htchLocSet PP\<^esub> m1'"

      from inR0 R0_def obtain \<iota>' \<iota>'' W' W'' 
        where R0pair: "V' = [spawn\<^bsub>\<iota>'\<^esub> W'] 
        \<and> V'' = [spawn\<^bsub>\<iota>''\<^esub> W''] \<and> (W',W'') \<in> R"
        by auto
      
      with step irange
      have conc_step1: "\<alpha> = W' \<and> p = None \<and> m2 = m1"
        by (simp, metis MWLsSteps_det_cases(6))
        
      from R0pair irange 
      obtain p' \<alpha>' m2' where conc_step2: "\<langle>V''!i,m1'\<rangle> \<rightarrow>\<lhd>\<alpha>'\<rhd> \<langle>p',m2'\<rangle>
        \<and> p' = None \<and> \<alpha>' = W'' \<and> m2' = m1'"
        by (simp, metis MWLsSteps_det.spawn) 
     
      with R0pair conc_step1 dhequal irange
      show "\<exists>p' \<alpha>' m2'. \<langle>V''!i,m1'\<rangle> \<rightarrow>\<lhd>\<alpha>'\<rhd> \<langle>p',m2'\<rangle> \<and>
        stepResultsinR p p' (R0 \<union> R) \<and>
        ((\<alpha>,\<alpha>') \<in> R0 \<or> (\<alpha>,\<alpha>') \<in> R) \<and>
        dhequality_alternative d PP (pp (V'!i)) m2 m2'"
        by (simp add: stepResultsinR_def 
          dhequality_alternative_def, auto)       
    qed
  \<comment> \<open>Step 5\<close>
  with Areflassump Up_To_Technique
  have "SdlHPPB d PP (R0 \<union> R)"
    by auto
      
  with inR0 show "\<exists>R. SdlHPPB d PP R \<and>
    ([spawn\<^bsub>\<iota>\<^esub> V],[spawn\<^bsub>\<iota>\<^esub> V]) \<in> R"  
    by auto
qed


theorem Compositionality_If:
  assumes dind: "\<forall>d. b \<equiv>\<^bsub>d\<^esub> b"
  assumes WWs_branch1: "WHATWHERE_Secure [c1]"
  assumes WWs_branch2: "WHATWHERE_Secure [c2]"
  assumes uniPPif: "unique_PPc (if\<^bsub>\<iota>\<^esub> b then c1 else c2 fi)"
  shows "WHATWHERE_Secure [if\<^bsub>\<iota>\<^esub> b then c1 else c2 fi]"
proof (simp add: WHATWHERE_Secure_def, auto)
  fix d PP
  from uniPPif have nocommonPP: "set (PPc c1) \<inter> set (PPc c2) = {}"
    by (simp add: unique_PPc_def)

  from uniPPif have pp_difference: "\<iota> \<notin> set (PPc c1) \<union> set (PPc c2)"
    by (simp add: unique_PPc_def)
  
  from WWs_branch1 obtain R1' where R1'assump: 
    "SdlHPPB d PP R1' \<and> ([c1],[c1]) \<in> R1'"
    by (simp add: WHATWHERE_Secure_def, auto)
  
  define R1 where "R1 = {(V,V'). (V,V') \<in> R1' \<and> set (PPV V) \<subseteq> set (PPc c1) 
    \<and> set (PPV V') \<subseteq> set (PPc c1)}"

  from R1'assump R1_def SdlHPPB_restricted_on_PP_is_SdlHPPB
  have SdlHPPR1: "SdlHPPB d PP R1"
    by force
    
  from WWs_branch2 obtain R2' where R2'assump: 
    "SdlHPPB d PP R2' \<and> ([c2],[c2]) \<in> R2'"
    by (simp add: WHATWHERE_Secure_def, auto)

  define R2 where "R2 = {(V,V'). (V,V') \<in> R2' \<and> set (PPV V) \<subseteq> set (PPc c2) 
    \<and> set (PPV V') \<subseteq> set (PPc c2)}"

  from R2'assump R2_def SdlHPPB_restricted_on_PP_is_SdlHPPB
  have SdlHPPR2: "SdlHPPB d PP R2"
    by force

  from nocommonPP have "Domain R1 \<inter> Domain R2 \<subseteq> {[]}"

    by (simp add: R1_def R2_def, auto,
      metis empty_subsetI inf_idem inf_mono set_eq_subset unique_V_uneq)

  with commonArefl_subset_commonDomain
  have Areflassump1: "Arefl R1 \<inter> Arefl R2 \<subseteq> {[]}"
    by force
    
  with SdlHPPR1 SdlHPPR2 Union_Strong_dlHPP_Bisim have SdlHPPR1R2: 
    "SdlHPPB d PP (R1 \<union> R2)"
    by force

  define R where "R = (R1 \<union> R2) \<union> {([],[])}"
  
  define R0 where "R0 = {(i1,i2). \<exists>\<iota>' \<iota>'' b' b'' c1' c1'' c2' c2''. 
    i1 = [if\<^bsub>\<iota>'\<^esub> b' then c1' else c2' fi]
    \<and> i2 = [if\<^bsub>\<iota>''\<^esub> b'' then c1'' else c2'' fi] 
    \<and> \<iota>' \<notin> (set (PPc c1) \<union> set (PPc c2))
    \<and> \<iota>'' \<notin> (set (PPc c1) \<union> set (PPc c2)) \<and> ([c1'],[c1'']) \<in> R1
    \<and> ([c2'],[c2'']) \<in> R2 \<and> b' \<equiv>\<^bsub>d\<^esub> b''}"

  with R_def R1_def R1'assump R2_def R2'assump pp_difference dind
  have inR0: "([if\<^bsub>\<iota>\<^esub> b then c1 else c2 fi],[if\<^bsub>\<iota>\<^esub> b then c1 else c2 fi]) \<in> R0"
    by auto
  
  from R0_def R_def R1_def R2_def
  have "Domain R0 \<inter> Domain R = {}"
    by auto
    
  with commonArefl_subset_commonDomain
  have Areflassump2: "Arefl R0 \<inter> Arefl R \<subseteq> {[]}"
    by force
  
  have disjuptoR0: 
    "disj_dlHPP_Bisimulation_Up_To_R' d PP R R0"
    proof (simp add: disj_dlHPP_Bisimulation_Up_To_R'_def, auto)
      from SdlHPPR1R2 adding_emptypair_keeps_SdlHPPB
      show "SdlHPPB d PP R"
        by (simp add: R_def)
    next
      from SdlHPPR1 have symR1: "sym R1"
        by (simp add: Strong_dlHPP_Bisimulation_def)
      from SdlHPPR2 have symR2: "sym R2"
        by (simp add: Strong_dlHPP_Bisimulation_def)
      from symR1 symR2 d_indistinguishable_sym R0_def show "sym R0"
        by (simp add: sym_def, fastforce)
    next
      from SdlHPPR1 have transR1: "trans R1"
        by (simp add: Strong_dlHPP_Bisimulation_def)
      from SdlHPPR2 have transR2: "trans R2"
        by (simp add: Strong_dlHPP_Bisimulation_def)
      show "trans R0"
        proof  -
          {
            fix V' V'' V'''
            assume p1: "(V',V'') \<in> R0"
            assume p2: "(V'',V''') \<in> R0"
            
            from p1 R0_def obtain \<iota>' \<iota>'' b' b'' c1' c1'' c2' c2'' where
              passump1: "V' = [if\<^bsub>\<iota>'\<^esub> b' then c1' else c2' fi]
              \<and> V'' = [if\<^bsub>\<iota>''\<^esub> b'' then c1'' else c2'' fi]
              \<and> \<iota>' \<notin> (set (PPc c1) \<union> set (PPc c2))
              \<and> \<iota>'' \<notin> (set (PPc c1) \<union> set (PPc c2)) 
              \<and> ([c1'],[c1'']) \<in> R1 \<and> ([c2'],[c2'']) \<in> R2 
              \<and> b' \<equiv>\<^bsub>d\<^esub> b''"
              by force

            with p2 R0_def obtain \<iota>''' b''' c1''' c2''' where
              passump2: "V''' = [if\<^bsub>\<iota>'''\<^esub> b''' then c1''' else c2''' fi]
              \<and> \<iota>''' \<notin> (set (PPc c1) \<union> set (PPc c2)) 
              \<and> ([c1''],[c1''']) \<in> R1 \<and> ([c2''],[c2''']) \<in> R2 
              \<and> b'' \<equiv>\<^bsub>d\<^esub> b'''"
              by force

            with passump1 transR1 transR2 d_indistinguishable_trans
            have "([c1'],[c1''']) \<in> R1 \<and> ([c2'],[c2''']) \<in> R2 
              \<and> b' \<equiv>\<^bsub>d\<^esub> b'''"
              by (metis transD)

            with passump1 passump2 R0_def have "(V',V''') \<in> R0"
              by auto
          }
          thus ?thesis unfolding trans_def by blast
        qed
    next
      fix V V'
      assume inR0: "(V,V') \<in> R0"
      with R0_def show "length V = length V'" by auto
    next
      fix V' V'' i
      assume inR0: "(V',V'') \<in> R0"
      assume irange: "i < length V'"
      assume notIDC: "\<not> IDC d (V'!i) (htchLoc (pp (V'!i)))"

      from inR0 R0_def obtain \<iota>' \<iota>'' b' b'' c1' c1'' c2' c2'' 
        where R0pair: "V' = [if\<^bsub>\<iota>'\<^esub> b' then c1' else c2' fi] 
        \<and> V'' = [if\<^bsub>\<iota>''\<^esub> b'' then c1'' else c2'' fi]
        \<and> \<iota>' \<notin> set (PPc c1) \<union> set (PPc c2) 
        \<and> \<iota>'' \<notin> set (PPc c1) \<union> set (PPc c2) 
        \<and> ([c1'],[c1'']) \<in> R1 \<and> ([c2'],[c2'']) \<in> R2
        \<and> b' \<equiv>\<^bsub>d\<^esub> b''"
        by force
      
      have "NDC d (if\<^bsub>\<iota>'\<^esub> b' then c1' else c2' fi)"
        proof -
          {
            fix m
            from nextmem_exists_and_unique obtain m' p \<alpha> where ifnextmem:
              "\<langle>if\<^bsub>\<iota>'\<^esub> b' then c1' else c2' fi,m\<rangle> \<rightarrow>\<lhd>\<alpha>\<rhd> \<langle>p,m'\<rangle> 
              \<and> (\<forall>m''.(\<exists>p \<alpha>.\<langle>if\<^bsub>\<iota>'\<^esub> b' then c1' else c2' fi,m\<rangle> \<rightarrow>\<lhd>\<alpha>\<rhd> \<langle>p,m''\<rangle>) 
              \<longrightarrow> m'' = m')"
              by blast
            
            hence "m = m'"
              by (metis MWLsSteps_det.iffalse MWLsSteps_det.iftrue)
            
            with ifnextmem have eqnextmem: 
              "\<lbrakk>if\<^bsub>\<iota>'\<^esub> b' then c1' else c2' fi\<rbrakk>(m) = m"
              by (simp add: NextMem_def, auto)
          }
          thus ?thesis
            by (simp add: NDC_def)
        qed

      with R0pair irange show "NDC d (V'!i)"
        by simp
    next
      fix V' V'' i m1 m1' m2 \<alpha> p 
      assume inR0: "(V',V'') \<in> R0"
      assume irange: "i < length V'"
      assume step: "\<langle>V'!i,m1\<rangle> \<rightarrow>\<lhd>\<alpha>\<rhd> \<langle>p,m2\<rangle>"
      assume dhequal: "m1 \<sim>\<^bsub>d,htchLocSet PP\<^esub> m1'"

      from inR0 R0_def obtain \<iota>' \<iota>'' b' b'' c1' c1'' c2' c2'' 
        where R0pair: "V' = [if\<^bsub>\<iota>'\<^esub> b' then c1' else c2' fi] 
        \<and> V'' = [if\<^bsub>\<iota>''\<^esub> b'' then c1'' else c2'' fi]
        \<and> \<iota>' \<notin> set (PPc c1) \<union> set (PPc c2) 
        \<and> \<iota>'' \<notin> set (PPc c1) \<union> set (PPc c2) 
        \<and> ([c1'],[c1'']) \<in> R1 \<and> ([c2'],[c2'']) \<in> R2
        \<and> b' \<equiv>\<^bsub>d\<^esub> b''"
        by force

      with R0pair irange step have case_distinction:
        "(p = Some c1' \<and> BMap (E b' m1) = True)
        \<or> (p = Some c2' \<and> BMap (E b' m1) = False)"
        by (simp, metis MWLsSteps_det_cases(4))
      moreover
      \<comment> \<open>Case 1: b evaluates to True\<close>
      {
        assume passump: "p = Some c1'"
        assume eval: "BMap (E b' m1) = True"

        from R0pair step irange have stepconcl: "\<alpha> = [] \<and> m2 = m1"
          by (simp, metis MWLs_semantics.MWLsSteps_det_cases(4))
          
        from eval R0pair dhequal have eval': "BMap (E b'' m1') = True"
          by (simp add: d_indistinguishable_def dH_equal_def, auto)

        hence step': "\<langle>if\<^bsub>\<iota>''\<^esub> b'' then c1'' else c2'' fi,m1'\<rangle> \<rightarrow>\<lhd>[]\<rhd> 
          \<langle>Some c1'',m1'\<rangle>"
          by (simp add: MWLsSteps_det.iftrue)

        with passump R0pair R_def dhequal stepconcl irange
        have "\<exists>p' \<alpha>' m2'. \<langle>V''!i,m1'\<rangle> \<rightarrow>\<lhd>\<alpha>'\<rhd> \<langle>p',m2'\<rangle> \<and>
        stepResultsinR p p' (R0 \<union> R) \<and>
        ((\<alpha>,\<alpha>') \<in> R0 \<or> (\<alpha>,\<alpha>') \<in> R) \<and>
        dhequality_alternative d PP (pp (V'!i)) m2 m2'"
          by (simp add: stepResultsinR_def dhequality_alternative_def, 
            auto)
      }
      moreover
      \<comment> \<open>Case 2: b evaluates to False\<close>
      {
        assume passump: "p = Some c2'"
        assume eval: "BMap (E b' m1) = False"

        from R0pair step irange have stepconcl: "\<alpha> = [] \<and> m2 = m1"
          by (simp, metis MWLs_semantics.MWLsSteps_det_cases(4))

        from eval R0pair dhequal have eval': "BMap (E b'' m1') = False"
          by (simp add: d_indistinguishable_def dH_equal_def, auto)

        hence step': "\<langle>if\<^bsub>\<iota>''\<^esub> b'' then c1'' else c2'' fi,m1'\<rangle> \<rightarrow>\<lhd>[]\<rhd> 
          \<langle>Some c2'',m1'\<rangle>"
          by (simp add: MWLsSteps_det.iffalse)

        with passump R0pair R_def dhequal stepconcl irange
        have "\<exists>p' \<alpha>' m2'. \<langle>V''!i,m1'\<rangle> \<rightarrow>\<lhd>\<alpha>'\<rhd> \<langle>p',m2'\<rangle> \<and>
        stepResultsinR p p' (R0 \<union> R) \<and>
        ((\<alpha>,\<alpha>') \<in> R0 \<or> (\<alpha>,\<alpha>') \<in> R) \<and>
        dhequality_alternative d PP (pp (V'!i)) m2 m2'"
          by (simp add: stepResultsinR_def dhequality_alternative_def, 
            auto)
      }
      ultimately 
      show "\<exists>p' \<alpha>' m2'. \<langle>V''!i,m1'\<rangle> \<rightarrow>\<lhd>\<alpha>'\<rhd> \<langle>p',m2'\<rangle> \<and>
        stepResultsinR p p' (R0 \<union> R) \<and>
        ((\<alpha>,\<alpha>') \<in> R0 \<or> (\<alpha>,\<alpha>') \<in> R) \<and>
        dhequality_alternative d PP (pp (V'!i)) m2 m2'"
        by auto
    qed
      
  with Areflassump2 Up_To_Technique
  have "SdlHPPB d PP (R0 \<union> R)"
    by auto

  with inR0 show "\<exists>R. SdlHPPB d PP R
    \<and> ([if\<^bsub>\<iota>\<^esub> b then c1 else c2 fi],[if\<^bsub>\<iota>\<^esub> b then c1 else c2 fi]) \<in> R"
    by auto
    
qed

theorem Compositionality_While:
  assumes dind: "\<forall>d. b \<equiv>\<^bsub>d\<^esub> b"
  assumes WWs_body: "WHATWHERE_Secure [c]"
  assumes uniPPwhile: "unique_PPc (while\<^bsub>\<iota>\<^esub> b do c od)"
  shows "WHATWHERE_Secure [while\<^bsub>\<iota>\<^esub> b do c od]"
proof (simp add: WHATWHERE_Secure_def, auto)
  fix d PP 
  
  from uniPPwhile have pp_difference: "\<iota> \<notin> set (PPc c)"
    by (simp add: unique_PPc_def)
   
  from WWs_body obtain R' where R'assump:
    "SdlHPPB d PP R' \<and> ([c],[c]) \<in> R'"
    by (simp add: WHATWHERE_Secure_def, auto)

  \<comment> \<open>add the empty pair because it is needed later in the proof\<close>
  define R where "R = {(V,V'). (V,V') \<in> R' \<and> set (PPV V) \<subseteq> set (PPc c) \<and>
    set (PPV V') \<subseteq> set (PPc c)} \<union> {([],[])}"
  
  with R'assump SdlHPPB_restricted_on_PP_is_SdlHPPB 
    adding_emptypair_keeps_SdlHPPB
  have SdlHPPR: "SdlHPPB d PP R"
    proof - 
      from R'assump SdlHPPB_restricted_on_PP_is_SdlHPPB have
        "SdlHPPB d PP 
          {(V,V'). (V,V') \<in> R' \<and> set (PPV V) \<subseteq> set (PPc c) \<and>
          set (PPV V') \<subseteq> set (PPc c)}"
        by force

      with adding_emptypair_keeps_SdlHPPB have
        "SdlHPPB d PP 
          ({(V,V'). (V,V') \<in> R' \<and> set (PPV V) \<subseteq> set (PPc c) \<and>
          set (PPV V') \<subseteq> set (PPc c)} \<union> {([],[])})"
        by auto

      with R_def show ?thesis
        by auto
    qed
 
  define R1 where "R1 = {(w1,w2). \<exists>\<iota> \<iota>' b b' c1 c1' c2 c2'. 
    w1 = [c1;(while\<^bsub>\<iota>\<^esub> b do c2 od)]
    \<and> w2 = [c1';(while\<^bsub>\<iota>'\<^esub> b' do c2' od)] 
    \<and> \<iota> \<notin> set (PPc c) \<and> \<iota>' \<notin> set (PPc c) 
    \<and> ([c1],[c1']) \<in> R \<and> ([c2],[c2']) \<in> R
    \<and> b \<equiv>\<^bsub>d\<^esub> b'}"

  define R2 where "R2 = {(w1,w2). \<exists>\<iota> \<iota>' b b' c1 c1'. 
    w1 = [while\<^bsub>\<iota>\<^esub> b do c1 od]
    \<and> w2 = [while\<^bsub>\<iota>'\<^esub> b' do c1' od] 
    \<and> \<iota> \<notin> set (PPc c) \<and> \<iota>' \<notin> set (PPc c) \<and>
    ([c1],[c1']) \<in> R \<and> b \<equiv>\<^bsub>d\<^esub> b'}"

  define R0 where "R0 = R1 \<union> R2" 

  from R2_def R_def R'assump pp_difference dind
  have inR2: "([while\<^bsub>\<iota>\<^esub> b do c od],[while\<^bsub>\<iota>\<^esub> b do c od]) \<in> R2"
    by auto

  from R0_def R1_def R2_def R_def R'assump have 
    "Domain R0 \<inter> Domain R = {}"
    by auto

  with commonArefl_subset_commonDomain
  have Areflassump: "Arefl R0 \<inter> Arefl R \<subseteq> {[]}"
    by force

  \<comment> \<open>show some facts about R1 and R2 needed later in the proof at several positions\<close>
  from SdlHPPR have symR: "sym R"
    by (simp add: Strong_dlHPP_Bisimulation_def)
  from symR R1_def d_indistinguishable_sym have symR1: "sym R1"
    by (simp add: sym_def, fastforce)
  from symR R2_def d_indistinguishable_sym have symR2: "sym R2"
    by (simp add: sym_def, fastforce)

  have disjuptoR1R2:
    "disj_dlHPP_Bisimulation_Up_To_R' d PP R R0"
  proof (simp add: disj_dlHPP_Bisimulation_Up_To_R'_def, auto)
      from SdlHPPR show "SdlHPPB d PP R"
        by auto
    next
      from symR1 symR2 R0_def show "sym R0"
        by (simp add: sym_def)
    next
      from SdlHPPR have transR: "trans R"
        by (simp add: Strong_dlHPP_Bisimulation_def)
      have transR1: "trans R1"
        proof - 
          {
            fix V V' V''
            assume p1: "(V,V') \<in> R1"
            assume p2: "(V',V'') \<in> R1"
            
            from p1 R1_def obtain \<iota> \<iota>' b b' c1 c1' c2 c2' where passump1:
              "V = [c1;(while\<^bsub>\<iota>\<^esub> b do c2 od)]
              \<and> V' = [c1';(while\<^bsub>\<iota>'\<^esub> b' do c2' od)] 
              \<and> \<iota> \<notin> set (PPc c) \<and> \<iota>' \<notin> set (PPc c) 
              \<and> ([c1],[c1']) \<in> R \<and> ([c2],[c2']) \<in> R
              \<and> b \<equiv>\<^bsub>d\<^esub> b'"
              by force

            with p2 R1_def obtain \<iota>'' b'' c1'' c2'' where passump2:
              "V'' = [c1'';(while\<^bsub>\<iota>''\<^esub> b'' do c2'' od)] \<and> \<iota>'' \<notin> set (PPc c) 
              \<and> ([c1'],[c1'']) \<in> R \<and> ([c2'],[c2'']) \<in> R
              \<and> b' \<equiv>\<^bsub>d\<^esub> b''"
              by force

            with passump1 transR d_indistinguishable_trans
            have "([c1],[c1'']) \<in> R \<and> ([c2],[c2'']) \<in> R \<and> b \<equiv>\<^bsub>d\<^esub> b''"
              by (metis trans_def)
              
            with passump1 passump2 R1_def have "(V,V'') \<in> R1"
              by auto
          }
          thus ?thesis unfolding trans_def by blast
        qed
          
        have transR2: "trans R2"
         proof - 
          {
            fix V V' V''
            assume p1: "(V,V') \<in> R2"
            assume p2: "(V',V'') \<in> R2"

            from p1 R2_def obtain \<iota> \<iota>' b b' c1 c1' where passump1:
              "V = [while\<^bsub>\<iota>\<^esub> b do c1 od]
              \<and> V' = [while\<^bsub>\<iota>'\<^esub> b' do c1' od] 
              \<and> \<iota> \<notin> set (PPc c) \<and> \<iota>' \<notin> set (PPc c) 
              \<and> ([c1],[c1']) \<in> R \<and> b \<equiv>\<^bsub>d\<^esub> b'"
              by force

            with p2 R2_def obtain \<iota>'' b'' c1'' where passump2:
              "V'' = [while\<^bsub>\<iota>''\<^esub> b'' do c1'' od] \<and> \<iota>'' \<notin> set (PPc c) 
              \<and> ([c1'],[c1'']) \<in> R \<and> b' \<equiv>\<^bsub>d\<^esub> b''"
              by force

            with passump1 transR d_indistinguishable_trans
            have "([c1],[c1'']) \<in> R \<and> b \<equiv>\<^bsub>d\<^esub> b''"
              by (metis trans_def)

            with passump1 passump2 R2_def have "(V,V'') \<in> R2"
              by auto
          }
          thus ?thesis unfolding trans_def by blast
        qed

      from SdlHPPR have eqlenR: "\<forall>(V,V')\<in>R. length V = length V'"
        by (simp add: Strong_dlHPP_Bisimulation_def)
      from R1_def eqlenR have eqlenR1: "\<forall>(V,V')\<in>R1. length V = length V'"
        by auto
      from R2_def eqlenR have eqlenR2: "\<forall>(V,V')\<in>R2. length V = length V'"
        by auto

      from R1_def R2_def have "Domain R1 \<inter> Domain R2 = {}"
        by auto

      with commonArefl_subset_commonDomain have Arefl_a:
        "Arefl R1 \<inter> Arefl R2 = {}"
        by force

      with symR1 symR2 transR1 transR2 eqlenR1 eqlenR2 trans_RuR'
      have "trans (R1 \<union> R2)"
        by force
      with R0_def show "trans R0" by auto
    next
      fix V V'
      assume inR0: "(V,V') \<in> R0"
      with R0_def R1_def R2_def show "length V = length V'" by auto
    next
      fix V V' i
      assume inR0: "(V,V') \<in> R0"
      assume irange: "i < length V"
      assume notIDC: "\<not> IDC d (V!i) 
        (htchLoc (pp (V!i)))"

      from inR0 R0_def R1_def R2_def obtain \<iota> \<iota>' b b' c1 c1' c2 c2' 
        where R0pair: "((V = [c1;(while\<^bsub>\<iota>\<^esub> b do c2 od)] 
        \<and> V' = [c1';(while\<^bsub>\<iota>'\<^esub> b' do c2' od)])
        \<or> (V = [while\<^bsub>\<iota>\<^esub> b do c1 od] \<and> V' = [while\<^bsub>\<iota>'\<^esub> b' do c1' od]))
        \<and> \<iota> \<notin> set (PPc c) \<and> \<iota>' \<notin> set (PPc c) 
        \<and> ([c1],[c1']) \<in> R \<and> ([c2],[c2']) \<in> R
        \<and> b \<equiv>\<^bsub>d\<^esub> b'"
        by force

      with irange SdlHPPR strongdlHPPB_NDCIDCaux
      [of "d" "PP" "R" "[c1]" "[c1']" "i"]
      have c1NDCIDC: 
        "NDC d c1 \<or> IDC d c1 (htchLoc (pp c1))"
        by auto

      \<comment> \<open>first alternative for V and V'\<close>
      have case1: "NDC d (c1;(while\<^bsub>\<iota>\<^esub> b do c2 od)) \<or>
        IDC d (c1;(while\<^bsub>\<iota>\<^esub> b do c2 od))
        (htchLoc (pp (c1;(while\<^bsub>\<iota>\<^esub> b do c2 od))))"
        proof -
          have eqnextmem: "\<And>m. \<lbrakk>c1;(while\<^bsub>\<iota>\<^esub> b do c2 od)\<rbrakk>(m) = \<lbrakk>c1\<rbrakk>(m)"
          proof -
            fix m
            from nextmem_exists_and_unique obtain m' where c1nextmem:
              "\<exists>p \<alpha>. \<langle>c1,m\<rangle> \<rightarrow>\<lhd>\<alpha>\<rhd> \<langle>p,m'\<rangle> 
              \<and> (\<forall>m''. (\<exists>p \<alpha>. \<langle>c1,m\<rangle> \<rightarrow>\<lhd>\<alpha>\<rhd> \<langle>p,m''\<rangle>) \<longrightarrow> m'' = m')"
              by force

            hence eqdir1: "\<lbrakk>c1\<rbrakk>(m) = m'"
              by (simp add: NextMem_def, auto)
            
            from c1nextmem obtain p \<alpha> where "\<langle>c1,m\<rangle> \<rightarrow>\<lhd>\<alpha>\<rhd> \<langle>p,m'\<rangle>"
              by auto

            with c1nextmem have 
              "\<exists>p \<alpha>. \<langle>c1;(while\<^bsub>\<iota>\<^esub> b do c2 od),m\<rangle> \<rightarrow>\<lhd>\<alpha>\<rhd> \<langle>p,m'\<rangle>
              \<and> (\<forall>m''. (\<exists>p \<alpha>. \<langle>c1;(while\<^bsub>\<iota>\<^esub> b do c2 od),m\<rangle> \<rightarrow>\<lhd>\<alpha>\<rhd> \<langle>p,m''\<rangle>) 
              \<longrightarrow> m'' = m')"
              by (auto, metis MWLsSteps_det.seq1 MWLsSteps_det.seq2 
                option.exhaust, metis MWLsSteps_det_cases(3))
             
            hence eqdir2: "\<lbrakk>c1;(while\<^bsub>\<iota>\<^esub> b do c2 od)\<rbrakk>(m) = m'"
              by (simp add: NextMem_def, auto)

            with eqdir1 show "\<lbrakk>c1;(while\<^bsub>\<iota>\<^esub> b do c2 od)\<rbrakk>(m) = \<lbrakk>c1\<rbrakk>(m)" 
              by auto
          qed
          
          have eqpp: "pp (c1;(while\<^bsub>\<iota>\<^esub> b do c2 od)) = pp c1"
            by simp

          with c1NDCIDC eqnextmem show 
            "NDC d (c1;(while\<^bsub>\<iota>\<^esub> b do c2 od)) \<or>
            IDC d (c1;(while\<^bsub>\<iota>\<^esub> b do c2 od))
            (htchLoc (pp (c1;(while\<^bsub>\<iota>\<^esub> b do c2 od))))"
            by (simp add: IDC_def NDC_def)
        qed

      \<comment> \<open>second alternative for V V'\<close>
      have case2: "NDC d (while\<^bsub>\<iota>\<^esub> b do c1 od)"
        proof -
          {
            fix m
            from nextmem_exists_and_unique obtain m' p \<alpha> 
              where whilenextmem: "\<langle>while\<^bsub>\<iota>\<^esub> b do c1 od,m\<rangle> \<rightarrow>\<lhd>\<alpha>\<rhd> \<langle>p,m'\<rangle> 
              \<and> (\<forall>m''. (\<exists>p \<alpha>. \<langle>while\<^bsub>\<iota>\<^esub> b do c1 od,m\<rangle> \<rightarrow>\<lhd>\<alpha>\<rhd> \<langle>p,m''\<rangle>) 
              \<longrightarrow> m'' = m')"
              by blast
            
            hence "m = m'"
              by (metis MWLsSteps_det.whilefalse MWLsSteps_det.whiletrue)
          
            with whilenextmem have eqnextmem: 
              "\<lbrakk>while\<^bsub>\<iota>\<^esub> b do c1 od\<rbrakk>(m) = m"
              by (simp add: NextMem_def, auto)
          }
          thus "NDC d (while\<^bsub>\<iota>\<^esub> b do c1 od)"
            by (simp add: NDC_def)
        qed

      from R0pair case1 case2 irange notIDC
      show "NDC d (V!i)"
        by force
    next
      fix V V' i m1 m1' m2 \<alpha> p
      assume inR0: "(V,V') \<in> R0"
      assume irange: "i < length V"
      assume step: "\<langle>V!i,m1\<rangle> \<rightarrow>\<lhd>\<alpha>\<rhd> \<langle>p,m2\<rangle>"
      assume dhequal: "m1 \<sim>\<^bsub>d,htchLocSet PP\<^esub> m1'"

      from inR0 R0_def R1_def R2_def obtain \<iota> \<iota>' b b' c1 c1' c2 c2' 
        where R0pair: "((V = [c1;(while\<^bsub>\<iota>\<^esub> b do c2 od)] 
        \<and> V' = [c1';(while\<^bsub>\<iota>'\<^esub> b' do c2' od)])
        \<or> (V = [while\<^bsub>\<iota>\<^esub> b do c1 od] \<and> V' = [while\<^bsub>\<iota>'\<^esub> b' do c1' od]))
        \<and> \<iota> \<notin> set (PPc c) \<and> \<iota>' \<notin> set (PPc c) 
        \<and> ([c1],[c1']) \<in> R \<and> ([c2],[c2']) \<in> R
        \<and> b \<equiv>\<^bsub>d\<^esub> b'"
        by force

      \<comment> \<open>Case 1: V and V' are sequential commands\<close>
      have case1: "\<lbrakk> V = [c1;(while\<^bsub>\<iota>\<^esub> b do c2 od)]; 
        V' = [c1';(while\<^bsub>\<iota>'\<^esub> b' do c2' od)] \<rbrakk>
        \<Longrightarrow> \<exists>p' \<alpha>' m2'. \<langle>V'!i,m1'\<rangle> \<rightarrow>\<lhd>\<alpha>'\<rhd> \<langle>p',m2'\<rangle> \<and>
        stepResultsinR p p' (R0 \<union> R) \<and> ((\<alpha>,\<alpha>') \<in> R0 \<or> (\<alpha>,\<alpha>') \<in> R) \<and>
        dhequality_alternative d PP (pp (V!i)) m2 m2'"
        proof -
          assume Vassump: "V = [c1;(while\<^bsub>\<iota>\<^esub> b do c2 od)]"
          assume V'assump: "V' = [c1';(while\<^bsub>\<iota>'\<^esub> b' do c2' od)]"

          have eqpp: "pp (c1;(while\<^bsub>\<iota>\<^esub> b do c2 od)) = pp c1"
            by simp

          from Vassump irange step irange obtain c3 
            where case_distinction:
            "(p = Some (while\<^bsub>\<iota>\<^esub> b do c2 od) \<and> \<langle>c1,m1\<rangle> \<rightarrow>\<lhd>\<alpha>\<rhd> \<langle>None,m2\<rangle>)
            \<or> (p = Some (c3;(while\<^bsub>\<iota>\<^esub> b do c2 od)) 
            \<and> \<langle>c1,m1\<rangle> \<rightarrow>\<lhd>\<alpha>\<rhd> \<langle>Some c3,m2\<rangle>)"
            by (simp, metis MWLsSteps_det_cases(3))
          moreover
          \<comment> \<open>Case 1a: first command terminates\<close>
          {
            assume passump: "p = Some (while\<^bsub>\<iota>\<^esub> b do c2 od)"
            assume stepassump: "\<langle>c1,m1\<rangle> \<rightarrow>\<lhd>\<alpha>\<rhd> \<langle>None,m2\<rangle>"

            with R0pair SdlHPPR dhequal
            strongdlHPPB_aux[of "d" "PP" "R"
            _ "[c1]" "[c1']" "m1" "\<alpha>" "None" "m2" "m1'"]
            obtain p' \<alpha>' m2' where c1c1'reason:
              "p' = None \<and> \<langle>c1',m1'\<rangle> \<rightarrow>\<lhd>\<alpha>'\<rhd> \<langle>p',m2'\<rangle> \<and> (\<alpha>,\<alpha>') \<in> R \<and>
              dhequality_alternative d PP (pp c1) m2 m2'"
              by (simp add: stepResultsinR_def, fastforce)

            hence conclpart:
            "\<langle>c1';(while\<^bsub>\<iota>'\<^esub> b' do c2' od),m1'\<rangle> 
              \<rightarrow>\<lhd>\<alpha>'\<rhd> \<langle>Some (while\<^bsub>\<iota>'\<^esub> b' do c2' od),m2'\<rangle>"
              by (auto, simp add: MWLsSteps_det.seq1)

            from R0pair R0_def R2_def have 
              "([while\<^bsub>\<iota>\<^esub> b do c2 od],[while\<^bsub>\<iota>'\<^esub> b' do c2' od]) \<in> R0"
              by simp
  
            with passump V'assump Vassump eqpp conclpart 
              c1c1'reason irange 
            have "\<exists>p' \<alpha>' m2'. \<langle>V'!i,m1'\<rangle> \<rightarrow>\<lhd>\<alpha>'\<rhd> \<langle>p',m2'\<rangle> \<and>
              stepResultsinR p p' (R0 \<union> R) \<and> ((\<alpha>,\<alpha>') \<in> R0 \<or> 
              (\<alpha>,\<alpha>') \<in> R) \<and> 
              dhequality_alternative d PP (pp (V!i)) m2 m2'"
              by (simp add: stepResultsinR_def, auto)
          }
          moreover
          \<comment> \<open>Case 1b: first command does not terminate\<close>
          {
            assume passump: "p = Some (c3;(while\<^bsub>\<iota>\<^esub> b do c2 od))"
            assume stepassump: "\<langle>c1,m1\<rangle> \<rightarrow>\<lhd>\<alpha>\<rhd> \<langle>Some c3,m2\<rangle>"

            with R0pair SdlHPPR dhequal
            strongdlHPPB_aux[of "d" "PP" "R"
            _ "[c1]" "[c1']" "m1" "\<alpha>" "Some c3" "m2" "m1'"]
            obtain p' c3' \<alpha>' m2' where c1c1'reason:
              "p' = Some c3' \<and> \<langle>c1',m1'\<rangle> \<rightarrow>\<lhd>\<alpha>'\<rhd> \<langle>p',m2'\<rangle> \<and> 
              ([c3],[c3']) \<in> R \<and> (\<alpha>,\<alpha>') \<in> R \<and>
              dhequality_alternative d PP (pp c1) m2 m2'"
              by (simp add: stepResultsinR_def, fastforce)

            hence conclpart: 
            "\<langle>c1';(while\<^bsub>\<iota>'\<^esub> b' do c2' od),m1'\<rangle> \<rightarrow>\<lhd>\<alpha>'\<rhd> 
              \<langle>Some (c3';while\<^bsub>\<iota>'\<^esub> b' do c2' od),m2'\<rangle>"
              by (auto, simp add: MWLsSteps_det.seq2)
            
            from c1c1'reason R0pair R0_def R1_def have
              "([c3;while\<^bsub>\<iota>\<^esub> b do c2 od],[c3';while\<^bsub>\<iota>'\<^esub> b' do c2' od]) \<in> R0"
              by simp
            
            with passump V'assump Vassump eqpp conclpart c1c1'reason irange
            have "\<exists>p' \<alpha>' m2'. \<langle>V'!i,m1'\<rangle> \<rightarrow>\<lhd>\<alpha>'\<rhd> \<langle>p',m2'\<rangle> \<and>
              stepResultsinR p p' (R0 \<union> R) \<and> 
              ((\<alpha>,\<alpha>') \<in> R0 \<or> (\<alpha>,\<alpha>') \<in> R) \<and>
              dhequality_alternative d PP (pp (V!i)) m2 m2'"
              by (simp add: stepResultsinR_def, auto)
          }
          ultimately show "\<exists>p' \<alpha>' m2'. \<langle>V'!i,m1'\<rangle> \<rightarrow>\<lhd>\<alpha>'\<rhd> \<langle>p',m2'\<rangle> \<and>
              stepResultsinR p p' (R0 \<union> R) \<and> 
            ((\<alpha>,\<alpha>') \<in> R0 \<or> (\<alpha>,\<alpha>') \<in> R) \<and>
              dhequality_alternative d PP (pp (V!i)) m2 m2'"
            by auto
        qed
          
      \<comment> \<open>Case 2: V and V' are while commands\<close>
      have case2: "\<lbrakk> V = [while\<^bsub>\<iota>\<^esub> b do c1 od]; V' = [while\<^bsub>\<iota>'\<^esub> b' do c1' od] \<rbrakk>
        \<Longrightarrow> \<exists>p' \<alpha>' m2'. \<langle>V'!i,m1'\<rangle> \<rightarrow>\<lhd>\<alpha>'\<rhd> \<langle>p',m2'\<rangle> \<and>
        stepResultsinR p p' (R0 \<union> R) \<and> ((\<alpha>,\<alpha>') \<in> R0 \<or> (\<alpha>,\<alpha>') \<in> R) \<and>
        dhequality_alternative d PP (pp (V!i)) m2 m2'"
        proof -
          assume Vassump: "V = [while\<^bsub>\<iota>\<^esub> b do c1 od]"
          assume V'assump: "V' = [while\<^bsub>\<iota>'\<^esub> b' do c1' od]"

          from Vassump irange step have case_distinction:
            "(p = None \<and> BMap (E b m1) = False)
            \<or> p = (Some (c1;while\<^bsub>\<iota>\<^esub> b do c1 od)) \<and> BMap (E b m1) = True"
            by (simp, metis MWLsSteps_det_cases(5) option.simps(2))
          moreover
          \<comment> \<open>Case 2a: b evaluates to False\<close>
          {
            assume passump: "p = None"
            assume eval: "BMap (E b m1) = False"

            with Vassump step irange have stepconcl: "\<alpha> = [] \<and> m2 = m1"
              by (simp, metis (no_types) MWLsSteps_det_cases(5))
                                      
            from eval R0pair dhequal have eval': "BMap (E b' m1') = False"
              by (simp add: d_indistinguishable_def dH_equal_def, auto)
           
            hence "\<langle>while\<^bsub>\<iota>'\<^esub> b' do c1' od,m1'\<rangle> \<rightarrow>\<lhd>[]\<rhd> \<langle>None,m1'\<rangle>"
              by (simp add: MWLsSteps_det.whilefalse)

            with passump R_def Vassump V'assump stepconcl dhequal irange
            have "\<exists>p' \<alpha>' m2'. \<langle>V'!i,m1'\<rangle> \<rightarrow>\<lhd>\<alpha>'\<rhd> \<langle>p',m2'\<rangle> \<and>
            stepResultsinR p p' (R0 \<union> R) \<and> ((\<alpha>,\<alpha>') \<in> R0 \<or> (\<alpha>,\<alpha>') \<in> R) \<and>
            dhequality_alternative d PP (pp (V!i)) m2 m2'"
              by (simp add: stepResultsinR_def dhequality_alternative_def, 
                auto)
          }
          moreover
          \<comment> \<open>Case 2b: b evaluates to True\<close>
          {
            assume passump: "p = (Some (c1;while\<^bsub>\<iota>\<^esub> b do c1 od))"
            assume eval: "BMap (E b m1) = True"

            with Vassump step irange have stepconcl: "\<alpha> = [] \<and> m2 = m1"
              by (simp, metis (no_types) MWLsSteps_det_cases(5))      
              
            from eval R0pair dhequal have eval': 
              "BMap (E b' m1') = True"
              by (simp add: d_indistinguishable_def dH_equal_def, auto)
           
            hence step': "\<langle>while\<^bsub>\<iota>'\<^esub> b' do c1' od,m1'\<rangle> \<rightarrow>\<lhd>[]\<rhd> 
              \<langle>Some (c1';while\<^bsub>\<iota>'\<^esub> b' do c1' od),m1'\<rangle>"
              by (simp add: MWLsSteps_det.whiletrue)

            from R1_def R0pair have inR1: 
              "([c1;while\<^bsub>\<iota>\<^esub> b do c1 od],[c1';while\<^bsub>\<iota>'\<^esub> b' do c1' od]) \<in> R1"
              by auto
              
            with step' R0_def passump R_def Vassump V'assump 
              stepconcl dhequal irange
            have "\<exists>p' \<alpha>' m2'. \<langle>V'!i,m1'\<rangle> \<rightarrow>\<lhd>\<alpha>'\<rhd> \<langle>p',m2'\<rangle> \<and>
            stepResultsinR p p' (R0 \<union> R) \<and> ((\<alpha>,\<alpha>') \<in> R0 \<or> (\<alpha>,\<alpha>') \<in> R) \<and>
            dhequality_alternative d PP (pp (V!i)) m2 m2'"
              by (simp add: stepResultsinR_def dhequality_alternative_def, 
                auto)
          }
          ultimately
          show "\<exists>p' \<alpha>' m2'. \<langle>V'!i,m1'\<rangle> \<rightarrow>\<lhd>\<alpha>'\<rhd> \<langle>p',m2'\<rangle> \<and>
            stepResultsinR p p' (R0 \<union> R) \<and> ((\<alpha>,\<alpha>') \<in> R0 \<or> (\<alpha>,\<alpha>') \<in> R) \<and>
            dhequality_alternative d PP (pp (V!i)) m2 m2'"
            by auto
        qed

      with case1 R0pair show "\<exists>p' \<alpha>' m2'. \<langle>V'!i,m1'\<rangle> \<rightarrow>\<lhd>\<alpha>'\<rhd> \<langle>p',m2'\<rangle> \<and>
        stepResultsinR p p' (R0 \<union> R) \<and> ((\<alpha>,\<alpha>') \<in> R0 \<or> (\<alpha>,\<alpha>') \<in> R) \<and>
        dhequality_alternative d PP (pp (V!i)) m2 m2'"
        by auto
    qed
      
  with Areflassump Up_To_Technique
  have "SdlHPPB d PP (R0 \<union> R)"
    by auto

  with inR2 R0_def show "\<exists>R. SdlHPPB d PP R \<and>
    ([while\<^bsub>\<iota>\<^esub> b do c od], [while\<^bsub>\<iota>\<^esub> b do c od]) \<in> R"
    by auto
qed      

end

end
