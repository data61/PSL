(*
Title: Strong-Security
Authors: Sylvia Grewe, Alexander Lux, Heiko Mantel, Jens Sauer
*)
theory Language_Composition
imports Strongly_Secure_Skip_Assign
begin

context Strongly_Secure_Programs
begin        
  
theorem Compositionality_Seq: 
  assumes relatedpart1: "[c1] \<approx>\<^bsub>d\<^esub> [c1']"
  assumes relatedpart2: "[c2] \<approx>\<^bsub>d\<^esub> [c2']"
  shows "[c1;c2] \<approx>\<^bsub>d\<^esub> [c1';c2']"
proof -
  define R0 where "R0 = {(S1,S2). \<exists>c1 c1' c2 c2' W W'. 
    S1 = (c1;c2)#W \<and> S2 = (c1';c2')#W' \<and> 
    [c1] \<approx>\<^bsub>d\<^esub> [c1'] \<and> [c2] \<approx>\<^bsub>d\<^esub> [c2'] \<and> W \<approx>\<^bsub>d\<^esub> W'}"
  
  from relatedpart1 relatedpart2 trivialpair_in_USdB
  have inR0: "([c1;c2],[c1';c2']) \<in> R0"
    by (simp add: R0_def)
   
  have uptoR0: "d_Bisimulation_Up_To_USdB d R0"
    proof (simp add: d_Bisimulation_Up_To_USdB_def, auto)
        from USdBsym 
        show "sym R0"
          by (simp add: sym_def R0_def, fastforce)
      next 
        fix S1 S2
        assume inR0: "(S1,S2) \<in> R0"
        with USdBeqlen show "length S1 = length S2"
          by (auto simp add: R0_def)
      next
        fix S1 S2 RS m1 m2 m1' i
        assume inR0: "(S1,S2) \<in> R0"
        assume irange: "i < length S1"
        assume S1step: "\<langle>S1!i,m1\<rangle> \<rightarrow> \<langle>RS,m2\<rangle>"
        assume dequal: "m1 =\<^bsub>d\<^esub> m1'"
        from inR0 obtain c1 c1' c2 c2' V V'
          where R0def': "S1 = (c1;c2)#V \<and> S2 = (c1';c2')#V' \<and> 
          [c1] \<approx>\<^bsub>d\<^esub> [c1'] \<and> [c2] \<approx>\<^bsub>d\<^esub> [c2'] \<and> V \<approx>\<^bsub>d\<^esub> V'"
          by (simp add: R0_def, force)

        with irange have case_distinction1: 
          "i = 0 \<or> (V \<noteq> [] \<and> i \<noteq> 0)"
          by auto
        moreover
        have case1: "i = 0 \<Longrightarrow> 
          \<exists>RS' m2'. \<langle>S2!i,m1'\<rangle> \<rightarrow> \<langle>RS',m2'\<rangle> \<and>
             ((RS,RS') \<in> R0 \<or> RS \<approx>\<^bsub>d\<^esub> RS') \<and> m2 =\<^bsub>d\<^esub> m2'"
          proof -
            assume i0: "i = 0"

              \<comment> \<open>get the two different sub-cases:\<close>
            with R0def' S1step obtain c3 W where case_distinction: 
              "RS = [c2] \<and> \<langle>c1,m1\<rangle> \<rightarrow> \<langle>[],m2\<rangle>
              \<or> RS = (c3;c2)#W \<and> \<langle>c1,m1\<rangle> \<rightarrow> \<langle>c3#W,m2\<rangle>"
              by (simp, metis MWLfSteps_det_cases(3))
            moreover
              \<comment> \<open>Case 1: first command terminates\<close>
            {
              assume RSassump: "RS = [c2]"
              assume StepAssump: "\<langle>c1,m1\<rangle> \<rightarrow> \<langle>[],m2\<rangle>" 

              from USdBeqlen[of "[]"] StepAssump R0def' 
                USdB_Strong_d_Bisimulation dequal
                strongdB_aux[of "d" "\<approx>\<^bsub>d\<^esub>" "i"
                "[c1]" "[c1']" "m1" "[]" "m2" "m1'"] i0
              obtain W' m2' where c1c1'reason: 
                "\<langle>c1',m1'\<rangle> \<rightarrow> \<langle>W',m2'\<rangle> \<and> W' = [] 
                \<and> [] \<approx>\<^bsub>d\<^esub> W' \<and> m2 =\<^bsub>d\<^esub> m2'"
                by fastforce

              with c1c1'reason have conclpart:
                "\<langle>c1';c2',m1'\<rangle> \<rightarrow> \<langle>[c2'],m2'\<rangle> \<and> m2 =\<^bsub>d\<^esub> m2'"
                by (simp add: MWLfSteps_det.seq1)
          
              with RSassump R0def' i0 have case1_concl:
                "\<exists>RS' m2'. \<langle>S2!i,m1'\<rangle> \<rightarrow> \<langle>RS',m2'\<rangle> \<and>
                 ((RS,RS') \<in> R0 \<or> RS \<approx>\<^bsub>d\<^esub> RS') \<and> m2 =\<^bsub>d\<^esub> m2'"   
                by (simp, rule_tac x="[c2']" in exI, auto)      
            }
            moreover
              \<comment> \<open>Case 2: first command does not terminate\<close>
            {
              assume RSassump: "RS = (c3;c2)#W"
              assume StepAssump: "\<langle>c1,m1\<rangle> \<rightarrow> \<langle>c3#W,m2\<rangle>"
              
              from StepAssump R0def' USdB_Strong_d_Bisimulation dequal
                strongdB_aux[of "d" "\<approx>\<^bsub>d\<^esub>" "i" "[c1]" "[c1']" "m1" 
                "c3#W" "m2" "m1'"] i0 
              obtain V'' m2' where c1c1'reason: 
                "\<langle>c1',m1'\<rangle> \<rightarrow> \<langle>V'',m2'\<rangle> 
                \<and> (c3#W) \<approx>\<^bsub>d\<^esub> V'' \<and> m2 =\<^bsub>d\<^esub> m2'"
                by fastforce
 
              with USdBeqlen[of "c3#W" "V''"] obtain c3' W' 
                where V''reason:
                "V'' = c3'#W' \<and> length W = length W'"
                by (cases V'', force, force)
          
              with c1c1'reason have conclpart1:
                "\<langle>c1';c2',m1'\<rangle> \<rightarrow> \<langle>(c3';c2')#W',m2'\<rangle> \<and> m2 =\<^bsub>d\<^esub> m2'"
                by (simp add: MWLfSteps_det.seq2)

              from V''reason c1c1'reason 
                USdB_decomp_head_tail[of "c3" "W"] 
                USdB_Strong_d_Bisimulation
              have c3aWinUSDB: 
                "[c3] \<approx>\<^bsub>d\<^esub> [c3'] \<and> W \<approx>\<^bsub>d\<^esub> W'"
                by blast
        
              with R0def' have conclpart2:
                "((c3;c2)#W,(c3';c2')#W') \<in> R0"
                by (auto simp add: R0_def)

              with i0 RSassump R0def' V''reason conclpart1 
              have case2_concl:
                "\<exists>RS' m2'. \<langle>S2!i,m1'\<rangle> \<rightarrow> \<langle>RS',m2'\<rangle> \<and>
                ((RS,RS') \<in> R0 \<or> RS \<approx>\<^bsub>d\<^esub> RS') \<and> m2 =\<^bsub>d\<^esub> m2'"
                by (rule_tac x="(c3';c2')#W'" in exI, auto)
            } 
            ultimately
            show "\<exists>RS' m2'. \<langle>S2!i,m1'\<rangle> \<rightarrow> \<langle>RS',m2'\<rangle> \<and>
               ((RS,RS') \<in> R0 \<or> RS \<approx>\<^bsub>d\<^esub> RS') \<and> m2 =\<^bsub>d\<^esub> m2'"
              by blast
          qed
          moreover
          have case2: "\<lbrakk> V \<noteq> []; i \<noteq> 0 \<rbrakk>
            \<Longrightarrow> \<exists>RS' m2'. \<langle>S2!i,m1'\<rangle> \<rightarrow> \<langle>RS',m2'\<rangle> \<and>
               ((RS,RS') \<in> R0 \<or> RS \<approx>\<^bsub>d\<^esub> RS') \<and> m2 =\<^bsub>d\<^esub> m2'"
            proof - 
              assume Vnonempt: "V \<noteq> []"
              assume inot0: "i \<noteq> 0"

              with Vnonempt irange R0def' have i1range:
                "(i-Suc 0) < length V"
                by simp

              from inot0 R0def' have S1ieq: "S1!i = V!(i-Suc 0)"
                by auto

              from inot0 R0def' have "S2!i = V'!(i-Suc 0)"
                by auto
              
              with S1ieq R0def' S1step i1range dequal 
                USdB_Strong_d_Bisimulation
                strongdB_aux[of "d" "USdB d"
                "i-Suc 0" "V" "V'" "m1" "RS" "m2" "m1'"]
              show "\<exists>RS' m2'. \<langle>S2!i,m1'\<rangle> \<rightarrow> \<langle>RS',m2'\<rangle> \<and>
                ((RS,RS') \<in> R0 \<or> RS \<approx>\<^bsub>d\<^esub> RS') \<and> m2 =\<^bsub>d\<^esub> m2'"
                by force
            qed
          ultimately show "\<exists>RS' m2'. \<langle>S2!i,m1'\<rangle> \<rightarrow> \<langle>RS',m2'\<rangle> \<and>
           ((RS,RS') \<in> R0 \<or> RS \<approx>\<^bsub>d\<^esub> RS') \<and> m2 =\<^bsub>d\<^esub> m2'"
            by auto
        qed          
  
  hence "R0 \<subseteq> \<approx>\<^bsub>d\<^esub>"
    by (rule Up_To_Technique)
  
  with inR0 show ?thesis
    by auto
  
qed

theorem Compositionality_Fork:
  fixes V::"('exp,'id) MWLfCom list"
  assumes relatedmain: "[c] \<approx>\<^bsub>d\<^esub> [c']"
  assumes relatedthreads: "V \<approx>\<^bsub>d\<^esub> V'"
  shows "[fork c V] \<approx>\<^bsub>d\<^esub> [fork c' V']"  
proof -
  define R0 where "R0 = {(F1,F2). \<exists>c1 c1' W W'. 
    F1 = [fork c1 W] \<and> F2 = [fork c1' W']
    \<and> [c1] \<approx>\<^bsub>d\<^esub> [c1'] \<and> W \<approx>\<^bsub>d\<^esub> W'}"
  from relatedmain relatedthreads 
  have inR0: "([fork c V],[fork c' V']) \<in> R0"
    by (simp add: R0_def)
  
  have uptoR0: "d_Bisimulation_Up_To_USdB d R0"
    proof (simp add: d_Bisimulation_Up_To_USdB_def, auto)
      from USdBsym show "sym R0"
        by (simp add: R0_def sym_def, auto)
    next 
      fix F1 F2
      assume inR0: "(F1,F2) \<in> R0"
      with R0_def USdBeqlen show "length F1 = length F2"
        by auto
    next
      fix F1 F2 c1V m1 m2 m1' i
      assume inR0: "(F1,F2) \<in> R0"
      assume irange: "i < length F1"
      assume F1step: "\<langle>F1!i,m1\<rangle> \<rightarrow> \<langle>c1V,m2\<rangle>"
      assume dequal: "m1 =\<^bsub>d\<^esub> m1'"

      from inR0 obtain c1 c1' V V' 
        where R0def': "F1 = [fork c1 V] \<and> F2 = [fork c1' V'] \<and> 
        [c1] \<approx>\<^bsub>d\<^esub> [c1'] \<and> V \<approx>\<^bsub>d\<^esub> V'"
        by (simp add: R0_def, force)

      from irange R0def' F1step
      have rew: "c1V = c1#V \<and> m2 = m1"
        by (simp, metis MWLf_semantics.MWLfSteps_det_cases(6))

      from irange R0def' MWLfSteps_det.fork have F2step: 
        "\<langle>F2!i,m1'\<rangle> \<rightarrow> \<langle>c1'#V',m1'\<rangle>"
        by force
      
      from R0def' USdB_comp_head_tail have conclpart: 
         "((c1#V,c1'#V') \<in> R0 \<or> (c1#V) \<approx>\<^bsub>d\<^esub> (c1'#V'))"
        by auto
        
      with irange rew inR0 F1step dequal R0def' F2step
      show "\<exists>c1V' m2'. \<langle>F2!i,m1'\<rangle> \<rightarrow> \<langle>c1V',m2'\<rangle> \<and> 
        ((c1V,c1V') \<in> R0 \<or> c1V \<approx>\<^bsub>d\<^esub> c1V') \<and> m2 =\<^bsub>d\<^esub> m2'"
        by fastforce
    qed
     
  hence "R0 \<subseteq> \<approx>\<^bsub>d\<^esub>"
    by (rule Up_To_Technique)
  
  with inR0 show ?thesis
    by auto
  
qed

theorem Compositionality_If:
  assumes dind_or_branchesrelated: 
  "b \<equiv>\<^bsub>d\<^esub> b' \<or> [c1] \<approx>\<^bsub>d\<^esub> [c2] \<or> [c1'] \<approx>\<^bsub>d\<^esub> [c2']"
  assumes branch1related: "[c1] \<approx>\<^bsub>d\<^esub> [c1']"
  assumes branch2related: "[c2] \<approx>\<^bsub>d\<^esub> [c2']"
  shows "[if b then c1 else c2 fi] \<approx>\<^bsub>d\<^esub> [if b' then c1' else c2' fi]"
proof -
  define R1 where "R1 = {(I1,I2). \<exists>c1 c1' c2 c2' b b'.
    I1 = [if b then c1 else c2 fi] \<and> I2 = [if b' then c1' else c2' fi] \<and>
    [c1] \<approx>\<^bsub>d\<^esub> [c1'] \<and> [c2] \<approx>\<^bsub>d\<^esub> [c2'] \<and> b \<equiv>\<^bsub>d\<^esub> b'}"

  define R2 where "R2 = {(I1,I2). \<exists>c1 c1' c2 c2' b b'.
    I1 = [if b then c1 else c2 fi] \<and> I2 = [if b' then c1' else c2' fi] \<and>
    [c1] \<approx>\<^bsub>d\<^esub> [c1'] \<and> [c2] \<approx>\<^bsub>d\<^esub> [c2'] \<and>
    ([c1] \<approx>\<^bsub>d\<^esub> [c2] \<or> [c1'] \<approx>\<^bsub>d\<^esub> [c2'])}"

  define R0 where "R0 = R1 \<union> R2"

  from dind_or_branchesrelated branch1related branch2related
  have inR0: "([if b then c1 else c2 fi],[if b' then c1' else c2' fi]) \<in> R0"
    by (simp add: R0_def R1_def R2_def)

  have uptoR0: "d_Bisimulation_Up_To_USdB d R0"
    proof (simp add: d_Bisimulation_Up_To_USdB_def, auto)
        from USdBsym d_indistinguishable_sym
        have symR1: "sym R1"
          by (simp add: sym_def R1_def, fastforce)
        from USdBsym 
        have symR2: "sym R2"
          by (simp add: sym_def R2_def, fastforce)
        
        from symR1 symR2 show "sym R0"
          by (simp add: sym_def R0_def)
      next
        fix I1 I2
        assume inR0: "(I1,I2) \<in> R0"
        thus "length I1 = length I2"
          by (simp add: R0_def R1_def R2_def, auto)
      next 
        fix I1 I2 RS m1 m1' m2 i
        assume inR0: "(I1,I2) \<in> R0"
        assume irange: "i < length I1"
        assume I1step: "\<langle>I1!i,m1\<rangle> \<rightarrow> \<langle>RS,m2\<rangle>"
        assume dequal: "m1 =\<^bsub>d\<^esub> m1'"

        have inR1case: "(I1,I2) \<in> R1
          \<Longrightarrow> \<exists>RS' m2'. \<langle>I2!i,m1'\<rangle> \<rightarrow> \<langle>RS',m2'\<rangle> \<and>
             ((RS,RS') \<in> R0 \<or> RS \<approx>\<^bsub>d\<^esub> RS') \<and> m2 =\<^bsub>d\<^esub> m2'"
          proof -
            assume inR1: "(I1,I2) \<in> R1"
            
            then obtain c1 c1' c2 c2' b b' where R1def':
              "I1 = [if b then c1 else c2 fi] 
              \<and> I2 = [if b' then c1' else c2' fi] \<and>
              [c1] \<approx>\<^bsub>d\<^esub> [c1'] \<and> [c2] \<approx>\<^bsub>d\<^esub> [c2'] \<and> b \<equiv>\<^bsub>d\<^esub> b'"
              by (simp add: R1_def, force)
            moreover
            \<comment> \<open>get the two different cases True and False from semantics:\<close>
            from irange R1def' I1step have case_distinction:
              "RS = [c1] \<and> BMap (E b m1) = True \<or>
              RS = [c2] \<and> BMap (E b m1) = False"
              by (simp, metis MWLf_semantics.MWLfSteps_det_cases(4))
            moreover
              \<comment> \<open>Case 1: b evaluates to True\<close>
            {
              assume bevalT: "BMap (E b m1) = True"
              assume RSassump: "RS = [c1]"
              from irange bevalT I1step R1def' RSassump have memeq:
                "m2 = m1"
                by (simp, metis MWLf_semantics.MWLfSteps_det_cases(4))
                             
              from bevalT R1def' dequal have b'evalT: 
                "BMap (E b' m1') = True"
                by (simp add: d_indistinguishable_def)

              hence I2step_case1:
                "\<langle>if b' then c1' else c2' fi,m1'\<rangle> \<rightarrow> \<langle>[c1'],m1'\<rangle>"
                by (simp add: MWLfSteps_det.iftrue)
              
              with irange dequal RSassump memeq R1def' 
              have case1_concl:
                "\<exists>RS' m2'. \<langle>I2!i,m1'\<rangle> \<rightarrow> \<langle>RS',m2'\<rangle> \<and>
                ((RS,RS') \<in> R0 \<or> RS \<approx>\<^bsub>d\<^esub> RS') \<and> m2 =\<^bsub>d\<^esub> m2'"
                by auto
            }
            moreover
              \<comment> \<open>Case 2: b evaluates to False\<close>
            {
              assume bevalF: "BMap (E b m1) = False"
              assume RSassump: "RS = [c2]"
              from irange bevalF I1step R1def' RSassump have memeq:
                "m1 = m2"
                by (simp, metis MWLf_semantics.MWLfSteps_det_cases(4))
                          
              from bevalF R1def' dequal have b'evalF: 
                "BMap (E b' m1') = False"
                by (simp add: d_indistinguishable_def)

              hence I2step_case1:
                "\<langle>if b' then c1' else c2' fi,m1'\<rangle> \<rightarrow> \<langle>[c2'],m1'\<rangle>"
                by (simp add: MWLfSteps_det.iffalse)
          
              with irange dequal RSassump memeq R1def' 
              have case1_concl:
                "\<exists>RS' m2'. \<langle>I2!i,m1'\<rangle> \<rightarrow> \<langle>RS',m2'\<rangle> \<and>
                ((RS,RS') \<in> R0 \<or> RS \<approx>\<^bsub>d\<^esub> RS') \<and> m2 =\<^bsub>d\<^esub> m2'"
                by auto
            }
            ultimately show
              "\<exists>RS' m2'. \<langle>I2!i,m1'\<rangle> \<rightarrow> \<langle>RS',m2'\<rangle> \<and>
               ((RS,RS') \<in> R0 \<or> RS \<approx>\<^bsub>d\<^esub> RS') \<and> m2 =\<^bsub>d\<^esub> m2'"
              by auto
          qed
            

        have inR2case: "(I1,I2) \<in> R2
          \<Longrightarrow> \<exists>RS' m2'. \<langle>I2!i,m1'\<rangle> \<rightarrow> \<langle>RS',m2'\<rangle> \<and>
             ((RS,RS') \<in> R0 \<or> RS \<approx>\<^bsub>d\<^esub> RS') \<and> m2 =\<^bsub>d\<^esub> m2'"
          proof -
            assume inR2: "(I1,I2) \<in> R2"
            then obtain c1 c1' c2 c2' b b' where R2def':
              "I1 = [if b then c1 else c2 fi] 
              \<and> I2 = [if b' then c1' else c2' fi] \<and>
              [c1] \<approx>\<^bsub>d\<^esub> [c1'] \<and> [c2] \<approx>\<^bsub>d\<^esub> [c2'] \<and>
              ([c1] \<approx>\<^bsub>d \<^esub>[c2] \<or> [c1'] \<approx>\<^bsub>d\<^esub> [c2'])"
              by (simp add: R2_def, force)
            moreover
              \<comment> \<open>get the two different cases for the result from semantics:\<close>
            from irange R2def' I1step have case_distinction_left:
              "(RS = [c1] \<or> RS = [c2]) \<and> m2 = m1"
              by (simp, metis MWLf_semantics.MWLfSteps_det_cases(4)) 
            moreover
            from irange R2def' dequal obtain RS' where I2step:
              "\<langle>I2!i,m1'\<rangle> \<rightarrow> \<langle>RS',m1'\<rangle>
              \<and> (RS' = [c1'] \<or> RS' = [c2']) \<and> m1 =\<^bsub>d\<^esub> m1'"
              by (simp, metis MWLfSteps_det.iffalse MWLfSteps_det.iftrue)
            moreover
            from USdBtrans have "\<lbrakk> [c1] \<approx>\<^bsub>d\<^esub> [c2]; [c2] \<approx>\<^bsub>d\<^esub> [c2'] \<rbrakk> 
              \<Longrightarrow> [c1] \<approx>\<^bsub>d\<^esub> [c2']"
              by (unfold trans_def, blast)
            moreover
            from USdBtrans have "\<lbrakk> [c1] \<approx>\<^bsub>d\<^esub> [c1']; [c1'] \<approx>\<^bsub>d\<^esub> [c2'] \<rbrakk> 
              \<Longrightarrow> [c1] \<approx>\<^bsub>d\<^esub> [c2']"
              by (unfold trans_def, blast)
            moreover
            from USdBsym have "[c1] \<approx>\<^bsub>d\<^esub> [c2] \<Longrightarrow> [c2] \<approx>\<^bsub>d\<^esub> [c1]"
              by (simp add: sym_def)
            moreover
            from USdBtrans have "\<lbrakk> [c2] \<approx>\<^bsub>d\<^esub> [c1]; [c1] \<approx>\<^bsub>d\<^esub> [c1'] \<rbrakk> 
              \<Longrightarrow> [c2] \<approx>\<^bsub>d\<^esub> [c1']"    
              by (unfold trans_def, blast)
            moreover
            from USdBsym have "[c1'] \<approx>\<^bsub>d\<^esub> [c2'] \<Longrightarrow> [c2'] \<approx>\<^bsub>d\<^esub> [c1']"
              by (simp add: sym_def)
            moreover
            from USdBtrans have "\<lbrakk> [c2] \<approx>\<^bsub>d\<^esub> [c2']; [c2'] \<approx>\<^bsub>d\<^esub> [c1'] \<rbrakk> 
              \<Longrightarrow> [c2] \<approx>\<^bsub>d\<^esub> [c1']"  
              by (unfold trans_def, blast)            
            ultimately show 
             "\<exists>RS' m2'. \<langle>I2!i,m1'\<rangle> \<rightarrow> \<langle>RS',m2'\<rangle> \<and>
              ((RS,RS') \<in> R0 \<or> RS \<approx>\<^bsub>d\<^esub> RS') \<and> m2 =\<^bsub>d\<^esub> m2'"
              by auto
          qed

        from inR0 inR1case inR2case show 
          "\<exists>RS' m2'. \<langle>I2!i,m1'\<rangle> \<rightarrow> \<langle>RS',m2'\<rangle> \<and>
          ((RS,RS') \<in> R0 \<or> RS \<approx>\<^bsub>d\<^esub> RS') \<and> m2 =\<^bsub>d\<^esub> m2'"
          by (auto simp add: R0_def)
        qed
       
  hence "R0 \<subseteq> \<approx>\<^bsub>d\<^esub>"
    by (rule Up_To_Technique)
  
  with inR0 show ?thesis
    by auto
  
qed

theorem Compositionality_While:
  assumes dind: "b \<equiv>\<^bsub>d\<^esub> b'"
  assumes bodyrelated: "[c] \<approx>\<^bsub>d\<^esub> [c']"
  shows "[while b do c od] \<approx>\<^bsub>d\<^esub> [while b' do c' od]"
proof -
  define R1 where "R1 = {(S1,S2). \<exists>c1 c1' c2 c2' b b' W W'.
    S1 = (c1;(while b do c2 od))#W \<and> 
    S2 = (c1';(while b' do c2' od))#W' \<and>
    [c1] \<approx>\<^bsub>d\<^esub> [c1'] \<and> [c2] \<approx>\<^bsub>d\<^esub> [c2'] \<and> W \<approx>\<^bsub>d\<^esub> W' \<and> b \<equiv>\<^bsub>d\<^esub> b'}"

  define R2 where "R2 = {(W1,W2). \<exists>c1 c1' b b'. 
    W1 = [while b do c1 od] \<and> W2 = [while b' do c1' od] \<and>
    [c1] \<approx>\<^bsub>d\<^esub> [c1'] \<and> b \<equiv>\<^bsub>d\<^esub> b'}"

  define R0 where "R0 = R1 \<union> R2"

  from dind bodyrelated 
  have inR0: "([while b do c od],[while b' do c' od]) \<in> R0"
    by (simp add: R0_def R1_def R2_def)
   
  have uptoR0: "d_Bisimulation_Up_To_USdB d R0"
    proof (simp add: d_Bisimulation_Up_To_USdB_def, auto)
        from USdBsym d_indistinguishable_sym have symR1: "sym R1"
          by (simp add: sym_def R1_def, fastforce)
        from USdBsym d_indistinguishable_sym have symR2: "sym R2"
          by (simp add: sym_def R2_def, fastforce)
        from symR1 symR2 show "sym R0"
          by (simp add: sym_def R0_def)
      next
        fix W1 W2
        assume inR0: "(W1,W2) \<in> R0"
        with USdBeqlen show "length W1 = length W2"
          by (simp add: R0_def R1_def R2_def, force)
      next
        fix W1 W2 i m1 m1' RS m2
        assume inR0: "(W1,W2) \<in> R0"
        assume irange: "i < length W1"
        assume W1step: "\<langle>W1!i,m1\<rangle> \<rightarrow> \<langle>RS,m2\<rangle>"
        assume dequal: "m1 =\<^bsub>d\<^esub> m1'"
       
        from inR0 show "\<exists>RS' m2'. \<langle>W2!i,m1'\<rangle> \<rightarrow> \<langle>RS',m2'\<rangle> \<and>
          ((RS,RS') \<in> R0 \<or> RS \<approx>\<^bsub>d\<^esub> RS') \<and> m2 =\<^bsub>d\<^esub> m2'"
          proof (simp add: R0_def, auto)
            assume inR1: "(W1,W2) \<in> R1"

            then obtain c1 c1' c2 c2' b b' V V'
              where R1def': "W1 = (c1;(while b do c2 od))#V 
              \<and> W2 = (c1';(while b' do c2' od))#V' \<and> 
              [c1] \<approx>\<^bsub>d\<^esub> [c1'] \<and> [c2] \<approx>\<^bsub>d\<^esub> [c2'] \<and> V \<approx>\<^bsub>d\<^esub> V' \<and> b \<equiv>\<^bsub>d\<^esub> b'"
              by (simp add: R1_def, force)

            with irange have case_distinction1: "i = 0 \<or>
              (V \<noteq> [] \<and> i \<noteq> 0)"
              by auto
            moreover
            have case1: "i = 0 \<Longrightarrow> 
              \<exists>RS' m2'. \<langle>W2!i,m1'\<rangle> \<rightarrow> \<langle>RS',m2'\<rangle> \<and>
              ((RS,RS') \<in> R1 \<or> (RS,RS') \<in> R2 \<or> RS \<approx>\<^bsub>d\<^esub> RS')
              \<and> m2 =\<^bsub>d\<^esub> m2'"
              proof -
                assume i0: "i = 0"
                  \<comment> \<open>get the two different sub-cases:\<close>
                with R1def' W1step obtain c3 W where case_distinction: 
                  "RS = [while b do c2 od] \<and> \<langle>c1,m1\<rangle> \<rightarrow> \<langle>[],m2\<rangle>
                  \<or> RS = (c3;(while b do c2 od))#W \<and> \<langle>c1,m1\<rangle> \<rightarrow> \<langle>c3#W,m2\<rangle>"
                  by (simp, metis MWLfSteps_det_cases(3))
                moreover
                  \<comment> \<open>Case 1: first command terminates\<close>
                {
                  assume RSassump: "RS = [while b do c2 od]"
                  assume StepAssump: "\<langle>c1,m1\<rangle> \<rightarrow> \<langle>[],m2\<rangle>" 

                  from USdBeqlen[of "[]"] StepAssump R1def' 
                    USdB_Strong_d_Bisimulation dequal
                    strongdB_aux[of "d" "\<approx>\<^bsub>d\<^esub>" "i"
                    "[c1]" "[c1']" "m1" "[]" "m2" "m1'"] i0
                  obtain W' m2' where c1c1'reason: 
                    "\<langle>c1',m1'\<rangle> \<rightarrow> \<langle>W',m2'\<rangle> \<and> W' = [] 
                    \<and> [] \<approx>\<^bsub>d\<^esub> W' \<and> m2 =\<^bsub>d\<^esub> m2'"
                    by fastforce

                  with c1c1'reason have conclpart1:
                    "\<langle>c1';(while b' do c2' od),m1'\<rangle> 
                    \<rightarrow> \<langle>[while b' do c2' od],m2'\<rangle> \<and> m2 =\<^bsub>d\<^esub> m2'"
                    by (simp add: MWLfSteps_det.seq1)

                  from R1def' have conclpart2:
                    "([while b do c2 od],[while b' do c2' od]) \<in> R2"
                    by (simp add: R2_def)

                  with conclpart1 RSassump i0 R1def'
                  have case1_concl:
                    "\<exists>RS' m2'. \<langle>W2!i,m1'\<rangle> \<rightarrow> \<langle>RS',m2'\<rangle> \<and>
                    ((RS,RS') \<in> R1 \<or> (RS,RS') \<in> R2 \<or> RS \<approx>\<^bsub>d\<^esub> RS')
                    \<and> m2 =\<^bsub>d\<^esub> m2'"
                    by auto
                }
                moreover
                  \<comment> \<open>Case 2: first command does not terminate\<close>
                {
                  assume RSassump: "RS = (c3;(while b do c2 od))#W"
                  assume StepAssump: "\<langle>c1,m1\<rangle> \<rightarrow> \<langle>c3#W,m2\<rangle>"
              
                  from StepAssump R1def' USdB_Strong_d_Bisimulation dequal
                    strongdB_aux[of "d" "\<approx>\<^bsub>d\<^esub>" "i"
                    "[c1]" "[c1']" "m1" "c3#W" "m2" "m1'"] i0 
                  obtain V'' m2' where c1c1'reason: 
                    "\<langle>c1',m1'\<rangle> \<rightarrow> \<langle>V'',m2'\<rangle> 
                    \<and> (c3#W) \<approx>\<^bsub>d\<^esub> V'' \<and> m2 =\<^bsub>d\<^esub> m2'"
                    by fastforce
 
                  with USdBeqlen[of "c3#W" "V''"] obtain c3' W' 
                    where V''reason: "V'' = c3'#W'"
                    by (cases V'', force, force)
          
                  with c1c1'reason have conclpart1:
                    "\<langle>c1';(while b' do c2' od),m1'\<rangle> \<rightarrow> 
                    \<langle>(c3';(while b' do c2' od))#W',m2'\<rangle> 
                    \<and> m2 =\<^bsub>d\<^esub> m2'"
                    by (simp add: MWLfSteps_det.seq2)

                  from V''reason 
                    c1c1'reason USdB_decomp_head_tail[of "c3" "W"] 
                    USdB_Strong_d_Bisimulation
                  have c3aWinUSDB: 
                    "[c3] \<approx>\<^bsub>d\<^esub> [c3'] \<and> W \<approx>\<^bsub>d\<^esub> W'"
                    by blast
        
                  with R1def' have conclpart2:
                    "((c3;(while b do c2 od))#W,
                       (c3';(while b' do c2' od))#W') \<in> R1"
                    by (simp add: R1_def)

                  with i0 RSassump R1def' V''reason conclpart1 
                  have case2_concl:
                    "\<exists>RS' m2'. \<langle>W2!i,m1'\<rangle> \<rightarrow> \<langle>RS',m2'\<rangle> \<and>
                    ((RS,RS') \<in> R1 \<or> (RS,RS') \<in> R2 \<or> RS \<approx>\<^bsub>d\<^esub> RS')
                    \<and> m2 =\<^bsub>d\<^esub> m2'"
                    by auto
                } 
                ultimately
                show "\<exists>RS' m2'. \<langle>W2!i,m1'\<rangle> \<rightarrow> \<langle>RS',m2'\<rangle> \<and>
                  ((RS,RS') \<in> R1 \<or> (RS,RS') \<in> R2 \<or> RS \<approx>\<^bsub>d\<^esub> RS')
                  \<and> m2 =\<^bsub>d\<^esub> m2'"
                  by blast
              qed
              moreover
              have case2: "\<lbrakk> V \<noteq> []; i \<noteq> 0 \<rbrakk>
                \<Longrightarrow> \<exists>RS' m2'. \<langle>W2!i,m1'\<rangle> \<rightarrow> \<langle>RS',m2'\<rangle> \<and>
                ((RS,RS') \<in> R1 \<or> (RS,RS') \<in> R2 \<or> RS \<approx>\<^bsub>d\<^esub> RS')
                \<and> m2 =\<^bsub>d\<^esub> m2'"
              proof - 
                assume Vnonempt: "V \<noteq> []"
                assume inot0: "i \<noteq> 0"

                with Vnonempt irange R1def' have i1range:
                  "(i-Suc 0) < length V"
                  by simp

                from inot0 R1def' have W1ieq: "W1!i = V!(i-Suc 0)"
                  by auto

                from inot0 R1def' have "W2!i = V'!(i-Suc 0)"
                  by auto
              
                with W1ieq R1def' W1step i1range dequal 
                  USdB_Strong_d_Bisimulation
                  strongdB_aux[of "d" "USdB d"
                  "i-Suc 0" "V" "V'" "m1" "RS" "m2" "m1'"]
                show "\<exists>RS' m2'. \<langle>W2!i,m1'\<rangle> \<rightarrow> \<langle>RS',m2'\<rangle> \<and>
                  ((RS,RS') \<in> R1 \<or> (RS,RS') \<in> R2 \<or> RS \<approx>\<^bsub>d\<^esub> RS')
                  \<and> m2 =\<^bsub>d\<^esub> m2'"
                  by force
              qed
              ultimately show "\<exists>RS' m2'. \<langle>W2!i,m1'\<rangle> \<rightarrow> \<langle>RS',m2'\<rangle> \<and>
                ((RS,RS') \<in> R1 \<or> (RS,RS') \<in> R2 \<or> RS \<approx>\<^bsub>d\<^esub> RS') 
                \<and> m2 =\<^bsub>d\<^esub> m2'"
                by auto
            next          
              assume inR2: "(W1,W2) \<in> R2"

              then obtain c1 c1' b b' where R2def': 
                "W1 = [while b do c1 od] \<and> W2 = [while b' do c1' od] \<and>
                [c1] \<approx>\<^bsub>d\<^esub> [c1'] \<and> b \<equiv>\<^bsub>d\<^esub> b'"
                by (auto simp add: R2_def)
                \<comment> \<open>get the two different cases:\<close>
              moreover
              from irange R2def' W1step have case_distinction:
                "RS = [c1;(while b do c1 od)] \<and> BMap (E b m1) = True \<or>
                RS = [] \<and> BMap (E b m1) = False"
                by (simp,metis MWLf_semantics.MWLfSteps_det_cases(5))
              moreover
                \<comment> \<open>Case 1: b evaluates to True\<close>
              {
                assume bevalT: "BMap (E b m1)"
                assume RSassump: "RS = [c1;(while b do c1 od)]"
                from irange bevalT W1step R2def' RSassump have memeq:
                  "m2 = m1"
                  by (simp,metis MWLf_semantics.MWLfSteps_det_cases(5))
          
                from bevalT R2def' dequal have b'evalT: "BMap (E b' m1')"
                  by (simp add: d_indistinguishable_def)

                hence W2step_case1: 
                  "\<langle>while b' do c1' od,m1'\<rangle> 
                    \<rightarrow> \<langle>[c1';(while b' do c1' od)],m1'\<rangle>"
                  by (simp add: MWLfSteps_det.whiletrue)

                from trivialpair_in_USdB R2def' have inWR2: 
                  "([c1;(while b do c1 od)],
                     [c1';(while b' do c1' od)]) \<in> R1"
                  by (auto simp add: R1_def)

                with irange dequal RSassump memeq W2step_case1 R2def' 
                have case1_concl:
                  "\<exists>RS' m2'. \<langle>W2!i,m1'\<rangle> \<rightarrow> \<langle>RS',m2'\<rangle> \<and>
                  ((RS,RS') \<in> R1 \<or> (RS,RS') \<in> R2 \<or> RS \<approx>\<^bsub>d\<^esub> RS')
                  \<and> m2 =\<^bsub>d\<^esub> m2'"
                  by auto
              }
              moreover
                \<comment> \<open>Case 2: b evaluates to False\<close>
              {
                assume bevalF: "BMap (E b m1) = False"
                assume RSassump: "RS = []"
                from irange bevalF W1step R2def' RSassump have memeq:
                  "m2 = m1"
                  by (simp,metis MWLf_semantics.MWLfSteps_det_cases(5))

                from bevalF R2def' dequal have b'equalF: 
                  "BMap (E b' m1') = False"
                  by (simp add: d_indistinguishable_def)
          
                hence W2step_case2:
                  "\<langle>while b' do c1' od,m1'\<rangle> \<rightarrow> \<langle>[],m1'\<rangle>"
                  by (simp add: MWLfSteps_det.whilefalse)
          
                with trivialpair_in_USdB irange dequal RSassump 
                  memeq R2def' 
                have case1_concl:
                  "\<exists>RS' m2'. \<langle>W2!i,m1'\<rangle> \<rightarrow> \<langle>RS',m2'\<rangle> \<and>
                  ((RS,RS') \<in> R1 \<or> (RS,RS') \<in> R2 \<or> RS \<approx>\<^bsub>d\<^esub> RS')
                  \<and> m2 =\<^bsub>d\<^esub> m2'"
                  by force
              }
              ultimately
              show "\<exists>RS' m2'. \<langle>W2!i,m1'\<rangle> \<rightarrow> \<langle>RS',m2'\<rangle> \<and>
                ((RS,RS') \<in> R1 \<or> (RS,RS') \<in> R2 \<or> RS \<approx>\<^bsub>d\<^esub> RS')
                \<and> m2 =\<^bsub>d\<^esub> m2'"
                by auto
            qed
          qed
                  
  hence "R0 \<subseteq> \<approx>\<^bsub>d\<^esub>"
    by (rule Up_To_Technique)
  
  with inR0 show ?thesis
    by auto
  
qed

end 

end
