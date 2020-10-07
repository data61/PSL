(*
Title: WHATandWHERE-Security
Authors: Sylvia Grewe, Alexander Lux, Heiko Mantel, Jens Sauer
*)
theory Parallel_Composition
imports Up_To_Technique MWLs
begin

locale WHATWHERE_Secure_Programs =
L? : MWLs_semantics "E" "BMap"
+ WWs? : WHATWHERE "MWLsSteps_det" "E" "pp" "DA" "lH"
for E :: "('exp, 'id, 'val) Evalfunction"
and BMap :: "'val \<Rightarrow> bool"
and DA :: "('id, 'd::order) DomainAssignment"
and lH :: "('d, 'exp) lHatches"
begin

lemma SdlHPPB_restricted_on_PP_is_SdlHPPB:
  assumes SdlHPPB: "SdlHPPB d PP R'"
  assumes inR': "(V,V) \<in> R'"
  assumes Rdef: "R = {(V',V''). (V',V'') \<in> R' 
    \<and> set (PPV V') \<subseteq> set (PPV V)
    \<and> set (PPV V'') \<subseteq> set (PPV V)}"
  shows "SdlHPPB d PP R"
proof (simp add: Strong_dlHPP_Bisimulation_def, auto)
  from SdlHPPB have "sym R'" 
    by (simp add: Strong_dlHPP_Bisimulation_def)
  with Rdef show "sym R" 
    by (simp add: sym_def)
next
  from SdlHPPB have "trans R'" 
    by (simp add: Strong_dlHPP_Bisimulation_def)
  with Rdef show "trans R" 
    by (simp add: trans_def, auto)
next
  fix V' V''
  assume inR_part: "(V',V'') \<in> R"
  with SdlHPPB Rdef show "length V' = length V''"
    by (simp add: Strong_dlHPP_Bisimulation_def, auto)
next
  fix V' V'' i
  assume inR_part: "(V',V'') \<in> R"
  assume irange: "i < length V'"
  assume notIDC: 
    "\<not> IDC d (V'!i) (htchLoc (pp (V'!i)))"
  with SdlHPPB inR_part irange Rdef 
  show "NDC d (V'!i)"
    by (simp add: Strong_dlHPP_Bisimulation_def, auto)
next
  fix V' V'' i \<alpha> p m1 m1' m2
  assume inR_part: "(V',V'') \<in> R"
  assume irange: "i < length V'"
  assume step: "\<langle>V'!i,m1\<rangle> \<rightarrow>\<lhd>\<alpha>\<rhd> \<langle>p,m2\<rangle>"
  assume dhequal: "m1 \<sim>\<^bsub>d,(htchLocSet PP)\<^esub> m1'"
  
  from inR_part SdlHPPB Rdef have eqlen: "length V' = length V''"
    by (simp add: Strong_dlHPP_Bisimulation_def, auto)
  
  from inR_part Rdef 
  have "set (PPV V') \<subseteq> set (PPV V) \<and> set (PPV V'') \<subseteq> set (PPV V)"
    by auto
  
  with irange PPc_in_PPV_version eqlen
  have PPc_Vs_at_i: 
    "set (PPc (V'!i)) \<subseteq> set (PPV V) \<and> set (PPc (V''!i)) \<subseteq> set (PPV V)"
    by (metis subset_trans)
  
  from SdlHPPB inR_part Rdef irange step dhequal
    strongdlHPPB_aux[of "d" "PP" "R'" "i" 
    "V'" "V''" "m1" "\<alpha>" "p" "m2" "m1'"]
  obtain p' \<alpha>' m2' where stepreq: "\<langle>V''!i,m1'\<rangle> \<rightarrow>\<lhd>\<alpha>'\<rhd> \<langle>p',m2'\<rangle> \<and>
    stepResultsinR p p' R' \<and> (\<alpha>,\<alpha>') \<in> R' \<and>
    dhequality_alternative d PP (pp (V'!i)) m2 m2'"
    by auto
  have Rpp': "stepResultsinR p p' R"
  proof -
    {
      fix c c'
      assume step1: "\<langle>V'!i,m1\<rangle> \<rightarrow>\<lhd>\<alpha>\<rhd> \<langle>Some c,m2\<rangle>"
      assume step2: "\<langle>V''!i,m1'\<rangle> \<rightarrow>\<lhd>\<alpha>'\<rhd> \<langle>Some c',m2'\<rangle>"
      assume inR'_res: "([c],[c']) \<in> R'"
      
      from PPc_Vs_at_i step1 step2 PPsc_of_step
      have "set (PPc c) \<subseteq> set (PPV V) \<and> set (PPc c') \<subseteq> set (PPV V)"
        by (metis (no_types) option.sel xt1(6))
      
      with inR'_res Rdef have "([c],[c']) \<in> R"
        by auto
    }
    thus ?thesis      
      by (metis step stepResultsinR_def stepreq)
  qed
             
  have R\<alpha>\<alpha>': "(\<alpha>,\<alpha>') \<in> R"
  proof - 
    from PPc_Vs_at_i step stepreq PPs\<alpha>_of_step have 
      "set (PPV \<alpha>) \<subseteq> set (PPV V) \<and> set (PPV \<alpha>') \<subseteq> set (PPV V)"
      by (metis (no_types) xt1(6))
    with stepreq Rdef show ?thesis
      by auto
  qed
  
  from stepreq Rpp' R\<alpha>\<alpha>' show 
    "\<exists>p' \<alpha>' m2'. \<langle>V''!i,m1'\<rangle> \<rightarrow>\<lhd>\<alpha>'\<rhd> \<langle>p',m2'\<rangle> \<and>
    stepResultsinR p p' R \<and> (\<alpha>,\<alpha>') \<in> R \<and>
    dhequality_alternative d PP (pp (V'!i)) m2 m2'"
    by auto
qed


theorem parallel_composition:
  "\<lbrakk> \<forall>i < length V. WHATWHERE_Secure [V!i]; unique_PPV V \<rbrakk>
  \<Longrightarrow> WHATWHERE_Secure V"
proof (simp add: WHATWHERE_Secure_def, induct V, auto)
  fix d PP
  from WHATWHERE_empty 
  show "\<exists>R. SdlHPPB d PP R \<and> ([],[]) \<in> R"
    by (simp add: WHATWHERE_Secure_def)
next
  fix c V d PP
  assume IH: "\<lbrakk> \<forall>i < length V.
    \<forall>d PP. \<exists>R. SdlHPPB d PP R \<and> ([V!i],[V!i]) \<in> R;
    unique_PPV V \<rbrakk>
    \<Longrightarrow> \<forall>d PP. \<exists>R. SdlHPPB d PP R \<and> (V,V) \<in> R"
  assume ISassump: "\<forall>i < Suc (length V).
    \<forall>d PP. \<exists>R. SdlHPPB d PP R \<and> ([(c#V)!i],[(c#V)!i]) \<in> R"
  assume uniPPcV: "unique_PPV (c#V)"
  
  hence IHassump1: "unique_PPV V"
    by (simp add: unique_PPV_def)

  from uniPPcV have nocommonPP: "set (PPc c) \<inter> set (PPV V) = {}"
    by (simp add: unique_PPV_def)
  
  from ISassump have IHassump2: "\<forall>i < length V. 
    \<forall>d PP. \<exists>R. SdlHPPB d PP R \<and> ([V!i],[V!i]) \<in> R"
    by auto

  with IHassump1 IH obtain RV' where RV'assump:
    "SdlHPPB d PP RV' \<and> (V,V) \<in> RV'"
    by blast

  define RV where "RV = {(V',V''). (V',V'') \<in> RV' \<and> set (PPV V') \<subseteq> set (PPV V)
    \<and> set (PPV V'') \<subseteq> set (PPV V)}"

  with RV'assump RV_def SdlHPPB_restricted_on_PP_is_SdlHPPB
  have SdlHPPRV: "SdlHPPB d PP RV"
    by force

  from ISassump obtain Rc' where Rc'assump: 
    "SdlHPPB d PP Rc' \<and> ([c],[c]) \<in> Rc'"
    by (metis append_Nil drop_Nil neq0_conv not_Cons_self 
      nth_append_length Cons_nth_drop_Suc zero_less_Suc)
 
  define Rc where "Rc = {(V',V''). (V',V'') \<in> Rc' \<and> set (PPV V') \<subseteq> set (PPc c)
    \<and> set (PPV V'') \<subseteq> set (PPc c)}"

  with Rc'assump Rc_def SdlHPPB_restricted_on_PP_is_SdlHPPB
  have SdlHPPRc: "SdlHPPB d PP Rc"
    by force

  from nocommonPP have "Domain RV \<inter> Domain Rc \<subseteq> {[]}"
    by (simp add: RV_def Rc_def, auto,
      metis Int_mono inf_commute inf_idem le_bot nocommonPP unique_V_uneq)

  with commonArefl_subset_commonDomain
  have Areflassump1: "Arefl RV \<inter> Arefl Rc \<subseteq> {[]}"
    by force
    
  define R where "R = {(V',V''). \<exists>c c' W W'. V' = c#W \<and> V'' = c'#W' \<and> W \<noteq> []
    \<and> W' \<noteq> [] \<and> ([c],[c']) \<in> Rc \<and> (W,W') \<in> RV}"

  with RV_def RV'assump Rc_def Rc'assump have inR: 
    "V \<noteq> [] \<Longrightarrow> (c#V,c#V) \<in> R"
    by auto
    
  from R_def Rc_def RV_def nocommonPP
  have "Domain R \<inter> Domain (Rc \<union> RV) = {}"
    by (simp add: R_def Rc_def RV_def, auto,
      metis inf_bot_right le_inf_iff subset_empty unique_V_uneq,
      metis (hide_lams, no_types) inf_absorb1 inf_bot_right le_inf_iff unique_c_uneq)
            
  with commonArefl_subset_commonDomain
  have Areflassump2: "Arefl R \<inter> Arefl (Rc \<union> RV) \<subseteq> {[]}"
    by force

  have disjuptoR: 
    "disj_dlHPP_Bisimulation_Up_To_R' d PP (Rc \<union> RV) R"
    proof (simp add: disj_dlHPP_Bisimulation_Up_To_R'_def, auto)
        from Areflassump1 SdlHPPRc SdlHPPRV Union_Strong_dlHPP_Bisim
        show "SdlHPPB d PP (Rc \<union> RV)"
          by force
      next
        from SdlHPPRV have symRV: "sym RV"
          by (simp add: Strong_dlHPP_Bisimulation_def)
        from SdlHPPRc have symRc: "sym Rc"
          by (simp add: Strong_dlHPP_Bisimulation_def)
        with symRV R_def show "sym R"
          by (simp add: sym_def, auto)
      next
        from SdlHPPRV have transRV: "trans RV"
          by (simp add: Strong_dlHPP_Bisimulation_def)
        from SdlHPPRc have transRc: "trans Rc"
          by (simp add: Strong_dlHPP_Bisimulation_def)
        show "trans R"
           proof -
            {
            fix V V' V''
            assume p1: "(V,V') \<in> R"
            assume p2: "(V',V'') \<in> R"
            have "(V,V'') \<in> R"
              proof -
                from p1 R_def obtain c c' W W' where p1assump:
                  "V = c#W \<and> V' = c'#W' \<and> W \<noteq> [] \<and> W' \<noteq> [] \<and>
                  ([c],[c']) \<in> Rc \<and> (W,W') \<in> RV"
                  by auto
                with p2 R_def obtain c'' W'' where p2assump:
                  "V'' = c''#W'' \<and> W'' \<noteq> [] \<and>
                  ([c'],[c'']) \<in> Rc \<and> (W',W'') \<in> RV"
                  by auto
                with p1assump transRc transRV have 
                  trans_assump: "([c],[c'']) \<in> Rc \<and> (W,W'') \<in> RV"
                  by (simp add: trans_def, blast)
                with p1assump p2assump R_def show ?thesis
                  by auto
              qed
             }
            thus ?thesis unfolding trans_def by blast
           qed
      next
        fix V V'
        assume "(V,V') \<in> R"
        with R_def SdlHPPRV show "length V = length V'"
          by (simp add: Strong_dlHPP_Bisimulation_def, auto)
      next
        fix V V' i
        assume inR: "(V,V') \<in> R"
        assume irange: "i < length V"
        assume notIDC: "\<not> IDC d (V!i) 
          (htchLoc (pp (V!i)))"
        from inR R_def obtain c c' W W' where VV'assump:
          "V = c#W \<and> V'=c'#W' \<and> W \<noteq> [] \<and> W' \<noteq> [] \<and>
          ([c],[c']) \<in> Rc \<and> (W,W') \<in> RV"
          by auto
        \<comment> \<open>Case separation for i\<close>
        from VV'assump SdlHPPRc have Case_i0:
          "i = 0 \<Longrightarrow> (NDC d (V!i) \<or>
            IDC d (V!i) (htchLoc (pp (V!i))))"
          by (simp add: Strong_dlHPP_Bisimulation_def, auto)

        from VV'assump SdlHPPRV have "\<forall>i < length W. 
          (NDC d (W!i) \<or>
            IDC d (W!i) (htchLoc (pp (W!i))))"
          by (simp add: Strong_dlHPP_Bisimulation_def, auto)

        with irange VV'assump have Case_in0:
          "i > 0 \<Longrightarrow> (NDC d (V!i) \<or> 
          IDC d (V!i) (htchLoc (pp (V!i))))"
          by simp
        from notIDC Case_i0 Case_in0 
        show "NDC d (V!i)"
          by auto
      next
        fix V V' m1 m1' m2 \<alpha> p i
        assume inR: "(V,V') \<in> R"
        assume irange: "i < length V"
        assume step: "\<langle>V!i,m1\<rangle> \<rightarrow>\<lhd>\<alpha>\<rhd> \<langle>p,m2\<rangle>"
        assume dhequal: "m1 \<sim>\<^bsub>d,(htchLocSet PP)\<^esub> m1'"
        
        from inR R_def obtain c c' W W' where VV'assump:
          "V = c#W \<and> V'=c'#W' \<and> W \<noteq> [] \<and> W' \<noteq> [] \<and>
          ([c],[c']) \<in> Rc \<and> (W,W') \<in> RV"
          by auto
        \<comment> \<open>Case separation for i\<close>
        from VV'assump SdlHPPRc strongdlHPPB_aux[of "d" "PP" 
          "Rc" "0" "[c]" "[c']"] step dhequal
        have Case_i0:
          "i = 0 \<Longrightarrow> \<exists>p' \<alpha>' m2'.
          \<langle>V'!i,m1'\<rangle> \<rightarrow>\<lhd>\<alpha>'\<rhd> \<langle>p',m2'\<rangle> \<and>
          stepResultsinR p p' (R \<union> (Rc \<union> RV)) \<and>
          ((\<alpha>,\<alpha>') \<in> R \<or> (\<alpha>,\<alpha>') \<in> Rc \<or> (\<alpha>,\<alpha>') \<in> RV) \<and>
          dhequality_alternative d PP (pp (V!i)) m2 m2'"
          by (simp add: stepResultsinR_def, blast)

        from step VV'assump irange have rewV: 
          "i > 0 \<Longrightarrow> (i-Suc 0) < length W \<and> V!i = W!(i-Suc 0)"
          by simp

        with irange VV'assump step dhequal SdlHPPRV 
          strongdlHPPB_aux[of "d" "PP" "RV" _ "W" "W'"]
        have Case_in0:
          "i > 0 \<Longrightarrow>  \<exists>p' \<alpha>' m2'.
          \<langle>V'!i,m1'\<rangle> \<rightarrow>\<lhd>\<alpha>'\<rhd> \<langle>p',m2'\<rangle> \<and>
          stepResultsinR p p' (R \<union> (Rc \<union> RV)) \<and>
          ((\<alpha>,\<alpha>') \<in> R \<or> (\<alpha>,\<alpha>') \<in> Rc \<or> (\<alpha>,\<alpha>') \<in> RV) \<and>
          dhequality_alternative d PP (pp (V!i)) m2 m2'"
          by (simp add: stepResultsinR_def, blast)
        
        from Case_i0 Case_in0 
        show "\<exists>p' \<alpha>' m2'.
          \<langle>V'!i,m1'\<rangle> \<rightarrow>\<lhd>\<alpha>'\<rhd> \<langle>p',m2'\<rangle> \<and>
          stepResultsinR p p' (R \<union> (Rc \<union> RV)) \<and>
          ((\<alpha>,\<alpha>') \<in> R \<or> (\<alpha>,\<alpha>') \<in> Rc \<or> (\<alpha>,\<alpha>') \<in> RV) \<and>
          dhequality_alternative d PP (pp (V!i)) m2 m2'"
          by auto
      qed
  with Areflassump2 Rc'assump Up_To_Technique
  show "\<exists>R. SdlHPPB d PP R \<and> (c#V, c#V) \<in> R"
    by (metis UnCI inR)

qed

end

end
