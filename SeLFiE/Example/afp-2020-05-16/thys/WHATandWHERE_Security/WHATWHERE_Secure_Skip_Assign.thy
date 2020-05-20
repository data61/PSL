(*
Title: WHATandWHERE-Security
Authors: Sylvia Grewe, Alexander Lux, Heiko Mantel, Jens Sauer
*)
theory WHATWHERE_Secure_Skip_Assign
imports Parallel_Composition
begin

context WHATWHERE_Secure_Programs
begin

abbreviation NextMem' 
("\<lbrakk>_\<rbrakk>'(_')")
where
"\<lbrakk>c\<rbrakk>(m) \<equiv> NextMem c m"

\<comment> \<open>define when two expressions are indistinguishable with respect to a domain d\<close>
definition d_indistinguishable :: "'d::order \<Rightarrow> 'exp \<Rightarrow> 'exp \<Rightarrow> bool"
where
"d_indistinguishable d e1 e2 \<equiv> \<forall>m m'. ((m =\<^bsub>d\<^esub> m') 
  \<longrightarrow> ((E e1 m) = (E e2 m')))"

abbreviation d_indistinguishable' :: "'exp \<Rightarrow> 'd::order \<Rightarrow> 'exp \<Rightarrow> bool" 
( "(_ \<equiv>\<^bsub>_\<^esub> _)" )
where
"e1 \<equiv>\<^bsub>d\<^esub> e2 \<equiv> d_indistinguishable d e1 e2"

\<comment> \<open>symmetry of d-indistinguishable\<close>
lemma d_indistinguishable_sym:
"e \<equiv>\<^bsub>d\<^esub> e' \<Longrightarrow> e' \<equiv>\<^bsub>d\<^esub> e"
by (simp add: d_indistinguishable_def d_equal_def, metis)

\<comment> \<open>transitivity of d-indistinguishable\<close>
lemma d_indistinguishable_trans:
"\<lbrakk> e \<equiv>\<^bsub>d\<^esub> e'; e' \<equiv>\<^bsub>d\<^esub> e'' \<rbrakk> \<Longrightarrow> e \<equiv>\<^bsub>d\<^esub> e''"
by (simp add: d_indistinguishable_def d_equal_def, metis)


\<comment> \<open>predicate for dH-indistinguishable\<close>
definition dH_indistinguishable :: "'d \<Rightarrow> ('d, 'exp) Hatches 
  \<Rightarrow> 'exp \<Rightarrow> 'exp \<Rightarrow> bool"
where
"dH_indistinguishable d H e1 e2 \<equiv> (\<forall>m m'. m \<sim>\<^bsub>d,H\<^esub> m' 
  \<longrightarrow> (E e1 m = E e2 m'))"

abbreviation dH_indistinguishable' :: "'exp \<Rightarrow> 'd 
  \<Rightarrow> ('d, 'exp) Hatches \<Rightarrow> 'exp \<Rightarrow> bool" 
( "(_ \<equiv>\<^bsub>_,_\<^esub> _)" )
where
"e1 \<equiv>\<^bsub>d,H\<^esub> e2 \<equiv> dH_indistinguishable d H e1 e2"

lemma empH_implies_dHindistinguishable_eq_dindistinguishable:
"(e \<equiv>\<^bsub>d,{}\<^esub> e') = (e \<equiv>\<^bsub>d\<^esub> e')"
by (simp add: d_indistinguishable_def dH_indistinguishable_def 
  dH_equal_def d_equal_def)


theorem WHATWHERE_Secure_Skip:
"WHATWHERE_Secure [skip\<^bsub>\<iota>\<^esub>]"
proof (simp add: WHATWHERE_Secure_def, auto)
  fix d PP
  define R where "R = {(V::('exp,'id) MWLsCom list,V'::('exp,'id) MWLsCom list). 
    V = V' \<and> (V = [] \<or> V = [skip\<^bsub>\<iota>\<^esub>])}"
  
  have inR: "([skip\<^bsub>\<iota>\<^esub>],[skip\<^bsub>\<iota>\<^esub>]) \<in> R"
    by (simp add: R_def)
  
  have "SdlHPPB d PP R"
    proof (simp add: Strong_dlHPP_Bisimulation_def R_def sym_def trans_def
      NDC_def NextMem_def, auto)
      fix m1 m1'
      assume dequal: "m1 =\<^bsub>d\<^esub> m1'"
      have nextm1: "(THE m2. (\<exists>p \<alpha>. \<langle>skip\<^bsub>\<iota>\<^esub>,m1\<rangle> \<rightarrow>\<lhd>\<alpha>\<rhd> \<langle>p,m2\<rangle>)) = m1"
        by (insert MWLsSteps_det.simps[of "skip\<^bsub>\<iota>\<^esub>" "m1"], 
          force)
    
      have nextm1': 
        "(THE m2'. (\<exists>p \<alpha>. \<langle>skip\<^bsub>\<iota>\<^esub>,m1'\<rangle> \<rightarrow>\<lhd>\<alpha>\<rhd> \<langle>p,m2'\<rangle>)) = m1'"
        by (insert MWLsSteps_det.simps[of "skip\<^bsub>\<iota>\<^esub>" "m1'"], 
          force)
    
      with dequal nextm1 show 
        "THE m2. \<exists>p \<alpha>. \<langle>skip\<^bsub>\<iota>\<^esub>,m1\<rangle> \<rightarrow>\<lhd>\<alpha>\<rhd> \<langle>p,m2\<rangle> =\<^bsub>d\<^esub>
        THE m2'. \<exists>p \<alpha>. \<langle>skip\<^bsub>\<iota>\<^esub>,m1'\<rangle> \<rightarrow>\<lhd>\<alpha>\<rhd> \<langle>p,m2'\<rangle>"
        by auto
     next
       fix p m1 m1' m2 \<alpha>
       assume dequal: "m1 \<sim>\<^bsub>d,(htchLocSet PP)\<^esub> m1'"
       assume skipstep: "\<langle>skip\<^bsub>\<iota>\<^esub>,m1\<rangle> \<rightarrow>\<lhd>\<alpha>\<rhd> \<langle>p,m2\<rangle>"
       with  MWLsSteps_det.simps[of "skip\<^bsub>\<iota>\<^esub>" "m1" "\<alpha>" "p" "m2"] 
       have aux: "p = None \<and> m2 = m1 \<and> \<alpha> = []"
         by auto
       with dequal skipstep MWLsSteps_det.skip
       show "\<exists>p' m2'.
         \<langle>skip\<^bsub>\<iota>\<^esub>,m1'\<rangle> \<rightarrow>\<lhd>\<alpha>\<rhd> \<langle>p',m2'\<rangle> \<and>
         stepResultsinR p p' {(V, V'). V = V' \<and> 
         (V = [] \<or> V = [skip\<^bsub>\<iota>\<^esub>])} \<and>
         (\<alpha> = [] \<or> \<alpha> = [skip\<^bsub>\<iota>\<^esub>]) \<and>
         dhequality_alternative d PP \<iota> m2 m2'"
         by (simp add: stepResultsinR_def dhequality_alternative_def, 
           fastforce)
     qed

     with inR show "\<exists>R. SdlHPPB d PP R \<and> ([skip\<^bsub>\<iota>\<^esub>],[skip\<^bsub>\<iota>\<^esub>]) \<in> R"
       by auto
qed
 

\<comment> \<open>auxiliary lemma for assign side condition (lemma 9 in original paper)\<close>
lemma semAssignSC_aux: 
  assumes dhind: "e \<equiv>\<^bsub>DA x,(htchLoc \<iota>)\<^esub> e"
  shows "NDC d (x :=\<^bsub>\<iota>\<^esub> e) \<or> IDC d (x :=\<^bsub>\<iota>\<^esub> e) (htchLoc (pp (x:=\<^bsub>\<iota>\<^esub> e)))"
proof (simp add: IDC_def, auto, simp add: NDC_def)
  fix m1 m1'
  assume dhequal: "m1 \<sim>\<^bsub>d,htchLoc \<iota>\<^esub> m1'"
  hence dequal: "m1 =\<^bsub>d\<^esub> m1'"
    by (simp add: dH_equal_def)

  obtain v where veq: "E e m1 = v" by auto
  hence m2eq: "\<lbrakk>x :=\<^bsub>\<iota>\<^esub> e\<rbrakk>(m1) = m1(x := v)"
    by (simp add: NextMem_def,
      insert MWLsSteps_det.simps[of "x :=\<^bsub>\<iota>\<^esub> e" "m1"],
      force)

  obtain v' where v'eq: "E e m1' = v'" by auto
  hence m2'eq: "\<lbrakk>x :=\<^bsub>\<iota>\<^esub> e\<rbrakk>(m1') = m1'(x := v')" 
    by (simp add: NextMem_def,
      insert MWLsSteps_det.simps[of "x :=\<^bsub>\<iota>\<^esub> e" "m1'"],
      force)

  from dhequal have shiftdomain: 
    "DA x \<le> d \<Longrightarrow> m1 \<sim>\<^bsub>DA x,(htchLoc \<iota>)\<^esub> m1'"
    by (simp add: dH_equal_def d_equal_def htchLoc_def)

  with veq v'eq dhind
  have "(DA x) \<le> d \<Longrightarrow> v = v'"
    by (simp add: dH_indistinguishable_def) 

  with dequal m2eq m2'eq
  show "\<lbrakk>x :=\<^bsub>\<iota>\<^esub> e\<rbrakk>(m1) =\<^bsub>d\<^esub> \<lbrakk>x :=\<^bsub>\<iota>\<^esub> e\<rbrakk>(m1')"
    by (simp add: d_equal_def)
qed


theorem WHATWHERE_Secure_Assign:
  assumes dhind: "e \<equiv>\<^bsub>DA x,(htchLoc \<iota>)\<^esub> e"
  assumes dheq_imp: "\<forall>m m' d \<iota>'. (m \<sim>\<^bsub>d,(htchLoc \<iota>')\<^esub> m' \<and> 
  \<lbrakk>x :=\<^bsub>\<iota>\<^esub> e\<rbrakk>(m) =\<^bsub>d\<^esub> \<lbrakk>x :=\<^bsub>\<iota>\<^esub> e\<rbrakk>(m'))
  \<longrightarrow> \<lbrakk>x :=\<^bsub>\<iota>\<^esub> e\<rbrakk>(m) \<sim>\<^bsub>d,(htchLoc \<iota>')\<^esub> \<lbrakk>x :=\<^bsub>\<iota>\<^esub> e\<rbrakk>(m')" 
  shows "WHATWHERE_Secure [x :=\<^bsub>\<iota>\<^esub> e]"
proof (simp add: WHATWHERE_Secure_def, auto)
  fix d PP 
  define R where "R = {(V::('exp,'id) MWLsCom list,V'::('exp,'id) MWLsCom list). 
    V = V' \<and> (V = [] \<or> V = [x :=\<^bsub>\<iota>\<^esub> e])}"
  
  have inR: "([x :=\<^bsub>\<iota>\<^esub> e],[x :=\<^bsub>\<iota>\<^esub> e]) \<in> R"
    by (simp add: R_def)
  
  have "SdlHPPB d PP R"
    proof (simp add: Strong_dlHPP_Bisimulation_def R_def 
        sym_def trans_def, auto)
      assume notIDC: "\<not> IDC d (x :=\<^bsub>\<iota>\<^esub> e) (htchLoc \<iota>)"
      with dhind semAssignSC_aux
      show "NDC d (x :=\<^bsub>\<iota>\<^esub> e)"
        by force
    next
      fix m1 m1' m2 p \<alpha>
      assume assignstep: "\<langle>x :=\<^bsub>\<iota>\<^esub> e,m1\<rangle> \<rightarrow>\<lhd>\<alpha>\<rhd> \<langle>p,m2\<rangle>"
      assume dhequal: "m1 \<sim>\<^bsub>d,htchLocSet PP\<^esub> m1'"
      
      from assignstep have nextm1: 
        "p = None \<and> \<alpha> = [] \<and> \<lbrakk>x :=\<^bsub>\<iota>\<^esub> e\<rbrakk>(m1) = m2"
        by (simp add: NextMem_def, 
          insert MWLsSteps_det.simps[of "x :=\<^bsub>\<iota>\<^esub> e" "m1"], force)
      
      obtain m2' where nextm1': 
        "\<langle>x :=\<^bsub>\<iota>\<^esub> e,m1'\<rangle> \<rightarrow>\<lhd>[]\<rhd> \<langle>None,m2'\<rangle> \<and> \<lbrakk>x :=\<^bsub>\<iota>\<^esub> e\<rbrakk>(m1') = m2'"
        by (simp add: NextMem_def, 
          insert MWLsSteps_det.simps[of "x :=\<^bsub>\<iota>\<^esub> e" "m1'"], force)
      
      from dhequal have dhequal_\<iota>: "\<And>\<iota>. htchLoc \<iota> \<subseteq> htchLocSet PP 
        \<Longrightarrow> m1 \<sim>\<^bsub>d,(htchLoc \<iota>)\<^esub> m1'"
        by (simp add: dH_equal_def, auto)
      
      with dhind semAssignSC_aux 
      have "htchLoc \<iota> \<subseteq> htchLocSet PP \<Longrightarrow> 
        \<lbrakk>x :=\<^bsub>\<iota>\<^esub> e\<rbrakk>(m1) =\<^bsub>d\<^esub> \<lbrakk>x :=\<^bsub>\<iota>\<^esub> e\<rbrakk>(m1')"
        by (simp add: NDC_def IDC_def dH_equal_def, fastforce)
      
      with dhind dheq_imp dhequal_\<iota> 
      have "htchLoc \<iota> \<subseteq> htchLocSet PP \<Longrightarrow> 
        \<lbrakk>x :=\<^bsub>\<iota>\<^esub> e\<rbrakk>(m1) \<sim>\<^bsub>d,(htchLocSet PP)\<^esub> \<lbrakk>x :=\<^bsub>\<iota>\<^esub> e\<rbrakk>(m1')"
        by (simp add: htchLocSet_def dH_equal_def, blast)
      
      with nextm1 nextm1' assignstep dhequal
      show "\<exists>p' m2'.
        \<langle>x :=\<^bsub>\<iota>\<^esub> e,m1'\<rangle> \<rightarrow>\<lhd>\<alpha>\<rhd> \<langle>p',m2'\<rangle> \<and>
        stepResultsinR p p' {(V, V'). V = V' \<and> (V = [] \<or> V = [x:=\<^bsub>\<iota>\<^esub> e])} \<and>
        (\<alpha> = [] \<or> \<alpha> = [x:=\<^bsub>\<iota>\<^esub> e]) \<and> dhequality_alternative d PP \<iota> m2 m2'"
        by (auto simp add: stepResultsinR_def dhequality_alternative_def)
    qed
  
  with inR show "\<exists>R. SdlHPPB d PP R \<and> ([x:=\<^bsub>\<iota>\<^esub> e],[x:=\<^bsub>\<iota>\<^esub> e]) \<in> R"
    by auto
qed

end

end
