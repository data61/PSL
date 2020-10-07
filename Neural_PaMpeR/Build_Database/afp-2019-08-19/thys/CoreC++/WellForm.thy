(*  Title:       CoreC++
    Author:      Daniel Wasserrab
    Maintainer:  Daniel Wasserrab <wasserra at fmi.uni-passau.de>

    Based on the Jinja theory Common/WellForm.thy by Tobias Nipkow 
*)

section \<open>Generic Well-formedness of programs\<close>

theory WellForm
imports SystemClasses TypeRel WellType
begin


text \<open>\noindent This theory defines global well-formedness conditions
for programs but does not look inside method bodies. Well-typing of 
expressions is defined elsewhere (in theory \<open>WellType\<close>). 

CoreC++ allows covariant return types\<close>


type_synonym wf_mdecl_test = "prog \<Rightarrow> cname \<Rightarrow> mdecl \<Rightarrow> bool"

definition wf_fdecl :: "prog \<Rightarrow> fdecl \<Rightarrow> bool" where
  "wf_fdecl P \<equiv> \<lambda>(F,T). is_type P T"

definition wf_mdecl :: "wf_mdecl_test \<Rightarrow> wf_mdecl_test" where
  "wf_mdecl wf_md P C \<equiv> \<lambda>(M,Ts,T,mb).
  (\<forall>T\<in>set Ts. is_type P T) \<and> is_type P T \<and> T \<noteq> NT \<and> wf_md P C (M,Ts,T,mb)"

definition wf_cdecl :: "wf_mdecl_test \<Rightarrow> prog \<Rightarrow> cdecl \<Rightarrow> bool" where
  "wf_cdecl wf_md P  \<equiv>  \<lambda>(C,(Bs,fs,ms)).
  (\<forall>M mthd Cs. P \<turnstile> C has M = mthd via Cs \<longrightarrow> 
               (\<exists>mthd' Cs'. P \<turnstile> (C,Cs) has overrider M = mthd' via Cs')) \<and> 
  (\<forall>f\<in>set fs. wf_fdecl P f) \<and>  distinct_fst fs \<and>
  (\<forall>m\<in>set ms. wf_mdecl wf_md P C m) \<and>  distinct_fst ms \<and>
  (\<forall>D \<in> baseClasses Bs.
   is_class P D \<and> \<not> P \<turnstile> D \<preceq>\<^sup>* C \<and>
   (\<forall>(M,Ts,T,m)\<in>set ms.
      \<forall>Ts' T' m' Cs. P \<turnstile> D has M = (Ts',T',m') via Cs \<longrightarrow>
                     Ts' = Ts \<and> P \<turnstile> T \<le> T'))"

definition wf_syscls :: "prog \<Rightarrow> bool" where
  "wf_syscls P  \<equiv>  sys_xcpts \<subseteq> set(map fst P)"

definition wf_prog :: "wf_mdecl_test \<Rightarrow> prog \<Rightarrow> bool" where
  "wf_prog wf_md P \<equiv> wf_syscls P \<and> distinct_fst P \<and> 
                     (\<forall>c \<in> set P. wf_cdecl wf_md P c)"



subsection\<open>Well-formedness lemmas\<close>

lemma class_wf: 
  "\<lbrakk>class P C = Some c; wf_prog wf_md P\<rbrakk> \<Longrightarrow> wf_cdecl wf_md P (C,c)"

apply (unfold wf_prog_def class_def)
apply (fast dest: map_of_SomeD)
done



lemma is_class_xcpt:
  "\<lbrakk> C \<in> sys_xcpts; wf_prog wf_md P \<rbrakk> \<Longrightarrow> is_class P C"

  apply (simp add: wf_prog_def wf_syscls_def is_class_def class_def)
  apply (fastforce intro!: map_of_SomeI)
  done



lemma is_type_pTs:
assumes "wf_prog wf_md P" and "(C,S,fs,ms) \<in> set P" and "(M,Ts,T,m) \<in> set ms"
shows "set Ts \<subseteq> types P"
proof
  from assms have "wf_mdecl wf_md P C (M,Ts,T,m)"
    by (unfold wf_prog_def wf_cdecl_def) auto
  hence "\<forall>t \<in> set Ts. is_type P t" by (unfold wf_mdecl_def) auto
  moreover fix t assume "t \<in> set Ts"
  ultimately have "is_type P t" by blast
  thus "t \<in> types P" ..
qed



subsection\<open>Well-formedness subclass lemmas\<close>

lemma subcls1_wfD:
  "\<lbrakk> P \<turnstile> C \<prec>\<^sup>1 D; wf_prog wf_md P \<rbrakk> \<Longrightarrow> D \<noteq> C \<and> (D,C) \<notin> (subcls1 P)\<^sup>+"

apply( frule r_into_trancl)
apply( drule subcls1D)
apply(clarify)
apply( drule (1) class_wf)
apply( unfold wf_cdecl_def baseClasses_def)
apply(force simp add: reflcl_trancl [THEN sym] simp del: reflcl_trancl)
done



lemma wf_cdecl_supD: 
  "\<lbrakk>wf_cdecl wf_md P (C,Bs,r); D \<in> baseClasses Bs\<rbrakk> \<Longrightarrow> is_class P D"
by (auto simp: wf_cdecl_def baseClasses_def)


lemma subcls_asym:
  "\<lbrakk> wf_prog wf_md P; (C,D) \<in> (subcls1 P)\<^sup>+ \<rbrakk> \<Longrightarrow> (D,C) \<notin> (subcls1 P)\<^sup>+"

apply(erule trancl.cases)
apply(fast dest!: subcls1_wfD )
apply(fast dest!: subcls1_wfD intro: trancl_trans)
done



lemma subcls_irrefl:
  "\<lbrakk> wf_prog wf_md P; (C,D) \<in> (subcls1 P)\<^sup>+ \<rbrakk> \<Longrightarrow> C \<noteq> D"

apply (erule trancl_trans_induct)
apply  (auto dest: subcls1_wfD subcls_asym)
done



lemma subcls_asym2:
  "\<lbrakk> (C,D) \<in> (subcls1 P)\<^sup>*; wf_prog wf_md P; (D,C) \<in> (subcls1 P)\<^sup>* \<rbrakk> \<Longrightarrow> C = D"

apply (induct rule:rtrancl.induct)
apply simp
apply (drule rtrancl_into_trancl1)
apply simp
apply (drule subcls_asym)
apply simp
apply(drule rtranclD)
apply simp
done



lemma acyclic_subcls1:
  "wf_prog wf_md P \<Longrightarrow> acyclic (subcls1 P)"

apply (unfold acyclic_def)
apply (fast dest: subcls_irrefl)
done



lemma wf_subcls1:
  "wf_prog wf_md P \<Longrightarrow> wf ((subcls1 P)\<inverse>)"

apply (rule finite_acyclic_wf_converse)
apply (rule finite_subcls1)
apply (erule acyclic_subcls1)
done



lemma subcls_induct: 
  "\<lbrakk> wf_prog wf_md P; \<And>C. \<forall>D. (C,D) \<in> (subcls1 P)\<^sup>+ \<longrightarrow> Q D \<Longrightarrow> Q C \<rbrakk> \<Longrightarrow> Q C"

  (is "?A \<Longrightarrow> PROP ?P \<Longrightarrow> _")

proof -
  assume p: "PROP ?P"
  assume ?A thus ?thesis apply -
apply(drule wf_subcls1)
apply(drule wf_trancl)
apply(simp only: trancl_converse)
apply(erule_tac a = C in wf_induct)
apply(rule p)
apply(auto)
done
qed




subsection\<open>Well-formedness leq\_path lemmas\<close>

lemma last_leq_path:
assumes leq:"P,C \<turnstile> Cs \<sqsubset>\<^sup>1 Ds" and wf:"wf_prog wf_md P"
shows "P \<turnstile> last Cs \<prec>\<^sup>1 last Ds"

using leq
proof (induct rule:leq_path1.induct)
  fix Cs Ds assume suboCs:"Subobjs P C Cs" and suboDs:"Subobjs P C Ds"
  and butlast:"Cs = butlast Ds"
  from suboDs have notempty:"Ds \<noteq> []" by -(drule Subobjs_nonempty)
  with butlast have DsCs:"Ds = Cs @ [last Ds]" by simp
  from suboCs have notempty:"Cs \<noteq> []" by -(drule Subobjs_nonempty)
  with DsCs have "Ds = ((butlast Cs) @ [last Cs]) @ [last Ds]" by simp
  with suboDs have "Subobjs P C ((butlast Cs) @ [last Cs,last Ds])"
    by simp
  thus "P \<turnstile> last Cs \<prec>\<^sup>1 last Ds" by (fastforce intro:subclsR_subcls1 Subobjs_subclsR)
next
  fix Cs D assume "P \<turnstile> last Cs \<prec>\<^sub>S D"
  thus "P \<turnstile> last Cs \<prec>\<^sup>1 last [D]" by (fastforce intro:subclsS_subcls1)
qed



lemma last_leq_paths:
assumes leq:"(Cs,Ds) \<in> (leq_path1 P C)\<^sup>+" and wf:"wf_prog wf_md P"
shows "(last Cs,last Ds) \<in> (subcls1 P)\<^sup>+"

using leq
proof (induct rule:trancl.induct)
  fix Cs Ds assume "P,C \<turnstile> Cs \<sqsubset>\<^sup>1 Ds"
  thus "(last Cs, last Ds) \<in> (subcls1 P)\<^sup>+" using wf
    by (fastforce intro:r_into_trancl elim:last_leq_path)
next
  fix Cs Cs' Ds assume "(last Cs, last Cs') \<in> (subcls1 P)\<^sup>+"
    and "P,C \<turnstile> Cs' \<sqsubset>\<^sup>1 Ds"
  thus "(last Cs, last Ds) \<in> (subcls1 P)\<^sup>+" using wf
    by (fastforce dest:last_leq_path)
qed



lemma leq_path1_wfD:
"\<lbrakk> P,C \<turnstile> Cs \<sqsubset>\<^sup>1 Cs'; wf_prog wf_md P \<rbrakk> \<Longrightarrow> Cs \<noteq> Cs' \<and> (Cs',Cs) \<notin> (leq_path1 P C)\<^sup>+"

apply (rule conjI)
 apply (erule leq_path1.cases) 
  apply simp
  apply (drule_tac Cs="Ds" in Subobjs_nonempty)
  apply (rule butlast_noteq) apply assumption
 apply clarsimp
 apply (drule subclsS_subcls1)
 apply (drule subcls1_wfD) apply simp_all
apply clarsimp
apply (frule last_leq_path)
 apply simp
apply (drule last_leq_paths)
 apply simp
apply (drule_tac r="subcls1 P" in r_into_trancl)
apply (drule subcls_asym) 
apply auto
done



lemma leq_path_asym:
"\<lbrakk>(Cs,Cs') \<in> (leq_path1 P C)\<^sup>+; wf_prog wf_md P\<rbrakk> \<Longrightarrow> (Cs',Cs) \<notin> (leq_path1 P C)\<^sup>+"

apply(erule tranclE)
apply(fast dest!:leq_path1_wfD )
apply(fast dest!:leq_path1_wfD intro: trancl_trans)
done



lemma leq_path_asym2:"\<lbrakk>P,C \<turnstile> Cs \<sqsubseteq> Cs'; P,C \<turnstile> Cs' \<sqsubseteq> Cs; wf_prog wf_md P\<rbrakk> \<Longrightarrow> Cs = Cs'"

apply (induct rule:rtrancl.induct)
 apply simp
apply (drule rtrancl_into_trancl1)
 apply simp
apply (drule leq_path_asym)
 apply simp
apply (drule_tac a="c" and b="a" in rtranclD)
apply simp
done



lemma leq_path_Subobjs:
"\<lbrakk>P,C \<turnstile> [C] \<sqsubseteq> Cs; is_class P C; wf_prog wf_md P\<rbrakk> \<Longrightarrow> Subobjs P C Cs"
by (induct rule:rtrancl_induct,auto intro:Subobjs_Base elim!:leq_path1.cases,
         auto dest!:Subobjs_subclass intro!:Subobjs_Sh SubobjsR_Base dest!:subclsSD
              intro:wf_cdecl_supD class_wf ShBaseclass_isBaseclass subclsSI)




subsection\<open>Lemmas concerning Subobjs\<close>

lemma Subobj_last_isClass:"\<lbrakk>wf_prog wf_md P; Subobjs P C Cs\<rbrakk> \<Longrightarrow> is_class P (last Cs)"

apply (frule Subobjs_isClass)
apply (drule Subobjs_subclass)
apply (drule rtranclD)
apply (erule disjE)
 apply simp
apply clarsimp
apply (erule trancl_induct)
 apply (fastforce dest:subcls1D class_wf elim:wf_cdecl_supD)
apply (fastforce dest:subcls1D class_wf elim:wf_cdecl_supD)
done



lemma converse_SubobjsR_Rep:
  "\<lbrakk>Subobjs\<^sub>R P C Cs; P \<turnstile> last Cs \<prec>\<^sub>R C'; wf_prog wf_md P\<rbrakk> 
\<Longrightarrow> Subobjs\<^sub>R P C (Cs@[C'])"

apply (induct rule:Subobjs\<^sub>R.induct)
 apply (frule subclsR_subcls1)
 apply (fastforce dest!:subcls1D class_wf wf_cdecl_supD SubobjsR_Base SubobjsR_Rep)
apply (fastforce elim:SubobjsR_Rep simp: SubobjsR_nonempty split:if_split_asm)
done



lemma converse_Subobjs_Rep:
  "\<lbrakk>Subobjs P C Cs; P \<turnstile> last Cs \<prec>\<^sub>R C';  wf_prog wf_md P\<rbrakk> 
\<Longrightarrow> Subobjs P C (Cs@[C'])"
by (induct rule:Subobjs.induct, fastforce dest:converse_SubobjsR_Rep Subobjs_Rep, 
  fastforce dest:converse_SubobjsR_Rep Subobjs_Sh)



lemma isSubobj_Subobjs_rev:
assumes subo:"is_subobj P ((C,C'#rev Cs'))" and wf:"wf_prog wf_md P"
shows "Subobjs P C (C'#rev Cs')"
using subo
proof (induct Cs')
  case Nil
  show ?case
  proof (cases "C=C'")
    case True
    have "is_subobj P ((C,C'#rev []))" by fact
    with True have "is_subobj P ((C,[C]))" by simp
    hence "is_class P C"
      by (fastforce elim:converse_rtranclE dest:subclsS_subcls1 elim:subcls1_class)
    with True show ?thesis by (fastforce intro:Subobjs_Base)
  next
    case False
    have "is_subobj P ((C,C'#rev []))" by fact
    with False obtain D where sup:"P \<turnstile> C \<preceq>\<^sup>* D" and subS:"P \<turnstile> D \<prec>\<^sub>S C'"
      by fastforce
    with wf have "is_class P C'"
      by (fastforce dest:subclsS_subcls1 subcls1D class_wf elim:wf_cdecl_supD)
    hence "Subobjs\<^sub>R P C' [C']" by (fastforce elim:SubobjsR_Base)
    with sup subS have "Subobjs P C [C']" by -(erule Subobjs_Sh, simp)
    thus ?thesis by simp
  qed 
next 
  case (Cons C'' Cs'')
  have IH:"is_subobj P ((C,C'#rev Cs'')) \<Longrightarrow> Subobjs P C (C'#rev Cs'')"
    and subo:"is_subobj P ((C,C'#rev(C''# Cs'')))" by fact+
  obtain Ds' where Ds':"Ds' = rev Cs''" by simp
  obtain D Ds where DDs:"D#Ds = Ds'@[C'']" by (cases Ds') auto
  with Ds' subo have "is_subobj P ((C,C'#D#Ds))" by simp
  hence subobl:"is_subobj P ((C,butlast(C'#D#Ds)))" 
    and subRbl:"P \<turnstile> last(butlast(C'#D#Ds)) \<prec>\<^sub>R last(C'#D#Ds)" by simp+
  with DDs Ds' have "is_subobj P ((C,C'#rev Cs''))" by (simp del: is_subobj.simps)
  with IH have suborev:"Subobjs P C (C'#rev Cs'')" by simp
  from subRbl DDs Ds' have subR:"P \<turnstile> last(C'#rev Cs'') \<prec>\<^sub>R C''" by simp
  with suborev wf show ?case by (fastforce dest:converse_Subobjs_Rep)
qed



lemma isSubobj_Subobjs:
assumes subo:"is_subobj P ((C,Cs))" and wf:"wf_prog wf_md P"
shows "Subobjs P C Cs"

using subo
proof (induct Cs)
  case Nil
  thus ?case by simp
next
  case (Cons C' Cs')
  have subo:"is_subobj P ((C,C'#Cs'))" by fact
  obtain Cs'' where Cs'':"Cs'' = rev Cs'" by simp
  with subo have "is_subobj P ((C,C'#rev Cs''))" by simp
  with wf have "Subobjs P C (C'#rev Cs'')" by - (rule isSubobj_Subobjs_rev)
  with Cs'' show ?case by simp
qed



lemma isSubobj_eq_Subobjs:
  "wf_prog wf_md P \<Longrightarrow> is_subobj P ((C,Cs)) = (Subobjs P C Cs)"
by(auto elim:isSubobj_Subobjs Subobjs_isSubobj)



lemma subo_trans_subcls:
  assumes subo:"Subobjs P C (Cs@ C'#rev Cs')"
  shows "\<forall>C'' \<in> set Cs'. (C',C'') \<in> (subcls1 P)\<^sup>+"

using subo
proof (induct Cs')
  case Nil
  thus ?case by simp
next
  case (Cons D Ds)
  have IH:"Subobjs P C (Cs @ C' # rev Ds) \<Longrightarrow>
           \<forall>C''\<in>set Ds. (C', C'') \<in> (subcls1 P)\<^sup>+"
    and "Subobjs P C (Cs @ C' # rev (D # Ds))" by fact+
  hence subo':"Subobjs P C (Cs@ C'#rev Ds @ [D])" by simp
  hence "Subobjs P C (Cs@ C'#rev Ds)"
    by -(rule appendSubobj,simp_all)
  with IH have set:"\<forall>C''\<in>set Ds. (C', C'') \<in> (subcls1 P)\<^sup>+" by simp
  hence revset:"\<forall>C''\<in>set (rev Ds). (C', C'') \<in> (subcls1 P)\<^sup>+" by simp
  have "(C',D) \<in> (subcls1 P)\<^sup>+"
  proof (cases "Ds = []")
    case True
    with subo' have "Subobjs P C (Cs@[C',D])" by simp
    thus ?thesis
      by (fastforce intro: subclsR_subcls1 Subobjs_subclsR)
  next
    case False
    with revset have hd:"(C',hd Ds) \<in> (subcls1 P)\<^sup>+"
      apply -
      apply (erule ballE)
       apply simp
      apply (simp add:in_set_conv_decomp)
      apply (erule_tac x="[]" in allE)
      apply (erule_tac x="tl Ds" in allE)
      apply simp
      done
    from False subo' have "(hd Ds,D) \<in> (subcls1 P)\<^sup>+"
      apply (cases Ds)
       apply simp
      apply simp
      apply (rule r_into_trancl)
      apply (rule subclsR_subcls1)
      apply (rule_tac Cs="Cs @ C' # rev list" in Subobjs_subclsR)
      apply simp
      done
    with hd show ?thesis by (rule trancl_trans)
  qed
  with set show ?case by simp
qed



lemma unique1:
  assumes subo:"Subobjs P C (Cs@ C'#Cs')" and wf:"wf_prog wf_md P"
  shows "C' \<notin> set Cs'"

proof -
  obtain Ds where Ds:"Ds = rev Cs'" by simp
  with subo have "Subobjs P C (Cs@ C'#rev Ds)" by simp
  with Ds subo have "\<forall>C'' \<in> set Cs'. (C',C'') \<in> (subcls1 P)\<^sup>+"
    by (fastforce dest:subo_trans_subcls)
  with wf have "\<forall>C'' \<in> set Cs'. C' \<noteq> C''"
    by (auto dest:subcls_irrefl)
  thus ?thesis by fastforce
qed



lemma subo_subcls_trans:
  assumes subo:"Subobjs P C (Cs@ C'#Cs')"
  shows "\<forall>C'' \<in> set Cs. (C'',C') \<in> (subcls1 P)\<^sup>+"

proof -
  from wf subo have "\<And>C''. C'' \<in> set Cs \<Longrightarrow> (C'',C') \<in> (subcls1 P)\<^sup>+"
    apply (auto simp:in_set_conv_decomp)
    apply (case_tac zs)
     apply (fastforce intro: subclsR_subcls1 Subobjs_subclsR)
    apply simp
    apply (rule_tac b="a" in trancl_rtrancl_trancl)
     apply (fastforce intro: subclsR_subcls1 Subobjs_subclsR)
    apply (subgoal_tac "P \<turnstile> a \<preceq>\<^sup>* last (a # list @ [C'])")
     apply simp
    apply (rule Subobjs_subclass)
    apply (rule_tac C="C" and Cs=" ys @[C'']" in Subobjs_Subobjs)
    apply (rule_tac Cs'="Cs'" in appendSubobj)
    apply simp_all
    done
  thus ?thesis by fastforce
qed



lemma unique2:
  assumes subo:"Subobjs P C (Cs@ C'#Cs')" and wf:"wf_prog wf_md P"
  shows "C' \<notin> set Cs"

proof -
  from subo wf have "\<forall>C'' \<in> set Cs. (C'',C') \<in> (subcls1 P)\<^sup>+"
    by (fastforce dest:subo_subcls_trans)
  with wf have "\<forall>C'' \<in> set Cs. C' \<noteq> C''"
    by (auto dest:subcls_irrefl)
  thus ?thesis by fastforce
qed




lemma mdc_hd_path:
assumes subo:"Subobjs P C Cs" and set:"C \<in> set Cs" and wf:"wf_prog wf_md P"
shows "C = hd Cs"

proof -
  from subo set obtain Ds Ds' where Cs:"Cs = Ds@ C#Ds'"
    by (auto simp:in_set_conv_decomp)
  then obtain Cs' where Cs':"Cs' = rev Ds" by simp
  with Cs subo have subo':"Subobjs P C ((rev Cs')@ C#Ds')" by simp
  thus ?thesis
  proof (cases Cs')
    case Nil
    with Cs Cs' show ?thesis by simp
  next
    case (Cons X Xs)
    with subo' have suboX:"Subobjs P C ((rev Xs)@[X,C]@Ds')" by simp
    hence leq:"P \<turnstile> X \<prec>\<^sup>1 C"
      by (fastforce intro:subclsR_subcls1 Subobjs_subclsR)
    from suboX wf have "P \<turnstile> C \<preceq>\<^sup>* last ((rev Xs)@[X])"
      by (fastforce intro:Subobjs_subclass appendSubobj)
    with leq have "(C,C) \<in> (subcls1 P)\<^sup>+" by simp
    with wf show ?thesis by (fastforce dest:subcls_irrefl)
  qed
qed



lemma mdc_eq_last:
  assumes subo:"Subobjs P C Cs" and last:"last Cs = C" and wf:"wf_prog wf_md P"
shows "Cs = [C]"

proof -
  from subo have notempty:"Cs \<noteq> []" by - (drule Subobjs_nonempty)
  hence lastset:"last Cs \<in> set Cs"
    apply (auto simp add:in_set_conv_decomp)
    apply (rule_tac x="butlast Cs" in exI)
    apply (rule_tac x="[]" in exI)
    apply simp
    done
  with last have C:"C \<in> set Cs" by simp
  with subo wf have hd:"C = hd Cs" by -(rule mdc_hd_path)
  then obtain Cs' where Cs':"Cs' = tl Cs" by simp
  thus ?thesis
  proof (cases Cs')
    case Nil
    with hd subo Cs' show ?thesis by (fastforce dest:Subobjs_nonempty hd_Cons_tl)
  next
    case (Cons D Ds)
    with Cs' hd notempty have Cs:"Cs=C#D#Ds" by simp
    with subo have "Subobjs P C (C#D#Ds)" by simp
    with wf have notset:"C \<notin> set (D#Ds)" by -(rule_tac Cs="[]" in unique1,simp_all)
    from Cs last have "last Cs = last (D#Ds)" by simp
    hence "last Cs \<in> set (D#Ds)"
      apply (auto simp add:in_set_conv_decomp)
      apply (erule_tac x="butlast Ds" in allE)
      apply (erule_tac x="[]" in allE)
      apply simp
      done
    with last have "C \<in> set (D#Ds)" by simp
    with notset show ?thesis by simp
  qed
qed



lemma assumes leq:"P \<turnstile> C \<preceq>\<^sup>* D" and wf:"wf_prog wf_md P"
  shows subcls_leq_path:"\<exists>Cs. P,C \<turnstile> [C] \<sqsubseteq> Cs@[D]"

using leq
proof (induct rule:rtrancl.induct)
  fix C show "\<exists>Cs. P,C \<turnstile> [C] \<sqsubseteq> Cs@[C]" by (rule_tac x="[]" in exI,simp)
next
  fix C C' D assume leq':"P \<turnstile> C \<preceq>\<^sup>* C'" and IH:"\<exists>Cs. P,C \<turnstile> [C] \<sqsubseteq> Cs@[C']"
    and sub:"P \<turnstile> C' \<prec>\<^sup>1 D"
  from sub have "is_class P C'" by (rule subcls1_class)
  with leq' have "class": "is_class P C" by (rule subcls_is_class)
  from IH obtain Cs where steps:"P,C \<turnstile> [C] \<sqsubseteq> Cs@[C']" by auto
  hence subo:"Subobjs P C (Cs@[C'])" using "class" wf 
    by (fastforce intro:leq_path_Subobjs)
  { assume "P \<turnstile> C' \<prec>\<^sub>R D"
    with subo wf have "Subobjs P C (Cs@[C',D])"
      by (fastforce dest:converse_Subobjs_Rep)
    with subo have "P,C \<turnstile> (Cs@[C']) \<sqsubset>\<^sup>1 (Cs@[C']@[D])"
      by (fastforce intro:leq_path_rep) }
  moreover 
  { assume "P \<turnstile> C' \<prec>\<^sub>S D"
    with subo have "P,C \<turnstile> (Cs@[C']) \<sqsubset>\<^sup>1 [D]" by (rule leq_path_sh) }
  ultimately show "\<exists>Cs. P,C \<turnstile> [C] \<sqsubseteq> Cs@[D]" using sub steps
    apply (auto dest!:subcls1_subclsR_or_subclsS)
    apply (rule_tac x="Cs@[C']" in exI) apply simp
    apply (rule_tac x="[]" in exI) apply simp
    done
qed

    


lemma assumes subo:"Subobjs P C (rev Cs)" and wf:"wf_prog wf_md P"
  shows subobjs_rel_rev:"P,C \<turnstile> [C] \<sqsubseteq> (rev Cs)"
using subo
proof (induct Cs)
  case Nil
  thus ?case by (fastforce dest:Subobjs_nonempty)
next
  case (Cons C' Cs')
  have subo':"Subobjs P C (rev (C'#Cs'))"
    and IH:"Subobjs P C (rev Cs') \<Longrightarrow> P,C \<turnstile> [C] \<sqsubseteq> rev Cs'" by fact+
  from subo' have "class": "is_class P C" by(rule Subobjs_isClass)
  show ?case
  proof (cases "Cs' = []")
    case True hence empty:"Cs' = []" .
    with subo' have subo'':"Subobjs P C [C']" by simp
    thus ?thesis
    proof (cases "C = C'")
      case True
      with empty show ?thesis by simp
    next
      case False
      with subo'' obtain D D' where leq:"P \<turnstile> C \<preceq>\<^sup>* D" and subS:"P \<turnstile> D \<prec>\<^sub>S D'"
        and suboR:"Subobjs\<^sub>R P D' [C']"
        by (auto elim:Subobjs.cases dest:hd_SubobjsR)
      from suboR have C':"C' = D'" by (fastforce dest:hd_SubobjsR)
      from leq wf obtain Ds where steps:"P,C \<turnstile> [C] \<sqsubseteq> Ds@[D]"
        by (auto dest:subcls_leq_path)
      hence suboSteps:"Subobjs P C (Ds@[D])" using "class" wf
        apply (induct rule:rtrancl_induct)
         apply (erule Subobjs_Base)
        apply (auto elim!:leq_path1.cases)
        apply (subgoal_tac "Subobjs\<^sub>R P D [D]")
         apply (fastforce dest:Subobjs_subclass intro:Subobjs_Sh)
        apply (fastforce dest!:subclsSD intro:SubobjsR_Base wf_cdecl_supD 
                                             class_wf ShBaseclass_isBaseclass)
        done
      hence step:"P,C \<turnstile> (Ds@[D]) \<sqsubset>\<^sup>1 [D']" using subS by (rule leq_path_sh)
      with steps empty False C' show ?thesis by simp
    qed
  next
    case False
    with subo' have subo'':"Subobjs P C (rev Cs')"
      by (fastforce intro:butlast_Subobjs)
    with IH have steps:"P,C \<turnstile> [C] \<sqsubseteq> rev Cs'" by simp
    from subo' subo'' have "P,C \<turnstile> rev Cs' \<sqsubset>\<^sup>1 rev (C'#Cs')"
      by (fastforce intro:leq_pathRep)
    with steps show ?thesis by simp
  qed
qed



lemma subobjs_rel:
assumes subo:"Subobjs P C Cs" and wf:"wf_prog wf_md P"
shows "P,C \<turnstile> [C] \<sqsubseteq> Cs"

proof -
  obtain Cs' where Cs':"Cs' = rev Cs" by simp
  with subo have "Subobjs P C (rev Cs')" by simp
  hence "P,C \<turnstile> [C] \<sqsubseteq> rev Cs'" using wf by (rule subobjs_rel_rev)
  with Cs' show ?thesis by simp
qed



lemma assumes wf:"wf_prog wf_md P"
  shows leq_path_last:"\<lbrakk>P,C \<turnstile> Cs \<sqsubseteq> Cs'; last Cs = last Cs'\<rbrakk> \<Longrightarrow> Cs = Cs'"

proof(induct rule:rtrancl_induct)
  show "Cs = Cs" by simp
next
  fix Cs' Cs''
  assume leqs:"P,C \<turnstile> Cs \<sqsubseteq> Cs'" and leq:"P,C \<turnstile> Cs' \<sqsubset>\<^sup>1 Cs''"
    and last:"last Cs = last Cs''"
    and IH:"last Cs = last Cs' \<Longrightarrow> Cs = Cs'"
  from leq wf have sup1:"P \<turnstile> last Cs' \<prec>\<^sup>1 last Cs''"
    by(rule last_leq_path)
  { assume "Cs = Cs'"
    with last have eq:"last Cs'' = last Cs'" by simp
    with eq wf sup1 have "Cs = Cs''" by(fastforce dest:subcls1_wfD) }
  moreover
  { assume "(Cs,Cs') \<in> (leq_path1 P C)\<^sup>+"
    hence sub:"(last Cs,last Cs') \<in> (subcls1 P)\<^sup>+" using wf
      by(rule last_leq_paths)
    with sup1 last have "(last Cs'',last Cs'') \<in> (subcls1 P)\<^sup>+" by simp
    with wf have "Cs = Cs''" by(fastforce dest:subcls_irrefl) }
  ultimately show "Cs = Cs''" using leqs
    by(fastforce dest:rtranclD)
qed

 


subsection\<open>Well-formedness and appendPath\<close>


lemma appendPath1:
  "\<lbrakk>Subobjs P C Cs; Subobjs P (last Cs) Ds; last Cs \<noteq> hd Ds\<rbrakk>
\<Longrightarrow> Subobjs P C Ds"

apply(subgoal_tac "\<not> Subobjs\<^sub>R P (last Cs) Ds")
 apply (subgoal_tac "\<exists>C' D. P \<turnstile> last Cs \<preceq>\<^sup>* C' \<and> P \<turnstile> C' \<prec>\<^sub>S D \<and> Subobjs\<^sub>R P D Ds")
  apply clarsimp
  apply (drule Subobjs_subclass)
  apply (subgoal_tac "P \<turnstile> C \<preceq>\<^sup>* C'")
   apply (erule_tac C'="C'" and D="D" in Subobjs_Sh)
    apply simp
   apply simp
  apply fastforce
 apply (erule Subobjs_notSubobjsR)
 apply simp
apply (fastforce dest:hd_SubobjsR)
done
 



lemma appendPath2_rev:
assumes subo1:"Subobjs P C Cs" and subo2:"Subobjs P (last Cs) (last Cs#rev Ds)"
  and wf:"wf_prog wf_md P"
shows "Subobjs P C (Cs@(tl (last Cs#rev Ds)))"
using subo2
proof (induct Ds)
  case Nil
  with subo1 show ?case by simp
next
  case (Cons D' Ds')
  have IH:"Subobjs P (last Cs) (last Cs#rev Ds')
    \<Longrightarrow> Subobjs P C (Cs@tl(last Cs#rev Ds'))"
    and subo:"Subobjs P (last Cs) (last Cs#rev (D'#Ds'))" by fact+
  from subo have "Subobjs P (last Cs) (last Cs#rev Ds')"
    by (fastforce intro:butlast_Subobjs)
  with IH have subo':"Subobjs P C (Cs@tl(last Cs#rev Ds'))"
    by simp
  have last:"last(last Cs#rev Ds') = last (Cs@tl(last Cs#rev Ds'))"
    by (cases Ds')auto
  obtain C' Cs' where C':"C' = last(last Cs#rev Ds')" and
    "Cs' = butlast(last Cs#rev Ds')" by simp
  then have "Cs' @ [C'] = last Cs # rev Ds'"
    using append_butlast_last_id by blast
  hence "last Cs#rev (D'#Ds') = Cs'@[C',D']" by simp
  with subo have "Subobjs P (last Cs) (Cs'@[C',D'])" by (cases Cs') auto
  hence "P \<turnstile> C' \<prec>\<^sub>R D'" by - (rule Subobjs_subclsR,simp)
  with C' last have "P \<turnstile> last (Cs@tl(last Cs#rev Ds')) \<prec>\<^sub>R D'" by simp
  with subo' wf have "Subobjs P C ((Cs@tl(last Cs#rev Ds'))@[D'])"
    by (erule_tac Cs="(Cs@tl(last Cs#rev Ds'))" in converse_Subobjs_Rep) simp
  thus ?case by simp
qed



lemma appendPath2:
assumes subo1:"Subobjs P C Cs" and subo2:"Subobjs P (last Cs) Ds" 
  and eq:"last Cs = hd Ds" and wf:"wf_prog wf_md P"
shows "Subobjs P C (Cs@(tl Ds))"

using subo2
proof (cases Ds)
  case Nil
  with subo1 show ?thesis by simp
next
  case (Cons D' Ds')
  with subo2 eq have subo:"Subobjs P (last Cs) (last Cs#Ds')" by simp
  obtain Ds'' where Ds'':"Ds'' = rev Ds'" by simp
  with subo have "Subobjs P (last Cs) (last Cs#rev Ds'')" by simp
  with subo1 wf have "Subobjs P C (Cs@(tl (last Cs#rev Ds'')))"
    by -(rule appendPath2_rev)
  with Ds'' eq Cons show ?thesis by simp
qed



lemma Subobjs_appendPath:
  "\<lbrakk>Subobjs P C Cs; Subobjs P (last Cs) Ds;wf_prog wf_md P\<rbrakk>
\<Longrightarrow> Subobjs P C (Cs@\<^sub>pDs)"
by(fastforce elim:appendPath2 appendPath1 simp:appendPath_def)


subsection\<open>Path and program size\<close>

lemma assumes subo:"Subobjs P C Cs" and wf:"wf_prog wf_md P"
  shows path_contains_classes:"\<forall>C' \<in> set Cs. is_class P C'"
using subo

proof clarsimp
  fix C' assume subo:"Subobjs P C Cs" and set:"C' \<in> set Cs"
  from set obtain Ds Ds' where Cs:"Cs = Ds@C'#Ds'"
    by (fastforce simp:in_set_conv_decomp)
  with Cs show "is_class P C'"
  proof (cases "Ds = []")
    case True
    with Cs subo have subo':"Subobjs P C (C'#Ds')" by simp
    thus ?thesis by (rule Subobjs.cases,
      auto dest:hd_SubobjsR intro:SubobjsR_isClass)
  next
    case False
    then obtain C'' Cs'' where Cs'':"Cs'' = butlast Ds"
      and last:"C'' = last Ds" by auto
    with False have Ds:"Ds = Cs''@[C'']" by simp
    with Cs subo have subo':"Subobjs P C (Cs''@[C'',C']@Ds')"
      by simp
    hence "P \<turnstile> C'' \<prec>\<^sub>R C'" by(fastforce intro:isSubobjs_subclsR Subobjs_isSubobj)
    with wf show ?thesis
      by (fastforce dest!:subclsRD
                   intro:wf_cdecl_supD class_wf RepBaseclass_isBaseclass subclsSI)
  qed
qed


lemma path_subset_classes:"\<lbrakk>Subobjs P C Cs; wf_prog wf_md P\<rbrakk> 
  \<Longrightarrow> set Cs \<subseteq> {C. is_class P C}"
by (auto dest:path_contains_classes)


lemma assumes subo:"Subobjs P C (rev Cs)" and wf:"wf_prog wf_md P"
  shows rev_path_distinct_classes:"distinct Cs"
  using subo
proof (induct Cs)
  case Nil thus ?case by(fastforce dest:Subobjs_nonempty)
next
  case (Cons C' Cs')
  have subo':"Subobjs P C (rev(C'#Cs'))"
    and IH:"Subobjs P C (rev Cs') \<Longrightarrow> distinct Cs'" by fact+
  show ?case
  proof (cases "Cs' = []")
    case True thus ?thesis by simp
  next
    case False
    hence rev:"rev Cs' \<noteq> []" by simp
    from subo' have subo'':"Subobjs P C (rev Cs'@[C'])" by simp
    hence "Subobjs P C (rev Cs')" using rev wf
      by(fastforce dest:appendSubobj)
    with IH have dist:"distinct Cs'" by simp
    from subo'' wf have "C' \<notin> set (rev Cs')"
      by(fastforce dest:unique2)
    with dist show ?thesis by simp
  qed
qed


lemma assumes subo:"Subobjs P C Cs" and wf:"wf_prog wf_md P"
  shows path_distinct_classes:"distinct Cs"

proof -
  obtain Cs' where Cs':"Cs' = rev Cs" by simp
  with subo have "Subobjs P C (rev Cs')" by simp
  with wf have "distinct Cs'"
    by -(rule rev_path_distinct_classes)
  with Cs' show ?thesis by simp
qed



lemma assumes wf:"wf_prog wf_md P" 
  shows prog_length:"length P = card {C. is_class P C}"

proof -
  from wf have dist_fst:"distinct_fst P" by (simp add:wf_prog_def)
  hence "distinct P" by (simp add:distinct_fst_def,induct P,auto)
  hence card_set:"card (set P) = length P" by (rule distinct_card)
  from dist_fst have set:"{C. is_class P C} = fst ` (set P)"
    by (simp add:is_class_def class_def,auto simp:distinct_fst_def,
      auto dest:map_of_eq_Some_iff intro!:image_eqI)
  from dist_fst have "card(fst ` (set P)) = card (set P)"
    by(auto intro:card_image simp:distinct_map distinct_fst_def)
  with card_set set show ?thesis by simp
qed




lemma assumes subo:"Subobjs P C Cs" and wf:"wf_prog wf_md P"
  shows path_length:"length Cs \<le> length P"

proof -
  from subo wf have "distinct Cs" by (rule path_distinct_classes)
  hence card_eq_length:"card (set Cs) = length Cs" by (rule distinct_card)
  from subo wf have "card (set Cs) \<le> card {C. is_class P C}"
    by (auto dest:path_subset_classes intro:card_mono finite_is_class)
  with card_eq_length have "length Cs \<le> card {C. is_class P C}" by simp
  with wf show ?thesis by(fastforce dest:prog_length)
qed



lemma empty_path_empty_set:"{Cs. Subobjs P C Cs \<and> length Cs \<le> 0} = {}" 
by (auto dest:Subobjs_nonempty)

lemma split_set_path_length:"{Cs. Subobjs P C Cs \<and> length Cs \<le> Suc(n)} = 
{Cs. Subobjs P C Cs \<and> length Cs \<le> n} \<union> {Cs. Subobjs P C Cs \<and> length Cs = Suc(n)}"
by auto

lemma empty_list_set:"{xs. set xs \<subseteq> F \<and> xs = []} = {[]}"
by auto

lemma suc_n_union_of_union:"{xs. set xs \<subseteq> F \<and> length xs = Suc n} = (UN x:F. UN xs : {xs. set xs \<le> F \<and> length xs = n}. {x#xs})"
by (auto simp:length_Suc_conv)

lemma max_length_finite_set:"finite F \<Longrightarrow> finite{xs. set xs <= F \<and> length xs = n}"
by(induct n,simp add:empty_list_set, simp add:suc_n_union_of_union)

lemma path_length_n_finite_set:
"wf_prog wf_md P \<Longrightarrow> finite{Cs. Subobjs P C Cs \<and> length Cs = n}"
by (rule_tac B="{Cs. set Cs <= {C. is_class P C} \<and> length Cs = n}" in finite_subset,
  auto dest:path_contains_classes intro:max_length_finite_set simp:finite_is_class)

lemma path_finite_leq:
"wf_prog wf_md P \<Longrightarrow> finite{Cs. Subobjs P C Cs \<and> length Cs \<le> length P}"
  by (induct ("length P"), simp only:empty_path_empty_set,
    auto intro:path_length_n_finite_set simp:split_set_path_length)

lemma path_finite:"wf_prog wf_md P \<Longrightarrow> finite{Cs. Subobjs P C Cs}"
by (subgoal_tac "{Cs. Subobjs P C Cs} = 
  {Cs. Subobjs P C Cs \<and> length Cs \<le> length P}",
  auto intro:path_finite_leq path_length)


subsection\<open>Well-formedness and Path\<close>

lemma path_via_reverse:
  assumes path_via:"P \<turnstile> Path C to D via Cs" and wf:"wf_prog wf_md P"
  shows "\<forall>Cs'. P \<turnstile> Path D to C via Cs' \<longrightarrow> Cs = [C] \<and> Cs' = [C] \<and> C = D"
proof -
  from path_via have subo:"Subobjs P C Cs" and last:"last Cs = D"
    by(simp add:path_via_def)+
  hence leq:"P \<turnstile> C \<preceq>\<^sup>* D" by(fastforce dest:Subobjs_subclass)
  { fix Cs' assume "P \<turnstile> Path D to C via Cs'"
    hence subo':"Subobjs P D Cs'" and last':"last Cs' = C"
      by(simp add:path_via_def)+
    hence leq':"P \<turnstile> D \<preceq>\<^sup>* C" by(fastforce dest:Subobjs_subclass)
    with leq wf have CeqD:"C = D" by(rule subcls_asym2)
    moreover have Cs:"Cs = [C]" using CeqD subo last wf by(fastforce intro:mdc_eq_last)
    moreover have "Cs' = [C]" using CeqD subo' last' wf by(fastforce intro:mdc_eq_last)
    ultimately have "Cs = [C] \<and> Cs' = [C] \<and> C = D" by simp }
  thus ?thesis by blast
qed


lemma path_hd_appendPath:
  assumes path:"P,C \<turnstile> Cs \<sqsubseteq> Cs'@\<^sub>pCs" and last:"last Cs' = hd Cs"
  and notemptyCs:"Cs \<noteq> []" and notemptyCs':"Cs' \<noteq> []" and wf:"wf_prog wf_md P"
  shows "Cs' = [hd Cs]"

using path
proof -
  from path notemptyCs last have path2:"P,C \<turnstile> Cs \<sqsubseteq> Cs'@ tl Cs"
    by (simp add:appendPath_def)
  thus ?thesis
  proof (auto dest!:rtranclD)
    assume "Cs = Cs'@ tl Cs"
    with notemptyCs show "Cs' = [hd Cs]" by (rule app_hd_tl)
  next
    assume trancl:"(Cs,Cs'@ tl Cs) \<in> (leq_path1 P C)\<^sup>+"
    from notemptyCs' last have butlastLast:"Cs' = butlast Cs' @ [hd Cs]"
      by -(drule append_butlast_last_id,simp)
    with trancl have trancl':"(Cs, (butlast Cs' @ [hd Cs]) @ tl Cs) \<in> (leq_path1 P C)\<^sup>+"
      by simp
    from notemptyCs have "(butlast Cs' @ [hd Cs]) @ tl Cs = butlast Cs' @ Cs"
      by simp
    with trancl' have "(Cs, butlast Cs' @ Cs) \<in> (leq_path1 P C)\<^sup>+" by simp
    hence "(last Cs, last (butlast Cs' @ Cs)) \<in> (subcls1 P)\<^sup>+" using wf
      by (rule last_leq_paths)
    with notemptyCs have "(last Cs, last Cs) \<in> (subcls1 P)\<^sup>+"
      by -(drule_tac xs="butlast Cs'" in last_appendR,simp)
    with wf show ?thesis by (auto dest:subcls_irrefl)
  qed
qed


lemma path_via_C: "\<lbrakk>P \<turnstile> Path C to C via Cs; wf_prog wf_md P\<rbrakk> \<Longrightarrow> Cs = [C]"
by (fastforce intro:mdc_eq_last simp:path_via_def)


lemma assumes wf:"wf_prog wf_md P"
  and path_via:"P \<turnstile> Path last Cs to C via Cs'"
  and path_via':"P \<turnstile> Path last Cs to C via Cs''"
  and appendPath:"Cs = Cs@\<^sub>pCs'"
shows appendPath_path_via:"Cs = Cs@\<^sub>pCs''"

proof -
  from path_via have notempty:"Cs' \<noteq> []"
    by(fastforce intro!:Subobjs_nonempty simp:path_via_def)
  { assume eq:"last Cs = hd Cs'"
    and Cs:"Cs = Cs@tl Cs'"
    from Cs have "tl Cs' = []" by simp
    with eq notempty have "Cs' = [last Cs]"
      by -(drule hd_Cons_tl,simp) }
  moreover
  { assume "Cs = Cs'"
    with wf path_via have "Cs' = [last Cs]"
      by(fastforce intro:mdc_eq_last simp:path_via_def) }
  ultimately have eq:"Cs' = [last Cs]" using appendPath
    by(simp add:appendPath_def,split if_split_asm,simp_all)
  with path_via have "C = last Cs"
    by(simp add:path_via_def)
  with wf path_via' have "Cs'' = [last Cs]"
    by simp(rule path_via_C)
  thus ?thesis by (simp add:appendPath_def)
qed



lemma subo_no_path:
  assumes subo:"Subobjs P C' (Cs @ C#Cs')" and wf:"wf_prog wf_md P"
  and notempty:"Cs' \<noteq> []"
  shows "\<not> P \<turnstile> Path last Cs' to C via Ds"

proof
  assume "P \<turnstile> Path last Cs' to C via Ds"
  hence subo':"Subobjs P (last Cs') Ds" and last:"last Ds = C"
    by (auto simp:path_via_def)
  hence notemptyDs:"Ds \<noteq> []" by -(drule Subobjs_nonempty)
  then obtain D' Ds' where D'Ds':"Ds = D'#Ds'" by(cases Ds)auto
  from subo have suboC:"Subobjs P C (C#Cs')" by (rule Subobjs_Subobjs)
  with wf subo' notempty have suboapp:"Subobjs P C ((C#Cs')@\<^sub>pDs)"
    by -(rule Subobjs_appendPath,simp_all)
  with notemptyDs last have last':"last ((C#Cs')@\<^sub>pDs) = C"
    by -(drule_tac Cs'="(C#Cs')" in appendPath_last,simp)
  from notemptyDs have "(C#Cs')@\<^sub>pDs \<noteq> []"
    by (simp add:appendPath_def)
  with last' have "C \<in> set ((C#Cs')@\<^sub>pDs)"
    apply (auto simp add:in_set_conv_decomp)
    apply (rule_tac x="butlast((C#Cs')@\<^sub>pDs)" in exI)
    apply (rule_tac x="[]" in exI)
    apply (drule append_butlast_last_id)
    apply simp
    done
  with suboapp wf have hd:"C = hd ((C#Cs')@\<^sub>pDs)" by -(rule  mdc_hd_path)
  thus "False"
  proof (cases "last (C#Cs') = hd Ds")
    case True
    hence eq:"(C#Cs')@\<^sub>pDs = (C#Cs')@(tl Ds)" by (simp add:appendPath_def)
    show ?thesis
    proof (cases Ds')
      case Nil
      with D'Ds' have Ds:"Ds = [D']" by simp
      with last have "C = D'" by simp
      with True notempty Ds have "last (C#Cs') = C" by simp
      with notempty have "last Cs' = C" by simp
      with notempty have Cset:"C \<in> set Cs'"
        apply (auto simp add:in_set_conv_decomp)
        apply (rule_tac x="butlast Cs'" in exI)
        apply (rule_tac x="[]" in exI)
        apply (drule append_butlast_last_id)
        apply simp
        done
      from subo wf have "C \<notin> set Cs'" by (rule unique1)
      with Cset show ?thesis by simp
    next
      case (Cons X Xs)
      with D'Ds' have tlnotempty:"tl Ds \<noteq> []" by simp
      with Cons last D'Ds' have "last (tl Ds) = C" by simp
      with tlnotempty have "C \<in> set (tl Ds)"
        apply (auto simp add:in_set_conv_decomp)
        apply (rule_tac x="butlast (tl Ds)" in exI)
        apply (rule_tac x="[]" in exI)
        apply (drule append_butlast_last_id)
        apply simp
        done
      hence Cset:"C \<in> set (Cs'@(tl Ds))" by simp
      from suboapp eq wf have "C \<notin> set (Cs'@(tl Ds))"
        by (subgoal_tac "Subobjs P C (C#(Cs'@(tl Ds)))",
          rule_tac Cs="[]" in unique1,simp_all)
      with Cset show ?thesis by simp
    qed
  next
    case False
    with notemptyDs have eq:"(C#Cs')@\<^sub>pDs = Ds" by (simp add:appendPath_def)
    with subo' last have lastleq:"P \<turnstile> last Cs' \<preceq>\<^sup>* C" 
      by (fastforce dest:Subobjs_subclass)
    from notempty obtain X Xs where X:"X = last Cs'" and "Xs = butlast Cs'"
      by auto
    with notempty have XXs:"Cs' = Xs@[X]" by simp
    hence CleqX:"(C,X) \<in> (subcls1 P)\<^sup>+"
    proof (cases Xs)
      case Nil
      with suboC XXs have "Subobjs P C [C,X]" by simp
      thus ?thesis
        apply -
        apply (rule r_into_trancl)
        apply (rule subclsR_subcls1)
        apply (rule_tac Cs="[]" in Subobjs_subclsR)
        apply simp
        done
    next
      case (Cons Y Ys)
      with suboC XXs have subo'':"Subobjs P C ([C,Y]@Ys@[X])" by simp
      hence plus:"(C,Y) \<in> (subcls1 P)\<^sup>+"
        apply -
        apply (rule r_into_trancl)
        apply (rule subclsR_subcls1)
        apply (rule_tac Cs="[]" in Subobjs_subclsR)
        apply simp
        done
      from subo'' have "P \<turnstile> Y \<preceq>\<^sup>* X"
        apply -
        apply (subgoal_tac "Subobjs P C ([C]@Y#(Ys@[X]))")
         apply (drule Subobjs_Subobjs)
         apply (drule_tac C="Y" in Subobjs_subclass) apply simp_all
        done
      with plus show ?thesis by (fastforce elim:trancl_rtrancl_trancl)
    qed
    from lastleq X have leq:"P \<turnstile> X \<preceq>\<^sup>* C" by simp
    with CleqX have "(C,C) \<in> (subcls1 P)\<^sup>+"
      by (rule trancl_rtrancl_trancl)
    with wf show ?thesis by (fastforce dest:subcls_irrefl)
  qed
qed



lemma leq_implies_path:
  assumes leq:"P \<turnstile> C \<preceq>\<^sup>* D" and "class": "is_class P C"
  and wf:"wf_prog wf_md P"
shows "\<exists>Cs. P \<turnstile> Path C to D via Cs"

using leq "class"
proof(induct rule:rtrancl.induct)
  fix C assume "is_class P C"
  thus "\<exists>Cs. P \<turnstile> Path C to C via Cs"
    by (rule_tac x="[C]" in exI,fastforce intro:Subobjs_Base simp:path_via_def)
next
  fix C C' D assume CleqC':"P \<turnstile> C \<preceq>\<^sup>* C'" and C'leqD:"P \<turnstile> C' \<prec>\<^sup>1 D"
    and classC:"is_class P C" and IH:"is_class P C \<Longrightarrow> \<exists>Cs. P \<turnstile> Path C to C' via Cs"
  from IH[OF classC] obtain Cs where subo:"Subobjs P C Cs" and last:"last Cs = C'"
    by (auto simp:path_via_def)
  with C'leqD show "\<exists>Cs. P \<turnstile> Path C to D via Cs"
  proof (auto dest!:subcls1_subclsR_or_subclsS)
    assume "P \<turnstile> last Cs \<prec>\<^sub>R D"
    with subo have "Subobjs P C (Cs@[D])" using wf
      by (rule converse_Subobjs_Rep)
    thus ?thesis by (fastforce simp:path_via_def)
  next
    assume subS:"P \<turnstile> last Cs \<prec>\<^sub>S D"
    from CleqC' last have Cleqlast:"P \<turnstile> C \<preceq>\<^sup>* last Cs" by simp
    from subS have classLast:"is_class P (last Cs)"
      by (auto intro:subcls1_class subclsS_subcls1)
    then obtain Bs fs ms where "class P (last Cs) = Some(Bs,fs,ms)"
      by (fastforce simp:is_class_def)
    hence classD:"is_class P D" using subS wf
      by (auto intro:wf_cdecl_supD dest:class_wf dest!:subclsSD 
               elim:ShBaseclass_isBaseclass)
    with Cleqlast subS have "Subobjs P C [D]"
      by (fastforce intro:Subobjs_Sh SubobjsR_Base)
    thus ?thesis by (fastforce simp:path_via_def)
  qed
qed


lemma least_method_implies_path_unique:
assumes least:"P \<turnstile> C has least M = (Ts,T,m) via Cs" and wf:"wf_prog wf_md P"
shows "P \<turnstile> Path C to (last Cs) unique"

proof (auto simp add:path_unique_def)
  (* Existence *)
  from least have "Subobjs P C Cs"
    by (simp add:LeastMethodDef_def MethodDefs_def)
  thus "\<exists>Cs'. Subobjs P C Cs' \<and> last Cs' = last Cs"
    by fastforce
next
  (* Uniqueness *)
  fix Cs' Cs''
  assume suboCs':"Subobjs P C Cs'" and suboCs'':"Subobjs P C Cs''"
    and lastCs':"last Cs' = last Cs" and lastCs'':"last Cs'' = last Cs"
  from suboCs' have notemptyCs':"Cs' \<noteq> []" by (rule Subobjs_nonempty)
  from suboCs'' have notemptyCs'':"Cs'' \<noteq> []" by (rule Subobjs_nonempty)
  from least have suboCs:"Subobjs P C Cs"
    and all:"\<forall>Ds. Subobjs P C Ds \<and> 
     (\<exists>Ts T m Bs ms. (\<exists>fs. class P (last Ds) = Some (Bs, fs, ms)) \<and> 
                 map_of ms M = Some(Ts,T,m)) \<longrightarrow> P,C \<turnstile> Cs \<sqsubseteq> Ds"
    by (auto simp:LeastMethodDef_def MethodDefs_def)
  from least obtain Bs fs ms T Ts m where 
    "class": "class P (last Cs) = Some(Bs, fs, ms)" and map:"map_of ms M = Some(Ts,T,m)"
    by (auto simp:LeastMethodDef_def MethodDefs_def intro:that)
  from suboCs' lastCs' "class" map all have pathCs':"P,C \<turnstile> Cs \<sqsubseteq> Cs'"
    by simp
  with wf lastCs' have eq:"Cs = Cs'" by(fastforce intro:leq_path_last)
  from suboCs'' lastCs'' "class" map all have pathCs'':"P,C \<turnstile> Cs \<sqsubseteq> Cs''"
    by simp
  with wf lastCs'' have "Cs = Cs''" by(fastforce intro:leq_path_last)
  with eq show "Cs' = Cs''" by simp
qed



lemma least_field_implies_path_unique:
assumes least:"P \<turnstile> C has least F:T via Cs" and wf:"wf_prog wf_md P"
shows "P \<turnstile> Path C to (hd Cs) unique"

proof (auto simp add:path_unique_def)
  (* Existence *)
  from least have "Subobjs P C Cs"
    by (simp add:LeastFieldDecl_def FieldDecls_def)
  hence "Subobjs P C ([hd Cs]@tl Cs)"
    by - (frule Subobjs_nonempty,simp)
  with wf have "Subobjs P C [hd Cs]"
    by (fastforce intro:appendSubobj)
  thus "\<exists>Cs'. Subobjs P C Cs' \<and> last Cs' = hd Cs"
    by fastforce
next
  (* Uniqueness *)
  fix Cs' Cs''
  assume suboCs':"Subobjs P C Cs'" and suboCs'':"Subobjs P C Cs''"
    and lastCs':"last Cs' = hd Cs" and lastCs'':"last Cs'' = hd Cs"
  from suboCs' have notemptyCs':"Cs' \<noteq> []" by (rule Subobjs_nonempty)
  from suboCs'' have notemptyCs'':"Cs'' \<noteq> []" by (rule Subobjs_nonempty)
  from least have suboCs:"Subobjs P C Cs"
    and all:"\<forall>Ds. Subobjs P C Ds \<and> 
     (\<exists>T Bs fs. (\<exists>ms. class P (last Ds) = Some (Bs, fs, ms)) \<and> 
                 map_of fs F = Some T) \<longrightarrow> P,C \<turnstile> Cs \<sqsubseteq> Ds"
    by (auto simp:LeastFieldDecl_def FieldDecls_def)
  from least obtain Bs fs ms T where 
    "class": "class P (last Cs) = Some(Bs, fs, ms)" and map:"map_of fs F = Some T"
    by (auto simp:LeastFieldDecl_def FieldDecls_def)
  from suboCs have notemptyCs:"Cs \<noteq> []" by (rule Subobjs_nonempty)
  from suboCs notemptyCs have suboHd:"Subobjs P (hd Cs) (hd Cs#tl Cs)"
    by -(rule_tac C="C" and Cs="[]" in Subobjs_Subobjs,simp)
  with suboCs' notemptyCs lastCs' wf have suboCs'App:"Subobjs P C (Cs'@\<^sub>pCs)"
    by -(rule Subobjs_appendPath,simp_all)
  from suboHd suboCs'' notemptyCs lastCs'' wf 
  have suboCs''App:"Subobjs P C (Cs''@\<^sub>pCs)"
    by -(rule Subobjs_appendPath,simp_all)
  from suboCs'App all "class" map notemptyCs have pathCs':"P,C \<turnstile> Cs \<sqsubseteq> Cs'@\<^sub>pCs"
    by -(erule_tac x="Cs'@\<^sub>pCs" in allE,drule_tac Cs'="Cs'" in appendPath_last,simp)
  from suboCs''App all "class" map notemptyCs have pathCs'':"P,C \<turnstile> Cs \<sqsubseteq> Cs''@\<^sub>pCs"
    by -(erule_tac x="Cs''@\<^sub>pCs" in allE,drule_tac Cs'="Cs''" in appendPath_last,simp)
  from pathCs' lastCs' notemptyCs notemptyCs' wf have Cs':"Cs' = [hd Cs]"
    by (rule path_hd_appendPath)
  from pathCs'' lastCs'' notemptyCs notemptyCs'' wf have "Cs'' = [hd Cs]"
    by (rule path_hd_appendPath)
  with Cs' show "Cs' = Cs''" by simp
qed



lemma least_field_implies_path_via_hd: 
"\<lbrakk>P \<turnstile> C has least F:T via Cs; wf_prog wf_md P\<rbrakk> 
\<Longrightarrow> P \<turnstile> Path C to (hd Cs) via [hd Cs]"

apply (simp add:LeastFieldDecl_def FieldDecls_def)
apply clarsimp
apply (simp add:path_via_def)
apply (frule Subobjs_nonempty)
apply (rule_tac Cs'="tl Cs" in appendSubobj)
apply auto
done


lemma path_C_to_C_unique:
"\<lbrakk>wf_prog wf_md P; is_class P C\<rbrakk> \<Longrightarrow> P \<turnstile> Path C to C unique"

apply (unfold path_unique_def)
apply (rule_tac a="[C]" in ex1I)
apply (auto intro:Subobjs_Base mdc_eq_last)
done


lemma leqR_SubobjsR:"\<lbrakk>(C,D) \<in> (subclsR P)\<^sup>*; is_class P C; wf_prog wf_md P\<rbrakk> 
\<Longrightarrow> \<exists>Cs. Subobjs\<^sub>R P C (Cs@[D])"

apply (induct rule:rtrancl_induct)
 apply (drule SubobjsR_Base)
 apply (rule_tac x="[]" in exI)
 apply simp
apply (auto dest:converse_SubobjsR_Rep)
done



lemma assumes path_unique:"P \<turnstile> Path C to D unique" and leq:"P \<turnstile> C \<preceq>\<^sup>* C'"
  and leqR:"(C',D) \<in> (subclsR P)\<^sup>*" and wf:"wf_prog wf_md P"
  shows "P \<turnstile> Path C to C' unique"

proof -
  from path_unique have "is_class P C"
    by (auto intro:Subobjs_isClass simp:path_unique_def)
  with leq wf obtain Cs where path_via:"P \<turnstile> Path C to C' via Cs"
    by (auto dest:leq_implies_path)
  with wf have classC':"is_class P C'"
    by (fastforce intro:Subobj_last_isClass simp:path_via_def)
  with leqR wf obtain Cs' where subo:"Subobjs\<^sub>R P C' Cs'" and last:"last Cs' = D"
    by (auto dest:leqR_SubobjsR)
  hence hd:"hd Cs' = C'"
    by (fastforce dest:hd_SubobjsR)
  with path_via subo wf have suboApp:"Subobjs P C (Cs@tl Cs')"
    by (auto dest!:Subobjs_Rep dest:Subobjs_appendPath 
                simp:path_via_def appendPath_def)
  hence last':"last (Cs@tl Cs') = D"
    proof (cases "tl Cs' = []")
      case True
      with subo hd last have "C' = D"
        by (subgoal_tac "Cs' = [C']",auto dest!:SubobjsR_nonempty hd_Cons_tl)
      with path_via have "last Cs = D"
        by (auto simp:path_via_def)
      with True show ?thesis by simp
    next
      case False
      from subo have Cs':"Cs' = hd Cs'#tl Cs'"
        by (auto dest:SubobjsR_nonempty)
      from False have "last(hd Cs'#tl Cs') = last (tl Cs')"
        by (rule last_ConsR)
      with False Cs' last show ?thesis by simp
    qed
  with path_unique suboApp 
  have all:"\<forall>Ds. Subobjs P C Ds \<and> last Ds = D \<longrightarrow> Ds = Cs@tl Cs'"
    by (auto simp add:path_unique_def)
  { fix Cs'' assume path_via2:"P \<turnstile> Path C to C' via Cs''" and noteq:"Cs'' \<noteq> Cs"
    with suboApp have "last (Cs''@tl Cs') = D"
    proof (cases "tl Cs' = []")
      case True
      with subo hd last have "C' = D"
        by (subgoal_tac "Cs' = [C']",auto dest!:SubobjsR_nonempty hd_Cons_tl)
      with path_via2 have "last Cs'' = D"
        by (auto simp:path_via_def)
      with True show ?thesis by simp
    next
      case False
      from subo have Cs':"Cs' = hd Cs'#tl Cs'"
        by (auto dest:SubobjsR_nonempty)
      from False have "last(hd Cs'#tl Cs') = last (tl Cs')"
        by (rule last_ConsR)
      with False Cs' last show ?thesis by simp
    qed
    with path_via2 noteq have False using all subo hd wf
      apply (auto simp:path_via_def)
      apply (drule Subobjs_Rep)
      apply (drule Subobjs_appendPath)
      apply (auto simp:appendPath_def)
      done }
  with path_via show ?thesis
    by (auto simp:path_via_def path_unique_def)
qed



subsection\<open>Well-formedness and member lookup\<close>

lemma has_path_has:
"\<lbrakk>P \<turnstile> Path D to C via Ds; P \<turnstile> C has M = (Ts,T,m) via Cs; wf_prog wf_md P\<rbrakk> 
  \<Longrightarrow> P \<turnstile> D has M = (Ts,T,m) via Ds@\<^sub>pCs"
by (clarsimp simp:HasMethodDef_def MethodDefs_def,frule Subobjs_nonempty,
         drule_tac Cs'="Ds" in appendPath_last,
         fastforce intro:Subobjs_appendPath simp:path_via_def)


lemma has_least_wf_mdecl:
  "\<lbrakk> wf_prog wf_md P; P \<turnstile> C has least M = m via Cs \<rbrakk> 
\<Longrightarrow> wf_mdecl wf_md P (last Cs) (M,m)"
by(fastforce dest:visible_methods_exist class_wf map_of_SomeD 
                 simp:LeastMethodDef_def wf_cdecl_def)



lemma has_overrider_wf_mdecl:
  "\<lbrakk> wf_prog wf_md P; P \<turnstile> (C,Cs) has overrider M = m via Cs' \<rbrakk> 
\<Longrightarrow> wf_mdecl wf_md P (last Cs') (M,m)"
by(fastforce dest:visible_methods_exist map_of_SomeD class_wf
                 simp:FinalOverriderMethodDef_def OverriderMethodDefs_def 
                      MinimalMethodDefs_def wf_cdecl_def)


lemma select_method_wf_mdecl:
  "\<lbrakk> wf_prog wf_md P; P \<turnstile> (C,Cs) selects M = m via Cs' \<rbrakk> 
\<Longrightarrow> wf_mdecl wf_md P (last Cs') (M,m)"
by(fastforce elim:SelectMethodDef.induct 
                 intro:has_least_wf_mdecl has_overrider_wf_mdecl)



lemma wf_sees_method_fun:
"\<lbrakk>P \<turnstile> C has least M = mthd via Cs; P \<turnstile> C has least M = mthd' via Cs'; 
  wf_prog wf_md P\<rbrakk>
  \<Longrightarrow> mthd = mthd' \<and> Cs = Cs'"

apply (auto simp:LeastMethodDef_def)
apply (erule_tac x="(Cs', mthd')" in ballE)
apply (erule_tac x="(Cs, mthd)" in ballE)
apply auto
apply (drule leq_path_asym2) apply simp_all
apply (rule sees_methods_fun) apply simp_all
apply (erule_tac x="(Cs', mthd')" in ballE)
apply (erule_tac x="(Cs, mthd)" in ballE)
apply (auto intro:leq_path_asym2)
done


lemma wf_select_method_fun: 
  assumes wf:"wf_prog wf_md P"
  shows "\<lbrakk>P \<turnstile> (C,Cs) selects M = mthd via Cs'; P \<turnstile> (C,Cs) selects M = mthd' via Cs''\<rbrakk>
  \<Longrightarrow> mthd = mthd' \<and> Cs' = Cs''"
proof(induct rule:SelectMethodDef.induct)
  case (dyn_unique C M mthd Cs' Cs)
  have "P \<turnstile> (C, Cs) selects M = mthd' via Cs''"
    and "P \<turnstile> C has least M = mthd via Cs'" by fact+
  thus ?case
  proof(induct rule:SelectMethodDef.induct)
    case (dyn_unique D M' mthd' Ds' Ds)
    have "P \<turnstile> D has least M' = mthd' via Ds'" 
      and "P \<turnstile> D has least M' = mthd via Cs'" by fact+
    with wf show ?case
      by -(rule wf_sees_method_fun,simp_all)
  next
    case (dyn_ambiguous D M' Ds mthd' Ds')
    have "\<forall>mthd Cs'. \<not> P \<turnstile> D has least M' = mthd via Cs'"
      and "P \<turnstile> D has least M' = mthd via Cs'" by fact+
    thus ?case by blast
  qed
next
  case (dyn_ambiguous C M Cs mthd Cs')
  have "P \<turnstile> (C, Cs) selects M = mthd' via Cs''"
    and "P \<turnstile> (C, Cs) has overrider M = mthd via Cs'"
    and "\<forall>mthd Cs'. \<not> P \<turnstile> C has least M = mthd via Cs'" by fact+
  thus ?case
  proof(induct rule:SelectMethodDef.induct)
    case (dyn_unique D M' mthd' Ds' Ds)
    have "P \<turnstile> D has least M' = mthd' via Ds'"
      and "\<forall>mthd Cs'. \<not> P \<turnstile> D has least M' = mthd via Cs'" by fact+
    thus ?case by blast
  next
    case (dyn_ambiguous D M' Ds mthd' Ds')
    have "P \<turnstile> (D, Ds) has overrider M' = mthd' via Ds'"
      and "P \<turnstile> (D, Ds) has overrider M' = mthd via Cs'" by fact+
    thus ?case by(fastforce dest:overrider_method_fun)
  qed
qed




lemma least_field_is_type:
assumes field:"P \<turnstile> C has least F:T via Cs" and wf:"wf_prog wf_md P"
shows "is_type P T"

proof -
  from field have "(Cs,T) \<in> FieldDecls P C F"
    by (simp add:LeastFieldDecl_def)
  from this obtain Bs fs ms 
    where "map_of fs F = Some T" 
    and "class": "class P (last Cs) = Some (Bs,fs,ms)"
    by (auto simp add:FieldDecls_def)
  hence "(F,T) \<in> set fs" by (simp add:map_of_SomeD)
  with "class" wf show ?thesis
    by(fastforce dest!: class_wf simp: wf_cdecl_def wf_fdecl_def)
qed 



lemma least_method_is_type:
assumes "method":"P \<turnstile> C has least M = (Ts,T,m) via Cs" and wf:"wf_prog wf_md P"
shows "is_type P T"

proof -
  from "method" have "(Cs,Ts,T,m) \<in> MethodDefs P C M"
    by (simp add:LeastMethodDef_def)
  from this obtain Bs fs ms 
    where "map_of ms M = Some(Ts,T,m)" 
    and "class": "class P (last Cs) = Some (Bs,fs,ms)"
    by (auto simp add:MethodDefs_def)
  hence "(M,Ts,T,m) \<in> set ms" by (simp add:map_of_SomeD)
  with "class" wf show ?thesis
    by(fastforce dest!: class_wf simp: wf_cdecl_def wf_mdecl_def)
qed 



lemma least_overrider_is_type:
assumes "method":"P \<turnstile> (C,Cs) has overrider M = (Ts,T,m) via Cs'" 
  and wf:"wf_prog wf_md P"
shows "is_type P T"

proof -
  from "method" have "(Cs',Ts,T,m) \<in> MethodDefs P C M"
    by(clarsimp simp:FinalOverriderMethodDef_def OverriderMethodDefs_def 
                     MinimalMethodDefs_def)
  from this obtain Bs fs ms 
    where "map_of ms M = Some(Ts,T,m)" 
    and "class": "class P (last Cs') = Some (Bs,fs,ms)"
    by (auto simp add:MethodDefs_def)
  hence "(M,Ts,T,m) \<in> set ms" by (simp add:map_of_SomeD)
  with "class" wf show ?thesis
    by(fastforce dest!: class_wf simp: wf_cdecl_def wf_mdecl_def)
qed 



lemma select_method_is_type:
"\<lbrakk> P \<turnstile> (C,Cs) selects M = (Ts,T,m) via Cs'; wf_prog wf_md P\<rbrakk> \<Longrightarrow> is_type P T"
by(auto elim:SelectMethodDef.cases
             intro:least_method_is_type least_overrider_is_type)


lemma base_subtype:
"\<lbrakk>wf_cdecl wf_md P (C,Bs,fs,ms); C' \<in> baseClasses Bs; 
  P \<turnstile> C' has M = (Ts',T',m') via Cs@\<^sub>p[D]; (M,Ts,T,m)\<in>set ms\<rbrakk>
  \<Longrightarrow> Ts' = Ts \<and> P \<turnstile> T \<le> T'"

apply (simp add:wf_cdecl_def)
apply clarsimp
apply (rotate_tac -1)
apply (erule_tac x="C'" in ballE)
 apply clarsimp
 apply (rotate_tac -1)
 apply (erule_tac x="(M, Ts, T, m)" in ballE)
  apply clarsimp
  apply (erule_tac x="Ts'" in allE)
  apply (erule_tac x="T'" in allE)
  apply (auto simp:HasMethodDef_def)
 apply (erule_tac x="fst m'" in allE)
 apply (erule_tac x="snd m'" in allE)
 apply (erule_tac x="Cs@\<^sub>p[D]" in allE)
 apply simp
apply (erule_tac x="fst m'" in allE)
apply (erule_tac x="snd m'" in allE)
apply (erule_tac x="Cs@\<^sub>p[D]" in allE)
apply simp
done



lemma subclsPlus_subtype:
  assumes classD:"class P D = Some(Bs',fs',ms')" 
  and mapMs':"map_of ms' M = Some(Ts',T',m')"
  and leq:"(C,D) \<in> (subcls1 P)\<^sup>+" and wf:"wf_prog wf_md P"
shows "\<forall>Bs fs ms Ts T m. class P C = Some(Bs,fs,ms) \<and> map_of ms M = Some(Ts,T,m) 
    \<longrightarrow> Ts' = Ts \<and> P \<turnstile> T \<le> T'"

using leq classD mapMs'
proof (erule_tac a="C" and b="D" in converse_trancl_induct)
  fix C
  assume CleqD:"P \<turnstile> C \<prec>\<^sup>1 D" and classD1:"class P D = Some(Bs',fs',ms')"
  { fix Bs fs ms Ts T m
    assume classC:"class P C = Some(Bs,fs,ms)" and mapMs:"map_of ms M = Some(Ts,T,m)"
    from classD1 mapMs' have hasViaD:"P \<turnstile> D has M = (Ts',T',m') via [D]"
      by (fastforce intro:Subobjs_Base simp:HasMethodDef_def MethodDefs_def is_class_def)
    from CleqD classC have base:"D \<in> baseClasses Bs"
      by (fastforce dest:subcls1D)
    from classC wf have cdecl:"wf_cdecl wf_md P (C,Bs,fs,ms)"
      by (rule class_wf)
    from classC mapMs have "(M,Ts,T,m)\<in>set ms"
      by -(drule map_of_SomeD)
    with cdecl base hasViaD have "Ts' = Ts \<and> P \<turnstile> T \<le> T'"
      by -(rule_tac Cs="[D]" in base_subtype,auto simp:appendPath_def) }
  thus "\<forall>Bs fs ms Ts T m. class P C = Some(Bs, fs, ms) \<and> map_of ms M = Some(Ts,T,m) 
             \<longrightarrow> Ts' = Ts \<and> P \<turnstile> T \<le> T'" by blast
next
  fix C C'
  assume  classD1:"class P D = Some(Bs',fs',ms')" and CleqC':"P \<turnstile> C \<prec>\<^sup>1 C'"
    and subcls:"(C',D) \<in> (subcls1 P)\<^sup>+"
    and IH:"\<forall>Bs fs ms Ts T m. class P C' = Some(Bs,fs,ms) \<and> 
                          map_of ms M = Some(Ts,T,m) \<longrightarrow> 
                  Ts' = Ts \<and> P \<turnstile> T \<le> T'"
  { fix Bs fs ms Ts T m
    assume classC:"class P C = Some(Bs,fs,ms)" and mapMs:"map_of ms M = Some(Ts,T,m)"
    from classD1 mapMs' have hasViaD:"P \<turnstile> D has M = (Ts',T',m') via [D]"
      by (fastforce intro:Subobjs_Base simp:HasMethodDef_def MethodDefs_def is_class_def)
    from subcls have C'leqD:"P \<turnstile> C' \<preceq>\<^sup>* D" by simp
    from classC wf CleqC' have "is_class P C'"
      by (fastforce intro:wf_cdecl_supD class_wf dest:subcls1D)
    with C'leqD wf obtain Cs where "P \<turnstile> Path C' to D via Cs"
      by (auto dest!:leq_implies_path simp:is_class_def)
    hence hasVia:"P \<turnstile> C' has M = (Ts',T',m') via Cs@\<^sub>p[D]" using hasViaD wf
      by (rule has_path_has)
    from CleqC' classC have base:"C' \<in> baseClasses Bs"
      by (fastforce dest:subcls1D)
    from classC wf have cdecl:"wf_cdecl wf_md P (C,Bs,fs,ms)"
      by (rule class_wf)
    from classC mapMs have "(M,Ts,T,m)\<in>set ms"
      by -(drule map_of_SomeD)
    with cdecl base hasVia have "Ts' = Ts \<and> P \<turnstile> T \<le> T'"
      by(rule base_subtype) }
  thus "\<forall>Bs fs ms Ts T m. class P C = Some(Bs, fs, ms) \<and> map_of ms M = Some(Ts,T,m) 
             \<longrightarrow> Ts' = Ts \<and> P \<turnstile> T \<le> T'" by blast
qed



lemma leq_method_subtypes:
  assumes leq:"P \<turnstile> D \<preceq>\<^sup>* C" and least:"P \<turnstile> D has least M = (Ts',T',m') via Ds"
  and wf:"wf_prog wf_md P"
  shows "\<forall>Ts T m Cs. P \<turnstile> C has M = (Ts,T,m) via Cs \<longrightarrow> 
                       Ts = Ts' \<and> P \<turnstile> T' \<le> T"
using assms
proof (induct rule:rtrancl.induct)
  fix C
  assume Cleast:"P \<turnstile> C has least M = (Ts',T',m') via Ds"
  { fix Ts T m Cs
    assume Chas:"P \<turnstile> C has M = (Ts,T,m) via Cs"
    with Cleast have path:"P,C \<turnstile> Ds \<sqsubseteq> Cs"
      by (fastforce simp:LeastMethodDef_def HasMethodDef_def)
    { assume "Ds = Cs"
      with Cleast Chas have "Ts = Ts' \<and> T' = T"
        by (auto simp:LeastMethodDef_def HasMethodDef_def MethodDefs_def)
      hence "Ts = Ts' \<and> P \<turnstile> T' \<le> T" by auto }
    moreover
    { assume "(Ds,Cs) \<in> (leq_path1 P C)\<^sup>+"
      hence subcls:"(last Ds,last Cs) \<in> (subcls1 P)\<^sup>+" using wf
        by -(rule last_leq_paths)
      from Chas obtain Bs fs ms where "class P (last Cs) = Some(Bs,fs,ms)" 
        and "map_of ms M = Some(Ts,T,m)"
        by (auto simp:HasMethodDef_def MethodDefs_def)
      hence ex:"\<forall>Bs' fs' ms' Ts' T' m'. class P (last Ds) = Some(Bs',fs',ms') \<and> 
        map_of ms' M = Some(Ts',T',m') \<longrightarrow> Ts = Ts' \<and> P \<turnstile> T' \<le> T"
        using subcls wf
        by -(rule subclsPlus_subtype,auto)
      from Cleast obtain Bs' fs' ms' where "class P (last Ds) = Some(Bs',fs',ms')" 
        and "map_of ms' M = Some(Ts',T',m')"
        by (auto simp:LeastMethodDef_def MethodDefs_def)
      with ex have "Ts = Ts'" and "P \<turnstile> T' \<le> T" by auto }
      ultimately have "Ts = Ts'" and "P \<turnstile> T' \<le> T" using path
        by (auto dest!:rtranclD) }
  thus "\<forall>Ts T m Cs. P \<turnstile> C has M = (Ts, T, m) via Cs \<longrightarrow> 
                      Ts = Ts' \<and> P \<turnstile> T' \<le> T"
    by (simp add:HasMethodDef_def MethodDefs_def)
next
  fix D C' C
  assume DleqC':"P \<turnstile> D \<preceq>\<^sup>* C'" and C'leqC:"P \<turnstile> C' \<prec>\<^sup>1 C"
  and Dleast:"P \<turnstile> D has least M = (Ts',T',m') via Ds"
  and IH:"\<lbrakk>P \<turnstile> D has least M = (Ts',T',m') via Ds; wf_prog wf_md P\<rbrakk>
   \<Longrightarrow> \<forall>Ts T m Cs. P \<turnstile> C' has M = (Ts, T, m) via Cs \<longrightarrow> 
            Ts = Ts' \<and> P \<turnstile> T' \<le> T"
  { fix Ts T m Cs
    assume Chas:"P \<turnstile> C has M = (Ts,T,m) via Cs"
    from Dleast have classD:"is_class P D"
      by (auto intro:Subobjs_isClass simp:LeastMethodDef_def MethodDefs_def)
    from DleqC' C'leqC have "P \<turnstile> D \<preceq>\<^sup>* C" by simp
    then obtain Cs' where "P \<turnstile> Path D to C via Cs'" using classD wf
      by (auto dest:leq_implies_path)
    hence Dhas:"P \<turnstile> D has M = (Ts,T,m) via Cs'@\<^sub>pCs" using Chas wf
      by (fastforce intro:has_path_has)
    with Dleast have path:"P,D \<turnstile> Ds \<sqsubseteq> Cs'@\<^sub>pCs"
      by (auto simp:LeastMethodDef_def HasMethodDef_def)
    { assume "Ds = Cs'@\<^sub>pCs"
      with Dleast Dhas have "Ts = Ts' \<and> T' = T"
        by (auto simp:LeastMethodDef_def HasMethodDef_def MethodDefs_def)
      hence "Ts = Ts' \<and> T' = T" by auto }
    moreover
    { assume "(Ds,Cs'@\<^sub>pCs) \<in> (leq_path1 P D)\<^sup>+"
      hence subcls:"(last Ds,last (Cs'@\<^sub>pCs)) \<in> (subcls1 P)\<^sup>+" using wf
        by -(rule last_leq_paths)
      from Dhas obtain Bs fs ms where "class P (last (Cs'@\<^sub>pCs)) = Some(Bs,fs,ms)" 
        and "map_of ms M = Some(Ts,T,m)"
        by (auto simp:HasMethodDef_def MethodDefs_def)
      hence ex:"\<forall>Bs' fs' ms' Ts' T' m'. class P (last Ds) = Some(Bs',fs',ms') \<and> 
                 map_of ms' M = Some(Ts',T',m') \<longrightarrow> 
                     Ts = Ts' \<and> P \<turnstile> T' \<le> T"
        using subcls wf
        by -(rule subclsPlus_subtype,auto)
      from Dleast obtain Bs' fs' ms' where "class P (last Ds) = Some(Bs',fs',ms')" 
        and "map_of ms' M = Some(Ts',T',m')"
        by (auto simp:LeastMethodDef_def MethodDefs_def)
      with ex have "Ts = Ts'" and "P \<turnstile> T' \<le> T" by auto }
    ultimately have "Ts = Ts'" and "P \<turnstile> T' \<le> T" using path
      by (auto dest!:rtranclD) }
  thus "\<forall>Ts T m Cs. P \<turnstile> C has M = (Ts, T, m) via Cs \<longrightarrow> 
            Ts = Ts' \<and> P \<turnstile> T' \<le> T"
    by simp
qed



lemma leq_methods_subtypes:
  assumes leq:"P \<turnstile> D \<preceq>\<^sup>* C" and least:"(Ds,(Ts',T',m')) \<in> MinimalMethodDefs P D M"
  and wf:"wf_prog wf_md P"
  shows "\<forall>Ts T m Cs Cs'. P \<turnstile> Path D to C via Cs' \<and> P,D \<turnstile> Ds \<sqsubseteq> Cs'@\<^sub>pCs \<and> Cs \<noteq> [] \<and> 
                         P \<turnstile> C has M = (Ts,T,m) via Cs 
                                \<longrightarrow>  Ts = Ts' \<and> P \<turnstile> T' \<le> T"
using assms
proof (induct rule:rtrancl.induct)
  fix C
  assume Cleast:"(Ds,(Ts',T',m')) \<in> MinimalMethodDefs P C M"
  { fix Ts T m Cs Cs'
    assume path':"P \<turnstile> Path C to C via Cs'"
      and leq_path:"P,C \<turnstile> Ds \<sqsubseteq> Cs' @\<^sub>p Cs" and notempty:"Cs \<noteq> []"
      and Chas:"P \<turnstile> C has M = (Ts,T,m) via Cs"
    from path' wf have Cs':"Cs' = [C]" by(rule path_via_C)
    from leq_path Cs' notempty have leq':"P,C \<turnstile> Ds \<sqsubseteq> Cs"
      by(auto simp:appendPath_def split:if_split_asm)
    { assume "Ds = Cs"
      with Cleast Chas have "Ts = Ts' \<and> T' = T"
        by (auto simp:MinimalMethodDefs_def HasMethodDef_def MethodDefs_def)
      hence "Ts = Ts' \<and> P \<turnstile> T' \<le> T" by auto }
    moreover
    { assume "(Ds,Cs) \<in> (leq_path1 P C)\<^sup>+"
      hence subcls:"(last Ds,last Cs) \<in> (subcls1 P)\<^sup>+" using wf
        by -(rule last_leq_paths)
      from Chas obtain Bs fs ms where "class P (last Cs) = Some(Bs,fs,ms)" 
        and "map_of ms M = Some(Ts,T,m)"
        by (auto simp:HasMethodDef_def MethodDefs_def)
      hence ex:"\<forall>Bs' fs' ms' Ts' T' m'. class P (last Ds) = Some(Bs',fs',ms') \<and> 
        map_of ms' M = Some(Ts',T',m') \<longrightarrow> Ts = Ts' \<and> P \<turnstile> T' \<le> T"
        using subcls wf
        by -(rule subclsPlus_subtype,auto)
      from Cleast obtain Bs' fs' ms' where "class P (last Ds) = Some(Bs',fs',ms')" 
        and "map_of ms' M = Some(Ts',T',m')"
        by (auto simp:MinimalMethodDefs_def MethodDefs_def)
      with ex have "Ts = Ts'" and "P \<turnstile> T' \<le> T" by auto }
      ultimately have "Ts = Ts'" and "P \<turnstile> T' \<le> T" using leq'
        by (auto dest!:rtranclD) }
  thus "\<forall>Ts T m Cs Cs'. P \<turnstile> Path C to C via Cs' \<and> P,C \<turnstile> Ds \<sqsubseteq> Cs' @\<^sub>p Cs \<and> Cs \<noteq> [] \<and> 
                        P \<turnstile> C has M = (Ts, T, m) via Cs \<longrightarrow> 
                            Ts = Ts' \<and> P \<turnstile> T' \<le> T" by blast
next
  fix D C' C
  assume DleqC':"P \<turnstile> D \<preceq>\<^sup>* C'" and C'leqC:"P \<turnstile> C' \<prec>\<^sup>1 C"
    and Dleast:"(Ds, Ts', T', m') \<in> MinimalMethodDefs P D M"
    and IH:"\<lbrakk>(Ds,Ts',T',m') \<in> MinimalMethodDefs P D M; wf_prog wf_md P\<rbrakk>
   \<Longrightarrow> \<forall>Ts T m Cs Cs'. P \<turnstile> Path D to C' via Cs' \<and>
              P,D \<turnstile> Ds \<sqsubseteq> Cs' @\<^sub>p Cs \<and> Cs \<noteq> [] \<and> P \<turnstile> C' has M = (Ts, T, m) via Cs \<longrightarrow> 
                             Ts = Ts' \<and> P \<turnstile> T' \<le> T"
  { fix Ts T m Cs Cs'
    assume path:"P \<turnstile> Path D to C via Cs'"
      and leq_path:"P,D \<turnstile> Ds \<sqsubseteq> Cs' @\<^sub>p Cs"
      and notempty:"Cs \<noteq> []"
      and Chas:"P \<turnstile> C has M = (Ts,T,m) via Cs"
    from Dleast have classD:"is_class P D"
      by (auto intro:Subobjs_isClass simp:MinimalMethodDefs_def MethodDefs_def)
    from path have Dhas:"P \<turnstile> D has M = (Ts,T,m) via Cs'@\<^sub>pCs" using Chas wf
      by (fastforce intro:has_path_has)
    { assume "Ds = Cs'@\<^sub>pCs"
      with Dleast Dhas have "Ts = Ts' \<and> T' = T"
        by (auto simp:MinimalMethodDefs_def HasMethodDef_def MethodDefs_def)
      hence "Ts = Ts' \<and> T' = T" by auto }
    moreover
    { assume "(Ds,Cs'@\<^sub>pCs) \<in> (leq_path1 P D)\<^sup>+"
      hence subcls:"(last Ds,last (Cs'@\<^sub>pCs)) \<in> (subcls1 P)\<^sup>+" using wf
        by -(rule last_leq_paths)
      from Dhas obtain Bs fs ms where "class P (last (Cs'@\<^sub>pCs)) = Some(Bs,fs,ms)" 
        and "map_of ms M = Some(Ts,T,m)"
        by (auto simp:HasMethodDef_def MethodDefs_def)
      hence ex:"\<forall>Bs' fs' ms' Ts' T' m'. class P (last Ds) = Some(Bs',fs',ms') \<and> 
                 map_of ms' M = Some(Ts',T',m') \<longrightarrow> 
                     Ts = Ts' \<and> P \<turnstile> T' \<le> T"
        using subcls wf
        by -(rule subclsPlus_subtype,auto)
      from Dleast obtain Bs' fs' ms' where "class P (last Ds) = Some(Bs',fs',ms')" 
        and "map_of ms' M = Some(Ts',T',m')"
        by (auto simp:MinimalMethodDefs_def MethodDefs_def)
      with ex have "Ts = Ts'" and "P \<turnstile> T' \<le> T" by auto }
    ultimately have "Ts = Ts'" and "P \<turnstile> T' \<le> T" using leq_path
      by (auto dest!:rtranclD) }
  thus "\<forall>Ts T m Cs Cs'. P \<turnstile> Path D to C via Cs' \<and> P,D \<turnstile> Ds \<sqsubseteq> Cs' @\<^sub>p Cs \<and> Cs \<noteq> [] \<and> 
                    P \<turnstile> C has M = (Ts, T, m) via Cs \<longrightarrow> 
                           Ts = Ts' \<and> P \<turnstile> T' \<le> T"
    by blast
qed


lemma select_least_methods_subtypes: 
  assumes select_method:"P \<turnstile> (C,Cs@\<^sub>pDs) selects M = (Ts,T,pns,body) via Cs'"
  and least_method:"P \<turnstile> last Cs has least M = (Ts',T',pns',body') via Ds"
  and path:"P \<turnstile> Path C to (last Cs) via Cs"
  and wf:"wf_prog wf_md P"
  shows "Ts' = Ts \<and> P \<turnstile> T \<le> T'"
using select_method
proof -
  from path have sub:"P \<turnstile> C \<preceq>\<^sup>* last Cs"
    by(fastforce intro:Subobjs_subclass simp:path_via_def)
  from least_method have has:"P \<turnstile> last Cs has M = (Ts',T',pns',body') via Ds"
    by(rule has_least_method_has_method)
  from select_method show ?thesis
  proof cases
    case dyn_unique
    hence dyn:"P \<turnstile> C has least M = (Ts,T,pns,body) via Cs'" by simp
    with sub has wf show ?thesis
      by -(drule leq_method_subtypes,assumption,simp,blast)+
  next
    case dyn_ambiguous
    hence overrider:"P \<turnstile> (C,Cs@\<^sub>pDs) has overrider M = (Ts,T,pns,body) via Cs'" 
      by simp
    from least_method have notempty:"Ds \<noteq> []"
      by(auto intro!:Subobjs_nonempty simp:LeastMethodDef_def MethodDefs_def)
    have "last Cs = hd Ds \<Longrightarrow> last (Cs @ tl Ds) = last Ds"
    proof(cases "tl Ds = []")
      case True
      assume last:"last Cs = hd Ds"
      with True notempty have "Ds = [last Cs]" by (fastforce dest:hd_Cons_tl)
      hence "last Ds = last Cs" by simp
      with True show ?thesis by simp
    next
      case False
      assume last:"last Cs = hd Ds"
      from notempty False have "last (tl Ds) = last Ds"
        by -(drule hd_Cons_tl,drule_tac x="hd Ds" in last_ConsR,simp)
      with False show ?thesis by simp
    qed
    hence eq:"(Cs @\<^sub>p Ds) @\<^sub>p [last Ds] = (Cs @\<^sub>p Ds)"
      by(simp add:appendPath_def)
    from least_method wf
    have "P \<turnstile> last Ds has least M = (Ts',T',pns',body') via [last Ds]"
      by(auto dest:Subobj_last_isClass intro:Subobjs_Base subobjs_rel
        simp:LeastMethodDef_def MethodDefs_def)
    with notempty
    have "P \<turnstile> last (Cs@\<^sub>pDs) has least M = (Ts',T',pns',body') via [last Ds]"
      by -(drule_tac Cs'="Cs" in appendPath_last,simp)
    with overrider wf eq have "(Cs',Ts,T,pns,body) \<in> MinimalMethodDefs P C M"
      and "P,C \<turnstile> Cs' \<sqsubseteq> Cs @\<^sub>p Ds"
      by -(auto simp:FinalOverriderMethodDef_def OverriderMethodDefs_def,
        drule wf_sees_method_fun,auto)
    with sub wf path notempty has show ?thesis
      by -(drule leq_methods_subtypes,simp_all,blast)+
  qed
qed



lemma wf_syscls:
  "set SystemClasses \<subseteq> set P \<Longrightarrow> wf_syscls P"
by (simp add: image_def SystemClasses_def wf_syscls_def sys_xcpts_def
          NullPointerC_def ClassCastC_def OutOfMemoryC_def,force intro:conjI)


subsection\<open>Well formedness and widen\<close>

lemma Class_widen: "\<lbrakk>P \<turnstile> Class C \<le> T; wf_prog wf_md P; is_class P C\<rbrakk>  
  \<Longrightarrow>  \<exists>D. T = Class D \<and> P \<turnstile> Path C to D unique"

apply (ind_cases "P \<turnstile> Class C \<le> T")
apply (auto intro:path_C_to_C_unique)
done


lemma Class_widen_Class [iff]: "\<lbrakk>wf_prog wf_md P; is_class P C\<rbrakk> \<Longrightarrow> 
  (P \<turnstile> Class C \<le> Class D) = (P \<turnstile> Path C to D unique)"

apply (rule iffI)
apply (ind_cases " P \<turnstile> Class C \<le> Class D")
apply (auto elim: widen_subcls intro:path_C_to_C_unique)
done


lemma widen_Class: "\<lbrakk>wf_prog wf_md P; is_class P C\<rbrakk> \<Longrightarrow> 
  (P \<turnstile> T \<le> Class C) = 
    (T = NT \<or> (\<exists>D. T = Class D \<and> P \<turnstile> Path D to C unique))"

apply(induct T) apply (auto intro:widen_subcls)
apply (ind_cases "P \<turnstile> Class D \<le> Class C" for D) apply (auto intro:path_C_to_C_unique)
done



subsection\<open>Well formedness and well typing\<close>

lemma assumes wf:"wf_prog wf_md P" 
shows WT_determ: "P,E \<turnstile> e :: T \<Longrightarrow> (\<And>T'. P,E \<turnstile> e :: T' \<Longrightarrow> T = T')"
and WTs_determ: "P,E \<turnstile> es [::] Ts \<Longrightarrow> (\<And>Ts'. P,E \<turnstile> es [::] Ts' \<Longrightarrow> Ts = Ts')"

proof(induct rule:WT_WTs_inducts)
  case (WTDynCast E e D C)
  have "P,E \<turnstile> Cast C e :: T'" by fact
  thus ?case by (fastforce elim:WT.cases)
next
  case (WTStaticCast E e D C)
  have "P,E \<turnstile> \<lparr>C\<rparr>e :: T'" by fact
  thus ?case by (fastforce elim:WT.cases)
next
  case (WTBinOp E e\<^sub>1 T\<^sub>1 e\<^sub>2 T\<^sub>2 bop T)
  have bop:"case bop of Eq \<Rightarrow> T\<^sub>1 = T\<^sub>2 \<and> T = Boolean
    | Add \<Rightarrow> T\<^sub>1 = Integer \<and> T\<^sub>2 = Integer \<and> T = Integer"
    and wt:"P,E \<turnstile> e\<^sub>1 \<guillemotleft>bop\<guillemotright> e\<^sub>2 :: T'" by fact+
  from wt obtain T1' T2' where
    bop':"case bop of Eq \<Rightarrow> T1' = T2' \<and> T' = Boolean
    | Add \<Rightarrow> T1' = Integer \<and> T2' = Integer \<and> T' = Integer"
    by auto
  from bop show ?case
  proof (cases bop)
    assume Eq:"bop = Eq"
    with bop have "T = Boolean" by auto
    with Eq bop' show ?thesis by simp
  next
    assume Add:"bop = Add"
    with bop have "T = Integer"
      by auto
    with Add bop' show ?thesis by simp
  qed
next
  case (WTLAss E V T e T' T'')
  have "P,E \<turnstile> V:=e :: T''" 
    and "E V = Some T" by fact+
  thus ?case by auto
next
  case (WTFAcc E e C F T Cs)
  have IH:"\<And>T'. P,E \<turnstile> e :: T' \<Longrightarrow> Class C = T'"
    and least:"P \<turnstile> C has least F:T via Cs"
    and wt:"P,E \<turnstile> e\<bullet>F{Cs} :: T'" by fact+
  from wt obtain C' where wte':"P,E \<turnstile> e :: Class C'"
    and least':"P \<turnstile> C' has least F:T' via Cs" by auto
  from IH[OF wte'] have "C = C'" by simp
  with least least' show ?case
    by (fastforce simp:sees_field_fun)
next
  case (WTFAss E e\<^sub>1 C F T Cs e\<^sub>2 T' T'')
  have least:"P \<turnstile> C has least F:T via Cs"
    and wt:"P,E \<turnstile> e\<^sub>1\<bullet>F{Cs} := e\<^sub>2 :: T''" 
    and IH:"\<And>S. P,E \<turnstile> e\<^sub>1 :: S \<Longrightarrow> Class C = S" by fact+
  from wt obtain C' where wte':"P,E \<turnstile> e\<^sub>1 :: Class C'" 
    and least':"P \<turnstile> C' has least F:T'' via Cs" by auto
  from IH[OF wte'] have "C = C'" by simp
  with least least' show ?case
    by (fastforce simp:sees_field_fun)
next
  case (WTCall E e C M Ts T pns body Cs es Ts')
  have IH:"\<And>T'. P,E \<turnstile> e :: T' \<Longrightarrow> Class C = T'"
    and least:"P \<turnstile> C has least M = (Ts, T, pns, body) via Cs"
    and wt:"P,E \<turnstile> e\<bullet>M(es) :: T'" by fact+
  from wt obtain C' Ts' pns' body' Cs' where wte':"P,E \<turnstile> e :: Class C'"
    and least':"P \<turnstile> C' has least M = (Ts',T',pns',body') via Cs'" by auto
  from IH[OF wte'] have "C = C'" by simp
  with least least' wf show ?case by (auto dest:wf_sees_method_fun)
next
  case (WTStaticCall E e C' C M Ts T pns body Cs es Ts')
  have IH:"\<And>T'. P,E \<turnstile> e :: T' \<Longrightarrow> Class C' = T'" 
    and unique:"P \<turnstile> Path C' to C unique"
    and least:"P \<turnstile> C has least M = (Ts, T, pns, body) via Cs"
    and wt:"P,E \<turnstile> e\<bullet>(C::)M(es) :: T'" by fact+
  from wt obtain Ts' pns' body' Cs' 
    where "P \<turnstile> C has least M = (Ts',T',pns',body') via Cs'" by auto
  with least wf show ?case by (auto dest:wf_sees_method_fun)
next
  case WTBlock thus ?case by (clarsimp simp del:fun_upd_apply)
next
  case (WTSeq E e\<^sub>1 T\<^sub>1 e\<^sub>2 T\<^sub>2)
  have IH:"\<And>T'. P,E \<turnstile> e\<^sub>2 :: T' \<Longrightarrow> T\<^sub>2 = T'"
    and wt:"P,E \<turnstile> e\<^sub>1;; e\<^sub>2 :: T'" by fact+
  from wt have wt':"P,E \<turnstile> e\<^sub>2 :: T'" by auto
  from IH[OF wt'] show ?case .
next
  case (WTCond E e e\<^sub>1 T e\<^sub>2)
  have IH:"\<And>S. P,E \<turnstile> e\<^sub>1 :: S \<Longrightarrow> T = S"
    and wt:"P,E \<turnstile> if (e) e\<^sub>1 else e\<^sub>2 :: T'" by fact+
  from wt have "P,E \<turnstile> e\<^sub>1 :: T'" by auto
  from IH[OF this] show ?case .
next
  case (WTCons E e T es Ts)
  have IHe:"\<And>T'. P,E \<turnstile> e :: T' \<Longrightarrow> T = T'"
    and IHes:"\<And>Ts'. P,E \<turnstile> es [::] Ts' \<Longrightarrow> Ts = Ts'"
    and wt:"P,E \<turnstile> e # es [::] Ts'" by fact+
  from wt show ?case
  proof (cases Ts')
    case Nil with wt show ?thesis by simp
  next
    case (Cons T'' Ts'')
    with wt have wte':"P,E \<turnstile> e :: T''" and wtes':"P,E \<turnstile> es [::] Ts''"
      by auto
    from IHe[OF wte'] IHes[OF wtes'] Cons show ?thesis by simp
  qed
qed clarsimp+

end
