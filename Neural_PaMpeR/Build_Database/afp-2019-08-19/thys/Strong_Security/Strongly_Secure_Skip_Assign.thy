(*
Title: Strong-Security
Authors: Sylvia Grewe, Alexander Lux, Heiko Mantel, Jens Sauer
*)
theory Strongly_Secure_Skip_Assign
imports MWLf Parallel_Composition
begin

locale Strongly_Secure_Programs =
L? : MWLf_semantics "E" "BMap" 
+ SS?: Strong_Security "MWLfSteps_det" "DA"
for E :: "('exp, 'id, 'val) Evalfunction"
and BMap :: "'val \<Rightarrow> bool"
and DA :: "('id, 'd::order) DomainAssignment"
begin 

abbreviation USdBname ::"'d \<Rightarrow> ('exp, 'id) MWLfCom Bisimulation_type"
("\<approx>\<^bsub>_\<^esub>")
where "\<approx>\<^bsub>d\<^esub> \<equiv> USdB d" 

abbreviation relatedbyUSdB :: "('exp,'id) MWLfCom list \<Rightarrow> 'd
  \<Rightarrow> ('exp,'id) MWLfCom list \<Rightarrow> bool" (infixr "\<approx>\<^bsub>_\<^esub>" 65)
where "V \<approx>\<^bsub>d\<^esub> V' \<equiv> (V,V') \<in> USdB d"

\<comment> \<open>define when two expressions are indistinguishable with respect to a domain d\<close>
definition d_indistinguishable :: "'d::order \<Rightarrow> 'exp \<Rightarrow> 'exp \<Rightarrow> bool"
where
"d_indistinguishable d e1 e2 \<equiv> 
  \<forall>m m'. ((m =\<^bsub>d\<^esub> m') \<longrightarrow> ((E e1 m) = (E e2 m')))"

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

theorem Strongly_Secure_Skip:
"[skip] \<approx>\<^bsub>d\<^esub> [skip]"
proof -
  define R0 where "R0 = {(V::('exp,'id) MWLfCom list,V'::('exp,'id) MWLfCom list). 
    V = [skip] \<and> V' = [skip]}"

  have uptoR0: "d_Bisimulation_Up_To_USdB d R0"
    proof (simp add: d_Bisimulation_Up_To_USdB_def, auto)
      show "sym R0" by (simp add: R0_def sym_def)
    next
      fix V V'
      assume "(V,V') \<in> R0"
      thus "length V = length V'"
        by (simp add: R0_def)
    next
      fix V V' i m1 m1' W m2
      assume inR0: "(V,V') \<in> R0"
      assume irange: "i < length V"
      assume step: "\<langle>V!i,m1\<rangle> \<rightarrow> \<langle>W,m2\<rangle>"
      assume dequal: "m1 =\<^bsub>d\<^esub> m1'"
      
      from inR0 have Vassump:
        "V = [skip] \<and> V' = [skip]"
        by (simp add: R0_def)
      
      with step irange have step1:
        "W = [] \<and> m2 = m1"
        by (simp, metis MWLf_semantics.MWLfSteps_det_cases(1))
        
      from Vassump irange obtain m2' where step2:
        "\<langle>V'!i,m1'\<rangle> \<rightarrow> \<langle>[],m2'\<rangle> \<and> m2' = m1'"
         by (simp, metis MWLfSteps_det.skip)

      with step1 dequal trivialpair_in_USdB show "\<exists>W' m2'.
        \<langle>V'!i,m1'\<rangle> \<rightarrow> \<langle>W',m2'\<rangle> \<and> 
        ((W,W') \<in> R0 \<or> W \<approx>\<^bsub>d\<^esub> W') \<and> m2 =\<^bsub>d\<^esub> m2'"
        by auto
   qed
   
   hence "R0 \<subseteq> \<approx>\<^bsub>d\<^esub>"
     by (rule Up_To_Technique)

   thus ?thesis
     by (simp add: R0_def)

qed

theorem Strongly_Secure_Assign:
  assumes d_indistinguishable_exp: "e \<equiv>\<^bsub>DA x\<^esub> e'"
  shows "[x := e] \<approx>\<^bsub>d\<^esub> [x := e']"
proof -
  define R0 where "R0 = {(V,V'). \<exists>x e e'. V = [x := e] \<and> V' = [x := e'] \<and>
    e \<equiv>\<^bsub>DA x\<^esub> e'}"

  from d_indistinguishable_exp have inR0: "([x:=e],[x:=e']) \<in> R0"
    by (simp add: R0_def)

  have "d_Bisimulation_Up_To_USdB d R0"
    proof (simp add: d_Bisimulation_Up_To_USdB_def, auto)
      from d_indistinguishable_sym show "sym R0"
        by (simp add: R0_def sym_def, fastforce)
    next
      fix V V'
      assume "(V,V') \<in> R0"
      thus "length V = length V'" 
        by (simp add: R0_def, auto)
    next
      fix V V' i m1 m1' W m2
      assume inR0: "(V,V') \<in> R0"
      assume irange: "i < length V"
      assume step: "\<langle>V!i,m1\<rangle> \<rightarrow> \<langle>W,m2\<rangle>"
      assume dequal: "m1 =\<^bsub>d\<^esub> m1'"
      
      from inR0 obtain x e e' where Vassump:
        "V = [x := e] \<and> V' = [x := e'] \<and>
        e \<equiv>\<^bsub>DA x\<^esub> e'"
        by (simp add: R0_def, auto)
      
      with step irange obtain v where step1:
        "E e m1 = v \<and> W = [] \<and> m2 = m1(x := v)"
        by (auto, metis MWLf_semantics.MWLfSteps_det_cases(2))
        
      from Vassump irange obtain m2' v' where step2:
        "E e' m1' = v' \<and> \<langle>V'!i,m1'\<rangle> \<rightarrow> \<langle>[],m2'\<rangle> \<and> m2' = m1'(x := v')"
        by (auto, metis MWLfSteps_det.assign)

      with Vassump dequal step step1
      have dequalnext: "m1(x := v) =\<^bsub>d\<^esub> m1'(x := v')"      
        by (simp add: d_equal_def d_indistinguishable_def, auto)

      with step1 step2 trivialpair_in_USdB show "\<exists>W' m2'.
        \<langle>V'!i,m1'\<rangle> \<rightarrow> \<langle>W',m2'\<rangle> \<and> ((W,W') \<in> R0 \<or> W \<approx>\<^bsub>d\<^esub> W') 
        \<and> m2 =\<^bsub>d\<^esub> m2'"
        by auto
   qed
   
   hence "R0 \<subseteq> \<approx>\<^bsub>d\<^esub>"
     by (rule Up_To_Technique)

   with inR0 show ?thesis
     by auto

qed

end

end
