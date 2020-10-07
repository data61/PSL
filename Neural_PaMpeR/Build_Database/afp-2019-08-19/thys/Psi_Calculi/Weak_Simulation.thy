(* 
   Title: Psi-calculi   
   Author/Maintainer: Jesper Bengtson (jebe@itu.dk), 2012
*)
theory Weak_Simulation
  imports Simulation Tau_Chain
begin

context env begin

definition
  "weakSimulation" :: "'b \<Rightarrow> ('a, 'b, 'c) psi \<Rightarrow>
                       ('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set \<Rightarrow> 
                       ('a, 'b, 'c) psi \<Rightarrow> bool" ("_ \<rhd> _ \<leadsto><_> _" [80, 80, 80, 80] 80)
where
  "\<Psi> \<rhd> P \<leadsto><Rel> Q \<equiv> (\<forall>\<Psi>' \<alpha> Q'. \<Psi> \<rhd> Q \<longmapsto>\<alpha> \<prec> Q' \<longrightarrow> bn \<alpha> \<sharp>* \<Psi> \<longrightarrow> bn \<alpha> \<sharp>* P \<longrightarrow> \<alpha> \<noteq> \<tau> \<longrightarrow>
                      (\<exists>P''. \<Psi> : Q \<rhd> P \<Longrightarrow>\<alpha> \<prec> P'' \<and> (\<exists>P'. \<Psi> \<otimes> \<Psi>' \<rhd> P'' \<Longrightarrow>\<^sup>^\<^sub>\<tau> P' \<and> (\<Psi> \<otimes> \<Psi>', P', Q') \<in> Rel))) \<and> 
                      (\<forall>Q'. \<Psi> \<rhd> Q \<longmapsto>\<tau> \<prec> Q' \<longrightarrow> (\<exists>P'. \<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P' \<and> (\<Psi>, P', Q') \<in> Rel))"

abbreviation
  weakSimulationNilJudge ("_ \<leadsto><_> _" [80, 80, 80] 80) where "P \<leadsto><Rel> Q \<equiv> SBottom' \<rhd> P \<leadsto><Rel> Q"

lemma weakSimI[consumes 1, case_names cAct cTau]:
  fixes \<Psi>   :: 'b
  and   P   :: "('a, 'b, 'c) psi"
  and   Rel :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
  and   Q   :: "('a, 'b, 'c) psi"
  and   C   :: "'d::fs_name"

  assumes Eqvt: "eqvt Rel"
  and     rAct: "\<And>\<Psi>' \<alpha> Q'. \<lbrakk>\<Psi> \<rhd> Q \<longmapsto>\<alpha> \<prec> Q';  bn \<alpha> \<sharp>* \<Psi>; bn \<alpha> \<sharp>* P; bn \<alpha> \<sharp>* Q;
                              bn \<alpha> \<sharp>* subject \<alpha>; bn \<alpha> \<sharp>* C; distinct(bn \<alpha>); \<alpha> \<noteq> \<tau>\<rbrakk> \<Longrightarrow>
                                         
                              \<exists>P''. \<Psi> : Q \<rhd> P \<Longrightarrow>\<alpha> \<prec> P'' \<and> (\<exists>P'. \<Psi> \<otimes> \<Psi>' \<rhd> P'' \<Longrightarrow>\<^sup>^\<^sub>\<tau> P' \<and> (\<Psi> \<otimes> \<Psi>', P', Q') \<in> Rel)"
  and     rTau:  "\<And>Q'. \<Psi> \<rhd> Q \<longmapsto>\<tau> \<prec> Q' \<Longrightarrow> \<exists>P'. \<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P' \<and> (\<Psi>, P', Q') \<in> Rel"

  shows "\<Psi> \<rhd> P \<leadsto><Rel> Q"
proof(auto simp add: weakSimulation_def)
  fix \<Psi>' \<alpha> Q'
  assume "\<Psi> \<rhd> Q \<longmapsto>\<alpha> \<prec> Q'" and "bn \<alpha> \<sharp>* \<Psi>" and "bn \<alpha> \<sharp>* P" and "\<alpha> \<noteq> \<tau>"
  thus "\<exists>P''. \<Psi> : Q \<rhd> P \<Longrightarrow>\<alpha> \<prec> P'' \<and> (\<exists>P'. \<Psi> \<otimes> \<Psi>' \<rhd> P'' \<Longrightarrow>\<^sup>^\<^sub>\<tau> P' \<and> (\<Psi> \<otimes> \<Psi>', P', Q') \<in> Rel)"
  proof(nominal_induct \<alpha> rule: action.strong_induct)
    case(In M N)
    thus ?case by(rule_tac rAct) auto
  next
    case(Out M xvec N)
    from \<open>bn(M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>) \<sharp>* \<Psi>\<close> \<open>bn(M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>) \<sharp>* P\<close> have "xvec \<sharp>* \<Psi>" and "xvec \<sharp>* P" by simp+
    from \<open>\<Psi> \<rhd> Q \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'\<close> have "distinct xvec" by(force dest: boundOutputDistinct)
    obtain p where "(p \<bullet> xvec) \<sharp>* \<Psi>" and "(p \<bullet> xvec) \<sharp>* M" and "(p \<bullet> xvec) \<sharp>* xvec"
               and"(p \<bullet> xvec) \<sharp>* P" and "(p \<bullet> xvec) \<sharp>* Q" and "(p \<bullet> xvec) \<sharp>* Q'" and "(p \<bullet> xvec) \<sharp>* \<Psi>'"
               and "(p \<bullet> xvec) \<sharp>* C" and "(p \<bullet> xvec) \<sharp>* xvec" and "(p \<bullet> xvec) \<sharp>* N"
               and S: "(set p) \<subseteq> (set xvec) \<times> (set(p \<bullet> xvec))" and "distinctPerm p"
      by(rule_tac xvec=xvec and c="(\<Psi>, M, Q, N, P, Q', xvec, C, \<Psi>')" in name_list_avoiding)
        (auto simp add: eqvts fresh_star_prod)
    from \<open>distinct xvec\<close> have "distinct(p \<bullet> xvec)" by simp
    from \<open>\<Psi> \<rhd> Q \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'\<close> \<open>(p \<bullet> xvec) \<sharp>* N\<close> \<open>(p \<bullet> xvec) \<sharp>* Q'\<close> S 
    have "\<Psi> \<rhd> Q \<longmapsto>M\<lparr>\<nu>*(p \<bullet> xvec)\<rparr>\<langle>(p \<bullet> N)\<rangle> \<prec> (p \<bullet> Q')" by(simp add: boundOutputChainAlpha'' residualInject)

    then obtain P'' P' where PTrans: "\<Psi> : Q \<rhd> P \<Longrightarrow>M\<lparr>\<nu>*(p \<bullet> xvec)\<rparr>\<langle>(p \<bullet> N)\<rangle> \<prec> P''" 
                         and P''Chain: "\<Psi> \<otimes> (p \<bullet> \<Psi>') \<rhd> P'' \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'"
                         and P'RelQ': "(\<Psi> \<otimes> (p \<bullet> \<Psi>'), P', p \<bullet> Q') \<in> Rel"
      using \<open>(p \<bullet> xvec) \<sharp>* \<Psi>\<close> \<open>(p \<bullet> xvec) \<sharp>* P\<close> \<open>(p \<bullet> xvec) \<sharp>* Q\<close> \<open>(p \<bullet> xvec) \<sharp>* M\<close> \<open>(p \<bullet> xvec) \<sharp>* C\<close> \<open>distinct(p \<bullet> xvec)\<close>
      by(drule_tac \<Psi>'="p \<bullet> \<Psi>'" in rAct) auto

    from PTrans S \<open>distinctPerm p\<close> \<open>xvec \<sharp>* P\<close> \<open>(p \<bullet> xvec) \<sharp>* xvec\<close> \<open>(p \<bullet> xvec) \<sharp>* M\<close> \<open>distinct xvec\<close> 
    have "\<Psi> : Q \<rhd> P \<Longrightarrow>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> (p \<bullet> P'')" 
      by(rule_tac weakOutputAlpha) auto
    moreover from P''Chain have "(p \<bullet> (\<Psi> \<otimes> (p \<bullet> \<Psi>'))) \<rhd> (p \<bullet> P'') \<Longrightarrow>\<^sup>^\<^sub>\<tau> (p \<bullet> P')" by(rule eqvts)
    with \<open>xvec \<sharp>* \<Psi>\<close> \<open>(p \<bullet> xvec) \<sharp>* \<Psi>\<close> \<open>(p \<bullet> xvec) \<sharp>* \<Psi>'\<close> S \<open>distinctPerm p\<close>
    have "\<Psi> \<otimes> \<Psi>' \<rhd> (p \<bullet> P'') \<Longrightarrow>\<^sup>^\<^sub>\<tau> (p \<bullet> P')" by(simp add: eqvts)
    moreover from P'RelQ' Eqvt S \<open>distinctPerm p\<close> have "(p \<bullet> (\<Psi> \<otimes> (p \<bullet> \<Psi>')), p \<bullet> P', p \<bullet> p \<bullet> Q') \<in> Rel"
      apply(simp add: eqvt_def eqvts)
      apply(erule_tac x="(\<Psi> \<otimes> (p \<bullet> \<Psi>'), P', p \<bullet> Q')" in ballE)
      apply(erule_tac x="p" in allE)
      by(auto simp add: eqvts)
    with \<open>xvec \<sharp>* \<Psi>\<close> \<open>(p \<bullet> xvec) \<sharp>* \<Psi>\<close> S \<open>distinctPerm p\<close>
    have "(\<Psi> \<otimes> \<Psi>', p \<bullet> P', Q') \<in> Rel" by(simp add: eqvts)
    ultimately show ?case by blast
  next
    case Tau
    thus ?case by simp
  qed
next
  fix Q'
  assume "\<Psi> \<rhd> Q \<longmapsto>\<tau> \<prec> Q'"
  thus "\<exists>P'. \<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P' \<and> (\<Psi>, P', Q') \<in> Rel"
    by(rule rTau)
qed

lemma weakSimI2[case_names cAct cTau]:
  fixes \<Psi>   :: 'b
  and   P   :: "('a, 'b, 'c) psi"
  and   Rel :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
  and   Q   :: "('a, 'b, 'c) psi"
  and   C   :: "'d::fs_name"

  assumes rOutput: "\<And>\<Psi>' \<alpha> Q'. \<lbrakk>\<Psi> \<rhd> Q \<longmapsto>\<alpha> \<prec> Q';  bn \<alpha> \<sharp>* \<Psi>; bn \<alpha> \<sharp>* P; \<alpha> \<noteq> \<tau>\<rbrakk> \<Longrightarrow>
                                \<exists>P''. \<Psi> : Q \<rhd> P \<Longrightarrow>\<alpha> \<prec> P'' \<and> (\<exists>P'. \<Psi> \<otimes> \<Psi>' \<rhd> P'' \<Longrightarrow>\<^sup>^\<^sub>\<tau> P' \<and> (\<Psi> \<otimes> \<Psi>', P', Q') \<in> Rel)"
  and     rTau:  "\<And>Q'. \<Psi> \<rhd> Q \<longmapsto>\<tau> \<prec> Q' \<Longrightarrow> \<exists>P'. \<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P' \<and> (\<Psi>, P', Q') \<in> Rel"

  shows "\<Psi> \<rhd> P \<leadsto><Rel> Q"
using assms by(simp add: weakSimulation_def)

lemma weakSimIChainFresh[consumes 4, case_names cOutput cInput]:
  fixes \<Psi>    :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   Rel  :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
  and   Q    :: "('a, 'b, 'c) psi"
  and   yvec :: "name list"
  and   C    :: "'d::fs_name"

  assumes Eqvt: "eqvt Rel"
  and     "yvec \<sharp>* \<Psi>"
  and     "yvec \<sharp>* P"
  and     "yvec \<sharp>* Q"
  and     rAct: "\<And>\<Psi>' \<alpha> Q'. \<lbrakk>\<Psi> \<rhd> Q \<longmapsto>\<alpha> \<prec> Q'; bn \<alpha> \<sharp>* \<Psi>; bn \<alpha> \<sharp>* P; bn \<alpha> \<sharp>* Q; \<alpha> \<noteq> \<tau>;
                             bn \<alpha> \<sharp>* subject \<alpha>; bn \<alpha> \<sharp>* C; yvec \<sharp>* \<alpha>; yvec \<sharp>* Q'; yvec \<sharp>* \<Psi>'\<rbrakk> \<Longrightarrow>
                             \<exists>P''. \<Psi> : Q \<rhd> P \<Longrightarrow>\<alpha> \<prec> P'' \<and> (\<exists>P'. \<Psi> \<otimes> \<Psi>' \<rhd> P'' \<Longrightarrow>\<^sup>^\<^sub>\<tau> P' \<and> (\<Psi> \<otimes> \<Psi>', P', Q') \<in> Rel)"
  and     rTau: "\<And>Q'. \<lbrakk>\<Psi> \<rhd> Q \<longmapsto>\<tau> \<prec> Q'; yvec \<sharp>* Q'\<rbrakk> \<Longrightarrow> \<exists>P'. \<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P' \<and> (\<Psi>, P', Q') \<in> Rel"

  shows "\<Psi> \<rhd> P \<leadsto><Rel> Q"
using \<open>eqvt Rel\<close>
proof(induct rule: weakSimI[of _ _ _ _ "(yvec, C)"])
  case(cAct \<Psi>' \<alpha> Q')
  obtain p::"name prm" where "(p \<bullet> yvec) \<sharp>* \<Psi>" and "(p \<bullet> yvec) \<sharp>* P" and  "(p \<bullet> yvec) \<sharp>* Q"
                         and  "(p \<bullet> yvec) \<sharp>* \<alpha>" and "(p \<bullet> yvec) \<sharp>* \<Psi>'"
                         and "(p \<bullet> yvec) \<sharp>* Q'" and S: "(set p) \<subseteq> set yvec \<times> set(p \<bullet> yvec)"
                         and "distinctPerm p"
    by(rule_tac c="(\<Psi>, P, Q, \<alpha>, Q', \<Psi>')" and xvec=yvec in name_list_avoiding) auto
  from \<open>bn \<alpha> \<sharp>* (yvec, C)\<close> have "bn \<alpha> \<sharp>* yvec" and "bn \<alpha> \<sharp>* C" by(simp add: freshChainSym)+ 
  show ?case
  proof(cases rule: actionCases[where \<alpha> = \<alpha>])
    case(cInput M N)
    from \<open>(p \<bullet> yvec) \<sharp>* \<alpha>\<close> \<open>\<alpha> = M\<lparr>N\<rparr>\<close> have "(p \<bullet> yvec) \<sharp>* M" and  "(p \<bullet> yvec) \<sharp>* N" by simp+
    from \<open>\<Psi> \<rhd> Q \<longmapsto>\<alpha> \<prec> Q'\<close> \<open>\<alpha> = M\<lparr>N\<rparr>\<close> \<open>yvec \<sharp>* \<Psi>\<close> \<open>(p \<bullet> yvec) \<sharp>* \<Psi>\<close> \<open>yvec \<sharp>* Q\<close> \<open>(p \<bullet> yvec) \<sharp>* Q\<close> S
    have "\<Psi> \<rhd> Q \<longmapsto>(p \<bullet> M)\<lparr>(p \<bullet> N)\<rparr> \<prec> (p \<bullet> Q')" 
      by(drule_tac pi=p in semantics.eqvt) (simp add: eqvts)
    moreover from \<open>(p \<bullet> yvec) \<sharp>* M\<close> have "(p \<bullet> (p \<bullet> yvec)) \<sharp>* (p \<bullet> M)"
      by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
    with \<open>distinctPerm p\<close> have "yvec \<sharp>* (p \<bullet> M)" by simp
    moreover from \<open>(p \<bullet> yvec) \<sharp>* N\<close> have "(p \<bullet> p \<bullet> yvec) \<sharp>* (p \<bullet> N)" 
      by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
    with \<open>distinctPerm p\<close> have "yvec \<sharp>* (p \<bullet> N)" by simp
    moreover from \<open>(p \<bullet> yvec) \<sharp>* Q'\<close> have "(p \<bullet> p \<bullet> yvec) \<sharp>* (p \<bullet> Q')" 
      by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
    with \<open>distinctPerm p\<close> have "yvec \<sharp>* (p \<bullet> Q')" by simp
    moreover from \<open>(p \<bullet> yvec) \<sharp>* \<Psi>'\<close> have "(p \<bullet> p \<bullet> yvec) \<sharp>* (p \<bullet> \<Psi>')"
      by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
    with \<open>distinctPerm p\<close> have "yvec \<sharp>* (p \<bullet> \<Psi>')" by simp
    ultimately obtain P' P'' where PTrans: "\<Psi> : Q \<rhd> P \<Longrightarrow>(p \<bullet> M)\<lparr>(p \<bullet> N)\<rparr> \<prec> P''" and P''Chain: "\<Psi> \<otimes> (p \<bullet> \<Psi>') \<rhd> P'' \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'"
                               and P'RelQ': "(\<Psi> \<otimes> (p \<bullet> \<Psi>'), P', (p \<bullet> Q')) \<in> Rel"
      by(auto dest: rAct)
    from PTrans have "(p \<bullet> \<Psi>) : (p \<bullet> Q) \<rhd> (p \<bullet> P) \<Longrightarrow>p \<bullet> ((p \<bullet> M)\<lparr>(p \<bullet> N)\<rparr>) \<prec> (p \<bullet> P'')"
      by(rule weakTransitionClosed)
    with S \<open>yvec \<sharp>* \<Psi>\<close> \<open>(p \<bullet> yvec) \<sharp>* \<Psi>\<close> \<open>yvec \<sharp>* Q\<close> \<open>(p \<bullet> yvec) \<sharp>* Q\<close> \<open>yvec \<sharp>* P\<close> \<open>(p \<bullet> yvec) \<sharp>* P\<close> \<open>distinctPerm p\<close>
    have "\<Psi> : Q \<rhd> P \<Longrightarrow>M\<lparr>N\<rparr> \<prec> (p \<bullet> P'')" by(simp add: eqvts)
    moreover from P''Chain have  "(p \<bullet> (\<Psi> \<otimes> (p \<bullet> \<Psi>'))) \<rhd> (p \<bullet> P'') \<Longrightarrow>\<^sup>^\<^sub>\<tau> (p \<bullet> P')" by(rule eqvts)
    with \<open>yvec \<sharp>* \<Psi>\<close> \<open>(p \<bullet> yvec) \<sharp>* \<Psi>\<close> S \<open>distinctPerm p\<close> 
    have "\<Psi> \<otimes> \<Psi>' \<rhd> (p \<bullet> P'') \<Longrightarrow>\<^sup>^\<^sub>\<tau> (p \<bullet> P')" by(simp add: eqvts)
    moreover from P'RelQ' Eqvt have "(p \<bullet> (\<Psi> \<otimes> (p \<bullet> \<Psi>')), p \<bullet> P', p \<bullet> p \<bullet> Q') \<in> Rel"
      apply(simp add: eqvt_def eqvts)
      apply(erule_tac x="(\<Psi> \<otimes> (p \<bullet> \<Psi>'), P', p \<bullet> Q')" in ballE)
      apply(erule_tac x="p" in allE)
      by(auto simp add: eqvts)
    with \<open>yvec \<sharp>* \<Psi>\<close> \<open>(p \<bullet> yvec) \<sharp>* \<Psi>\<close> S \<open>distinctPerm p\<close> have "(\<Psi> \<otimes> \<Psi>', p \<bullet> P', Q') \<in> Rel" by(simp add: eqvts)
    ultimately show ?thesis using \<open>\<alpha>=M\<lparr>N\<rparr>\<close> by blast
  next
    case(cOutput M xvec N)
    from \<open>bn \<alpha> \<sharp>* \<Psi>\<close> \<open>bn \<alpha> \<sharp>* P\<close> \<open>bn \<alpha> \<sharp>* Q\<close>  \<open>bn \<alpha> \<sharp>* subject \<alpha>\<close> \<open>\<alpha>=M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>\<close> \<open>bn \<alpha> \<sharp>* yvec\<close>
         \<open>(p \<bullet> yvec) \<sharp>* \<alpha>\<close> \<open>bn \<alpha> \<sharp>* C\<close> \<open>bn \<alpha> \<sharp>* subject \<alpha>\<close> \<open>distinct(bn \<alpha>)\<close>
    have "xvec \<sharp>* \<Psi>" and "xvec \<sharp>* P" and "xvec \<sharp>* Q" and "xvec \<sharp>* M" and "yvec \<sharp>* xvec"
     and "(p \<bullet> yvec) \<sharp>* M" and "(p \<bullet> yvec) \<sharp>* xvec" and "xvec \<sharp>* C" and "xvec \<sharp>* M" and "(p \<bullet> yvec) \<sharp>* N" 
     and "distinct xvec" by simp+
    from \<open>\<Psi> \<rhd> Q \<longmapsto>\<alpha> \<prec> Q'\<close> \<open>yvec \<sharp>* \<Psi>\<close> \<open>(p \<bullet> yvec) \<sharp>* \<Psi>\<close> \<open>yvec \<sharp>* Q\<close> \<open>(p \<bullet> yvec) \<sharp>* Q\<close> S \<open>\<alpha>=M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>\<close>
    have "\<Psi> \<rhd> Q \<longmapsto>(p \<bullet> M)\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'"
      by(rule_tac outputPermSubject) (assumption | simp add: fresh_star_def)+
    moreover note \<open>xvec \<sharp>* \<Psi>\<close> \<open>xvec \<sharp>* P\<close> 
    moreover note \<open>xvec \<sharp>* Q\<close>
    moreover from \<open>xvec \<sharp>* M\<close> have "(p \<bullet> xvec) \<sharp>* (p \<bullet> M)"
      by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
    with \<open>yvec \<sharp>* xvec\<close> \<open>(p \<bullet> yvec) \<sharp>* xvec\<close> S have "xvec \<sharp>* (p \<bullet> M)"
      by simp
    moreover note \<open>xvec \<sharp>* C\<close>
    moreover from \<open>(p \<bullet> yvec) \<sharp>* M\<close> have "(p \<bullet> (p \<bullet> yvec)) \<sharp>* (p \<bullet> M)"
      by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
    with \<open>distinctPerm p\<close> have "yvec \<sharp>* (p \<bullet> M)" by simp
    moreover note \<open>yvec \<sharp>* xvec\<close>
    moreover from \<open>\<Psi> \<rhd> Q \<longmapsto>\<alpha> \<prec> Q'\<close> \<open>yvec \<sharp>* Q\<close> \<open>yvec \<sharp>* xvec\<close> \<open>\<alpha>=M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>\<close> \<open>xvec \<sharp>* M\<close> \<open>distinct xvec\<close>
    have "yvec \<sharp>* N" and "yvec \<sharp>* Q'"  by(force dest: outputFreshChainDerivative)+
    moreover from \<open>(p \<bullet> yvec) \<sharp>* \<Psi>'\<close> have "(p \<bullet> p \<bullet> yvec) \<sharp>* (p \<bullet> \<Psi>')"
      by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
    with \<open>distinctPerm p\<close> have "yvec \<sharp>* (p \<bullet> \<Psi>')" by simp
    ultimately obtain P'' P' where PTrans: "\<Psi> : Q \<rhd> P \<Longrightarrow>(p \<bullet> M)\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P''"
                               and PChain: "\<Psi> \<otimes> (p \<bullet> \<Psi>') \<rhd> P'' \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'"
                               and P'RelQ': "(\<Psi> \<otimes> (p \<bullet> \<Psi>'), P', Q') \<in> Rel"
      by(drule_tac rAct) auto
    from PTrans have "(p \<bullet> \<Psi>) : (p \<bullet> Q) \<rhd> (p \<bullet> P) \<Longrightarrow>(p \<bullet> ((p \<bullet> M)\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>)) \<prec> (p \<bullet> P'')" 
      by(rule eqvts)
    with S \<open>yvec \<sharp>* \<Psi>\<close> \<open>(p \<bullet> yvec) \<sharp>* \<Psi>\<close> \<open>yvec \<sharp>* P\<close> \<open>(p \<bullet> yvec) \<sharp>* P\<close> \<open>yvec \<sharp>* Q\<close> \<open>(p \<bullet> yvec) \<sharp>* Q\<close> \<open>yvec \<sharp>* xvec\<close> \<open>(p \<bullet> yvec) \<sharp>* xvec\<close> 
      \<open>yvec \<sharp>* N\<close> \<open>(p \<bullet> yvec) \<sharp>* N\<close> \<open>distinctPerm p\<close> have "\<Psi> : Q \<rhd> P \<Longrightarrow>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> (p \<bullet> P'')"
      by(simp add: eqvts)
    moreover from PChain have "(p \<bullet> (\<Psi> \<otimes> (p \<bullet> \<Psi>'))) \<rhd> (p \<bullet> P'') \<Longrightarrow>\<^sup>^\<^sub>\<tau> (p \<bullet> P')" by(rule eqvts)
    with S \<open>yvec \<sharp>* \<Psi>\<close> \<open>(p \<bullet> yvec) \<sharp>* \<Psi>\<close> \<open>distinctPerm p\<close> have "\<Psi> \<otimes> \<Psi>' \<rhd> (p \<bullet> P'') \<Longrightarrow>\<^sup>^\<^sub>\<tau> (p \<bullet> P')" by(simp add: eqvts)
    moreover from P'RelQ' \<open>eqvt Rel\<close> have "p \<bullet> (\<Psi> \<otimes> (p \<bullet> \<Psi>'), P', Q') \<in> Rel"
      by(simp add: eqvt_def) auto
    with \<open>yvec \<sharp>* \<Psi>\<close> \<open>(p \<bullet> yvec) \<sharp>* \<Psi>\<close>\<open>yvec \<sharp>* Q'\<close> \<open>(p \<bullet> yvec) \<sharp>* Q'\<close> S \<open>distinctPerm p\<close> 
    have "(\<Psi> \<otimes> \<Psi>', p \<bullet> P', Q') \<in> Rel" by(simp add: eqvts)
    ultimately show ?thesis using \<open>\<alpha>=M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>\<close> by blast
  next
    case cTau
    from \<open>\<alpha> = \<tau>\<close> \<open>\<alpha> \<noteq> \<tau>\<close> have "False" by simp
    thus ?thesis by simp
  qed
next
  case(cTau Q')
  from \<open>\<Psi> \<rhd> Q \<longmapsto>\<tau> \<prec> Q'\<close> \<open>yvec \<sharp>* Q\<close> have "yvec \<sharp>* Q'"
    by(force dest: tauFreshChainDerivative)
  with \<open>\<Psi> \<rhd> Q \<longmapsto>\<tau> \<prec> Q'\<close> show ?case
    by(rule rTau)
qed

lemma weakSimIFresh[consumes 4, case_names cAct cTau]:
  fixes \<Psi>   :: 'b
  and   P   :: "('a, 'b, 'c) psi"
  and   Rel :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
  and   Q   :: "('a, 'b, 'c) psi"
  and   x   :: name
  and   C   :: "'d::fs_name"

  assumes Eqvt: "eqvt Rel"
  and     "x \<sharp> \<Psi>"
  and     "x \<sharp> P"
  and     "x \<sharp> Q"
  and     "\<And>\<alpha> Q' \<Psi>'. \<lbrakk>\<Psi> \<rhd> Q \<longmapsto>\<alpha> \<prec> Q'; bn \<alpha> \<sharp>* \<Psi>; bn \<alpha> \<sharp>* P; bn \<alpha> \<sharp>* Q; \<alpha> \<noteq> \<tau>;
                       bn \<alpha> \<sharp>* subject \<alpha>; bn \<alpha> \<sharp>* C; x \<sharp> \<alpha>; x \<sharp> Q'; x \<sharp> \<Psi>'\<rbrakk> \<Longrightarrow>
                       \<exists>P''. \<Psi> : Q \<rhd> P \<Longrightarrow>\<alpha> \<prec> P'' \<and> (\<exists>P'. \<Psi> \<otimes> \<Psi>' \<rhd> P'' \<Longrightarrow>\<^sup>^\<^sub>\<tau> P' \<and> (\<Psi> \<otimes> \<Psi>', P', Q') \<in> Rel)"
  and     "\<And>Q'. \<lbrakk>\<Psi> \<rhd> Q \<longmapsto>\<tau> \<prec> Q'; x \<sharp> Q'\<rbrakk> \<Longrightarrow> \<exists>P'. \<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P' \<and> (\<Psi>, P', Q') \<in> Rel"

  shows "\<Psi> \<rhd> P \<leadsto><Rel> Q"
using assms
by(rule_tac yvec="[x]" and C=C in weakSimIChainFresh) auto

lemma weakSimE:
  fixes F   :: 'b
  and   P   :: "('a, 'b, 'c) psi"
  and   Rel :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
  and   Q   :: "('a, 'b, 'c) psi"

  assumes "\<Psi> \<rhd> P \<leadsto><Rel> Q"

  shows "\<And>\<Psi>' \<alpha> Q'. \<lbrakk>\<Psi> \<rhd> Q \<longmapsto>\<alpha> \<prec> Q'; bn \<alpha> \<sharp>* \<Psi>; bn \<alpha> \<sharp>* P; \<alpha> \<noteq> \<tau>\<rbrakk> \<Longrightarrow> 
                            \<exists>P''. \<Psi> : Q \<rhd> P \<Longrightarrow>\<alpha> \<prec> P'' \<and> (\<exists>P'. \<Psi> \<otimes> \<Psi>' \<rhd> P'' \<Longrightarrow>\<^sup>^\<^sub>\<tau> P' \<and> (\<Psi> \<otimes> \<Psi>', P', Q') \<in> Rel)"
  and   "\<And>Q'. \<Psi> \<rhd> Q \<longmapsto>\<tau> \<prec> Q' \<Longrightarrow> \<exists>P'. \<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P' \<and> (\<Psi>, P', Q') \<in> Rel"
using assms
by(auto simp add: weakSimulation_def)

lemma weakSimClosedAux:
  fixes \<Psi>   :: 'b
  and   P   :: "('a, 'b, 'c) psi"
  and   Rel :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
  and   Q   :: "('a, 'b, 'c) psi"
  and   p   :: "name prm"

  assumes EqvtRel: "eqvt Rel"
  and     PSimQ: "\<Psi> \<rhd> P \<leadsto><Rel> Q"

  shows "(p \<bullet> \<Psi>) \<rhd> (p \<bullet> P) \<leadsto><Rel> (p \<bullet> Q)"
using EqvtRel
proof(induct rule: weakSimI[of _ _ _ _ "(\<Psi>, P, p)"])
  case(cAct \<Psi>' \<alpha> Q')
  from \<open>p \<bullet> \<Psi> \<rhd> p \<bullet> Q \<longmapsto>\<alpha> \<prec> Q'\<close> 
  have "(rev p \<bullet> p \<bullet> \<Psi>) \<rhd> (rev p \<bullet> p \<bullet> Q) \<longmapsto>(rev p \<bullet> (\<alpha> \<prec> Q'))"
    by(blast dest: semantics.eqvt)
  hence "\<Psi> \<rhd> Q \<longmapsto>(rev p \<bullet> \<alpha>) \<prec> (rev p \<bullet> Q')"
    by(simp add: eqvts)
  moreover with \<open>bn \<alpha> \<sharp>* (\<Psi>, P, p)\<close> have "bn \<alpha>  \<sharp>* \<Psi>" and "bn \<alpha>  \<sharp>* P" and "bn \<alpha>  \<sharp>* p" by simp+
  moreover from \<open>\<alpha> \<noteq> \<tau>\<close> have "(rev p \<bullet> \<alpha>) \<noteq> \<tau>"
    by(cases rule: actionCases[where \<alpha>=\<alpha>]) auto
  ultimately obtain P'' P' where PTrans: "\<Psi> : Q \<rhd> P \<Longrightarrow>(rev p \<bullet> \<alpha>) \<prec> P''"
                          and P''Chain: "\<Psi> \<otimes> (rev p \<bullet> \<Psi>') \<rhd> P'' \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'" and P'RelQ': "(\<Psi> \<otimes> (rev p \<bullet> \<Psi>'), P', rev p \<bullet> Q') \<in> Rel"
    using \<open>\<alpha> \<noteq> \<tau>\<close> PSimQ
    by(drule_tac \<Psi>'="rev p \<bullet> \<Psi>'" in weakSimE(1)) (auto simp add: freshChainPermSimp bnEqvt[symmetric])

  from PTrans have "(p \<bullet> \<Psi>) : (p \<bullet> Q) \<rhd> (p \<bullet> P) \<Longrightarrow>(p \<bullet> (rev p \<bullet> \<alpha>)) \<prec> (p \<bullet> P'')"
    by(rule eqvts)
  hence "(p \<bullet> \<Psi>) : (p \<bullet> Q) \<rhd> (p \<bullet> P) \<Longrightarrow>\<alpha> \<prec> (p \<bullet> P'')" by(simp add: eqvts freshChainPermSimp)
  moreover from P''Chain have  "(p \<bullet> (\<Psi> \<otimes> (rev p \<bullet> \<Psi>'))) \<rhd> (p \<bullet> P'') \<Longrightarrow>\<^sup>^\<^sub>\<tau> (p \<bullet> P')" by(rule eqvts)
  hence "(p \<bullet> \<Psi>) \<otimes> \<Psi>' \<rhd> (p \<bullet> P'') \<Longrightarrow>\<^sup>^\<^sub>\<tau> (p \<bullet> P')" by(simp add: eqvts)
  moreover from P'RelQ' EqvtRel have "(p \<bullet> ((\<Psi> \<otimes> (rev p \<bullet> \<Psi>')), P', rev p \<bullet> Q')) \<in> Rel"
    by(simp only: eqvt_def)
  hence "((p \<bullet> \<Psi>) \<otimes> \<Psi>', p \<bullet> P', Q') \<in> Rel" by(simp add: eqvts)
  ultimately show ?case by blast
next
  case(cTau Q')
  from \<open>p \<bullet> \<Psi> \<rhd> p \<bullet> Q \<longmapsto>\<tau> \<prec> Q'\<close> 
  have "(rev p \<bullet> p \<bullet> \<Psi>) \<rhd> (rev p \<bullet> p \<bullet> Q) \<longmapsto>(rev p \<bullet> (\<tau> \<prec> Q'))"
    by(blast dest: semantics.eqvt)
  hence "\<Psi> \<rhd> Q \<longmapsto>\<tau> \<prec> (rev p \<bullet> Q')" by(simp add: eqvts)
  with PSimQ obtain P' where PChain: "\<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'" and P'RelQ': "(\<Psi>, P', rev p \<bullet> Q') \<in> Rel"
    by(blast dest: weakSimE)
  from PChain have "(p \<bullet> \<Psi>) \<rhd> (p \<bullet> P) \<Longrightarrow>\<^sup>^\<^sub>\<tau> (p \<bullet> P')" by(rule tauChainEqvt)
  moreover from P'RelQ' EqvtRel have "(p \<bullet> (\<Psi>,  P', rev p \<bullet> Q')) \<in> Rel"
    by(simp only: eqvt_def)
  hence "(p \<bullet> \<Psi>, p \<bullet> P', Q') \<in> Rel" by(simp add: eqvts)
  ultimately show ?case
    by blast
qed

lemma weakSimClosed:
  fixes \<Psi>   :: 'b
  and   P   :: "('a, 'b, 'c) psi"
  and   Rel :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
  and   Q   :: "('a, 'b, 'c) psi"
  and   p   :: "name prm"

  assumes EqvtRel: "eqvt Rel"

  shows "\<Psi> \<rhd> P \<leadsto><Rel> Q \<Longrightarrow> (p \<bullet> \<Psi>) \<rhd> (p \<bullet> P) \<leadsto><Rel> (p \<bullet> Q)"
  and   "P \<leadsto><Rel> Q \<Longrightarrow> (p \<bullet> P) \<leadsto><Rel> (p \<bullet> Q)"
using EqvtRel
by(force dest: weakSimClosedAux simp add: permBottom)+

lemma weakSimReflexive:
  fixes Rel :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
  and   \<Psi>   :: 'b
  and   P   :: "('a, 'b, 'c) psi"

  assumes "{(\<Psi>, P, P) | \<Psi> P. True} \<subseteq> Rel"

  shows "\<Psi> \<rhd> P \<leadsto><Rel> P"
using assms
by(auto simp add: weakSimulation_def weakTransition_def dest: rtrancl_into_rtrancl) force+

lemma weakSimTauChain:
  fixes \<Psi>   :: 'b
  and   Q   :: "('a, 'b, 'c) psi"
  and   Q'  :: "('a, 'b, 'c) psi"
  and   P   :: "('a, 'b, 'c) psi"
  and   Rel :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"

  assumes "\<Psi> \<rhd> Q \<Longrightarrow>\<^sup>^\<^sub>\<tau> Q'"
  and     "(\<Psi>, P, Q) \<in> Rel"
  and     Sim: "\<And>\<Psi>' R S. (\<Psi>', R, S) \<in> Rel \<Longrightarrow> \<Psi>' \<rhd> R \<leadsto><Rel> S"
  
  obtains P' where "\<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'" and "(\<Psi>, P', Q') \<in> Rel"
proof -
  assume A: "\<And>P'. \<lbrakk>\<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'; (\<Psi>, P', Q') \<in> Rel\<rbrakk> \<Longrightarrow> thesis"
  from \<open>\<Psi> \<rhd> Q \<Longrightarrow>\<^sup>^\<^sub>\<tau> Q'\<close> \<open>(\<Psi>, P, Q) \<in> Rel\<close> A show ?thesis
  proof(induct arbitrary: P thesis rule: tauChainInduct)
    case(TauBase Q P)
    moreover have "\<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P" by simp
    ultimately show ?case by blast
  next
    case(TauStep Q Q' Q'' P)
    from \<open>(\<Psi>, P, Q) \<in> Rel\<close> obtain P' where PChain: "\<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'" and "(\<Psi>, P', Q') \<in> Rel"
      by(rule TauStep)
    from \<open>(\<Psi>, P', Q') \<in> Rel\<close> have "\<Psi> \<rhd> P' \<leadsto><Rel> Q'" by(rule Sim)
    then obtain P'' where P'Chain: "\<Psi> \<rhd> P' \<Longrightarrow>\<^sup>^\<^sub>\<tau> P''" and "(\<Psi>, P'', Q'') \<in> Rel"
      using \<open>\<Psi> \<rhd> Q' \<longmapsto>\<tau> \<prec> Q''\<close> by(blast dest: weakSimE)
    from PChain P'Chain have "\<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P''" by simp
    thus ?case using \<open>(\<Psi>, P'', Q'') \<in> Rel\<close> by(rule TauStep)
  qed
qed

lemma weakSimE2:
  fixes \<Psi>  :: 'b
  and   P   :: "('a, 'b, 'c) psi"
  and   Rel :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set" 
  and   Q   :: "('a, 'b, 'c) psi"

  assumes PRelQ: "(\<Psi>, P, Q) \<in> Rel"
  and     Sim: "\<And>\<Psi>' R S. (\<Psi>', R, S) \<in> Rel \<Longrightarrow> \<Psi>' \<rhd> R \<leadsto><Rel> S"
  and     QTrans: "\<Psi> : R \<rhd> Q \<Longrightarrow>\<alpha> \<prec> Q'"
  and     "bn \<alpha> \<sharp>* \<Psi>"
  and     "bn \<alpha> \<sharp>* P"
  and     "\<alpha> \<noteq> \<tau>"

  obtains P'' P' where "\<Psi> : R \<rhd> P \<Longrightarrow>\<alpha> \<prec> P''" and "\<Psi> \<otimes> \<Psi>' \<rhd> P'' \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'" and "(\<Psi> \<otimes> \<Psi>', P', Q') \<in> Rel"
proof -
  assume A: "\<And>P'' P'. \<lbrakk>\<Psi> : R \<rhd> P \<Longrightarrow>\<alpha> \<prec> P''; \<Psi> \<otimes> \<Psi>' \<rhd> P'' \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'; (\<Psi> \<otimes> \<Psi>', P', Q') \<in> Rel\<rbrakk> \<Longrightarrow> thesis"
  from QTrans obtain Q'' 
    where QChain: "\<Psi> \<rhd> Q \<Longrightarrow>\<^sup>^\<^sub>\<tau> Q''" 
      and ReqQ'': "insertAssertion (extractFrame R) \<Psi> \<hookrightarrow>\<^sub>F insertAssertion (extractFrame Q'') \<Psi>"
      and Q''Trans: "\<Psi> \<rhd> Q'' \<longmapsto>\<alpha> \<prec> Q'"
    by(rule weakTransitionE)

  from QChain PRelQ Sim
  obtain P'' where PChain: "\<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P''" and P''RelQ'': "(\<Psi>, P'', Q'') \<in> Rel" by(rule weakSimTauChain)

  from PChain \<open>bn \<alpha> \<sharp>* P\<close> have "bn \<alpha> \<sharp>* P''" by(rule tauChainFreshChain)
  from P''RelQ'' have "\<Psi> \<rhd> P'' \<leadsto><Rel> Q''" by(rule Sim)
  with Q''Trans \<open>bn \<alpha> \<sharp>* \<Psi>\<close> \<open>bn \<alpha> \<sharp>* P''\<close> \<open>\<alpha> \<noteq> \<tau>\<close>
  obtain P''' P' where P''Trans: "\<Psi> : Q'' \<rhd> P'' \<Longrightarrow>\<alpha> \<prec> P'''" and P'''Chain: "\<Psi> \<otimes> \<Psi>' \<rhd> P''' \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'"
                   and P'RelQ': "(\<Psi> \<otimes> \<Psi>', P', Q') \<in> Rel"
    by(blast dest: weakSimE)
  
  from P''Trans obtain P'''' where P''Chain: "\<Psi> \<rhd> P'' \<Longrightarrow>\<^sup>^\<^sub>\<tau> P''''"
                               and Q''eqP'''': "insertAssertion (extractFrame Q'') \<Psi> \<hookrightarrow>\<^sub>F insertAssertion (extractFrame P'''') \<Psi>"
                               and P''''Trans: "\<Psi> \<rhd> P'''' \<longmapsto>\<alpha> \<prec> P'''"
    by(rule weakTransitionE)
  from PChain P''Chain have "\<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P''''" by simp
  moreover from ReqQ'' Q''eqP'''' have "insertAssertion (extractFrame R) \<Psi> \<hookrightarrow>\<^sub>F insertAssertion (extractFrame P'''') \<Psi>"
    by(rule FrameStatImpTrans)
  ultimately have "\<Psi> : R \<rhd> P \<Longrightarrow>\<alpha> \<prec> P'''" using P''''Trans by(rule weakTransitionI)
  with P'''Chain P'RelQ' A show ?thesis by blast
qed

lemma weakSimTransitive:
  fixes \<Psi>     :: 'b
  and   P     :: "('a, 'b, 'c) psi"
  and   Rel   :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
  and   Q     :: "('a, 'b, 'c) psi"
  and   Rel'  :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
  and   T     :: "('a, 'b, 'c) psi"
  and   Rel'' :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"

  assumes PRelQ: "(\<Psi>, P, Q) \<in> Rel"
  and     QSimR: "\<Psi> \<rhd> Q \<leadsto><Rel'> R"
  and     Eqvt: "eqvt Rel''"
  and     Set: "{(\<Psi>, P, R) | \<Psi> P R. \<exists>Q. (\<Psi>, P, Q) \<in> Rel \<and> (\<Psi>, Q, R) \<in> Rel'} \<subseteq> Rel''"
  and     Sim: "\<And>\<Psi>' R S. (\<Psi>', R, S) \<in> Rel \<Longrightarrow> \<Psi>' \<rhd> R \<leadsto><Rel> S"

  shows "\<Psi> \<rhd> P \<leadsto><Rel''> R"
using \<open>eqvt Rel''\<close>
proof(induct rule: weakSimI[of _ _ _ _ Q])
  case(cAct \<Psi>' \<alpha> R')
  from QSimR \<open>\<Psi> \<rhd> R \<longmapsto>\<alpha> \<prec> R'\<close> \<open>bn \<alpha> \<sharp>* \<Psi>\<close> \<open>bn \<alpha> \<sharp>* Q\<close> \<open>\<alpha> \<noteq> \<tau>\<close>
  obtain Q'' Q' where QTrans: "\<Psi> : R \<rhd> Q \<Longrightarrow>\<alpha> \<prec> Q''" and Q''Chain: "\<Psi> \<otimes> \<Psi>' \<rhd> Q'' \<Longrightarrow>\<^sup>^\<^sub>\<tau> Q'"
                  and Q'RelR': "(\<Psi> \<otimes> \<Psi>', Q', R') \<in> Rel'"
    by(blast dest: weakSimE)
  with PRelQ Sim QTrans \<open>bn \<alpha> \<sharp>* \<Psi>\<close> \<open>bn \<alpha> \<sharp>* P\<close> \<open>\<alpha> \<noteq> \<tau>\<close>
  obtain P''' P'' where PTrans: "\<Psi> : R \<rhd> P \<Longrightarrow>\<alpha> \<prec> P'''" 
                and P'''Chain: "\<Psi> \<otimes> \<Psi>' \<rhd> P''' \<Longrightarrow>\<^sup>^\<^sub>\<tau> P''" and P''RelQ'': "(\<Psi> \<otimes> \<Psi>', P'', Q'') \<in> Rel"
    by(drule_tac weakSimE2) auto

  note PTrans
  moreover from Q''Chain P''RelQ'' Sim obtain P' where P''Chain: "\<Psi> \<otimes> \<Psi>' \<rhd> P'' \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'" and P'RelQ': "(\<Psi> \<otimes> \<Psi>', P', Q') \<in> Rel"
    by(rule weakSimTauChain)
  from P'''Chain P''Chain have "\<Psi> \<otimes> \<Psi>' \<rhd> P''' \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'" by simp
  moreover from P'RelQ' Q'RelR' Set have "(\<Psi> \<otimes> \<Psi>', P', R') \<in> Rel''" by blast
  ultimately show ?case by blast
next
  case(cTau R')
  from QSimR \<open>\<Psi> \<rhd> R \<longmapsto>\<tau> \<prec> R'\<close> obtain Q' where QChain: "\<Psi> \<rhd> Q \<Longrightarrow>\<^sup>^\<^sub>\<tau> Q'" and Q'RelR': "(\<Psi>, Q', R') \<in> Rel'" 
    by(blast dest: weakSimE)
  from QChain PRelQ Sim obtain P' where PChain: "\<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'" and P'RelQ': "(\<Psi>, P', Q') \<in> Rel"
    by(rule weakSimTauChain)
  note PChain
  moreover from P'RelQ' Q'RelR' Set have "(\<Psi>, P', R') \<in> Rel''" by blast
  ultimately show ?case by blast
qed

lemma weakSimStatEq:
  fixes \<Psi>   :: 'b
  and   P   :: "('a, 'b, 'c) psi"
  and   Rel :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
  and   Q   :: "('a, 'b, 'c) psi"
  and   \<Psi>'  :: 'b

  assumes PSimQ: "\<Psi> \<rhd> P \<leadsto><Rel> Q"
  and     "eqvt Rel'"
  and     "\<Psi> \<simeq> \<Psi>'"
  and     C1: "\<And>\<Psi>' R S \<Psi>''. \<lbrakk>(\<Psi>', R, S) \<in> Rel; \<Psi>' \<simeq> \<Psi>''\<rbrakk> \<Longrightarrow> (\<Psi>'', R, S) \<in> Rel'"

  shows "\<Psi>' \<rhd> P \<leadsto><Rel'> Q"
using \<open>eqvt Rel'\<close>
proof(induct rule: weakSimI[of _ _ _ _ \<Psi>])
  case(cAct \<Psi>'' \<alpha> Q')
  from \<open>\<Psi>' \<rhd> Q \<longmapsto>\<alpha> \<prec> Q'\<close> \<open>\<Psi> \<simeq> \<Psi>'\<close>
  have "\<Psi> \<rhd> Q \<longmapsto>\<alpha> \<prec> Q'" by(metis statEqTransition AssertionStatEqSym)
  with PSimQ \<open>bn \<alpha> \<sharp>* \<Psi>\<close> \<open>bn \<alpha> \<sharp>* P\<close> \<open>\<alpha> \<noteq> \<tau>\<close>
  obtain P'' P' where PTrans: "\<Psi> : Q \<rhd> P \<Longrightarrow>\<alpha> \<prec> P''" and P''Chain: "\<Psi> \<otimes> \<Psi>'' \<rhd> P'' \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'" 
                  and P'RelQ': "(\<Psi> \<otimes> \<Psi>'', P', Q') \<in> Rel"
    by(blast dest: weakSimE)

  from PTrans \<open>\<Psi> \<simeq> \<Psi>'\<close> have "\<Psi>' : Q \<rhd> P \<Longrightarrow>\<alpha> \<prec> P''" by(rule weakTransitionStatEq)
  moreover from P''Chain \<open>\<Psi> \<simeq> \<Psi>'\<close> have "\<Psi>' \<otimes> \<Psi>'' \<rhd> P'' \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'" by(metis tauChainStatEq Composition)
  moreover from P'RelQ' \<open>\<Psi> \<simeq> \<Psi>'\<close> have "(\<Psi>' \<otimes> \<Psi>'', P', Q') \<in> Rel'"
    by(metis C1 Composition)
  ultimately show ?case
    by blast
next
  case(cTau Q')
  from \<open>\<Psi>' \<rhd> Q \<longmapsto>\<tau> \<prec> Q'\<close> \<open>\<Psi> \<simeq> \<Psi>'\<close>
  have "\<Psi> \<rhd> Q \<longmapsto>\<tau> \<prec> Q'" by(metis statEqTransition AssertionStatEqSym)
  with PSimQ obtain P' where PChain: "\<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'" and P'RelQ': "(\<Psi>, P', Q') \<in> Rel"
    by(blast dest: weakSimE)
  
  from PChain \<open>\<Psi> \<simeq> \<Psi>'\<close> have "\<Psi>' \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'" by(rule tauChainStatEq)
  moreover from \<open>(\<Psi>, P', Q') \<in> Rel\<close> \<open>\<Psi> \<simeq> \<Psi>'\<close> have "(\<Psi>', P', Q') \<in> Rel'"
    by(rule C1)
  ultimately show ?case by blast
qed

lemma weakSimMonotonic: 
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   A :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
  and   Q :: "('a, 'b, 'c) psi"
  and   B :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"

  assumes "\<Psi> \<rhd> P \<leadsto><A> Q"
  and     "A \<subseteq> B"

  shows "\<Psi> \<rhd> P \<leadsto><B> Q"
using assms
by(simp (no_asm) add: weakSimulation_def) (blast dest: weakSimE)+

lemma strongSimWeakSim:
  fixes \<Psi>   :: 'b
  and   P   :: "('a, 'b, 'c) psi"
  and   Q   :: "('a, 'b, 'c) psi"
  and   Rel :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"

  assumes PRelQ: "(\<Psi>, P, Q) \<in> Rel"
  and     StatImp: "\<And>\<Psi>' R S. (\<Psi>', R, S) \<in> Rel \<Longrightarrow> insertAssertion(extractFrame S) \<Psi>' \<hookrightarrow>\<^sub>F insertAssertion(extractFrame R) \<Psi>'"
  and     Sim:     "\<And>\<Psi>' R S. (\<Psi>', R, S) \<in> Rel \<Longrightarrow> \<Psi>' \<rhd> R \<leadsto>[Rel] S"
  and     Ext:     "\<And>\<Psi>' R S \<Psi>''. (\<Psi>', R, S) \<in> Rel \<Longrightarrow> (\<Psi>' \<otimes> \<Psi>'', R, S) \<in> Rel"

  shows "\<Psi> \<rhd> P \<leadsto><Rel> Q"
proof(induct rule: weakSimI2)
  case(cAct \<Psi>' \<alpha> Q')
  from PRelQ have "\<Psi> \<rhd> P \<leadsto>[Rel] Q" by(rule Sim)
  with \<open>\<Psi> \<rhd> Q \<longmapsto>\<alpha> \<prec> Q'\<close> \<open>bn \<alpha> \<sharp>* \<Psi>\<close> \<open>bn \<alpha> \<sharp>* P\<close>
  obtain P' where PTrans: "\<Psi> \<rhd> P \<longmapsto>\<alpha> \<prec> P'" and P'RelQ': "(\<Psi>, P', Q') \<in> Rel"
    by(blast dest: simE)
  
  from PRelQ have "insertAssertion(extractFrame Q) \<Psi> \<hookrightarrow>\<^sub>F insertAssertion(extractFrame P) \<Psi>" by(rule StatImp)
  with PTrans have "\<Psi> : Q \<rhd> P \<Longrightarrow>\<alpha> \<prec> P'" by(rule transitionWeakTransition)
  moreover from P'RelQ' have "\<forall>\<Psi>'. \<exists>P''. \<Psi> \<otimes> \<Psi>' \<rhd> P' \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'' \<and> (\<Psi> \<otimes> \<Psi>', P'', Q') \<in> Rel"
    by(force intro: Ext)
  ultimately show ?case by blast
next
  case(cTau Q')
  from PRelQ have "\<Psi> \<rhd> P \<leadsto>[Rel] Q" by(rule Sim)
  with \<open>\<Psi> \<rhd> Q \<longmapsto>\<tau> \<prec> Q'\<close> obtain P' where PTrans: "\<Psi> \<rhd> P \<longmapsto>\<tau> \<prec> P'" and P'RelQ': "(\<Psi>, P', Q') \<in> Rel"
    by(force dest: simE)
  with PTrans have "\<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'" by auto
  thus ?case using P'RelQ' by blast
qed

lemma strongAppend:
  fixes \<Psi>    :: 'b
  and   P     :: "('a, 'b, 'c) psi"
  and   Q     :: "('a, 'b, 'c) psi"
  and   R     :: "('a, 'b, 'c) psi"
  and   Rel   :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
  and   Rel'  :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
  and   Rel'' :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"

  assumes PSimQ: "\<Psi> \<rhd> P \<leadsto><Rel> Q"
  and     QSimR: "\<Psi> \<rhd> Q \<leadsto>[Rel'] R"
  and     Eqvt'': "eqvt Rel''"
  and     RimpQ: "insertAssertion (extractFrame R) \<Psi> \<hookrightarrow>\<^sub>F insertAssertion (extractFrame Q) \<Psi>"
  and     Set: "{(\<Psi>, P, R) | \<Psi> P R. \<exists>Q. (\<Psi>, P, Q) \<in> Rel \<and> (\<Psi>, Q, R) \<in> Rel'} \<subseteq> Rel''"
  and     C1: "\<And>\<Psi> P Q \<Psi>'. (\<Psi>, P, Q) \<in> Rel' \<Longrightarrow> (\<Psi> \<otimes> \<Psi>', P, Q) \<in> Rel'"

  shows "\<Psi> \<rhd> P \<leadsto><Rel''> R"
proof -
  from Eqvt'' show ?thesis
  proof(induct rule: weakSimI[of _ _ _ _ Q])
    case(cAct \<Psi>' \<alpha> R')
    from \<open>\<Psi> \<rhd> Q \<leadsto>[Rel'] R\<close> \<open>\<Psi> \<rhd> R \<longmapsto>\<alpha> \<prec> R'\<close> \<open>bn \<alpha> \<sharp>* \<Psi>\<close> \<open>bn \<alpha> \<sharp>* Q\<close>
    obtain Q' where QTrans: "\<Psi> \<rhd> Q \<longmapsto>\<alpha> \<prec> Q'" and "(\<Psi>, Q', R') \<in> Rel'"
      by(blast dest: simE)

    from \<open>(\<Psi>, Q', R') \<in> Rel'\<close> have Q'RelR': "(\<Psi> \<otimes> \<Psi>', Q', R') \<in> Rel'" by(rule C1)

    from \<open>\<Psi> \<rhd> P \<leadsto><Rel> Q\<close> QTrans \<open>bn \<alpha> \<sharp>* \<Psi>\<close> \<open>bn \<alpha> \<sharp>* P\<close> \<open>\<alpha> \<noteq> \<tau>\<close> 
    obtain P'' P' where PTrans: "\<Psi> : Q \<rhd> P \<Longrightarrow>\<alpha> \<prec> P''" and P''Chain: "\<Psi> \<otimes> \<Psi>' \<rhd> P'' \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'"
                    and P'RelQ': "(\<Psi> \<otimes> \<Psi>', P', Q') \<in> Rel"
      by(blast dest: weakSimE)

    from PTrans RimpQ have "\<Psi> : R \<rhd> P \<Longrightarrow>\<alpha> \<prec> P''" by(rule weakTransitionFrameImp)
    moreover note P''Chain
    moreover from P'RelQ' Q'RelR' Set have "(\<Psi> \<otimes> \<Psi>', P', R') \<in> Rel''" by blast
    ultimately show ?case by blast
  next
    case(cTau R')
    from \<open>\<Psi> \<rhd> Q \<leadsto>[Rel'] R\<close> \<open>\<Psi> \<rhd> R \<longmapsto>\<tau> \<prec> R'\<close>
    obtain Q' where QTrans: "\<Psi> \<rhd> Q \<longmapsto>\<tau> \<prec> Q'" and Q'RelR': "(\<Psi>, Q', R') \<in> Rel'"
      by(force dest: simE)

    from \<open>\<Psi> \<rhd> P \<leadsto><Rel> Q\<close> QTrans
    obtain P' where PTrans: "\<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'" and P'RelQ': "(\<Psi>, P', Q') \<in> Rel"
      by(blast dest: weakSimE)

    note PTrans
    moreover from P'RelQ' Q'RelR' Set have "(\<Psi>, P', R') \<in> Rel''" by blast
    ultimately show ?case by blast
  qed
qed

lemma quietSim:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"

  assumes "quiet P"
  and     "eqvt Rel"
  and     cQuiet: "\<And>P. quiet P \<Longrightarrow> (\<Psi>, \<zero>, P) \<in> Rel"

  shows "\<Psi> \<rhd> \<zero> \<leadsto><Rel> P"
using \<open>eqvt Rel\<close>
proof(induct rule: weakSimI[of _ _ _ _ "()"])
  case(cAct \<Psi>' \<alpha> P')
  from \<open>\<Psi> \<rhd> P \<longmapsto>\<alpha> \<prec> P'\<close> \<open>\<alpha> \<noteq> \<tau>\<close> have False using \<open>quiet P\<close> 
    by(cases rule: actionCases[where \<alpha>=\<alpha>]) (auto intro: quietOutput quietInput)
  thus ?case by simp
next
  case(cTau P')
  from \<open>\<Psi> \<rhd> P \<longmapsto>\<tau> \<prec> P'\<close> \<open>quiet P\<close> have "quiet P'"
    by(erule_tac quiet.cases) (force simp add: residualInject)
  have "\<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P" by simp
  moreover from \<open>quiet P'\<close> have "(\<Psi>, \<zero>, P') \<in> Rel" by(rule cQuiet)
  ultimately show ?case by blast
qed


end

end


