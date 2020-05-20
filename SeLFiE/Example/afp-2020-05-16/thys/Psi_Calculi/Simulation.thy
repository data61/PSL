(* 
   Title: Psi-calculi   
   Author/Maintainer: Jesper Bengtson (jebe@itu.dk), 2012
*)
theory Simulation
  imports Semantics
begin

context env begin

definition
  "simulation" :: "'b \<Rightarrow> ('a, 'b, 'c) psi \<Rightarrow>
                   ('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set \<Rightarrow> 
                   ('a, 'b, 'c) psi \<Rightarrow> bool" ("_ \<rhd> _ \<leadsto>[_] _" [80, 80, 80, 80] 80)
where
  "\<Psi> \<rhd> P \<leadsto>[Rel] Q \<equiv> \<forall>\<alpha> Q'. \<Psi> \<rhd> Q \<longmapsto>\<alpha> \<prec> Q' \<longrightarrow> bn \<alpha> \<sharp>* \<Psi> \<longrightarrow> bn \<alpha> \<sharp>* P \<longrightarrow> (\<exists>P'. \<Psi> \<rhd> P \<longmapsto>\<alpha> \<prec> P' \<and> (\<Psi>, P', Q') \<in> Rel)"

abbreviation
  simulationNilJudge ("_ \<leadsto>[_] _" [80, 80, 80] 80) where "P \<leadsto>[Rel] Q \<equiv> SBottom' \<rhd> P \<leadsto>[Rel] Q"

lemma simI[consumes 1, case_names cSim]:
  fixes \<Psi>   :: 'b
  and   P   :: "('a, 'b, 'c) psi"
  and   Rel :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
  and   Q   :: "('a, 'b, 'c) psi"
  and   C   :: "'d::fs_name"

  assumes Eqvt: "eqvt Rel"
  and     Sim: "\<And>\<alpha> Q'. \<lbrakk>\<Psi> \<rhd> Q \<longmapsto>\<alpha> \<prec> Q'; bn \<alpha> \<sharp>* P; bn \<alpha> \<sharp>* Q; bn \<alpha>  \<sharp>* \<Psi>; distinct(bn \<alpha>);
                         bn \<alpha> \<sharp>* (subject \<alpha>); bn \<alpha> \<sharp>* C\<rbrakk> \<Longrightarrow> \<exists>P'. \<Psi> \<rhd> P \<longmapsto>\<alpha> \<prec> P' \<and> (\<Psi>, P', Q') \<in> Rel"

  shows "\<Psi> \<rhd> P \<leadsto>[Rel] Q"
proof(auto simp add: simulation_def)
  fix \<alpha> Q'
  assume "\<Psi> \<rhd> Q \<longmapsto>\<alpha> \<prec> Q'" and "bn \<alpha> \<sharp>* \<Psi>" and "bn \<alpha> \<sharp>* P"
  thus "\<exists>P'. \<Psi> \<rhd> P \<longmapsto>\<alpha> \<prec> P' \<and> (\<Psi>, P', Q') \<in> Rel"
  proof(nominal_induct \<alpha> rule: action.strong_induct)
    case(In M N)
    thus ?case by(rule_tac Sim) auto
  next
    case(Out M xvec N)
    moreover {
      fix M xvec N Q'
      assume "(xvec::name list) \<sharp>* \<Psi>" and "xvec \<sharp>* P"
      obtain p where xvecFreshPsi: "((p::name prm) \<bullet> (xvec::name list)) \<sharp>* \<Psi>"
                 and xvecFreshM: "(p \<bullet> xvec) \<sharp>* (M::'a)"
                 and xvecFreshN: "(p \<bullet> xvec) \<sharp>* (N::'a)"
                 and xvecFreshP: "(p \<bullet> xvec) \<sharp>* P"
                 and xvecFreshQ: "(p \<bullet> xvec) \<sharp>* Q"
                 and xvecFreshQ': "(p \<bullet> xvec) \<sharp>* (Q'::('a, 'b, 'c) psi)"
                 and xvecFreshC: "(p \<bullet> xvec) \<sharp>* C"
                 and xvecFreshxvec: "(p \<bullet> xvec) \<sharp>* xvec"
                 and S: "(set p) \<subseteq> (set xvec) \<times> (set(p \<bullet> xvec))"
                 and dpr: "distinctPerm p"
        by(rule_tac xvec=xvec and c="(\<Psi>, M, Q, N, P, Q', xvec, C)" in name_list_avoiding)
          (auto simp add: eqvts fresh_star_prod)

      from \<open>(p \<bullet> xvec) \<sharp>* M\<close> \<open>distinctPerm p\<close> have "xvec \<sharp>* (p \<bullet> M)"
        by(subst pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst, where pi=p, symmetric]) simp

      assume Trans: "\<Psi> \<rhd> Q \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'"
      with xvecFreshN xvecFreshQ' S
      have "\<Psi> \<rhd> Q \<longmapsto>M\<lparr>\<nu>*(p \<bullet> xvec)\<rparr>\<langle>(p \<bullet> N)\<rangle> \<prec> (p \<bullet> Q')"
        by(simp add: boundOutputChainAlpha'' residualInject)
      moreover hence "distinct(p \<bullet> xvec)"  by(auto dest: boundOutputDistinct)
      
      moreover note xvecFreshPsi xvecFreshP xvecFreshQ xvecFreshM xvecFreshC
      ultimately obtain P' where PTrans: "\<Psi> \<rhd> P \<longmapsto>M\<lparr>\<nu>*(p \<bullet> xvec)\<rparr>\<langle>(p \<bullet> N)\<rangle> \<prec> P'"
                            and P'RelQ': "(\<Psi>, P', p \<bullet> Q') \<in> Rel"
        by(drule_tac Sim) auto
      hence "(p \<bullet> \<Psi>) \<rhd> (p \<bullet> P) \<longmapsto>(p \<bullet> (M\<lparr>\<nu>*(p \<bullet> xvec)\<rparr>\<langle>(p \<bullet> N)\<rangle> \<prec> P'))"
        by(rule_tac semantics.eqvt)
      with \<open>xvec \<sharp>* \<Psi>\<close> xvecFreshPsi \<open>xvec \<sharp>* P\<close> xvecFreshP S dpr
      have "\<Psi> \<rhd> P \<longmapsto>(p \<bullet> M)\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> (p \<bullet> P')"
        by(simp add: eqvts name_set_fresh_fresh)
      with \<open>xvec \<sharp>* \<Psi>\<close> xvecFreshPsi \<open>xvec \<sharp>* P\<close> xvecFreshP S \<open>xvec \<sharp>* (p \<bullet> M)\<close>
      have "\<Psi> \<rhd> P \<longmapsto>(p \<bullet> p \<bullet> M)\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> (p \<bullet> P')"
       by(rule_tac outputPermSubject)
         (simp add: fresh_star_def | assumption)+

      with dpr have "\<Psi> \<rhd> P \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> (p \<bullet> P')"
        by simp

      moreover from P'RelQ' Eqvt have "(p \<bullet> \<Psi>, p \<bullet> P', p \<bullet> p \<bullet> Q') \<in> Rel"
        apply(simp add: eqvt_def eqvts)
        apply(erule_tac x="(\<Psi>, P', p \<bullet> Q')" in ballE)
        apply(erule_tac x="p" in allE)
        by(auto simp add: eqvts)


      with \<open>xvec \<sharp>* \<Psi>\<close> xvecFreshPsi S dpr have "(\<Psi>, p \<bullet> P', Q') \<in> Rel" by simp
      ultimately have "\<exists>P'. \<Psi> \<rhd> P \<longmapsto> M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P' \<and> (\<Psi>, P', Q') \<in> Rel"
        by blast
    }
    ultimately show ?case by force
  next
    case Tau
    thus ?case by(rule_tac Sim) auto
  qed
qed

lemma simI2[case_names cSim]:
  fixes \<Psi>   :: 'b
  and   P   :: "('a, 'b, 'c) psi"
  and   Rel :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
  and   Q   :: "('a, 'b, 'c) psi"
  and   C   :: "'d::fs_name"

  assumes Sim: "\<And>\<alpha> Q'. \<lbrakk>\<Psi> \<rhd> Q \<longmapsto>\<alpha> \<prec> Q'; bn \<alpha> \<sharp>* P; bn \<alpha>  \<sharp>* \<Psi>; distinct(bn \<alpha>)\<rbrakk> \<Longrightarrow> \<exists>P'. \<Psi> \<rhd> P \<longmapsto>\<alpha> \<prec> P' \<and> (\<Psi>, P', Q') \<in> Rel"

  shows "\<Psi> \<rhd> P \<leadsto>[Rel] Q"
using assms
by(auto simp add: simulation_def dest: boundOutputDistinct)

lemma simIChainFresh[consumes 4, case_names cSim]:
  fixes \<Psi>    :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   Rel  :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
  and   Q    :: "('a, 'b, 'c) psi"
  and   xvec :: "name list"
  and   C    :: "'d::fs_name"

  assumes Eqvt: "eqvt Rel"
  and     "xvec \<sharp>* \<Psi>"
  and     "xvec \<sharp>* P"
  and     "xvec \<sharp>* Q"
  and     Sim: "\<And>\<alpha> Q'. \<lbrakk>\<Psi> \<rhd> Q \<longmapsto>\<alpha> \<prec> Q'; bn \<alpha> \<sharp>* P; bn \<alpha> \<sharp>* Q; bn \<alpha> \<sharp>* \<Psi>;
                         bn \<alpha> \<sharp>* subject \<alpha>; distinct(bn \<alpha>); bn \<alpha> \<sharp>* C; xvec \<sharp>* \<alpha>; xvec \<sharp>* Q'\<rbrakk> \<Longrightarrow>
                         \<exists>P'. \<Psi> \<rhd> P \<longmapsto>\<alpha> \<prec> P' \<and> (\<Psi>, P', Q') \<in> Rel"
  shows "\<Psi> \<rhd> P \<leadsto>[Rel] Q"
using \<open>eqvt Rel\<close>
proof(induct rule: simI[where C="(xvec, C)"])
  case(cSim \<alpha> Q')
  from \<open>bn \<alpha> \<sharp>* (xvec, C)\<close> have "bn \<alpha> \<sharp>* xvec" and "bn \<alpha> \<sharp>* C" by(simp add: freshChainSym)+ 
  obtain p::"name prm" where "(p \<bullet> xvec) \<sharp>* \<Psi>" and  "(p \<bullet> xvec) \<sharp>* P" and  "(p \<bullet> xvec) \<sharp>* Q"
                         and  "(p \<bullet> xvec) \<sharp>* \<alpha>" and S: "set p \<subseteq> set xvec \<times> set(p \<bullet> xvec)"
                         and "distinctPerm p"
    by(rule_tac c="(\<Psi>, P, Q, \<alpha>)" and xvec=xvec in name_list_avoiding) auto
  show ?case
  proof(cases rule: actionCases[where \<alpha>=\<alpha>])
    case(cInput M N)
    from \<open>\<Psi> \<rhd> Q \<longmapsto>\<alpha> \<prec> Q'\<close> \<open>\<alpha>=M\<lparr>N\<rparr>\<close> have "(p \<bullet> \<Psi>) \<rhd> (p \<bullet> Q) \<longmapsto>(p \<bullet> (M\<lparr>N\<rparr> \<prec> Q'))"
      by(fastforce intro: semantics.eqvt)
    with \<open>xvec \<sharp>* \<Psi>\<close> \<open>(p \<bullet> xvec) \<sharp>* \<Psi>\<close> \<open>xvec \<sharp>* Q\<close> \<open>(p \<bullet> xvec) \<sharp>* Q\<close> S
    have QTrans: "\<Psi> \<rhd> Q \<longmapsto>(p \<bullet> M)\<lparr>(p \<bullet> N)\<rparr> \<prec> (p \<bullet> Q')"
      by(simp add: eqvts)
    moreover from \<open>(p \<bullet> xvec) \<sharp>* \<alpha>\<close> have "(p \<bullet> (p \<bullet> xvec)) \<sharp>* (p \<bullet> \<alpha>)"
      by(simp only: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])  
    with \<open>distinctPerm p\<close> \<open>\<alpha>=M\<lparr>N\<rparr>\<close> have "xvec \<sharp>* (p \<bullet> M)" and "xvec \<sharp>* (p \<bullet> N)" by simp+
    moreover with QTrans \<open>xvec \<sharp>* Q\<close> have "xvec \<sharp>* (p \<bullet> Q')" by(rule_tac inputFreshChainDerivative)
    ultimately have "\<exists>P'. \<Psi> \<rhd> P \<longmapsto> (p \<bullet> M)\<lparr>(p \<bullet> N)\<rparr> \<prec> P' \<and> (\<Psi>, P', (p \<bullet> Q')) \<in> Rel"
      by(rule_tac Sim) (assumption | simp)+
    then obtain P' where PTrans: "\<Psi> \<rhd> P \<longmapsto> (p \<bullet> M)\<lparr>(p \<bullet> N)\<rparr> \<prec> P'" and P'RelQ': "(\<Psi>, P', (p \<bullet> Q')) \<in> Rel"
      by blast
    from PTrans have "(p \<bullet> \<Psi>) \<rhd> (p \<bullet> P) \<longmapsto> (p \<bullet> ((p \<bullet> M)\<lparr>(p \<bullet> N)\<rparr> \<prec> P'))"
      by(rule semantics.eqvt)
    with \<open>xvec \<sharp>* \<Psi>\<close> \<open>(p \<bullet> xvec) \<sharp>* \<Psi>\<close> \<open>xvec \<sharp>* P\<close> \<open>(p \<bullet> xvec) \<sharp>* P\<close> S \<open>distinctPerm p\<close>
    have "\<Psi> \<rhd> P \<longmapsto> M\<lparr>N\<rparr> \<prec> (p \<bullet> P')" by(simp add: eqvts)
    moreover from P'RelQ' \<open>eqvt Rel\<close> have "(p \<bullet> \<Psi>, p \<bullet> P', p \<bullet> p \<bullet> Q') \<in> Rel"
      by(auto simp add: eqvt_def)
    with \<open>xvec \<sharp>* \<Psi>\<close> \<open>(p \<bullet> xvec) \<sharp>* \<Psi>\<close> S \<open>distinctPerm p\<close>
    have "(\<Psi>, p \<bullet> P', Q') \<in> Rel" by simp
    ultimately show ?thesis using \<open>\<alpha>=M\<lparr>N\<rparr>\<close> by blast
  next
    case(cOutput M yvec N)
    from \<open>distinct(bn \<alpha>)\<close> \<open>bn \<alpha> \<sharp>* subject \<alpha>\<close> \<open>\<alpha>=M\<lparr>\<nu>*yvec\<rparr>\<langle>N\<rangle>\<close> have "distinct yvec" and "yvec \<sharp>* M" by simp+
    from \<open>\<Psi> \<rhd> Q \<longmapsto>\<alpha> \<prec> Q'\<close> \<open>\<alpha>=M\<lparr>\<nu>*yvec\<rparr>\<langle>N\<rangle>\<close> have "(p \<bullet> \<Psi>) \<rhd> (p \<bullet> Q) \<longmapsto>(p \<bullet> (M\<lparr>\<nu>*yvec\<rparr>\<langle>N\<rangle> \<prec> Q'))"
      by(fastforce intro: semantics.eqvt)
    with \<open>xvec \<sharp>* \<Psi>\<close> \<open>(p \<bullet> xvec) \<sharp>* \<Psi>\<close> \<open>xvec \<sharp>* Q\<close> \<open>(p \<bullet> xvec) \<sharp>* Q\<close> S
    have QTrans: "\<Psi> \<rhd> Q \<longmapsto>(p \<bullet> M)\<lparr>\<nu>*(p \<bullet> yvec)\<rparr>\<langle>(p \<bullet> N)\<rangle> \<prec> (p \<bullet> Q')"
      by(simp add: eqvts)
    with S \<open>bn \<alpha> \<sharp>* xvec\<close> \<open>(p \<bullet> xvec) \<sharp>* \<alpha>\<close> \<open>\<alpha>=M\<lparr>\<nu>*yvec\<rparr>\<langle>N\<rangle>\<close> have "\<Psi> \<rhd> Q \<longmapsto>(p \<bullet> M)\<lparr>\<nu>*yvec\<rparr>\<langle>(p \<bullet> N)\<rangle> \<prec> (p \<bullet> Q')"
      by simp
    moreover from \<open>(p \<bullet> xvec) \<sharp>* \<alpha>\<close> have "(p \<bullet> (p \<bullet> xvec)) \<sharp>* (p \<bullet> \<alpha>)"
      by(simp only: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])  
    with \<open>distinctPerm p\<close> \<open>\<alpha>=M\<lparr>\<nu>*yvec\<rparr>\<langle>N\<rangle>\<close> have "xvec \<sharp>* (p \<bullet> M)" and "xvec \<sharp>* (p \<bullet> N)" and "xvec \<sharp>* (p \<bullet> yvec)" by simp+
    moreover with QTrans \<open>xvec \<sharp>* Q\<close> \<open>distinct yvec\<close> \<open>yvec \<sharp>* M\<close> have "xvec \<sharp>* (p \<bullet> Q')"
      by(drule_tac outputFreshChainDerivative(2)) (auto simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
    moreover from \<open>yvec \<sharp>* M\<close> S \<open>bn \<alpha> \<sharp>* xvec\<close> \<open>(p \<bullet> xvec) \<sharp>* \<alpha>\<close> \<open>\<alpha>=M\<lparr>\<nu>*yvec\<rparr>\<langle>N\<rangle>\<close> \<open>distinctPerm p\<close>
    have "yvec \<sharp>* (p \<bullet> M)" by(subst pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst, symmetric, where pi=p]) simp
    ultimately have "\<exists>P'. \<Psi> \<rhd> P \<longmapsto> (p \<bullet> M)\<lparr>\<nu>*yvec\<rparr>\<langle>(p \<bullet> N)\<rangle> \<prec> P' \<and> (\<Psi>, P', (p \<bullet> Q')) \<in> Rel"
      using \<open>bn \<alpha> \<sharp>* \<Psi>\<close> \<open>bn \<alpha> \<sharp>* P\<close> \<open>bn \<alpha> \<sharp>* Q\<close>\<open>bn \<alpha> \<sharp>* xvec\<close> \<open>bn \<alpha> \<sharp>* C\<close> \<open>yvec \<sharp>* M\<close> \<open>\<alpha>=M\<lparr>\<nu>*yvec\<rparr>\<langle>N\<rangle>\<close> \<open>distinct yvec\<close>
      by(rule_tac Sim) auto
    then obtain P' where PTrans: "\<Psi> \<rhd> P \<longmapsto> (p \<bullet> M)\<lparr>\<nu>*yvec\<rparr>\<langle>(p \<bullet> N)\<rangle> \<prec> P'" and P'RelQ': "(\<Psi>, P', (p \<bullet> Q')) \<in> Rel"
      by blast
    from PTrans have "(p \<bullet> \<Psi>) \<rhd> (p \<bullet> P) \<longmapsto> (p \<bullet> ((p \<bullet> M)\<lparr>\<nu>*yvec\<rparr>\<langle>(p \<bullet> N)\<rangle> \<prec> P'))"
      by(rule semantics.eqvt)
    with \<open>xvec \<sharp>* \<Psi>\<close> \<open>(p \<bullet> xvec) \<sharp>* \<Psi>\<close> \<open>xvec \<sharp>* P\<close> \<open>(p \<bullet> xvec) \<sharp>* P\<close> S \<open>distinctPerm p\<close> \<open>bn \<alpha> \<sharp>* xvec\<close> \<open>(p \<bullet> xvec) \<sharp>* \<alpha>\<close> \<open>\<alpha>=M\<lparr>\<nu>*yvec\<rparr>\<langle>N\<rangle>\<close>
    have "\<Psi> \<rhd> P \<longmapsto> M\<lparr>\<nu>*yvec\<rparr>\<langle>N\<rangle> \<prec> (p \<bullet> P')" by(simp add: eqvts)
    moreover from P'RelQ' \<open>eqvt Rel\<close> have "(p \<bullet> \<Psi>, p \<bullet> P', p \<bullet> p \<bullet> Q') \<in> Rel"
      by(auto simp add: eqvt_def)
    with \<open>xvec \<sharp>* \<Psi>\<close> \<open>(p \<bullet> xvec) \<sharp>* \<Psi>\<close> S \<open>distinctPerm p\<close>
    have "(\<Psi>, p \<bullet> P', Q') \<in> Rel" by simp
    ultimately show ?thesis using \<open>\<alpha>=M\<lparr>\<nu>*yvec\<rparr>\<langle>N\<rangle>\<close> by blast
  next
    case cTau
    from \<open>\<Psi> \<rhd> Q \<longmapsto>\<alpha> \<prec> Q'\<close> \<open>\<alpha> = \<tau>\<close> \<open>xvec \<sharp>* Q\<close> have "xvec \<sharp>* Q'"
      by(blast dest: tauFreshChainDerivative)
    with \<open>\<Psi> \<rhd> Q \<longmapsto>\<alpha> \<prec> Q'\<close> \<open>\<alpha> = \<tau>\<close> 
    show ?thesis by(drule_tac Sim) auto
  qed
qed

lemma simIFresh[consumes 4, case_names cSim]:
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
  and     "\<And>\<alpha> Q'. \<lbrakk>\<Psi> \<rhd> Q \<longmapsto>\<alpha> \<prec> Q'; bn \<alpha> \<sharp>* P; bn \<alpha> \<sharp>* Q; bn \<alpha> \<sharp>* \<Psi>;
                    bn \<alpha> \<sharp>* subject \<alpha>; distinct(bn \<alpha>); bn \<alpha> \<sharp>* C; x \<sharp> \<alpha>; x \<sharp> Q'\<rbrakk> \<Longrightarrow>
                    \<exists>P'. \<Psi> \<rhd> P \<longmapsto>\<alpha> \<prec> P' \<and> (\<Psi>, P', Q') \<in> Rel"

  shows "\<Psi> \<rhd> P \<leadsto>[Rel] Q"
using assms
by(rule_tac xvec="[x]" and C=C in simIChainFresh) auto

lemma simE:
  fixes F   :: 'b
  and   P   :: "('a, 'b, 'c) psi"
  and   Rel :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
  and   Q   :: "('a, 'b, 'c) psi"

  assumes "\<Psi> \<rhd> P \<leadsto>[Rel] Q"

  shows "\<And>\<alpha> Q'. \<lbrakk>\<Psi> \<rhd> Q \<longmapsto>\<alpha> \<prec> Q'; bn \<alpha> \<sharp>* \<Psi>; bn \<alpha> \<sharp>* P\<rbrakk> \<Longrightarrow> \<exists>P'. \<Psi> \<rhd> P \<longmapsto>\<alpha> \<prec> P' \<and> (\<Psi>, P', Q') \<in> Rel"
using assms
by(auto simp add: simulation_def)

lemma simClosedAux:
  fixes \<Psi>   :: 'b
  and   P   :: "('a, 'b, 'c) psi"
  and   Rel :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
  and   Q   :: "('a, 'b, 'c) psi"
  and   p   :: "name prm"

  assumes EqvtRel: "eqvt Rel"
  and     PSimQ: "\<Psi> \<rhd> P \<leadsto>[Rel] Q"

  shows "(p \<bullet> \<Psi>) \<rhd> (p \<bullet> P) \<leadsto>[Rel] (p \<bullet> Q)"
using EqvtRel
proof(induct rule: simI[of _ _ _ _ "(\<Psi>, P, p)"])
  case(cSim \<alpha> Q')
  from \<open>p \<bullet> \<Psi> \<rhd> p \<bullet> Q \<longmapsto>\<alpha> \<prec> Q'\<close> 
  have "(rev p \<bullet> p \<bullet> \<Psi>) \<rhd> (rev p \<bullet> p \<bullet> Q) \<longmapsto>(rev p \<bullet> (\<alpha> \<prec> Q'))"
    by(blast dest: semantics.eqvt)
  hence "\<Psi> \<rhd> Q \<longmapsto>(rev p \<bullet> \<alpha>) \<prec> (rev p \<bullet> Q')"
    by(simp add: eqvts)
  moreover with \<open>bn \<alpha> \<sharp>* (\<Psi>, P, p)\<close> have "bn \<alpha> \<sharp>* \<Psi>" and "bn \<alpha> \<sharp>* P" and "bn \<alpha> \<sharp>* p" by simp+
  ultimately obtain P' where PTrans: "\<Psi> \<rhd> P \<longmapsto>(rev p \<bullet> \<alpha>) \<prec> P'"
                         and P'RelQ': "(\<Psi>, P', rev p \<bullet> Q') \<in> Rel"
    using PSimQ
    by(force dest: simE freshChainPermSimp simp add: eqvts)
  from PTrans have "(p \<bullet> \<Psi>) \<rhd> (p \<bullet> P) \<longmapsto>(p \<bullet> ((rev p \<bullet> \<alpha>) \<prec> P'))"
    by(rule semantics.eqvt)
  with \<open>bn \<alpha> \<sharp>* p\<close> have "(p \<bullet> \<Psi>) \<rhd> (p \<bullet> P) \<longmapsto>\<alpha> \<prec> (p \<bullet> P')"
    by(simp add: eqvts freshChainPermSimp)
  moreover from P'RelQ' EqvtRel have "(p \<bullet> (\<Psi>, P', rev p \<bullet> Q')) \<in> Rel"
    by(simp only: eqvt_def)
  hence "(p \<bullet> \<Psi>, p \<bullet> P', Q') \<in> Rel" by simp
  ultimately show ?case by blast
qed

lemma simClosed:
  fixes \<Psi>   :: 'b
  and   P   :: "('a, 'b, 'c) psi"
  and   Rel :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
  and   Q   :: "('a, 'b, 'c) psi"
  and   p   :: "name prm"

  assumes EqvtRel: "eqvt Rel"

  shows "\<Psi> \<rhd> P \<leadsto>[Rel] Q \<Longrightarrow> (p \<bullet> \<Psi>) \<rhd> (p \<bullet> P) \<leadsto>[Rel] (p \<bullet> Q)"
  and   "P \<leadsto>[Rel] Q \<Longrightarrow> (p \<bullet> P) \<leadsto>[Rel] (p \<bullet> Q)"
using EqvtRel
by(force dest: simClosedAux simp add: permBottom)+

lemma reflexive:
  fixes Rel :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
  and   \<Psi>   :: 'b
  and   P   :: "('a, 'b, 'c) psi"

  assumes "{(\<Psi>, P, P) | \<Psi> P. True} \<subseteq> Rel"

  shows "\<Psi> \<rhd> P \<leadsto>[Rel] P"
using assms
by(auto simp add: simulation_def)

lemma transitive:
  fixes \<Psi>     :: 'b
  and   P     :: "('a, 'b, 'c) psi"
  and   Rel   :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
  and   Q     :: "('a, 'b, 'c) psi"
  and   Rel'  :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
  and   R     :: "('a, 'b, 'c) psi"
  and   Rel'' :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"

  assumes PSimQ: "\<Psi> \<rhd> P \<leadsto>[Rel] Q"
  and     QSimR: "\<Psi> \<rhd> Q \<leadsto>[Rel'] R"
  and     Eqvt: "eqvt Rel''"
  and     Set: "{(\<Psi>, P, R) | \<Psi> P R. \<exists>Q. (\<Psi>, P, Q) \<in> Rel \<and> (\<Psi>, Q, R) \<in> Rel'} \<subseteq> Rel''"

  shows "\<Psi> \<rhd> P \<leadsto>[Rel''] R"
using \<open>eqvt Rel''\<close>
proof(induct rule: simI[where C=Q])
  case(cSim \<alpha> R')
  from QSimR \<open>\<Psi> \<rhd> R \<longmapsto>\<alpha> \<prec> R'\<close> \<open>(bn \<alpha>) \<sharp>* \<Psi>\<close> \<open>(bn \<alpha>) \<sharp>* Q\<close>
  obtain Q' where QTrans: "\<Psi> \<rhd> Q \<longmapsto>\<alpha> \<prec> Q'" and Q'Rel'R': "(\<Psi>, Q', R') \<in> Rel'"
    by(blast dest: simE)
  from PSimQ QTrans \<open>bn \<alpha> \<sharp>* \<Psi>\<close> \<open>bn \<alpha> \<sharp>* P\<close>
  obtain P' where PTrans: "\<Psi> \<rhd> P \<longmapsto>\<alpha> \<prec> P'" and P'RelQ': "(\<Psi>, P', Q') \<in> Rel"
    by(blast dest: simE)
  with PTrans Q'Rel'R' P'RelQ' Set
  show ?case by blast
qed

lemma statEqSim:
  fixes \<Psi>   :: 'b
  and   P   :: "('a, 'b, 'c) psi"
  and   Rel :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
  and   Q   :: "('a, 'b, 'c) psi"
  and   \<Psi>'  :: 'b

  assumes PSimQ: "\<Psi> \<rhd> P \<leadsto>[Rel] Q"
  and     "eqvt Rel'"
  and     "\<Psi> \<simeq> \<Psi>'"
  and     C1: "\<And>\<Psi>'' R S \<Psi>'''. \<lbrakk>(\<Psi>'', R, S) \<in> Rel; \<Psi>'' \<simeq> \<Psi>'''\<rbrakk> \<Longrightarrow> (\<Psi>''', R, S) \<in> Rel'"

  shows "\<Psi>' \<rhd> P \<leadsto>[Rel'] Q"
using \<open>eqvt Rel'\<close>
proof(induct rule: simI[of _ _ _ _ \<Psi>])
  case(cSim \<alpha> Q')
  from \<open>\<Psi>' \<rhd> Q \<longmapsto>\<alpha> \<prec> Q'\<close> \<open>\<Psi> \<simeq> \<Psi>'\<close>
  have "\<Psi> \<rhd> Q \<longmapsto>\<alpha> \<prec> Q'" by(metis statEqTransition AssertionStatEqSym)
  with PSimQ \<open>bn \<alpha> \<sharp>* \<Psi>\<close> \<open>bn \<alpha> \<sharp>* P\<close>
  obtain P' where "\<Psi> \<rhd> P \<longmapsto>\<alpha> \<prec> P'" and "(\<Psi>, P', Q') \<in> Rel"
    by(blast dest: simE)
  
  from \<open>\<Psi> \<rhd> P \<longmapsto>\<alpha> \<prec> P'\<close> \<open>\<Psi> \<simeq> \<Psi>'\<close> have "\<Psi>' \<rhd> P \<longmapsto>\<alpha> \<prec> P'"
    by(rule statEqTransition)
  moreover from \<open>(\<Psi>, P', Q') \<in> Rel\<close> \<open>\<Psi> \<simeq> \<Psi>'\<close> have "(\<Psi>', P', Q') \<in> Rel'"
    by(rule C1)
  ultimately show ?case by blast
qed

lemma monotonic: 
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   A :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
  and   Q :: "('a, 'b, 'c) psi"
  and   B :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"

  assumes "\<Psi> \<rhd> P \<leadsto>[A] Q"
  and     "A \<subseteq> B"

  shows "\<Psi> \<rhd> P \<leadsto>[B] Q"
using assms
by(simp (no_asm) add: simulation_def) (auto dest: simE)

end

end

