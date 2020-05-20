(* 
   Title: Psi-calculi   
   Author/Maintainer: Jesper Bengtson (jebe@itu.dk), 2012
*)
theory Tau_Laws_Weak
  imports Weaken_Bisimulation Weak_Congruence Tau_Sim Tau_Stat_Imp
begin

context weakTauLaws begin

lemma tauLaw1:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  
  shows "\<Psi> \<rhd> \<tau>.(P) \<approx> P"
proof - 
  let ?X = "{(\<Psi>, \<tau>.(P), P) | \<Psi> P. True}" let ?Y = "{(\<Psi>, P, \<tau>.(P)) | \<Psi> P. True}"
  have "(\<Psi>, \<tau>.(P), P) \<in> ?X \<union> ?Y" by auto
  moreover have "eqvt(?X \<union> ?Y)" by(auto simp add: eqvt_def simp add: eqvts)
  ultimately have "\<Psi> \<rhd> \<tau>.(P) \<approx>\<^sub>w P"
  proof(coinduct rule: weakenTransitiveCoinduct)
    case(cStatImp \<Psi> P Q)
    show ?case
    proof(cases "(\<Psi>, P, Q) \<in> ?X")
      case True
      {
        fix \<Psi> P
        have "\<Psi> \<rhd> P \<lessapprox>\<^sub>w<(?X \<union> ?Y \<union> weakBisim)> P" by(auto simp add: weakenStatImp_def intro: weakBisimReflexive)
        moreover have "(\<Psi>, \<tau>.(P), P) \<in> ?X \<union> ?Y \<union> weakBisim" by auto
        ultimately have "\<Psi> \<rhd> \<tau>.(P) \<lessapprox>\<^sub>w<(?X \<union> ?Y \<union> weakBisim)> P"
          by(rule tauLaw1StatImpLeft)
      }
      with \<open>(\<Psi>, P, Q) \<in> ?X\<close> show ?thesis by auto 
    next
      case False
      from \<open>(\<Psi>, P, Q) \<notin> ?X\<close> \<open>(\<Psi>, P, Q) \<in> ?X \<union> ?Y\<close> have "(\<Psi>, P, Q) \<in> ?Y" by auto
      {
        fix \<Psi> P
        have "\<Psi> \<rhd> P \<lessapprox><weakBisim> P" using weakBisimReflexive
          by(rule weakBisimE)
        moreover have "\<And>\<Psi> P Q R. \<lbrakk>\<Psi> \<rhd> P \<approx> Q; \<Psi> \<rhd> Q \<sim> R\<rbrakk> \<Longrightarrow> (\<Psi>, P, R) \<in> ?X \<union> ?Y \<union> weakBisim"
          by(fastforce intro: weakBisimTransitive strongBisimWeakBisim)
        ultimately have  "\<Psi> \<rhd> P \<lessapprox><( ?X \<union> ?Y \<union> weakBisim)> \<tau>.(P)" by(rule tauLaw1StatImpRight)
        moreover have "\<And>\<Psi> P Q \<Psi>'. \<lbrakk>(\<Psi>, P, Q) \<in> ?X \<union> ?Y \<union> weakBisim; \<Psi> \<simeq> \<Psi>'\<rbrakk> \<Longrightarrow> (\<Psi>', P, Q) \<in> ?X \<union> ?Y \<union> weakBisim"
          by(auto dest: statEqWeakBisim)
        ultimately have "\<Psi> \<rhd> P \<lessapprox>\<^sub>w<( ?X \<union> ?Y \<union> weakBisim)> \<tau>.(P)" by(rule weakStatImpWeakenStatImp)
      }
      with \<open>(\<Psi>, P, Q) \<in> ?Y\<close> show ?thesis by auto
    qed
  next
    case(cSim \<Psi> P Q)
    let ?Z = "{(\<Psi>, P, Q) | \<Psi> P Q. \<exists>P' Q'. \<Psi> \<rhd> P \<sim> P' \<and> (\<Psi>, P', Q') \<in> ?X \<union> ?Y \<union> weakenBisim \<and> \<Psi> \<rhd> Q' \<sim> Q}"
    have "eqvt ?Z" 
      apply auto
      apply(auto simp add: eqvt_def eqvts)
      apply(rule_tac x="(p \<bullet> (\<tau>.(Q')))" in exI)
      apply(auto intro: bisimClosed)
      apply(simp add: eqvts)
      apply(blast intro: bisimClosed weakBisimClosed)
      apply(rule_tac x="(p \<bullet> P')" in exI)
      apply(auto intro: bisimClosed)
      apply(rule_tac x="\<tau>.(p \<bullet> P')" in exI)
      apply auto
      apply(drule_tac p=p and Q=b in bisimClosed)
      apply(simp add: eqvts)
      apply(rule_tac x="(p \<bullet> P')" in exI)
      apply(auto intro: bisimClosed)
      apply(rule_tac x="p \<bullet> Q'" in exI)
      apply auto
      by(blast intro: bisimClosed dest: weakBisimClosed)+
    show ?case
    proof(cases "(\<Psi>, P, Q) \<in> ?X")
      case True
      {
        fix P
        have "\<Psi> \<rhd> P \<leadsto><?Z> P" using weakenBisimEqWeakBisim by(blast intro: weakSimReflexive weakBisimReflexive bisimReflexive)
        moreover note \<open>eqvt ?Z\<close>
        moreover have "\<And>\<Psi> P Q R. \<lbrakk>\<Psi> \<rhd> P \<sim> Q; (\<Psi>, Q, R) \<in> ?Z\<rbrakk> \<Longrightarrow> (\<Psi>, P, R) \<in> ?Z"
          by(blast intro: bisimTransitive)
        ultimately have "\<Psi> \<rhd> \<tau>.(P) \<leadsto><?Z> P"
          by(rule tauLaw1SimLeft)
        moreover have "\<And>\<Psi> P Q \<Psi>'. \<lbrakk>(\<Psi>, P, Q) \<in> ?Z; \<Psi> \<simeq> \<Psi>'\<rbrakk> \<Longrightarrow> (\<Psi>', P, Q) \<in> ?Z"
          by simp (blast intro: statEqWeakBisim statEqBisim)
        ultimately have "\<Psi> \<rhd> \<tau>.(P) \<leadsto>\<^sub>w<?Z> P" by(rule weakSimWeakenSim)
      }
      with \<open>(\<Psi>, P, Q) \<in> ?X\<close> show ?thesis by auto
    next
      case False
      from \<open>(\<Psi>, P, Q) \<notin> ?X\<close> \<open>(\<Psi>, P, Q) \<in> ?X \<union> ?Y\<close> have "(\<Psi>, P, Q) \<in> ?Y" by auto
      moreover {
        fix P
        note \<open>eqvt ?Z\<close>  
        moreover have "(\<Psi>, P, P) \<in> ?Z" by simp (blast intro: weakBisimReflexive bisimReflexive)
        moreover have "\<And>\<Psi> P Q R. \<lbrakk>(\<Psi>, P, Q) \<in> ?Z; \<Psi> \<rhd> Q \<sim> R\<rbrakk> \<Longrightarrow> (\<Psi>, P, R) \<in> ?Z"
          by(blast intro: bisimTransitive)
        ultimately have "\<Psi> \<rhd> P \<leadsto><?Z> \<tau>.(P)" by(rule tauLaw1SimRight)
        moreover have "\<And>\<Psi> P Q \<Psi>'. \<lbrakk>(\<Psi>, P, Q) \<in> ?Z; \<Psi> \<simeq> \<Psi>'\<rbrakk> \<Longrightarrow> (\<Psi>', P, Q) \<in> ?Z"
          by simp (blast intro: statEqWeakBisim statEqBisim)
        ultimately have "\<Psi> \<rhd> P \<leadsto>\<^sub>w<?Z> \<tau>.(P)" by(rule weakSimWeakenSim)
      }
      ultimately show ?thesis by auto
    qed
  next
    case(cExt \<Psi> P Q \<Psi>')
    thus ?case by auto
  next
    case(cSym \<Psi> P Q)
    thus ?case by auto
  qed
  thus ?thesis by simp
qed

lemma tauLaw3:
  fixes \<Psi> :: 'b
  and   \<alpha> :: "'a prefix"
  and   P :: "('a, 'b, 'c) psi"

  shows "\<Psi> \<rhd> \<alpha>\<cdot>(\<tau>.(P)) \<approx> \<alpha>\<cdot>P"
proof -
  let ?X = "({(\<Psi>, \<alpha>\<cdot>(\<tau>.(P)), \<alpha>\<cdot>P) | \<Psi> \<alpha> P. True})"
  let ?Y = "({(\<Psi>, \<alpha>\<cdot>P, \<alpha>\<cdot>(\<tau>.(P))) | \<Psi> \<alpha> P. True})"

  have "(\<Psi>, \<alpha>\<cdot>(\<tau>.(P)), \<alpha>\<cdot>P) \<in> ?X \<union> ?Y" by blast
  moreover have "eqvt(?X \<union> ?Y)" by(fastforce simp add: eqvt_def simp add: eqvts)
  ultimately have "\<Psi> \<rhd> \<alpha>\<cdot>(\<tau>.(P)) \<approx>\<^sub>w \<alpha>\<cdot>P"
  proof(coinduct rule: weakenTransitiveCoinduct)
    case(cStatImp \<Psi> P Q)
    show ?case
    proof(cases "(\<Psi>, P, Q) \<in> ?X")
      case True
      {
        fix \<Psi> \<alpha> P
        have "\<And>\<Psi>'. (\<Psi> \<otimes> \<Psi>', \<alpha>\<cdot>(\<tau>.(P)), \<alpha>\<cdot>P) \<in> ?X \<union> ?Y \<union> weakenBisim" by auto
        hence "\<Psi> \<rhd> \<alpha>\<cdot>(\<tau>.(P)) \<lessapprox><(?X \<union> ?Y \<union> weakenBisim)> \<alpha>\<cdot>P" by(rule tauLaw3StatImpLeft)
        moreover have "\<And>\<Psi> P Q \<Psi>'. \<lbrakk>(\<Psi>, P, Q) \<in> ?X \<union> ?Y \<union> weakenBisim; \<Psi> \<simeq> \<Psi>'\<rbrakk> \<Longrightarrow> (\<Psi>', P, Q) \<in> ?X \<union> ?Y \<union> weakenBisim"
          by(fastforce intro: statEqWeakBisim)
        ultimately have "\<Psi> \<rhd> \<alpha>\<cdot>(\<tau>.(P)) \<lessapprox>\<^sub>w<(?X \<union> ?Y \<union> weakenBisim)> \<alpha>\<cdot>P" by(rule weakStatImpWeakenStatImp)
      }
      with \<open>(\<Psi>, P, Q) \<in> ?X\<close> show ?thesis by blast
    next
      case False
      {
        fix \<Psi> \<alpha> P
        have "\<And>\<Psi>'. (\<Psi> \<otimes> \<Psi>', \<alpha>\<cdot>P, \<alpha>\<cdot>(\<tau>.(P))) \<in> ?X \<union> ?Y \<union> weakenBisim" by auto
        hence "\<Psi> \<rhd> \<alpha>\<cdot>P \<lessapprox><(?X \<union> ?Y \<union> weakenBisim)> \<alpha>\<cdot>(\<tau>.(P))" by(rule tauLaw3StatImpRight)
        moreover have "\<And>\<Psi> P Q \<Psi>'. \<lbrakk>(\<Psi>, P, Q) \<in> ?X \<union> ?Y \<union> weakenBisim; \<Psi> \<simeq> \<Psi>'\<rbrakk> \<Longrightarrow> (\<Psi>', P, Q) \<in> ?X \<union> ?Y \<union> weakenBisim"
          by(fastforce intro: statEqWeakBisim)
        ultimately have "\<Psi> \<rhd> \<alpha>\<cdot>P \<lessapprox>\<^sub>w<(?X \<union> ?Y \<union> weakenBisim)> \<alpha>\<cdot>(\<tau>.(P))" by(rule weakStatImpWeakenStatImp)
      }
      moreover from \<open>(\<Psi>, P, Q) \<notin> ?X\<close> \<open>(\<Psi>, P, Q) \<in> ?X \<union> ?Y\<close> have "(\<Psi>, P, Q) \<in> ?Y" by blast
      ultimately show ?thesis by auto
    qed
  next
    case(cSim \<Psi> P Q)
    let ?Z = "{(\<Psi>, P, Q) | \<Psi> P Q. \<exists>P' Q'. \<Psi> \<rhd> P \<sim> P' \<and> (\<Psi>, P', Q') \<in> ?X \<union> ?Y \<union> weakenBisim \<and> \<Psi> \<rhd> Q' \<sim> Q}"
    have "eqvt ?Z" 
      apply(clarsimp simp add: eqvt_def)
      apply(elim disjE)
      apply(rule_tac x="p \<bullet> P'" in exI)
      apply(clarsimp simp add: bisimClosed eqvts)
      apply(blast intro: bisimClosed eqvts)
      apply(rule_tac x="p \<bullet> P'" in exI)
      apply(clarsimp simp add: bisimClosed eqvts)
      apply(rule_tac x="p \<bullet> (\<alpha>\<cdot>(\<tau>.(P)))" in exI)
      apply(clarsimp simp add: eqvts)
      apply(rule conjI)
      apply(rule disjI2)
      apply(blast intro: bisimClosed eqvts)
      apply(drule_tac p=p in bisimClosed)
      apply(drule_tac p=p in bisimClosed)
      apply(simp add: eqvts)
      by(blast dest: bisimClosed weakBisimClosed)
    show ?case
    proof(cases "(\<Psi>, P, Q) \<in> ?X")
      case True
      note \<open>(\<Psi>, P, Q) \<in> ?X\<close>
      moreover {
        fix \<Psi> P \<alpha>
        note \<open>eqvt ?Z\<close>
        moreover have "(\<Psi>, P, P) \<in> ?Z" using weakenBisimEqWeakBisim by(blast intro: weakBisimReflexive bisimReflexive)
        moreover have "\<And>xvec Tvec. length xvec = length Tvec \<Longrightarrow> (\<Psi>, P[xvec::=Tvec], P[xvec::=Tvec]) \<in> ?Z"
           using weakenBisimEqWeakBisim by(blast intro: weakBisimReflexive bisimReflexive)
        moreover have "\<And>\<Psi> P Q R S. \<lbrakk>\<Psi> \<rhd> P \<sim> Q; (\<Psi>, Q, R) \<in> ?Z; \<Psi> \<rhd> R \<sim> S\<rbrakk> \<Longrightarrow> (\<Psi>, P, S) \<in> ?Z" by(blast intro: bisimTransitive)
        moreover have "\<And>\<Psi> P Q \<Psi>'. (\<Psi>, P, Q) \<in> ?Z \<Longrightarrow> (\<Psi> \<otimes> \<Psi>', P, Q) \<in> ?Z" by(blast dest: weakenBisimE(3) bisimE(3))
        ultimately have "\<Psi> \<rhd> \<alpha>\<cdot>(\<tau>.(P)) \<leadsto><?Z> \<alpha>\<cdot>P" by(rule tauLaw3SimLeft)
        moreover have "\<And>\<Psi> P Q \<Psi>'. \<lbrakk>(\<Psi>, P, Q) \<in> ?Z; \<Psi> \<simeq> \<Psi>'\<rbrakk> \<Longrightarrow> (\<Psi>', P, Q) \<in> ?Z" by simp (blast dest: statEqWeakBisim statEqBisim)
        ultimately have "\<Psi> \<rhd> \<alpha>\<cdot>(\<tau>.(P)) \<leadsto>\<^sub>w<?Z> \<alpha>\<cdot>P" by(rule weakSimWeakenSim)
      }
      ultimately show ?thesis by auto
    next
      case False
      from \<open>(\<Psi>, P, Q) \<notin> ?X\<close> \<open>(\<Psi>, P, Q) \<in> ?X \<union> ?Y\<close> have "(\<Psi>, P, Q) \<in> ?Y" by blast
      moreover {
        fix \<Psi> P \<alpha>
        note \<open>eqvt ?Z\<close>
        moreover have "\<And>\<Psi> xvec Tvec. length xvec=length Tvec \<Longrightarrow> (\<Psi>, P[xvec::=Tvec], \<tau>.(P[xvec::=Tvec])) \<in> ?Z"
          by simp (blast intro: weakBisimE(4) bisimReflexive tauLaw1)
        moreover have "\<And>\<Psi> P Q R S. \<lbrakk>\<Psi> \<rhd> P \<sim> Q; (\<Psi>, Q, R) \<in> ?Z; \<Psi> \<rhd> R \<sim> S\<rbrakk> \<Longrightarrow> (\<Psi>, P, S) \<in> ?Z" by(blast intro: bisimTransitive)
        moreover have "\<And>\<Psi>. (\<Psi>, P, \<tau>.(P)) \<in> ?Z" by simp (blast intro: weakBisimE(4) bisimReflexive tauLaw1)
        ultimately have "\<Psi> \<rhd> \<alpha>\<cdot>P \<leadsto><?Z> \<alpha>\<cdot>(\<tau>.(P))" by(rule tauLaw3SimRight)
        moreover have "\<And>\<Psi> P Q \<Psi>'. \<lbrakk>(\<Psi>, P, Q) \<in> ?Z; \<Psi> \<simeq> \<Psi>'\<rbrakk> \<Longrightarrow> (\<Psi>', P, Q) \<in> ?Z" by simp (blast dest: statEqWeakBisim statEqBisim)
        ultimately have "\<Psi> \<rhd> \<alpha>\<cdot>P \<leadsto>\<^sub>w<?Z> \<alpha>\<cdot>(\<tau>.(P))" by(rule weakSimWeakenSim)
      }
      ultimately show ?thesis by auto
    qed
  next
    case(cExt \<Psi> P Q \<Psi>')
    thus ?case by auto
  next
    case(cSym \<Psi> P Q)
    thus ?case by blast 
  qed
  thus ?thesis by simp
qed
  
lemma tauLaw3PsiCong:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"

  shows "\<Psi> \<rhd> \<alpha>\<cdot>(\<tau>.(P)) \<doteq> \<alpha>\<cdot>P"
proof(induct rule: weakPsiCongI)
  case cWeakBisim
  show ?case by(rule tauLaw3)
next
  case cSimLeft
  have "\<Psi> \<rhd> P \<approx> P" by(rule weakBisimReflexive)
  moreover have "\<And>\<Psi> P Q R S. \<lbrakk>\<Psi> \<rhd> P \<sim> Q; \<Psi> \<rhd> Q \<approx> R; \<Psi> \<rhd> R \<sim> S\<rbrakk> \<Longrightarrow> \<Psi> \<rhd> P \<approx> S"
    by(blast intro: weakBisimTransitive strongBisimWeakBisim)
  ultimately show ?case using weakBisimE(3) by(rule tauLaw3CongSimLeft)
next
  case cSimRight
  have "\<Psi> \<rhd>  P \<approx> P" by(rule weakBisimReflexive)
  moreover have "\<And>\<Psi> P Q R S. \<lbrakk>\<Psi> \<rhd> P \<sim> Q; \<Psi> \<rhd> Q \<approx> R; \<Psi> \<rhd> R \<sim> S\<rbrakk> \<Longrightarrow> \<Psi> \<rhd> P \<approx> S"
    by(blast intro: weakBisimTransitive strongBisimWeakBisim)
  ultimately show ?case using tauLaw1[THEN weakBisimE(4)]
    by(rule tauLaw3CongSimRight)
qed
  
lemma tauLaw3Cong:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"

  shows "\<alpha>\<cdot>(\<tau>.(P)) \<doteq>\<^sub>c \<alpha>\<cdot>P"
proof(induct rule: weakCongI)
  case(cWeakPsiCong \<Psi> \<sigma>)
  show ?case
  proof(nominal_induct \<alpha> rule: prefix.strong_inducts)
  next
    case(pInput M yvec N)
    obtain p where "set p \<subseteq> set yvec \<times> set(p \<bullet> yvec)" and "(p \<bullet> yvec) \<sharp>* N" and "(p \<bullet> yvec) \<sharp>* P" and "(p \<bullet> yvec) \<sharp>* \<sigma>"
      by(rule_tac xvec=yvec and c="(N, P, \<sigma>)" in name_list_avoiding) auto
    thus ?case using \<open>wellFormedSubst \<sigma>\<close> tauLaw3PsiCong[where \<alpha>="pInput (substTerm.seqSubst M \<sigma>) (p \<bullet> yvec) (substTerm.seqSubst (p \<bullet> N) \<sigma>)"]
      by(simp add: inputChainAlpha' eqvts)
  next
    case(pOutput M N)
    thus ?case using  \<open>wellFormedSubst \<sigma>\<close> tauLaw3PsiCong[where \<alpha>="pOutput (substTerm.seqSubst M \<sigma>) (substTerm.seqSubst N \<sigma>)"]
      by simp
  next
    case pTau
    thus ?case using  \<open>wellFormedSubst \<sigma>\<close> tauLaw3PsiCong[where \<alpha>="pTau"]
      by simp
  qed
qed

end

end
