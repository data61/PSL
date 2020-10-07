(* 
   Title: Psi-calculi   
   Author/Maintainer: Jesper Bengtson (jebe@itu.dk), 2012
*)
theory Tau_Laws_No_Weak
  imports Tau_Sim Tau_Stat_Imp
begin

context tauSum
begin

lemma tauLaw2:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  
  shows "\<Psi> \<rhd> P \<oplus> \<tau>.(P) \<approx> \<tau>.(P)"
proof -
  let ?X = "{(\<Psi>, P \<oplus> \<tau>.(P), \<tau>.(P)) | \<Psi> P. True}"
  let ?Y = "{(\<Psi>, \<tau>.(P), P \<oplus> \<tau>.(P)) | \<Psi> P. True}"

  have "(\<Psi>, P \<oplus> \<tau>.(P), \<tau>.(P)) \<in> ?X \<union> ?Y" by auto
  moreover have "eqvt(?X \<union> ?Y)" by(auto simp add: eqvt_def eqvts)
  ultimately show ?thesis
  proof(coinduct rule: weakTransitiveCoinduct)
    case(cStatImp \<Psi> P Q)
    show ?case
    proof(cases "(\<Psi>, P, Q) \<in> ?X")
      case True
      note \<open>(\<Psi>, P, Q) \<in> ?X\<close>
      moreover {
        fix \<Psi> P
        have "\<And>\<Psi>'. (\<Psi> \<otimes> \<Psi>', P \<oplus> \<tau>.(P), \<tau>.(P)) \<in> ?X \<union> ?Y \<union> weakBisim" by auto
        hence "\<Psi> \<rhd> P \<oplus> \<tau>.(P) \<lessapprox><(?X \<union> ?Y \<union> weakBisim)> \<tau>.(P)" by(rule tauLaw2StatImpLeft)
      }
      ultimately show ?thesis by blast
    next
      case False
      from \<open>(\<Psi>, P, Q) \<notin> ?X\<close> \<open>(\<Psi>, P, Q) \<in> ?X \<union> ?Y\<close> have "(\<Psi>, P, Q) \<in> ?Y" by auto
      moreover {
        fix \<Psi> P
        have "\<And>\<Psi>'. (\<Psi> \<otimes> \<Psi>', \<tau>.(P), P \<oplus> \<tau>.(P)) \<in> ?X \<union> ?Y \<union> weakBisim" by auto
        hence "\<Psi> \<rhd> \<tau>.(P) \<lessapprox><(?X \<union> ?Y \<union> weakBisim)> P \<oplus> \<tau>.(P)" by(rule tauLaw2StatImpRight)
      }
      ultimately show ?thesis by blast
    qed
  next
    case(cSim \<Psi> P Q)
    let ?Z = "{(\<Psi>, P, S) | \<Psi> P S. \<exists>Q R. \<Psi> \<rhd> P \<sim> Q \<and> (\<Psi>, Q, R) \<in> ?X \<union> ?Y \<union> weakBisim \<and> \<Psi> \<rhd> R \<sim> S}"
    show ?case
      
    proof(cases "(\<Psi>, P, Q) \<in> ?X")
      case True
      note \<open>(\<Psi>, P, Q) \<in> ?X\<close>
      moreover {
        fix \<Psi> P
        have "\<And>\<Psi> P. (\<Psi>, P, P) \<in> ?Z" by(blast intro: weakBisimReflexive bisimReflexive)
        moreover have "\<And>\<Psi> P Q R S. \<lbrakk>\<Psi> \<rhd> P \<sim> Q; (\<Psi>, Q, R) \<in> ?Z; \<Psi> \<rhd> R \<sim> S\<rbrakk> \<Longrightarrow> (\<Psi>, P, S) \<in> ?Z"
          by(blast intro: bisimTransitive dest: bisimE(4))
        ultimately have "\<Psi> \<rhd> P \<oplus> \<tau>.(P) \<leadsto><?Z> \<tau>.(P)" by(rule tauLaw2SimLeft)
      }
      ultimately show ?thesis by blast
    next
      case False
      from \<open>(\<Psi>, P, Q) \<notin> ?X\<close> \<open>(\<Psi>, P, Q) \<in> ?X \<union> ?Y\<close> have "(\<Psi>, P, Q) \<in> ?Y" by auto
      moreover {
        fix \<Psi> P
        have "\<And>\<Psi> P Q. \<Psi> \<rhd> P \<sim> Q \<Longrightarrow> (\<Psi>, P, Q) \<in> ?Z" by(blast intro: weakBisimReflexive bisimReflexive)
        hence "\<Psi> \<rhd> \<tau>.(P) \<leadsto><?Z> P \<oplus> \<tau>.(P)" by(rule tauLaw2SimRight)
      }
      ultimately show ?thesis by blast
    qed
  next
    case(cExt \<Psi> P Q \<Psi>')
    thus ?case by auto
  next
    case(cSym \<Psi> P Q)
    thus ?case by auto
  qed
qed

lemma tauLawPsiCong2:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"

  shows "\<Psi> \<rhd> P \<oplus> \<tau>.(P) \<doteq> \<tau>.(P)"
proof(induct rule: weakPsiCongI)
  case cWeakBisim
  thus ?case by(rule tauLaw2)
next
  case cSimLeft
  note weakBisimReflexive
  moreover have "\<And>\<Psi> P Q R S. \<lbrakk>\<Psi> \<rhd> P \<sim> Q; \<Psi> \<rhd> Q \<approx> R; \<Psi> \<rhd> R \<sim> S\<rbrakk> \<Longrightarrow> \<Psi> \<rhd> P \<approx> S"
    by(metis weakBisimTransitive strongBisimWeakBisim)
  ultimately show ?case by(rule tauLaw2CongSimLeft)
next
  case cSimRight
  from strongBisimWeakBisim show ?case by(rule tauLaw2CongSimRight)
qed

lemma tauLawCong2:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  
  shows "P \<oplus> \<tau>.(P) \<doteq>\<^sub>c \<tau>.(P)"
using tauLawPsiCong2
by(rule_tac weakCongI) auto

lemma tauLaw4:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   \<alpha> :: "'a prefix"
  
  shows "\<Psi> \<rhd> \<alpha>\<cdot>P \<oplus> \<alpha>\<cdot>(\<tau>.(P) \<oplus> Q) \<approx> \<alpha>\<cdot>(\<tau>.(P) \<oplus> Q)"
proof -
  let ?X = "{(\<Psi>, \<alpha>\<cdot>P \<oplus> \<alpha>\<cdot>(\<tau>.(P) \<oplus> Q), \<alpha>\<cdot>(\<tau>.(P) \<oplus> Q)) | \<Psi> P \<alpha> Q. True}"
  let ?Y = "{(\<Psi>, \<alpha>\<cdot>(\<tau>.(P) \<oplus> Q), \<alpha>\<cdot>P \<oplus> \<alpha>\<cdot>(\<tau>.(P) \<oplus> Q)) | \<Psi> P \<alpha> Q. True}"
  have "(\<Psi>, \<alpha>\<cdot>P \<oplus> \<alpha>\<cdot>(\<tau>.(P) \<oplus> Q), \<alpha>\<cdot>(\<tau>.(P) \<oplus> Q)) \<in> ?X \<union> ?Y" by auto
  moreover have "eqvt(?X \<union> ?Y)" by(fastforce simp add: eqvt_def eqvts)
  ultimately show ?thesis
  proof(coinduct rule: weakTransitiveCoinduct)
    case(cStatImp \<Psi> P Q)
    show ?case
    proof(cases "(\<Psi>, P, Q) \<in> ?X")
      case True
      note \<open>(\<Psi>, P, Q) \<in> ?X\<close>
      moreover {
        fix \<Psi> \<alpha> P Q
        have "\<And>\<Psi>'. (\<Psi> \<otimes> \<Psi>', \<alpha>\<cdot>P \<oplus> \<alpha>\<cdot>(\<tau>.(P) \<oplus> Q), \<alpha>\<cdot>(\<tau>.(P) \<oplus> Q)) \<in> ?X \<union> ?Y \<union> weakBisim" by blast
        hence "\<Psi> \<rhd>  \<alpha>\<cdot>P \<oplus> \<alpha>\<cdot>(\<tau>.(P) \<oplus> Q) \<lessapprox><(?X \<union> ?Y \<union> weakBisim)>  \<alpha>\<cdot>(\<tau>.(P) \<oplus> Q)" by(rule tauLaw4StatImpLeft)
      }
      ultimately show ?thesis by blast
    next
      case False
      from \<open>(\<Psi>, P, Q) \<notin> ?X\<close> \<open>(\<Psi>, P, Q) \<in> ?X \<union> ?Y\<close> have "(\<Psi>, P, Q) \<in> ?Y" by blast
      moreover {
        fix \<Psi> \<alpha> P Q
        have "\<And>\<Psi>'. (\<Psi> \<otimes> \<Psi>', \<alpha>\<cdot>(\<tau>.(P) \<oplus> Q), \<alpha>\<cdot>P \<oplus> \<alpha>\<cdot>(\<tau>.(P) \<oplus> Q)) \<in> ?X \<union> ?Y \<union> weakBisim" by auto
        hence "\<Psi> \<rhd>  \<alpha>\<cdot>(\<tau>.(P) \<oplus> Q) \<lessapprox><(?X \<union> ?Y \<union> weakBisim)> \<alpha>\<cdot>P \<oplus> \<alpha>\<cdot>(\<tau>.(P) \<oplus> Q)" by(rule tauLaw4StatImpRight)
      }
      ultimately show ?thesis by blast
    qed
  next      
    case(cSim \<Psi> P Q)
    let ?Z = "{(\<Psi>, P, S) | \<Psi> P S. \<exists>Q R. \<Psi> \<rhd> P \<sim> Q \<and> (\<Psi>, Q, R) \<in> ?X \<union> ?Y \<union> weakBisim \<and> \<Psi> \<rhd> R \<sim> S}"
    show ?case
    proof(cases "(\<Psi>, P, Q) \<in> ?X")
      case True
      note \<open>(\<Psi>, P, Q) \<in> ?X\<close>
      moreover {
        fix \<Psi> P \<alpha> Q
        have "\<And>\<Psi> P. (\<Psi>, P, P) \<in> ?Z" by(blast intro: weakBisimReflexive bisimReflexive)
        moreover have "\<And>\<Psi> P Q. \<Psi> \<rhd> P \<sim> Q \<Longrightarrow> (\<Psi>, P, Q) \<in> ?Z" by(blast intro: weakBisimReflexive bisimReflexive)
        ultimately have "\<Psi> \<rhd>  \<alpha>\<cdot>P \<oplus> \<alpha>\<cdot>(\<tau>.(P) \<oplus> Q) \<leadsto><?Z>  \<alpha>\<cdot>(\<tau>.(P) \<oplus> Q)" by(rule tauLaw4SimLeft)
      }
      ultimately show ?thesis by blast
    next
      case False
      from \<open>(\<Psi>, P, Q) \<notin> ?X\<close> \<open>(\<Psi>, P, Q) \<in> ?X \<union> ?Y\<close> have "(\<Psi>, P, Q) \<in> ?Y" by blast
      moreover {
        fix \<Psi> P \<alpha> Q
        have "\<And>\<Psi> P Q. \<Psi> \<rhd> P \<sim> Q \<Longrightarrow> (\<Psi>, P, Q) \<in> ?Z" by(blast intro: weakBisimReflexive bisimReflexive)
        moreover have "\<And>\<Psi> P. (\<Psi>, P, P) \<in> ?Z" by(blast intro: weakBisimReflexive bisimReflexive)
        ultimately have "\<Psi> \<rhd> \<alpha>\<cdot>(\<tau>.(P) \<oplus> Q) \<leadsto><?Z> \<alpha>\<cdot>P \<oplus> \<alpha>\<cdot>(\<tau>.(P) \<oplus> Q)" by(rule tauLaw4SimRight)
      }
      ultimately show ?thesis by blast
    qed
  next
    case(cExt \<Psi> P Q \<Psi>')
    thus ?case by auto
  next
    case(cSym \<Psi> P Q)
    thus ?case by blast
  qed
qed

lemma tauLaw4PsiCong:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   \<alpha> :: "'a prefix"
  and   Q :: "('a, 'b, 'c) psi"

  shows "\<Psi> \<rhd> \<alpha>\<cdot>P \<oplus> \<alpha>\<cdot>(\<tau>.(P) \<oplus> Q) \<doteq> \<alpha>\<cdot>(\<tau>.(P) \<oplus> Q)"
proof(induct rule: weakPsiCongI)
  case cWeakBisim
  show ?case by(rule tauLaw4)
next
  case cSimLeft
  from weakBisimReflexive strongBisimWeakBisim show ?case by(rule tauLaw4CongSimLeft)
next
  case cSimRight
  from strongBisimWeakBisim show ?case by(rule tauLaw4CongSimRight)
qed

lemma tauLaw4Cong:
  fixes P :: "('a, 'b, 'c) psi"
  and   \<alpha> :: "'a prefix"
  and   Q :: "('a, 'b, 'c) psi"

  shows "\<alpha>\<cdot>P \<oplus> \<alpha>\<cdot>(\<tau>.(P) \<oplus> Q) \<doteq>\<^sub>c \<alpha>\<cdot>(\<tau>.(P) \<oplus> Q)"
proof(induct rule: weakCongI)
  case(cWeakPsiCong \<Psi> \<sigma>)
  show ?case
  proof(nominal_induct \<alpha> rule: prefix.strong_inducts)
  next
    case(pInput M yvec N)
    obtain p where "set p \<subseteq> set yvec \<times> set(p \<bullet> yvec)" and "(p \<bullet> yvec) \<sharp>* N" and "(p \<bullet> yvec) \<sharp>* P" and "(p \<bullet> yvec) \<sharp>* Q" and "(p \<bullet> yvec) \<sharp>* \<sigma>"
      by(rule_tac xvec=yvec and c="(N, P, Q, \<sigma>)" in name_list_avoiding) auto
    thus ?case using \<open>wellFormedSubst \<sigma>\<close> tauLaw4PsiCong[where \<alpha>="pInput (substTerm.seqSubst M \<sigma>) (p \<bullet> yvec) (substTerm.seqSubst (p \<bullet> N) \<sigma>)"]
      by(simp add: inputChainAlpha' eqvts)
  next
    case(pOutput M N)
    thus ?case using  \<open>wellFormedSubst \<sigma>\<close> tauLaw4PsiCong[where \<alpha>="pOutput (substTerm.seqSubst M \<sigma>) (substTerm.seqSubst N \<sigma>)"]
      by simp
  next
    case pTau
    thus ?case using  \<open>wellFormedSubst \<sigma>\<close> tauLaw4PsiCong[where \<alpha>="pTau"]
      by simp
  qed
qed

end

end
