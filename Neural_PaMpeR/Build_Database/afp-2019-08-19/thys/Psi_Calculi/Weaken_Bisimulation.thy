(* 
   Title: Psi-calculi   
   Author/Maintainer: Jesper Bengtson (jebe@itu.dk), 2012
*)
theory Weaken_Bisimulation
  imports Weaken_Simulation Weaken_Stat_Imp
begin

context weak
begin

lemma weakenMonoCoinduct: "\<And>x y xa xb xc P Q \<Psi>.
                      x \<le> y \<Longrightarrow>
                      (\<Psi> \<rhd> Q \<leadsto>\<^sub>w<{(xc, xb, xa). x xc xb xa}> P) \<longrightarrow>
                     (\<Psi> \<rhd> Q \<leadsto>\<^sub>w<{(xb, xa, xc). y xb xa xc}> P)"
apply auto
apply(rule weakenSimMonotonic)
by(auto dest: le_funE)

lemma weakenMonoCoinduct2: "\<And>x y xa xb xc P Q \<Psi>.
                      x \<le> y \<Longrightarrow>
                      (\<Psi> \<rhd> Q \<lessapprox>\<^sub>w<{(xc, xb, xa). x xc xb xa}> P) \<longrightarrow>
                     (\<Psi> \<rhd> Q \<lessapprox>\<^sub>w<{(xb, xa, xc). y xb xa xc}> P)"
apply auto
apply(rule weakenStatImpMonotonic)
by(auto dest: le_funE)

coinductive_set weakenBisim :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set" 
where
  step: "\<lbrakk>\<Psi> \<rhd> P \<lessapprox>\<^sub>w<weakenBisim> Q; \<Psi> \<rhd> P \<leadsto>\<^sub>w<weakenBisim> Q;
          \<forall>\<Psi>'. (\<Psi> \<otimes> \<Psi>',  P, Q) \<in> weakenBisim; (\<Psi>, Q, P) \<in> weakenBisim\<rbrakk> \<Longrightarrow> (\<Psi>, P, Q) \<in> weakenBisim"
monos weakenMonoCoinduct weakenMonoCoinduct2

abbreviation
  weakenBisimJudge ("_ \<rhd> _ \<approx>\<^sub>w _" [70, 70, 70] 65) where "\<Psi> \<rhd> P \<approx>\<^sub>w Q \<equiv> (\<Psi>, P, Q) \<in> weakenBisim"
abbreviation
  weakenBisimNilJudge ("_ \<approx>\<^sub>w _" [70, 70] 65) where "P \<approx>\<^sub>w Q \<equiv> \<one> \<rhd> P \<approx>\<^sub>w Q"

lemma weakenBisimCoinductAux[consumes 1]:
  fixes F :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"
  and   X :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"

  assumes "(\<Psi>, P, Q) \<in> X"
  and     "\<And>\<Psi> P Q. (\<Psi>, P, Q) \<in> X \<Longrightarrow> (\<Psi> \<rhd> P \<lessapprox>\<^sub>w<(X \<union> weakenBisim)> Q) \<and>
                                    (\<Psi> \<rhd> P \<leadsto>\<^sub>w<(X \<union> weakenBisim)> Q) \<and>
                                    (\<forall>\<Psi>'. (\<Psi> \<otimes> \<Psi>', P, Q) \<in> X \<or> (\<Psi> \<otimes> \<Psi>', P, Q) \<in> weakenBisim) \<and>
                                    ((\<Psi>, Q, P) \<in> X \<or> (\<Psi>, Q, P) \<in> weakenBisim)"

  shows "(\<Psi>, P, Q) \<in> weakenBisim"
proof -
  have "X \<union> weakenBisim = {(\<Psi>, P, Q). (\<Psi>, P, Q) \<in> X \<or> (\<Psi>, P, Q) \<in> weakenBisim}" by auto
  with assms show ?thesis
    by coinduct (simp add: rtrancl_def)
qed

lemma weakenBisimCoinduct[consumes 1, case_names cStatImp cSim cExt cSym]:
  fixes F :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"
  and   X :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"

  assumes "(\<Psi>, P, Q) \<in> X"
  and     "\<And>\<Psi>' R S. (\<Psi>', R, S) \<in> X \<Longrightarrow> \<Psi>' \<rhd> R \<lessapprox>\<^sub>w<(X \<union> weakenBisim)> S"
  and     "\<And>\<Psi>' R S. (\<Psi>', R, S) \<in> X \<Longrightarrow> \<Psi>' \<rhd> R \<leadsto>\<^sub>w<(X \<union> weakenBisim)> S"
  and     "\<And>\<Psi>' R S \<Psi>''. (\<Psi>', R, S) \<in> X \<Longrightarrow> (\<Psi>' \<otimes> \<Psi>'', R, S) \<in> X \<or> \<Psi>' \<otimes> \<Psi>'' \<rhd> R \<approx>\<^sub>w S"
  and     "\<And>\<Psi>' R S. (\<Psi>', R, S) \<in> X \<Longrightarrow> (\<Psi>', S, R) \<in> X \<or> \<Psi>' \<rhd> S \<approx>\<^sub>w R"

  shows "\<Psi> \<rhd> P \<approx>\<^sub>w Q"
proof -
  have "X \<union> weakenBisim = {(\<Psi>, P, Q). (\<Psi>, P, Q) \<in> X \<or> (\<Psi>, P, Q) \<in> weakenBisim}" by auto
  with assms show ?thesis
    by coinduct (simp add: rtrancl_def)
qed

lemma weakenBisimWeakCoinductAux[consumes 1]:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"
  and   X :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"

  assumes "(\<Psi>, P, Q) \<in> X"
  and     "\<And>\<Psi> P Q. (\<Psi>, P, Q) \<in> X \<Longrightarrow> \<Psi> \<rhd> P \<lessapprox>\<^sub>w<X> Q \<and>
                                     \<Psi> \<rhd> P \<leadsto>\<^sub>w<X> Q \<and> (\<forall>\<Psi>'. (\<Psi> \<otimes> \<Psi>', P, Q) \<in> X) \<and> 
                                    (\<Psi>, Q, P) \<in> X" 

  shows "\<Psi> \<rhd> P \<approx>\<^sub>w Q"
using assms
by(coinduct rule: weakenBisimCoinductAux) (blast intro: weakenSimMonotonic weakenStatImpMonotonic)

lemma weakenBisimE:
  fixes P  :: "('a, 'b, 'c) psi"
  and   Q  :: "('a, 'b, 'c) psi"
  and   \<Psi>  :: 'b
  and   \<Psi>' :: 'b

  assumes "\<Psi> \<rhd> P \<approx>\<^sub>w Q"

  shows "\<Psi> \<rhd> P \<lessapprox>\<^sub>w<weakenBisim> Q"
  and   "\<Psi> \<rhd> P \<leadsto>\<^sub>w<weakenBisim> Q"
  and   "\<Psi> \<otimes> \<Psi>' \<rhd> P \<approx>\<^sub>w Q"
  and   "\<Psi> \<rhd> Q \<approx>\<^sub>w P"
using assms
by(auto intro: weakenBisim.cases simp add: rtrancl_def)

lemma weakenBisimWeakCoinduct[consumes 1, case_names cStatImp cSim cExt cSym]:
  fixes F :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"
  and   X :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"

  assumes "(\<Psi>, P, Q) \<in> X"
  and     "\<And>\<Psi> P Q. (\<Psi>, P, Q) \<in> X \<Longrightarrow> \<Psi> \<rhd> P \<lessapprox>\<^sub>w<X> Q"
  and     "\<And>\<Psi> P Q. (\<Psi>, P, Q) \<in> X \<Longrightarrow> \<Psi> \<rhd> P \<leadsto>\<^sub>w<X> Q"
  and     "\<And>\<Psi> P Q \<Psi>'. (\<Psi>, P, Q) \<in> X \<Longrightarrow> (\<Psi> \<otimes> \<Psi>', P, Q) \<in> X"
  and     "\<And>\<Psi> P Q. (\<Psi>, P, Q) \<in> X \<Longrightarrow> (\<Psi>, Q, P) \<in> X"

  shows "(\<Psi>, P, Q) \<in> weakenBisim"
proof -
  have "X \<union> weakenBisim = {(\<Psi>, P, Q). (\<Psi>, P, Q) \<in> X \<or> (\<Psi>, P, Q) \<in> weakenBisim}" by auto
  with assms show ?thesis
    by(coinduct rule: weakenBisimWeakCoinductAux) blast
qed

lemma weakenBisimEqWeakBisim[simp]: "weakenBisim = weakBisim"
proof auto
  fix \<Psi> P Q
  assume "\<Psi> \<rhd> P \<approx>\<^sub>w Q" thus "\<Psi> \<rhd> P \<approx> Q"
  proof(coinduct rule: weakBisimWeakCoinduct)
    case(cStatImp \<Psi> P Q)
    from \<open>\<Psi> \<rhd> P \<approx>\<^sub>w Q\<close> have "\<Psi> \<rhd> P \<lessapprox>\<^sub>w<weakenBisim> Q" by(rule weakenBisimE)
    thus ?case using weakenBisimE(3) by(rule weakenStatImpWeakStatImp)
  next
    case(cSim \<Psi> P Q)
    from \<open>\<Psi> \<rhd> P \<approx>\<^sub>w Q\<close> weakenBisimE
    show ?case by(rule weakenSimWeakSim)
  next
    case(cExt \<Psi> P Q \<Psi>')
    thus ?case by(rule weakenBisimE)
  next
    case(cSym \<Psi> P Q)
    thus ?case by(rule weakenBisimE)
  qed
next
  fix \<Psi> P Q
  assume "\<Psi> \<rhd> P \<approx> Q" thus "\<Psi> \<rhd> P \<approx>\<^sub>w Q"
  proof(coinduct rule: weakenBisimWeakCoinduct)
    case(cStatImp \<Psi> P Q)
    from \<open>\<Psi> \<rhd> P \<approx> Q\<close> have "\<Psi> \<rhd> P \<lessapprox><weakBisim> Q" by(rule weakBisimE)
    thus ?case using statEqWeakBisim by(rule weakStatImpWeakenStatImp)
  next
    case(cSim \<Psi> P Q)
    from \<open>\<Psi> \<rhd> P \<approx> Q\<close> have "\<Psi> \<rhd> P \<leadsto><weakBisim> Q" by(rule weakBisimE)
    thus ?case using statEqWeakBisim by(rule weakSimWeakenSim)
  next
    case(cExt \<Psi> P Q \<Psi>')
    thus ?case by(rule weakBisimE)
  next
    case(cSym \<Psi> P Q)
    thus ?case by(rule weakBisimE)
  qed
qed

lemma weakenTransitiveWeakCoinduct[case_names cStatImp cSim cExt cSym, case_conclusion bisim step, consumes 2]:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"
  and   X :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"

  assumes p: "(\<Psi>, P, Q) \<in> X"
  and Eqvt: "eqvt X"
  and rStatImp: "\<And>\<Psi> P Q. (\<Psi>, P, Q) \<in> X \<Longrightarrow> \<Psi> \<rhd> P \<lessapprox>\<^sub>w<X> Q"
  and rSim: "\<And>\<Psi> P Q. (\<Psi>, P, Q) \<in> X \<Longrightarrow> \<Psi> \<rhd> P \<leadsto>\<^sub>w<({(\<Psi>, P, Q) | \<Psi> P Q. \<exists>P' Q'. \<Psi> \<rhd> P \<sim> P' \<and>
                                                                        (\<Psi>, P', Q') \<in> X \<and>
                                                                        \<Psi> \<rhd> Q' \<sim> Q})> Q"
  and rExt: "\<And>\<Psi> P Q \<Psi>'. (\<Psi>, P, Q) \<in> X \<Longrightarrow> (\<Psi> \<otimes> \<Psi>', P, Q) \<in> X"
  and rSym: "\<And>\<Psi> P Q. (\<Psi>, P, Q) \<in> X \<Longrightarrow> (\<Psi>, Q, P) \<in> X"

  shows "\<Psi> \<rhd> P \<approx>\<^sub>w Q"
proof -
  from p \<open>eqvt X\<close> have "\<Psi> \<rhd> P \<approx> Q"
  proof(coinduct rule: weakTransitiveWeakCoinduct)
    case(cStatImp \<Psi> P Q)
    from \<open>(\<Psi>, P, Q) \<in> X\<close> have "\<Psi> \<rhd> P \<lessapprox>\<^sub>w<X> Q" by(rule rStatImp)
    thus ?case using rExt by(rule weakenStatImpWeakStatImp)
  next
    case(cSim \<Psi> P Q)
    let ?Y = "{(\<Psi>, P, Q) | \<Psi> P Q. \<exists>P' Q'. \<Psi> \<rhd> P \<sim> P' \<and> (\<Psi>, P', Q') \<in> X \<and> \<Psi> \<rhd> Q' \<sim> Q}"
    note \<open>(\<Psi>, P, Q) \<in> X\<close>
    moreover note rStatImp rSim
    moreover have "\<And>\<Psi> P Q \<Psi>'. (\<Psi>, P, Q) \<in> ?Y \<Longrightarrow> (\<Psi> \<otimes> \<Psi>', P, Q) \<in> ?Y"
      by(blast dest: bisimE rExt)
    ultimately show ?case using rSym by(rule weakenSimWeakSim)
  next
    case(cExt \<Psi> P Q \<Psi>')
    thus ?case by(rule rExt) 
  next
    case(cSym \<Psi> P Q)
    thus ?case by(rule rSym)
  qed
  thus ?thesis by(simp add: weakenBisimEqWeakBisim)
qed

lemma weakenTransitiveCoinduct[case_names cStatImp cSim cExt cSym, case_conclusion bisim step, consumes 2]:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"
  and   X :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"

  assumes p: "(\<Psi>, P, Q) \<in> X"
  and Eqvt: "eqvt X"
  and rStatImp: "\<And>\<Psi> P Q. (\<Psi>, P, Q) \<in> X \<Longrightarrow> \<Psi> \<rhd> P \<lessapprox>\<^sub>w<(X \<union> weakenBisim)> Q"
  and rSim: "\<And>\<Psi> P Q. (\<Psi>, P, Q) \<in> X \<Longrightarrow> \<Psi> \<rhd> P \<leadsto>\<^sub>w<({(\<Psi>, P, Q) | \<Psi> P Q. \<exists>P' Q'. \<Psi> \<rhd> P \<sim> P' \<and>
                                                                        (\<Psi>, P', Q') \<in> (X \<union> weakenBisim) \<and>
                                                                        \<Psi> \<rhd> Q' \<sim> Q})> Q"
  and rExt: "\<And>\<Psi> P Q \<Psi>'. (\<Psi>, P, Q) \<in> X \<Longrightarrow> (\<Psi> \<otimes> \<Psi>', P, Q) \<in> X \<union> weakenBisim"
  and rSym: "\<And>\<Psi> P Q. (\<Psi>, P, Q) \<in> X \<Longrightarrow> (\<Psi>, Q, P) \<in> X \<union> weakenBisim"

  shows "\<Psi> \<rhd> P \<approx>\<^sub>w Q"
proof -
  from p have "(\<Psi>, P, Q) \<in> X \<union> weakenBisim" by auto
  moreover from \<open>eqvt X\<close> have "eqvt(X \<union> weakenBisim)" by auto
  ultimately show ?thesis
  proof(coinduct rule: weakenTransitiveWeakCoinduct)
    case(cStatImp \<Psi> P Q)
    thus ?case by(fastforce intro: rStatImp weakenBisimE(1) weakenStatImpMonotonic)
  next
    case(cSim \<Psi> P Q)
    thus ?case by(fastforce intro: rSim weakenBisimE(2) weakenSimMonotonic bisimReflexive)
  next
    case(cExt \<Psi> P Q \<Psi>')
    thus ?case by(blast dest: weakenBisimE rExt) 
  next
    case(cSym \<Psi> P Q)
    thus ?case by(blast dest: weakenBisimE rSym)
  qed
qed

end

end

