(* 
   Title: The pi-calculus   
   Author/Maintainer: Jesper Bengtson (jebe.dk), 2012
*)
theory Strong_Late_Bisim
  imports Strong_Late_Sim
begin

lemma monoAux: "A \<subseteq> B \<Longrightarrow> P \<leadsto>[A] Q \<longrightarrow> P \<leadsto>[B] Q"
by(auto intro: Strong_Late_Sim.monotonic)

coinductive_set bisim :: "(pi \<times> pi) set"
where
  step: "\<lbrakk>P \<leadsto>[bisim] Q; (Q, P) \<in> bisim\<rbrakk> \<Longrightarrow> (P, Q) \<in> bisim"
monos monoAux

abbreviation
  strongBisimJudge (infixr "\<sim>" 65) where "P \<sim> Q \<equiv> (P, Q) \<in> bisim"

lemma monotonic': "mono(\<lambda>S. {(P, Q) |P Q. P \<leadsto>[S] Q \<and> Q \<leadsto>[S] P})"
apply(rule monoI)
by(auto dest: monoAux)

lemma monotonic: "mono(\<lambda>p x1 x2.
        \<exists>P Q. x1 = P \<and>
              x2 = Q \<and> P \<leadsto>[{(xa, x). p xa x}] Q \<and> Q \<leadsto>[{(xa, x). p xa x}] P)"
apply(rule monoI)
by(auto intro: Strong_Late_Sim.monotonic)


lemma bisimCoinduct[case_names cSim cSym , consumes 1]:
  assumes p: "(P, Q) \<in> X"
  and     rSim: "\<And>R S. (R, S) \<in> X \<Longrightarrow> R \<leadsto>[(X \<union> bisim)] S"
  and     rSym: "\<And>R S. (R, S) \<in> X \<Longrightarrow> (S, R) \<in> X"

  shows "P \<sim> Q"
proof -
  have aux: "X \<union> bisim = {(P, Q). (P, Q) \<in> X \<or> P \<sim> Q}" by blast

  from p show ?thesis
    apply(coinduct, auto)
    apply(fastforce dest: rSim simp add: aux)
    by(fastforce dest: rSym)
qed

lemma bisimE:
  fixes P :: pi
  and   Q :: pi

  assumes "P \<sim> Q"
  
  shows "P \<leadsto>[bisim] Q"
using assms
by(auto intro: bisim.cases)

lemma bisimI:
  fixes P :: pi
  and   Q :: pi
  
  assumes "P \<leadsto>[bisim] Q"
  and     "Q \<sim> P"

  shows "P \<sim> Q"
using assms
by(rule bisim.intros)

definition old_bisim :: "(pi \<times> pi) set \<Rightarrow> bool" where
  "old_bisim Rel \<equiv> \<forall>(P, Q) \<in> Rel. P \<leadsto>[Rel] Q \<and> (Q, P) \<in> Rel"

lemma oldBisimBisimEq:
  shows "(\<Union>{Rel. (old_bisim Rel)}) = bisim"  (is "?LHS = ?RHS")
proof
  show "?LHS \<subseteq> ?RHS"
  proof auto
    fix P Q Rel
    assume "(P, Q) \<in> Rel" and "old_bisim Rel"
    thus "P \<sim> Q"
    proof(coinduct rule: bisimCoinduct)
      case(cSim P Q)
      with \<open>old_bisim Rel\<close> show ?case
        by(fastforce simp add: old_bisim_def intro: Strong_Late_Sim.monotonic)
    next
      case(cSym P Q)
      with \<open>old_bisim Rel\<close> show ?case
        by(auto simp add: old_bisim_def)
    qed
  qed
next
  show "?RHS \<subseteq> ?LHS"
  proof auto
    fix P Q
    assume "P \<sim> Q"
    moreover hence "old_bisim bisim"
      by(auto simp add: old_bisim_def dest: bisim.cases)
    ultimately show "\<exists>Rel. old_bisim Rel \<and> (P, Q) \<in> Rel"
      by blast
  qed
qed

lemma reflexive:
  fixes P :: pi

  shows "P \<sim> P"
proof -
  have "(P, P) \<in> Id" by simp
  thus ?thesis
    by(coinduct rule: bisimCoinduct, auto intro: Strong_Late_Sim.reflexive)
qed

lemma symmetric:
  fixes P :: pi
  and   Q :: pi
   
  assumes "P \<sim> Q"

  shows "Q \<sim> P"
using assms
by(auto dest: bisim.cases)

lemma bisimClosed:
  fixes P :: pi
  and   Q :: pi
  and   p :: "name prm"
  
  assumes "P \<sim> Q"

  shows "(p \<bullet> P) \<sim> (p \<bullet> Q)" 
proof -
  let ?X = "{(p \<bullet> P, p \<bullet> Q) | P Q (p::name prm). P \<sim> Q}"
  from \<open>P \<sim> Q\<close> have  "(p \<bullet> P, p \<bullet> Q) \<in> ?X" by blast
  thus ?thesis
  proof(coinduct rule: bisimCoinduct)
    case(cSim pP pQ)
    from \<open>(pP, pQ) \<in> ?X\<close> obtain P Q p where "P \<sim> Q" and "pP = (p::name prm) \<bullet> P" and "pQ = p \<bullet> Q"
      by auto
    from \<open>P \<sim> Q\<close> have "P \<leadsto>[bisim] Q" by(rule bisimE)
    moreover have "bisim \<subseteq> ?X"
    proof 
      fix x
      assume "x \<in> bisim"
      moreover have "x = (([]::name prm) \<bullet> x)" by auto
      ultimately show "x \<in> ?X"
        apply(case_tac x)
        by(clarify, simp only: eqvts) metis
    qed
    moreover have "eqvt ?X"
    proof(auto simp add: eqvt_def)
      fix P Q
      fix perm1::"name prm"
      fix perm2::"name prm"
      
      assume "P \<sim> Q"
      moreover have "perm1 \<bullet> perm2 \<bullet> P = (perm1 @ perm2) \<bullet> P" by(simp add: pt2[OF pt_name_inst])
      moreover have "perm1 \<bullet> perm2 \<bullet> Q = (perm1 @ perm2) \<bullet> Q" by(simp add: pt2[OF pt_name_inst])
      
      ultimately show "\<exists>P' Q'. (\<exists>(perm::name prm). perm1 \<bullet> perm2 \<bullet> P = perm \<bullet> P' \<and>
                                                   perm1 \<bullet> perm2 \<bullet> Q = perm \<bullet> Q') \<and> P' \<sim> Q'"
        by blast
    qed
    ultimately have "(p \<bullet> P) \<leadsto>[?X] (p \<bullet> Q)" 
      by(rule Strong_Late_Sim.eqvtI)
    with \<open>pP = p \<bullet> P\<close> \<open>pQ = p \<bullet> Q\<close> show ?case
      by(force intro: Strong_Late_Sim.monotonic)
  next
    case(cSym P Q)
    thus ?case by(auto intro: symmetric)
  qed
qed

lemma bisimEqvt[simp]:
  shows "eqvt bisim"
by(auto simp add: eqvt_def bisimClosed)

lemma transitive:
  fixes P :: pi
  and   Q :: pi
  and   R :: pi

  assumes "P \<sim> Q"
  and     "Q \<sim> R"

  shows "P \<sim> R"
proof -
  let ?X = "bisim O bisim"
  from assms have "(P, R) \<in> ?X" by blast
  thus ?thesis
  proof(coinduct rule: bisimCoinduct)
    case(cSim P R)
    thus ?case
      by(fastforce intro: Strong_Late_Sim.transitive dest: bisimE simp add: eqvtTrans)
  next
    case(cSym P R)
    thus ?case
      by(auto dest: symmetric)
  qed
qed

lemma bisimTransitiveCoinduct[case_names cSim cSym, case_conclusion bisim step, consumes 2]:
  assumes "(P, Q) \<in> X"
  and "eqvt X"
  and rSim: "\<And>R S. (R, S) \<in> X \<Longrightarrow> R \<leadsto>[(bisim O (X \<union> bisim) O bisim)] S"
  and rSym: "\<And>R S. (R, S) \<in> X \<Longrightarrow> (S, R) \<in> bisim O (X \<union> bisim) O bisim"

  shows "P \<sim> Q"
proof -
  let ?X = "bisim O (X \<union> bisim) O bisim"
  from \<open>(P, Q) \<in> X\<close>  have "(P, Q) \<in> ?X" by(auto intro: reflexive)
  thus ?thesis
  proof(coinduct rule: bisimCoinduct)
    case(cSim P Q)
    {
      fix P P' Q' Q

      assume "P \<sim> P'" and "(P', Q') \<in> X \<union> bisim" and "Q' \<sim> Q"
      have "P \<leadsto>[(?X \<union> bisim)] Q"
      proof(cases "(P', Q') \<in> X")
        case True
        from \<open>P \<sim> P'\<close> have "P \<leadsto>[bisim] P'" by(rule bisimE)
        moreover from \<open>(P', Q') \<in> X\<close> have "P' \<leadsto>[(?X)] Q'" by(rule rSim)
        moreover from \<open>eqvt X\<close> bisimEqvt have "eqvt(?X \<union> bisim)" by blast
        moreover have "bisim O ?X \<subseteq> ?X \<union> bisim" by(auto dest: transitive)
        ultimately have "P \<leadsto>[(?X \<union> bisim)] Q'" by(rule Strong_Late_Sim.transitive)
        moreover from \<open>Q' \<sim> Q\<close> have "Q' \<leadsto>[bisim] Q" by(rule bisimE)
        moreover note \<open>eqvt(?X \<union> bisim)\<close>
        moreover have "(?X \<union> bisim) O bisim \<subseteq> ?X \<union> bisim"
          by auto (blast dest: transitive)+
        ultimately show ?thesis by(rule Strong_Late_Sim.transitive)
      next
        case False
        from \<open>(P', Q') \<notin> X\<close> \<open>(P', Q') \<in> X \<union> bisim\<close> have "P' \<sim> Q'" by simp
        with \<open>P \<sim> P'\<close> \<open>Q' \<sim> Q\<close> have "P \<sim> Q" by(blast dest: transitive)
        hence "P \<leadsto>[bisim] Q" by(rule bisimE)
        moreover have "bisim \<subseteq> ?X \<union> bisim" by auto
        ultimately show ?thesis by(rule Strong_Late_Sim.monotonic)
      qed
    }
    with \<open>(P, Q) \<in> ?X\<close> show ?case by auto
    case(cSym P Q)
    {
      fix P P' Q' Q

      assume "P \<sim> P'" and "(P', Q') \<in> X \<union> bisim" and "Q' \<sim> Q"
      have "(Q, P) \<in> bisim O (X \<union> bisim) O bisim"
      proof(cases "(P', Q') \<in> X")
        case True
        from \<open>(P', Q') \<in> X\<close> have "(Q', P') \<in> ?X" by(rule rSym)
        then obtain Q'' P'' where "Q' \<sim> Q''" and "(Q'', P'') \<in> X \<union> bisim" and "P'' \<sim> P'"
          by auto
        from \<open>Q' \<sim> Q\<close> \<open>Q' \<sim> Q''\<close> have "Q \<sim> Q''" by(metis transitive symmetric)
        moreover from \<open>P \<sim> P'\<close> \<open>P'' \<sim> P'\<close> have "P'' \<sim> P" by(metis transitive symmetric)
        ultimately show ?thesis using \<open>(Q'', P'') \<in> X \<union> bisim\<close> by blast
      next
        case False
        from \<open>(P', Q') \<notin> X\<close> \<open>(P', Q') \<in> X \<union> bisim\<close> have "P' \<sim> Q'" by simp
        with \<open>P \<sim> P'\<close> \<open>Q' \<sim> Q\<close> have "Q \<sim> P" by(metis transitive symmetric)
        thus ?thesis by(blast intro: reflexive)
      qed
    }
    with \<open>(P, Q) \<in> ?X\<close> show ?case by blast
  qed
qed

end
