(* 
   Title: The pi-calculus   
   Author/Maintainer: Jesper Bengtson (jebe.dk), 2012
*)
theory Weak_Late_Bisim_Pres
  imports Weak_Late_Bisim_SC Weak_Late_Sim_Pres Strong_Late_Bisim_SC
begin

lemma tauPres:
  fixes P :: pi
  and   Q :: pi

  assumes "P \<approx> Q"

  shows "\<tau>.(P) \<approx> \<tau>.(Q)"
proof -
  let ?X = "{(\<tau>.(P), \<tau>.(Q)) | P Q. P \<approx> Q}"
  from assms have "(\<tau>.(P), \<tau>.(Q)) \<in> ?X" by auto
  thus ?thesis
    by(coinduct rule: weakBisimCoinduct)
      (auto simp add: pi.inject intro:  Weak_Late_Sim_Pres.tauPres symmetric)
qed

lemma inputPres:
  fixes P :: pi
  and   Q :: pi
  and   a :: name
  and   x :: name

  assumes PSimQ: "\<forall>y. P[x::=y] \<approx> Q[x::=y]"
  
  shows "a<x>.P \<approx> a<x>.Q"
proof -
  let ?X = "{(a<x>.P, a<x>.Q) | a x P Q. \<forall>y. P[x::=y] \<approx> Q[x::=y]}"
  {
    fix axP axQ p
    assume "(axP, axQ) \<in> ?X"
    then obtain a x P Q where A: "\<forall>y. P[x::=y] \<approx> Q[x::=y]" and B: "axP = a<x>.P" and C: "axQ = a<x>.Q"
      by auto
    have "\<And>y. ((p::name prm) \<bullet> P)[(p \<bullet> x)::=y] \<approx> (p \<bullet> Q)[(p \<bullet> x)::=y]"
    proof -
      fix y
      from A have "P[x::=(rev p \<bullet> y)] \<approx> Q[x::=(rev p \<bullet> y)]"
        by blast
      hence "(p \<bullet> (P[x::=(rev p \<bullet> y)])) \<approx> p \<bullet> (Q[x::=(rev p \<bullet> y)])"
        by(rule eqvtI)
      thus "(p \<bullet> P)[(p \<bullet> x)::=y] \<approx> (p \<bullet> Q)[(p \<bullet> x)::=y]"
        by(simp add: eqvts pt_pi_rev[OF pt_name_inst, OF at_name_inst])
    qed
    hence "((p::name prm) \<bullet> axP, p \<bullet> axQ) \<in> ?X" using B C
      by auto
  }
  hence "eqvt ?X" by(simp add: eqvt_def)

  from PSimQ have "(a<x>.P, a<x>.Q) \<in> ?X" by auto
  thus ?thesis
  proof(coinduct rule: weakBisimCoinduct)
    case(cSim P Q)
    thus ?case using \<open>eqvt ?X\<close>
      by(force intro: inputPres)
  next
    case(cSym P Q)
    thus ?case
      by(blast dest: symmetric)
  qed
qed

lemma outputPres:
  fixes P :: pi
  and   Q :: pi
  and   a :: name
  and   b :: name

  assumes "P \<approx> Q"

  shows "a{b}.(P) \<approx> a{b}.(Q)"
proof -
  let ?X = "{(a{b}.(P), a{b}.(Q)) | a b P Q. P \<approx> Q}"
  from assms have "(a{b}.(P), a{b}.(Q)) \<in> ?X" by auto
  thus ?thesis
    by(coinduct rule: weakBisimCoinduct)
      (auto simp add: pi.inject intro:  Weak_Late_Sim_Pres.outputPres symmetric)
qed

lemma resPres:
  fixes P :: pi
  and   Q :: pi
  and   x :: name
  
  assumes PBiSimQ: "P \<approx> Q"

  shows "<\<nu>x>P \<approx> <\<nu>x>Q"
proof -
  let ?X = "{x. \<exists>P Q. P \<approx> Q \<and> (\<exists>a. x = (<\<nu>a>P, <\<nu>a>Q))}"
  from PBiSimQ have "(<\<nu>x>P, <\<nu>x>Q) \<in> ?X" by blast
  moreover have "\<And>P Q a. P \<leadsto>\<^sup>^<weakBisim> Q \<Longrightarrow> <\<nu>a>P \<leadsto>\<^sup>^<(?X \<union> weakBisim)> <\<nu>a>Q"
  proof -
    fix P Q a
    assume PSimQ: "P \<leadsto>\<^sup>^<weakBisim> Q"
    moreover have "\<And>P Q a. P \<approx> Q \<Longrightarrow> (<\<nu>a>P, <\<nu>a>Q) \<in> ?X \<union> weakBisim" by blast
    moreover have "weakBisim \<subseteq> ?X \<union> weakBisim" by blast
    moreover have "eqvt weakBisim" by(rule eqvt)
    moreover have "eqvt (?X \<union> weakBisim)"
      by(auto simp add: eqvt_def dest: eqvtI)+
    ultimately show "<\<nu>a>P \<leadsto>\<^sup>^<(?X \<union> weakBisim)> <\<nu>a>Q"
      by(rule Weak_Late_Sim_Pres.resPres)
  qed
    
  ultimately show ?thesis using PBiSimQ
    by(coinduct rule: weakBisimCoinductAux, blast dest: unfoldE)
qed

lemma matchPres:
  fixes P :: pi
  and   Q :: pi
  and   a :: name
  and   b :: name

  assumes "P \<approx> Q"

  shows "[a\<frown>b]P \<approx> [a\<frown>b]Q"
proof -
  let ?X = "{([a\<frown>b]P, [a\<frown>b]Q) | a b P Q. P \<approx> Q}"
  from assms have "([a\<frown>b]P, [a\<frown>b]Q) \<in> ?X" by auto
  thus ?thesis
  proof(coinduct rule: weakBisimCoinduct)
    case(cSim P Q)
    {
      fix P Q a b
      assume "P \<approx> Q"
      hence "P \<leadsto>\<^sup>^<weakBisim> Q" by(rule unfoldE)
      moreover {
        fix P Q a
        assume "P \<approx> Q"
        moreover have "[a\<frown>a]P \<approx> P" by(rule matchId)
        ultimately have "[a\<frown>a]P \<approx> Q" by(blast intro: transitive)
      }
      moreover have "weakBisim \<subseteq> ?X \<union> weakBisim" by blast
      ultimately have "[a\<frown>b]P \<leadsto>\<^sup>^<(?X \<union> weakBisim)> [a\<frown>b]Q"
        by(rule matchPres)
    }
    with \<open>(P, Q) \<in> ?X\<close> show ?case by auto
  next
    case(cSym P Q)
    thus ?case by(auto simp add: pi.inject dest: symmetric)
  qed
qed

lemma mismatchPres:
  fixes P :: pi
  and   Q :: pi
  and   a :: name
  and   b :: name

  assumes "P \<approx> Q"

  shows "[a\<noteq>b]P \<approx> [a\<noteq>b]Q"
proof -
  let ?X = "{([a\<noteq>b]P, [a\<noteq>b]Q) | a b P Q. P \<approx> Q}"
  from assms have "([a\<noteq>b]P, [a\<noteq>b]Q) \<in> ?X" by auto
  thus ?thesis
  proof(coinduct rule: weakBisimCoinduct)
    case(cSim P Q)
    {
      fix P Q a b
      assume "P \<approx> Q"
      hence "P \<leadsto>\<^sup>^<weakBisim> Q" by(rule unfoldE)
      moreover {
        fix P Q a b
        assume "P \<approx> Q" and "(a::name) \<noteq> b"
        note \<open>P \<approx> Q\<close>
        moreover from \<open>a \<noteq> b\<close> have "[a\<noteq>b]P \<approx> P" by(rule mismatchId)
        ultimately have "[a\<noteq>b]P \<approx> Q" by(blast intro: transitive)
      }
      moreover have "weakBisim \<subseteq> ?X \<union> weakBisim" by blast
      ultimately have "[a\<noteq>b]P \<leadsto>\<^sup>^<(?X \<union> weakBisim)> [a\<noteq>b]Q"
        by(rule mismatchPres)
    }
    with \<open>(P, Q) \<in> ?X\<close> show ?case by auto
  next
    case(cSym P Q)
    thus ?case by(auto simp add: pi.inject dest: symmetric)
  qed
qed

lemma parPres:
  fixes P :: pi
  and   Q :: pi
  and   R :: pi

  assumes "P \<approx> Q"

  shows "P \<parallel> R \<approx> Q \<parallel> R"
proof -
  let ?ParSet = "{(resChain lst (P \<parallel> R), resChain lst (Q \<parallel> R)) | lst P Q R. P \<approx> Q}"
  have BC: "\<And>P Q. P \<parallel> Q = resChain [] (P \<parallel> Q)" by auto
  from assms have "(P \<parallel> R, Q \<parallel> R) \<in> ?ParSet" by(blast intro: BC)
  thus ?thesis
  proof(coinduct rule: weakBisimCoinduct)
    case(cSim PR QR)
    {
      fix P Q R lst
      assume "P \<approx> Q"
    
      from eqvtI have "eqvt (?ParSet \<union> weakBisim)"
        by(auto simp add: eqvt_def, blast)
      moreover have "\<And>P Q a. (P, Q) \<in> ?ParSet \<union> weakBisim \<Longrightarrow> (<\<nu>a>P, <\<nu>a>Q) \<in> ?ParSet \<union> weakBisim"
        by(blast intro: resChain.step[THEN sym] resPres)
      moreover {
        from \<open>P \<approx> Q\<close> have "P \<leadsto>\<^sup>^<weakBisim> Q" by(rule unfoldE)
        moreover note \<open>P \<approx> Q\<close>
        moreover {
          fix P Q R
          assume "P \<approx> Q"
          moreover have "P \<parallel> R = resChain [] (P \<parallel> R)" by simp
          moreover have "Q \<parallel> R = resChain [] (Q \<parallel> R)" by simp
          ultimately have "(P \<parallel> R, Q \<parallel> R) \<in> ?ParSet \<union> weakBisim" by blast
        }
        moreover {
          fix P Q a
          assume A: "(P, Q) \<in> ?ParSet \<union> weakBisim"
          hence "(<\<nu>a>P, <\<nu>a>Q) \<in> ?ParSet \<union> weakBisim" (is "?goal")
            apply(auto intro: resPres)
            by(rule_tac x="a#lst" in exI) auto
        }
        ultimately have "(P \<parallel> R) \<leadsto>\<^sup>^<(?ParSet \<union> weakBisim)> (Q \<parallel> R)" using eqvt \<open>eqvt(?ParSet \<union> weakBisim)\<close>
          by(rule Weak_Late_Sim_Pres.parPres)
      }

      ultimately have "resChain lst (P \<parallel> R) \<leadsto>\<^sup>^<(?ParSet \<union> weakBisim)> resChain lst (Q \<parallel> R)"
        by(rule resChainI)
    }
    with \<open>(PR, QR) \<in> ?ParSet\<close> show ?case by blast
  next
    case(cSym PR QR)
    thus ?case by(auto dest: symmetric)
  qed
qed

lemma bangPres:
  fixes P :: pi
  and   Q :: pi

  assumes PBisimQ: "P \<approx> Q"

  shows "!P \<approx> !Q"
proof -
  let ?X = "(bangRel weakBisim)"
  let ?Y = "Strong_Late_Bisim.bisim O (bangRel weakBisim) O Strong_Late_Bisim.bisim"

  from eqvt Strong_Late_Bisim.bisimEqvt have eqvtY: "eqvt ?Y" by(blast intro: eqvtBangRel)
  have XsubY: "?X \<subseteq> ?Y" by(auto intro: Strong_Late_Bisim.reflexive)

  have RelStay: "\<And>P Q. (P \<parallel> !P, Q) \<in> ?Y \<Longrightarrow> (!P, Q) \<in> ?Y"
  proof(auto)
    fix P Q R T
    assume PBisimQ: "P \<parallel> !P \<sim> Q" 
       and QBRR: "(Q, R) \<in> bangRel weakBisim"
       and RBisimT: "R \<sim> T"
    have "!P \<sim> Q" 
    proof -
      have "!P \<sim> P \<parallel> !P" by(rule Strong_Late_Bisim_SC.bangSC)
      thus ?thesis using PBisimQ by(rule Strong_Late_Bisim.transitive)
    qed
    with QBRR RBisimT show "(!P, T) \<in> ?Y" by blast
  qed
 
  have ParCompose: "\<And>P Q R T. \<lbrakk>P \<approx> Q; (R, T) \<in> ?Y\<rbrakk> \<Longrightarrow> (P \<parallel> R, Q \<parallel> T) \<in> ?Y"
  proof -
    fix P Q R T
    assume PBisimQ: "P \<approx> Q"
       and RYT:     "(R, T) \<in> ?Y"
    thus "(P \<parallel> R, Q \<parallel> T) \<in> ?Y"
    proof(auto)
      fix T' R'
      assume T'BisimT: "T' \<sim> T" and RBisimR': "R \<sim> R'"
         and R'BRT': "(R', T') \<in> bangRel weakBisim"
      have "P \<parallel> R \<sim> P \<parallel> R'"
      proof -
        from RBisimR' have "R \<parallel> P \<sim> R' \<parallel> P" by(rule Strong_Late_Bisim_Pres.parPres)
        moreover have "P \<parallel> R \<sim> R \<parallel> P" and "R' \<parallel> P \<sim> P \<parallel> R'" by(rule Strong_Late_Bisim_SC.parSym)+
        ultimately show ?thesis by(blast intro: Strong_Late_Bisim.transitive)
      qed
      moreover from PBisimQ R'BRT' have "(P \<parallel> R', Q \<parallel> T') \<in> bangRel weakBisim" by(rule BRPar)
      moreover have "Q \<parallel> T' \<sim> Q \<parallel> T"
      proof -
        from T'BisimT have "T' \<parallel> Q \<sim> T \<parallel> Q" by(rule Strong_Late_Bisim_Pres.parPres)
        moreover have "Q \<parallel> T' \<sim> T' \<parallel> Q" and "T \<parallel> Q \<sim> Q \<parallel> T" by(rule Strong_Late_Bisim_SC.parSym)+
        ultimately show ?thesis by(blast intro: Strong_Late_Bisim.transitive)
      qed
      ultimately show ?thesis by blast
    qed
  qed

  have ResCong: "\<And>P Q x. (P, Q) \<in> ?Y \<Longrightarrow> (<\<nu>x>P, <\<nu>x>Q) \<in> ?Y"
    by(auto intro: BRRes Strong_Late_Bisim_Pres.resPres transitive)

  from PBisimQ have "(!P, !Q) \<in> ?X" by(rule BRBang)
  moreover from eqvt have "eqvt (bangRel weakBisim)" by(rule eqvtBangRel)
  ultimately show ?thesis
  proof(coinduct rule: weakBisimTransitiveCoinduct)
    case(cSim P Q)
    from \<open>(P, Q) \<in> ?X\<close>
    show "P \<leadsto>\<^sup>^<?Y> Q"
    proof(induct)
      case(BRBang P Q)
      have "P \<approx> Q" by fact
      moreover hence "P \<leadsto>\<^sup>^<weakBisim> Q" by(blast dest: unfoldE)
      moreover have "\<And>P Q. P \<approx> Q \<Longrightarrow> P \<leadsto>\<^sup>^<weakBisim> Q" by(blast dest: unfoldE)
      moreover from Strong_Late_Bisim.bisimEqvt eqvt have "eqvt ?Y" by(blast intro: eqvtBangRel)

      ultimately show "!P \<leadsto>\<^sup>^<?Y> !Q" using ParCompose ResCong RelStay XsubY
        by(rule_tac Weak_Late_Sim_Pres.bangPres, simp_all)
    next
      case(BRPar P Q R T)
      have PBiSimQ: "P \<approx> Q" by fact
      have RBangRelT: "(R, T) \<in> ?X" by fact
      have RSimT: "R \<leadsto>\<^sup>^<?Y> T" by fact
      moreover from PBiSimQ  have "P \<leadsto>\<^sup>^<weakBisim> Q" by(blast dest: unfoldE)
      moreover from RBangRelT have "(R, T) \<in> ?Y" by(blast intro: Strong_Late_Bisim.reflexive)
      ultimately show "P \<parallel> R \<leadsto>\<^sup>^<?Y> Q \<parallel> T" using ParCompose ResCong eqvt eqvtY \<open>P \<approx> Q\<close>
        by(rule_tac Weak_Late_Sim_Pres.parCompose)
    next
      case(BRRes P Q x)
      have "P \<leadsto>\<^sup>^<?Y> Q" by fact
      thus "<\<nu>x>P \<leadsto>\<^sup>^<?Y> <\<nu>x>Q" using ResCong eqvtY XsubY
        by(rule_tac Weak_Late_Sim_Pres.resPres, simp_all)
    qed
  next
    case(cSym P Q)
    thus ?case by(metis symmetric bangRelSymetric)
  qed
qed

end
