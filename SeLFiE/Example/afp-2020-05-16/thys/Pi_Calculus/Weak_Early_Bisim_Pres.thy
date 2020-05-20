(* 
   Title: The pi-calculus   
   Author/Maintainer: Jesper Bengtson (jebe.dk), 2012
*)
theory Weak_Early_Bisim_Pres
  imports Strong_Early_Bisim_Pres Weak_Early_Sim_Pres Weak_Early_Bisim_SC Weak_Early_Bisim
begin

(************ Preservation rules ************)

lemma tauPres:
  fixes P :: pi
  and   Q :: pi

  assumes "P \<approx> Q"

  shows "\<tau>.(P) \<approx> \<tau>.(Q)"
proof -
  let ?X = "{(\<tau>.(P), \<tau>.(Q)) | P Q. P \<approx> Q}"
  from \<open>P \<approx> Q\<close> have "(\<tau>.(P), \<tau>.(Q)) \<in> ?X" by auto
  thus ?thesis
  proof(coinduct rule: weakBisimCoinduct)
    case(cSim P Q)
    thus ?case
      by(force intro: Weak_Early_Sim_Pres.tauPres)
  next
    case(cSym P Q)
    thus ?case by(force dest: Weak_Early_Bisim.symetric simp add: pi.inject)
  qed
qed

lemma outputPres:
  fixes P :: pi
  and   Q :: pi
  and   a :: name
  and   b :: name

  assumes "P \<approx> Q"

  shows "a{b}.P \<approx> a{b}.Q"
proof -
  let ?X = "{(a{b}.(P), a{b}.(Q)) | P Q a b. P \<approx> Q}"
  from \<open>P \<approx> Q\<close> have "(a{b}.(P), a{b}.(Q)) \<in> ?X" by auto
  thus ?thesis
  proof(coinduct rule: weakBisimCoinduct)
    case(cSim P Q)
    thus ?case
      by(force intro: Weak_Early_Sim_Pres.outputPres)
  next
    case(cSym P Q)
    thus ?case by(force dest: Weak_Early_Bisim.symetric simp add: pi.inject)
  qed
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
        by(rule eqvts)
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
      by(force intro: Weak_Early_Sim_Pres.inputPres)
  next
    case(cSym P Q)
    thus ?case
      by(blast dest: weakBisimE)
  qed
qed

lemma resPres:
  fixes P :: pi
  and   Q :: pi
  and   x :: name
  
  assumes "P \<approx> Q"

  shows "<\<nu>x>P \<approx> <\<nu>x>Q"
proof -
  let ?X = "{(<\<nu>x>P, <\<nu>x>Q) | x P Q. P \<approx> Q}"
  from \<open>P \<approx> Q\<close> have "(<\<nu>x>P, <\<nu>x>Q) \<in> ?X" by blast
  thus ?thesis
  proof(coinduct rule: weakBisimCoinduct)
    case(cSim xP xQ)
    {
      fix P Q x
      assume "P \<approx> Q"
      hence "P \<leadsto><weakBisim> Q" by(rule weakBisimE)
      moreover have "\<And>P Q x. P \<approx> Q \<Longrightarrow> (<\<nu>x>P, <\<nu>x>Q) \<in> ?X \<union> weakBisim" by blast
      moreover have "weakBisim \<subseteq> ?X \<union> weakBisim" by blast
      moreover have "eqvt weakBisim" by simp
      moreover have "eqvt (?X \<union> weakBisim)"
        by(auto simp add: eqvt_def dest: Weak_Early_Bisim.eqvtI)+
      ultimately have "<\<nu>x>P \<leadsto><(?X \<union> weakBisim)> <\<nu>x>Q"
        by(rule Weak_Early_Sim_Pres.resPres)
    }
    with \<open>(xP, xQ) \<in> ?X\<close> show ?case by blast
  next
    case(cSym xP xQ)
    thus ?case by(blast dest: Weak_Early_Bisim.symetric)
  qed
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
  from \<open>P \<approx> Q\<close> have "([a\<frown>b]P, [a\<frown>b]Q) \<in> ?X" by blast
  thus ?thesis
  proof(coinduct rule: weakBisimCoinduct)
    case(cSim abP abQ)
    {
      fix P Q a b
      assume "P \<approx> Q"
      hence "P \<leadsto><weakBisim> Q" by(rule weakBisimE)
      moreover have "weakBisim \<subseteq> (?X \<union> weakBisim)" by blast
      moreover have "\<And>P Q a. P \<approx> Q \<Longrightarrow> [a\<frown>a]P \<approx> Q"
        by (metis (full_types) strongBisimWeakBisim Strong_Early_Bisim_SC.matchId Weak_Early_Bisim.transitive)
      ultimately have"[a\<frown>b]P \<leadsto><(?X \<union> weakBisim)> [a\<frown>b]Q" 
        by(rule Weak_Early_Sim_Pres.matchPres)
    }
    with \<open>(abP, abQ) \<in> ?X\<close> show ?case by blast
  next
    case(cSym abP abQ)
    thus ?case by(blast dest: Weak_Early_Bisim.symetric)
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
  let ?X = "{([a\<noteq>b]P, [a\<noteq>b]Q)| a b P Q. P \<approx> Q}"
  from \<open>P \<approx> Q\<close> have "([a\<noteq>b]P, [a\<noteq>b]Q) \<in> ?X" by blast
  thus ?thesis
  proof(coinduct rule: weakBisimCoinduct)
    case(cSim abP abQ)
    {
      fix P Q a b
      assume "P \<approx> Q"
      hence "P \<leadsto><weakBisim> Q" by(rule weakBisimE)
      moreover have "weakBisim \<subseteq> (?X \<union> weakBisim)" by blast
      moreover have "\<And>P Q a b. \<lbrakk>P \<approx> Q; a \<noteq> b\<rbrakk> \<Longrightarrow> [a\<noteq>b]P \<approx> Q"
        by (metis (full_types) strongBisimWeakBisim Strong_Early_Bisim_SC.mismatchId Weak_Early_Bisim.transitive)
      ultimately have "[a\<noteq>b]P \<leadsto><(?X \<union> weakBisim)> [a\<noteq>b]Q"
        by(rule Weak_Early_Sim_Pres.mismatchPres) 
    }
    with \<open>(abP, abQ) \<in> ?X\<close> show ?case by blast
  next
    case(cSym abP abQ)
    thus ?case by(blast dest: Weak_Early_Bisim.symetric)
  qed
qed

lemma parPres:
  fixes P :: pi
  and   Q :: pi
  and   R :: pi

  assumes "P \<approx> Q"

  shows "P \<parallel> R \<approx> Q \<parallel> R"
proof -
  let ?X = "{(resChain lst (P \<parallel> R), resChain lst (Q \<parallel> R)) | lst P R Q. P \<approx> Q}"
  have BC: "\<And>P Q. P \<parallel> Q = resChain [] (P \<parallel> Q)" by auto
  from \<open>P \<approx> Q\<close> have "(P \<parallel> R, Q \<parallel> R) \<in> ?X" by(blast intro: BC)
  thus ?thesis
  proof(coinduct rule: weakBisimCoinduct)
    case(cSym PR QR)
    {
      fix P Q R lst
      assume "P \<approx> Q"
      moreover hence "P \<leadsto><weakBisim> Q" by(rule weakBisimE)
      moreover have "\<And>P Q R. P \<approx> Q \<Longrightarrow> (P \<parallel> R, Q \<parallel> R) \<in> ?X" using BC
        by blast
      moreover {
        fix PR QR x
        assume "(PR, QR) \<in> ?X"
        then obtain lst P Q R where "P \<approx> Q" and A: "PR = resChain lst (P \<parallel> R)" and B: "QR = resChain lst (Q \<parallel> R)"
          by auto
        from A have "<\<nu>x>PR = resChain (x#lst) (P \<parallel> R)" by auto
        moreover from B have "<\<nu>x>QR = resChain (x#lst) (Q \<parallel> R)" by auto
        ultimately have "(<\<nu>x>PR, <\<nu>x>QR) \<in> ?X" using \<open>P \<approx> Q\<close>
          by blast
      }
      note Res = this
      ultimately have "P \<parallel> R \<leadsto><?X> Q \<parallel> R"
        by(rule_tac Weak_Early_Sim_Pres.parPres)
      moreover have "eqvt ?X"
        by(auto simp add: eqvt_def) (blast intro: eqvts)
      ultimately have "resChain lst (P \<parallel> R) \<leadsto><?X> resChain lst (Q \<parallel> R)" using Res
        by(rule_tac Weak_Early_Sim_Pres.resChainI)
      hence "resChain lst (P \<parallel> R) \<leadsto><(?X \<union> weakBisim)> resChain lst (Q \<parallel> R)"
        by(force intro: Weak_Early_Sim.monotonic)
    }
    with \<open>(PR, QR) \<in> ?X\<close> show "PR \<leadsto><(?X \<union> weakBisim)> QR"
      by blast
  next
    case(cSym PR QR)
    thus ?case by(blast dest: Weak_Early_Bisim.symetric)
  qed
qed

lemma bangPres:
  fixes P :: pi
  and   Q :: pi

  assumes PBisimQ: "P \<approx> Q"

  shows "!P \<approx> !Q"
proof -
  let ?X = "(bangRel weakBisim)"
  let ?Y = "Strong_Early_Bisim.bisim O (bangRel weakBisim) O Strong_Early_Bisim.bisim"

  from Weak_Early_Bisim.eqvt Strong_Early_Bisim.eqvt have eqvtY: "eqvt ?Y" by(blast intro: eqvtBangRel)
  have XsubY: "?X \<subseteq> ?Y" by(auto intro: Strong_Early_Bisim.reflexive)

  have RelStay: "\<And>P Q. (P \<parallel> !P, Q) \<in> ?Y \<Longrightarrow> (!P, Q) \<in> ?Y"
  proof(auto)
    fix P Q R T
    assume PBisimQ: "P \<parallel> !P \<sim>\<^sub>e Q" 
       and QBRR: "(Q, R) \<in> bangRel weakBisim"
       and RBisimT: "R \<sim>\<^sub>e T"
    have "!P \<sim>\<^sub>e Q" 
    proof -
      have "!P \<sim>\<^sub>e P \<parallel> !P" by(rule Strong_Early_Bisim_SC.bangSC)
      thus ?thesis using PBisimQ by(rule Strong_Early_Bisim.transitive)
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
      assume T'BisimT: "T' \<sim>\<^sub>e T" and RBisimR': "R \<sim>\<^sub>e R'"
         and R'BRT': "(R', T') \<in> bangRel weakBisim"
      have "P \<parallel> R \<sim>\<^sub>e P \<parallel> R'"
      proof -
        from RBisimR' have "R \<parallel> P \<sim>\<^sub>e R' \<parallel> P" by(rule Strong_Early_Bisim_Pres.parPres)
        moreover have "P \<parallel> R \<sim>\<^sub>e R \<parallel> P" and "R' \<parallel> P \<sim>\<^sub>e P \<parallel> R'" by(rule Strong_Early_Bisim_SC.parSym)+
        ultimately show ?thesis by(blast intro: Strong_Early_Bisim.transitive)
      qed
      moreover from PBisimQ R'BRT' have "(P \<parallel> R', Q \<parallel> T') \<in> bangRel weakBisim" by(rule BRPar)
      moreover have "Q \<parallel> T' \<sim>\<^sub>e Q \<parallel> T"
      proof -
        from T'BisimT have "T' \<parallel> Q \<sim>\<^sub>e T \<parallel> Q" by(rule Strong_Early_Bisim_Pres.parPres)
        moreover have "Q \<parallel> T' \<sim>\<^sub>e T' \<parallel> Q" and "T \<parallel> Q \<sim>\<^sub>e Q \<parallel> T" by(rule Strong_Early_Bisim_SC.parSym)+
        ultimately show ?thesis by(blast intro: Strong_Early_Bisim.transitive)
      qed
      ultimately show ?thesis by blast
    qed
  qed

  have ResCong: "\<And>P Q x. (P, Q) \<in> ?Y \<Longrightarrow> (<\<nu>x>P, <\<nu>x>Q) \<in> ?Y"
    by(auto intro: BRRes Strong_Early_Bisim_Pres.resPres transitive)

  have Sim: "\<And>P Q. (P, Q) \<in> ?X \<Longrightarrow> P \<leadsto><?Y> Q"
  proof -
    fix P Q
    assume "(P, Q) \<in> ?X"
    thus "P \<leadsto><?Y> Q"
    proof(induct)
      case(BRBang P Q)
      have "P \<approx> Q" by fact
      moreover hence "P \<leadsto><weakBisim> Q" by(blast dest: weakBisimE)
      moreover have "\<And>P Q. P \<approx> Q \<Longrightarrow> P \<leadsto><weakBisim> Q" by(blast dest: weakBisimE)
      moreover from Strong_Early_Bisim.eqvt Weak_Early_Bisim.eqvt have "eqvt ?Y" by(blast intro: eqvtBangRel)

      ultimately show "!P \<leadsto><?Y> !Q" using ParCompose ResCong RelStay XsubY
        by(rule_tac Weak_Early_Sim_Pres.bangPres, simp_all)
    next
      case(BRPar P Q R T)
      have PBiSimQ: "P \<approx> Q" by fact
      moreover have RBangRelT: "(R, T) \<in> ?X" by fact
      have RSimT: "R \<leadsto><?Y> T" by fact
      moreover from PBiSimQ  have "P \<leadsto><weakBisim> Q" by(blast dest: weakBisimE)
      moreover from RBangRelT have "(R, T) \<in> ?Y" by(blast intro: Strong_Early_Bisim.reflexive)
      ultimately show "P \<parallel> R \<leadsto><?Y> Q \<parallel> T" using ParCompose ResCong eqvt eqvtY
        by(rule_tac Weak_Early_Sim_Pres.parCompose)
    next
      case(BRRes P Q x)
      have "P \<leadsto><?Y> Q" by fact
      thus "<\<nu>x>P \<leadsto><?Y> <\<nu>x>Q" using ResCong eqvtY XsubY
        by(rule_tac Weak_Early_Sim_Pres.resPres, simp_all)
    qed
  qed

  from PBisimQ have "(!P, !Q) \<in> ?X" by(rule BRBang)
  moreover from Weak_Early_Bisim.eqvt have "eqvt (bangRel weakBisim)" by(rule eqvtBangRel)
  ultimately show ?thesis
    apply(coinduct rule: Weak_Early_Bisim.transitive_coinduct_weak)
    apply(blast intro: Sim)
    by(blast dest: bangRelSymetric Weak_Early_Bisim.symetric intro: Strong_Early_Bisim.reflexive)
qed

lemma bangRelSubWeakBisim:
  shows "bangRel weakBisim \<subseteq> weakBisim"
proof(auto)
  fix a b
  assume "(a, b) \<in> bangRel weakBisim"
  thus "a \<approx> b"
  proof(induct)
    fix P Q
    assume "P \<approx> Q"
    thus "!P \<approx> !Q" by(rule bangPres)
  next
    fix P Q R T
    assume "R \<approx> T" and "P \<approx> Q"
    thus "R \<parallel> P \<approx> T \<parallel> Q" by(metis parPres parSym Weak_Early_Bisim.transitive)
  next
    fix P Q
    fix a::name
    assume "P \<approx> Q"
    thus "<\<nu>a>P \<approx> <\<nu>a>Q" by(rule resPres)
  qed
qed

end
