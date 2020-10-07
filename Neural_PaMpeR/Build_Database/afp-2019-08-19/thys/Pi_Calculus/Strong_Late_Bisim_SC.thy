(* 
   Title: The pi-calculus   
   Author/Maintainer: Jesper Bengtson (jebe.dk), 2012
*)
theory Strong_Late_Bisim_SC
  imports Strong_Late_Bisim_Pres Strong_Late_Sim_SC
begin

lemma nilBisim[dest]:
  fixes a :: name
  and   b :: name
  and   x :: name
  and   P :: pi

  shows "\<tau>.(P) \<sim> \<zero> \<Longrightarrow> False"
  and   "a<x>.P \<sim> \<zero> \<Longrightarrow> False"
  and   "a{b}.P \<sim> \<zero> \<Longrightarrow> False"
  and   "\<zero> \<sim> \<tau>.(P) \<Longrightarrow> False"
  and   "\<zero> \<sim> a<x>.P \<Longrightarrow> False"
  and   "\<zero> \<sim> a{b}.P \<Longrightarrow> False"
by(auto dest: bisimE symmetric)

(******** Structural Congruence **********)

lemma matchId:
  fixes a :: name
  and   P :: pi

  shows "[a\<frown>a]P \<sim> P"
proof -
  let ?X = "{([a\<frown>a]P, P), (P, [a\<frown>a]P)}"
  have "([a\<frown>a]P, P) \<in> ?X" by simp
  thus ?thesis
    by(coinduct rule: bisimCoinduct) (auto intro: matchIdLeft matchIdRight reflexive)
qed

lemma matchNil:
  fixes a :: name
  and   b :: name

  assumes "a \<noteq> b"

  shows "[a\<frown>b]P \<sim> \<zero>"
proof -
  let ?X = "{([a\<frown>b]P, \<zero>), (\<zero>, [a\<frown>b]P)}"
  have "([a\<frown>b]P, \<zero>) \<in> ?X" by simp
  thus ?thesis using \<open>a \<noteq> b\<close>
    by(coinduct rule: bisimCoinduct) (auto intro: matchNilLeft nilSimRight reflexive)
qed

lemma mismatchId:
  fixes a :: name
  and   b :: name
  and   P :: pi

  assumes "a \<noteq> b"

  shows "[a\<noteq>b]P \<sim> P"
proof -
  let ?X = "{([a\<noteq>b]P, P), (P, [a\<noteq>b]P)}"
  have "([a\<noteq>b]P, P) \<in> ?X" by simp
  thus ?thesis using \<open>a \<noteq> b\<close>
    by(coinduct rule: bisimCoinduct) (auto intro: mismatchIdLeft mismatchIdRight reflexive)
qed

lemma mismatchNil:
  fixes a :: name
  and   P :: pi
  
  shows "[a\<noteq>a]P \<sim> \<zero>"
proof -
  let ?X = "{([a\<noteq>a]P, \<zero>), (\<zero>, [a\<noteq>a]P)}"
  have "([a\<noteq>a]P, \<zero>) \<in> ?X" by simp
  thus ?thesis
    by(coinduct rule: bisimCoinduct) (auto intro: mismatchNilLeft nilSimRight reflexive)
qed
(******** The \<nu>-operator *****************)

lemma nilRes:
  fixes x :: name

  shows "<\<nu>x>\<zero> \<sim> \<zero>"
proof -
  let ?X = "{(<\<nu>x>\<zero>, \<zero>), (\<zero>, <\<nu>x>\<zero>)}"
  have "(<\<nu>x>\<zero>, \<zero>) \<in> ?X" by simp
  thus ?thesis
    by(coinduct rule: bisimCoinduct) (auto intro: nilSimRight resNilRight)
qed

lemma resComm:
  fixes x :: name
  and   y :: name
  and   P :: pi
  
  shows "<\<nu>x><\<nu>y>P \<sim> <\<nu>y><\<nu>x>P"
proof -
  let ?X = "{(<\<nu>x><\<nu>y>P, <\<nu>y><\<nu>x>P) | x y P. True}"
  have "(<\<nu>x><\<nu>y>P, <\<nu>y><\<nu>x>P) \<in> ?X" by auto
  thus ?thesis
  proof(coinduct rule: bisimCoinduct)
    case(cSim xyP yxP)
    {
      fix x y P
      have "\<And>x y P. (<\<nu>x><\<nu>y>P, <\<nu>y><\<nu>x>P) \<in> ?X \<union> bisim" by auto
      moreover have "Id \<subseteq> ?X \<union> bisim" by(auto intro: reflexive)
      moreover have "eqvt ?X" by(force simp add: eqvt_def)
      hence "eqvt(?X \<union> bisim)" by auto
      ultimately have "<\<nu>x><\<nu>y>P \<leadsto>[(?X \<union> bisim)] <\<nu>y><\<nu>x>P" by(rule resComm)
    }
    with \<open>(xyP, yxP) \<in> ?X\<close> show ?case by auto
  next
    case(cSym xyP yxP)
    thus ?case by auto
  qed
qed

(******** The +-operator *********)

lemma sumSym:
  fixes P :: pi
  and   Q :: pi
  
  shows "P \<oplus> Q \<sim> Q \<oplus> P"
proof -
  let ?X = "{(P \<oplus> Q, Q \<oplus> P), (Q \<oplus> P, P \<oplus> Q)}"
  have "(P \<oplus> Q, Q \<oplus> P) \<in> ?X" by simp
  thus ?thesis
    by(coinduct rule: bisimCoinduct) (auto intro: reflexive sumSym)
qed

lemma sumIdemp:
  fixes P :: pi
  
  shows "P \<oplus> P \<sim> P"
proof -
  let ?X = "{(P \<oplus> P, P), (P, P \<oplus> P)}"
  have "(P \<oplus> P, P) \<in> ?X" by simp
  thus ?thesis
    by(coinduct rule: bisimCoinduct) (auto intro: reflexive sumIdempLeft sumIdempRight)
qed

lemma sumAssoc:
  fixes P :: pi
  and   Q :: pi
  and   R :: pi
  
  shows "(P \<oplus> Q) \<oplus> R \<sim> P \<oplus> (Q \<oplus> R)"
proof -
  let ?X = "{((P \<oplus> Q) \<oplus> R, P \<oplus> (Q \<oplus> R)), (P \<oplus> (Q \<oplus> R), (P \<oplus> Q) \<oplus> R)}"
  have "((P \<oplus> Q) \<oplus> R, P \<oplus> (Q \<oplus> R)) \<in> ?X" by simp
  thus ?thesis
    by(coinduct rule: bisimCoinduct) (auto intro: reflexive sumAssocLeft sumAssocRight)
qed

lemma sumZero:
  fixes P :: pi
  
  shows "P \<oplus> \<zero> \<sim> P"
proof -
  let ?X = "{(P \<oplus> \<zero>, P), (P, P \<oplus> \<zero>)}"
  have "(P \<oplus> \<zero>, P) \<in> ?X" by simp
  thus ?thesis
    by(coinduct rule: bisimCoinduct) (auto intro: reflexive sumZeroLeft sumZeroRight)
qed

(******** The |-operator *********)

lemma parZero:
  fixes P :: pi
  
  shows "P \<parallel> \<zero> \<sim> P"
proof -
  let ?X = "{(P \<parallel> \<zero>, P) | P. True} \<union> {(P, P \<parallel> \<zero>) | P . True}"
  have "(P \<parallel> \<zero>, P) \<in> ?X" by blast
  thus ?thesis
    by(coinduct rule: bisimCoinduct, auto intro: parZeroRight parZeroLeft)
qed

lemma parSym:
  fixes P :: pi
  and   Q :: pi

  shows "P \<parallel> Q \<sim> Q \<parallel> P"
proof -
  let ?X = "{(resChain lst (P \<parallel> Q), resChain lst (Q \<parallel> P)) | lst P Q. True}"
  have "(P \<parallel> Q, Q \<parallel> P) \<in> ?X" by(blast intro: resChain.base[THEN sym])
  thus ?thesis
  proof(coinduct rule: bisimCoinduct)
    case(cSim PQ QP)
    {
      fix lst P Q
      have "\<And>P Q. (P \<parallel> Q, Q \<parallel> P) \<in> ?X \<union> bisim" by(blast intro: resChain.base[THEN sym])
      moreover have Res: "\<And>x P Q. (P, Q) \<in> ?X \<union> bisim \<Longrightarrow> (<\<nu>x>P, <\<nu>x>Q) \<in> ?X \<union> bisim"
        by(auto intro: resPres resChain.step[THEN sym])
      ultimately have "P \<parallel> Q \<leadsto>[(?X \<union> bisim)] Q \<parallel> P" by(rule parSym)
      moreover have "eqvt ?X" by(force simp add: eqvt_def) 
      hence "eqvt(?X \<union> bisim)" by auto
      ultimately have "resChain lst (P \<parallel> Q) \<leadsto>[(?X \<union> bisim)] resChain lst (Q \<parallel> P)" using Res
        by(rule resChainI)
    }
    with \<open>(PQ, QP) \<in> ?X\<close> show ?case by auto
  next
    case(cSym PQ QP)
    thus ?case by auto
  qed
qed

lemma scopeExtPar:
  fixes P :: pi
  and   Q :: pi
  and   x :: name

  assumes "x \<sharp> P"

  shows "<\<nu>x>(P \<parallel> Q) \<sim> P \<parallel> <\<nu>x>Q"
proof -
  let ?X = "{(resChain lst (<\<nu>x>(P \<parallel> Q)), resChain lst (P \<parallel> <\<nu>x>Q)) | lst x P Q. x \<sharp> P} \<union>
            {(resChain lst (P \<parallel> <\<nu>x>Q), resChain lst (<\<nu>x>(P \<parallel> Q))) | lst x P Q. x \<sharp> P}"
  let ?Y = "bisim O (?X \<union> bisim) O bisim"

  have Res: "\<And>P Q x. (P, Q) \<in> ?X \<Longrightarrow> (<\<nu>x>P, <\<nu>x>Q) \<in> ?X" by(blast intro: resChain.step[THEN sym])

  from \<open>x \<sharp> P\<close> have "(<\<nu>x>(P \<parallel> Q), P \<parallel> <\<nu>x>Q) \<in> ?X" by(blast intro: resChain.base[THEN sym])
  moreover have EqvtX: "eqvt ?X" by(fastforce simp add: eqvt_def name_fresh_left name_rev_per)
  ultimately show ?thesis
  proof(coinduct rule: bisimTransitiveCoinduct)
    case(cSim P Q)
    {
      fix P Q lst x
      assume "(x::name) \<sharp> (P::pi)"
      moreover have "Id \<subseteq> ?Y" by(blast intro: reflexive)
      moreover from \<open>eqvt ?X\<close> bisimEqvt have "eqvt ?Y" by blast
      moreover have "\<And>P Q x. x \<sharp> P \<Longrightarrow> (<\<nu>x>(P \<parallel> Q), P \<parallel> <\<nu>x>Q) \<in> ?Y"
        by(blast intro: resChain.base[THEN sym] reflexive)
      moreover {
        fix P Q x y
        have "<\<nu>x><\<nu>y>(P \<parallel> Q) \<sim> <\<nu>y><\<nu>x>(P \<parallel> Q)" by(rule resComm)
        moreover assume "x \<sharp> P"
        hence "(<\<nu>x>(P \<parallel> Q), P \<parallel> <\<nu>x>Q) \<in> ?X" by(fastforce intro: resChain.base[THEN sym])
        hence "(<\<nu>y><\<nu>x>(P \<parallel> Q), <\<nu>y>(P \<parallel> <\<nu>x>Q)) \<in> ?X" by(rule Res)
        ultimately have  "(<\<nu>x><\<nu>y>(P \<parallel> Q), <\<nu>y>(P \<parallel> <\<nu>x>Q)) \<in> ?Y" by(blast intro: reflexive)
      }
      ultimately have "<\<nu>x>(P \<parallel> Q) \<leadsto>[?Y] (P \<parallel> <\<nu>x>Q)" by(rule scopeExtParLeft) 
      moreover note \<open>eqvt ?Y\<close>
      moreover from Res have "\<And>P Q x. (P, Q) \<in> ?Y \<Longrightarrow> (<\<nu>x>P, <\<nu>x>Q) \<in> ?Y"
        by(blast intro: resChain.step[THEN sym] dest: resPres)
      ultimately have "resChain lst (<\<nu>x>(P \<parallel> Q)) \<leadsto>[?Y] resChain lst (P \<parallel> <\<nu>x>Q)" 
        by(rule resChainI)
    }
    moreover {
      fix P Q lst x
      assume "(x::name) \<sharp> (P::pi)"
      moreover have "Id \<subseteq> ?Y" by(blast intro: reflexive)
      moreover from \<open>eqvt ?X\<close> bisimEqvt have "eqvt ?Y" by blast
      moreover have "\<And>P Q x. x \<sharp> P \<Longrightarrow> (P \<parallel> <\<nu>x>Q, <\<nu>x>(P \<parallel> Q)) \<in> ?Y"
        by(blast intro: resChain.base[THEN sym] reflexive)
      moreover {
        fix P Q x y
        have "<\<nu>y><\<nu>x>(P \<parallel> Q) \<sim> <\<nu>x><\<nu>y>(P \<parallel> Q)" by(rule resComm)
        moreover assume "x \<sharp> P"
        hence "(P \<parallel> <\<nu>x>Q, <\<nu>x>(P \<parallel> Q)) \<in> ?X" by(fastforce intro: resChain.base[THEN sym])
        hence "(<\<nu>y>(P \<parallel> <\<nu>x>Q), <\<nu>y><\<nu>x>(P \<parallel> Q)) \<in> ?X" by(rule Res)
        ultimately have  "(<\<nu>y>(P \<parallel> <\<nu>x>Q), <\<nu>x><\<nu>y>(P \<parallel> Q)) \<in> ?Y" by(blast intro: reflexive)
      }
      ultimately have "(P \<parallel> <\<nu>x>Q) \<leadsto>[?Y] <\<nu>x>(P \<parallel> Q)" 
        by(rule scopeExtParRight) 
      moreover note \<open>eqvt ?Y\<close>
      moreover from Res have "\<And>P Q x. (P, Q) \<in> ?Y \<Longrightarrow> (<\<nu>x>P, <\<nu>x>Q) \<in> ?Y"
        by(blast intro: resChain.step[THEN sym] dest: resPres)
      ultimately have "resChain lst (P \<parallel> <\<nu>x>Q) \<leadsto>[?Y] resChain lst (<\<nu>x>(P \<parallel> Q))" 
        by(rule resChainI)
    }
    ultimately show ?case using \<open>(P, Q) \<in> ?X\<close> by auto
  next
    case(cSym P Q)
    thus ?case 
      by auto (blast dest: symmetric transitive intro: resChain.base[THEN sym] reflexive)+
  qed
qed

lemma scopeExtPar':
  fixes P :: pi
  and   Q :: pi
  and   x :: name

  assumes xFreshQ: "x \<sharp> Q"

  shows "<\<nu>x>(P \<parallel> Q) \<sim> (<\<nu>x>P) \<parallel> Q"
proof -
  have "<\<nu>x>(P \<parallel> Q) \<sim> <\<nu>x>(Q \<parallel> P)"
  proof -
    have "P \<parallel> Q \<sim> Q \<parallel> P" by(rule parSym)
    thus ?thesis by(rule resPres)
  qed
  moreover from xFreshQ have "<\<nu>x>(Q \<parallel> P) \<sim> Q \<parallel> (<\<nu>x>P)" by(rule scopeExtPar)
  moreover have "Q \<parallel> <\<nu>x>P \<sim> (<\<nu>x>P) \<parallel> Q" by(rule parSym)
  ultimately show ?thesis by(blast intro: transitive)
qed

lemma parAssoc:
  fixes P :: pi
  and   Q :: pi
  and   R :: pi

  shows "(P \<parallel> Q) \<parallel> R \<sim> P \<parallel> (Q \<parallel> R)"
proof -
  let ?X = "{(resChain lst ((P \<parallel> Q) \<parallel> R), resChain lst (P \<parallel> (Q \<parallel> R))) | lst P Q R. True}"
  let ?Y = "bisim O (?X \<union> bisim) O bisim"

  have ResX: "\<And>P Q x. (P, Q) \<in> ?X \<Longrightarrow> (<\<nu>x>P, <\<nu>x>Q) \<in> ?X" 
    by(blast intro: resChain.step[symmetric])
  hence ResY: "\<And>P Q x. (P, Q) \<in> ?Y \<Longrightarrow> (<\<nu>x>P, <\<nu>x>Q) \<in> ?Y"
    by(blast intro: resChain.step[symmetric] dest: resPres)

  have "((P \<parallel> Q) \<parallel> R, P \<parallel> (Q \<parallel> R)) \<in> ?X" by(blast intro: resChain.base[symmetric])
  moreover have "eqvt ?X" by(fastforce simp add: eqvt_def) 
  ultimately show ?thesis
  proof(coinduct rule: bisimTransitiveCoinduct)
    case(cSim P Q)
    {
      fix P Q R lst
      have "\<And>P Q R. ((P \<parallel> Q) \<parallel> R, P \<parallel> (Q \<parallel> R)) \<in> ?Y" by(blast intro: reflexive resChain.base[symmetric])
      moreover have "\<And>P Q x. (P, Q) \<in> ?Y \<Longrightarrow> (<\<nu>x>P, <\<nu>x>Q) \<in> ?Y" by(blast intro: resChain.step[symmetric] resPres)
      moreover {
        fix P Q R x
        have "(<\<nu>x>((P \<parallel> Q) \<parallel> R), <\<nu>x>(P \<parallel> (Q \<parallel> R))) \<in> ?X" by(rule_tac ResX) (blast intro: resChain.base[symmetric])
        moreover assume "x \<sharp> P"
        hence "<\<nu>x>(P \<parallel> (Q \<parallel> R)) \<sim> P \<parallel> <\<nu>x>(Q \<parallel> R)" by(rule scopeExtPar)
        ultimately have "(<\<nu>x>((P \<parallel> Q) \<parallel> R), P \<parallel> <\<nu>x>(Q \<parallel> R)) \<in> ?Y" by(blast intro: reflexive)
      }
      moreover {
        fix P Q R x
        have "(<\<nu>x>((P \<parallel> Q) \<parallel> R), <\<nu>x>(P \<parallel> (Q \<parallel> R))) \<in> ?X" by(rule_tac ResX) (blast intro: resChain.base[symmetric])
        moreover assume "x \<sharp> R"
        hence "<\<nu>x>(P \<parallel> Q) \<parallel> R \<sim> <\<nu>x>((P \<parallel> Q) \<parallel> R)" by(metis scopeExtPar' symmetric)
        ultimately have "(<\<nu>x>(P \<parallel> Q) \<parallel> R, <\<nu>x>(P \<parallel> (Q \<parallel> R))) \<in> ?Y" by(blast intro: reflexive)
      }
      ultimately have "(P \<parallel> Q) \<parallel> R \<leadsto>[?Y] P \<parallel> (Q \<parallel> R)" by(rule parAssocLeft)
      moreover from \<open>eqvt ?X\<close> bisimEqvt have "eqvt ?Y" by blast
      ultimately have "resChain lst ((P \<parallel> Q) \<parallel> R) \<leadsto>[?Y] resChain lst (P \<parallel> (Q \<parallel> R))" using ResY
        by(rule resChainI)
    }
    with \<open>(P, Q) \<in> ?X\<close> show ?case by auto
  next
    case(cSym P Q)
    {
      fix P Q R lst
      have "P \<parallel> (Q \<parallel> R) \<sim> (R \<parallel> Q) \<parallel> P" by(metis parPres parSym transitive)
      moreover have "((R \<parallel> Q) \<parallel> P, R \<parallel> (Q \<parallel> P)) \<in> ?X" by(blast intro: resChain.base[symmetric])
      moreover have "R \<parallel> (Q \<parallel> P) \<sim> (P \<parallel> Q) \<parallel> R" by(metis parPres parSym transitive)
      ultimately have "(P \<parallel> (Q \<parallel> R), (P \<parallel> Q) \<parallel> R) \<in> ?Y" by blast
      hence "(resChain lst (P \<parallel> (Q \<parallel> R)), resChain lst ((P \<parallel> Q) \<parallel> R)) \<in> ?Y" using ResY
        by(induct lst) auto
    }
    with \<open>(P, Q) \<in> ?X\<close> show ?case by blast
  qed
qed

lemma scopeFresh:
  fixes x :: name
  and   P :: pi

  assumes "x \<sharp> P"

  shows "<\<nu>x>P \<sim> P"
proof -
  have "<\<nu>x>P \<sim> <\<nu>x>P \<parallel> \<zero>" by(rule parZero[THEN symmetric])

  moreover have "<\<nu>x>P \<parallel> \<zero> \<sim> \<zero> \<parallel> <\<nu>x>P" by(rule parSym)
  moreover have "\<zero> \<parallel> <\<nu>x>P \<sim> <\<nu>x>(\<zero> \<parallel> P)" by(rule scopeExtPar[THEN symmetric]) auto
  moreover have "<\<nu>x>(\<zero> \<parallel> P) \<sim> <\<nu>x>(P \<parallel> \<zero>)" by(rule resPres[OF parSym])
  moreover from \<open>x \<sharp> P\<close> have "<\<nu>x>(P \<parallel> \<zero>) \<sim> P \<parallel> <\<nu>x>\<zero>" by(rule scopeExtPar)
  moreover have  "P \<parallel> <\<nu>x>\<zero> \<sim> <\<nu>x>\<zero> \<parallel> P" by(rule parSym)
  moreover have "<\<nu>x>\<zero> \<parallel> P \<sim> \<zero> \<parallel> P" by(rule parPres[OF nilRes])
  moreover have "\<zero> \<parallel> P \<sim> P \<parallel> \<zero>" by(rule parSym)
  moreover have "P \<parallel> \<zero> \<sim> P" by(rule parZero)
  ultimately show ?thesis by(metis transitive)
qed

lemma sumRes:
  fixes x :: name
  and   P :: pi
  and   Q :: pi

  shows "<\<nu>x>(P \<oplus> Q) \<sim> (<\<nu>x>P) \<oplus> (<\<nu>x>Q)"
proof -
  let ?X = "{(<\<nu>x>(P \<oplus> Q), <\<nu>x>P \<oplus> <\<nu>x>Q) | x P Q. True} \<union>
            {(<\<nu>x>P \<oplus> <\<nu>x>Q, <\<nu>x>(P \<oplus> Q)) | x P Q. True}"
  have "(<\<nu>x>(P \<oplus> Q), <\<nu>x>P \<oplus> <\<nu>x>Q) \<in> ?X" by auto
  moreover have "eqvt ?X" by(fastforce simp add: eqvt_def)
  ultimately show ?thesis
    by(coinduct rule: bisimCoinduct) (fastforce intro: sumResLeft sumResRight reflexive)+
qed


lemma scopeExtSum:
  fixes P :: pi
  and   Q :: pi
  and   x :: name
  
  assumes "x \<sharp> P"

  shows "<\<nu>x>(P \<oplus> Q) \<sim> P \<oplus> <\<nu>x>Q"
proof -
  have "<\<nu>x>(P \<oplus> Q) \<sim> <\<nu>x>P \<oplus> <\<nu>x>Q" by(rule sumRes)
  moreover from \<open>x \<sharp> P\<close> have "<\<nu>x>P \<oplus> <\<nu>x>Q \<sim> P \<oplus> <\<nu>x>Q"
    by(rule sumPres[OF scopeFresh])
  ultimately show ?thesis by(rule transitive)
qed

lemma bangSC:
  fixes P :: pi

  shows "!P \<sim> P \<parallel> !P"
proof -
  let ?X = "{(!P, P \<parallel> !P), (P \<parallel> !P, !P)}"
  have "(!P, P \<parallel> !P) \<in> ?X" by simp
  thus ?thesis
    by(coinduct rule: bisimCoinduct) (auto intro: bangLeftSC bangRightSC reflexive)
qed

lemma resNil:
  fixes x :: name
  and   y :: name
  and   P :: pi
  and   b :: name

  shows "<\<nu>x>x<y>.P \<sim> \<zero>"
  and   "<\<nu>x>x{b}.P \<sim> \<zero>"
proof -
  let ?X = "{(<\<nu>x>x<y>.P, \<zero>), (\<zero>, <\<nu>x>x<y>.P)}"
  have "(<\<nu>x>x<y>.P, \<zero>) \<in> ?X" by simp
  thus "<\<nu>x>x<y>.P \<sim> \<zero>"
    by(coinduct rule: bisimCoinduct) (auto simp add: simulation_def)
next
  let ?X = "{(<\<nu>x>x{b}.P, \<zero>), (\<zero>, <\<nu>x>x{b}.P)}"
  have "(<\<nu>x>x{b}.P, \<zero>) \<in> ?X" by simp
  thus "<\<nu>x>x{b}.P \<sim> \<zero>"
    by(coinduct rule: bisimCoinduct) (auto simp add: simulation_def)
qed

lemma resInput:
  fixes x :: name
  and   a :: name
  and   y :: name
  and   P :: pi

  assumes "x \<noteq> a"
  and     "x \<noteq> y"

  shows "<\<nu>x>a<y>.P \<sim> a<y>.(<\<nu>x>P)"
proof -
  let ?X = "{(<\<nu>x>a<y>.P, a<y>.(<\<nu>x>P)) | x a y P. x \<noteq> a \<and> x \<noteq> y} \<union>
            {(a<y>.(<\<nu>x>P), <\<nu>x>a<y>.P) | x a y P. x \<noteq> a \<and> x \<noteq> y}"
  from assms have "(<\<nu>x>a<y>.P, a<y>.(<\<nu>x>P)) \<in> ?X" by auto
  moreover have "eqvt ?X" by(fastforce simp add: eqvt_def pt_bij[OF pt_name_inst, OF at_name_inst])
  ultimately show ?thesis
    by(coinduct rule: bisimCoinduct) (fastforce intro: resInputLeft reflexive resInputRight)+
qed

lemma resOutput:
  fixes x :: name
  and   a :: name
  and   b :: name
  and   P :: pi

  assumes "x \<noteq> a"
  and     "x \<noteq> b"

  shows "<\<nu>x>a{b}.P \<sim> a{b}.(<\<nu>x>P)"
proof -
  let ?X = "{(<\<nu>x>a{b}.P, a{b}.(<\<nu>x>P)) | x a b P. x \<noteq> a \<and> x \<noteq> b} \<union>
            {(a{b}.(<\<nu>x>P), <\<nu>x>a{b}.P) | x a b P. x \<noteq> a \<and> x \<noteq> b}"
  from assms have "(<\<nu>x>a{b}.P, a{b}.(<\<nu>x>P)) \<in> ?X" by blast
  moreover have "eqvt ?X" by(fastforce simp add: eqvt_def pt_bij[OF pt_name_inst, OF at_name_inst])
  ultimately show ?thesis
    by(coinduct rule: bisimCoinduct) (fastforce intro: resOutputLeft resOutputRight reflexive)+
qed

lemma resTau:
  fixes x :: name
  and   P :: pi

  shows "<\<nu>x>\<tau>.(P) \<sim> \<tau>.(<\<nu>x>P)"
proof -
  let ?X = "{(<\<nu>x>\<tau>.(P), \<tau>.(<\<nu>x>P)), (\<tau>.(<\<nu>x>P), <\<nu>x>\<tau>.(P))}"
  have "(<\<nu>x>\<tau>.(P), \<tau>.(<\<nu>x>P)) \<in> ?X" by auto
  thus ?thesis
    by(coinduct rule: bisimCoinduct) (fastforce intro: resTauLeft resTauRight reflexive)+
qed

inductive structCong :: "pi \<Rightarrow> pi \<Rightarrow> bool" ("_ \<equiv>\<^sub>s _" [70, 70] 70)
where
  Refl: "P \<equiv>\<^sub>s P"
| Sym:  "P \<equiv>\<^sub>s Q \<Longrightarrow> Q \<equiv>\<^sub>s P"
| Trans: "\<lbrakk>P \<equiv>\<^sub>s Q; Q \<equiv>\<^sub>s R\<rbrakk> \<Longrightarrow> P \<equiv>\<^sub>s R"

| SumComm: "P \<oplus> Q \<equiv>\<^sub>s Q \<oplus> P"
| SumAssoc: "(P \<oplus> Q) \<oplus> R \<equiv>\<^sub>s P \<oplus> (Q \<oplus> R)"
| SumId: "P \<oplus> \<zero> \<equiv>\<^sub>s P"

| ParComm: "P \<parallel> Q \<equiv>\<^sub>s Q \<parallel> P"
| ParAssoc: "(P \<parallel> Q) \<parallel> R \<equiv>\<^sub>s P \<parallel> (Q \<parallel> R)"
| ParId: "P \<parallel> \<zero> \<equiv>\<^sub>s P"

| MatchId: "[a\<frown>a]P \<equiv>\<^sub>s P"

| ResNil: "<\<nu>x>\<zero> \<equiv>\<^sub>s \<zero>"
| ResComm: "<\<nu>x><\<nu>y>P \<equiv>\<^sub>s <\<nu>y><\<nu>x>P"
| ResSum: "<\<nu>x>(P \<oplus> Q) \<equiv>\<^sub>s <\<nu>x>P \<oplus> <\<nu>x>Q"
| ScopeExtPar: "x \<sharp> P \<Longrightarrow> <\<nu>x>(P \<parallel> Q) \<equiv>\<^sub>s P \<parallel> <\<nu>x>Q"
| InputRes: "\<lbrakk>x \<noteq> a; x \<noteq> y\<rbrakk> \<Longrightarrow> <\<nu>x>a<y>.P \<equiv>\<^sub>s a<y>.(<\<nu>x>P)"
| OutputRes: "\<lbrakk>x \<noteq> a; x \<noteq> b\<rbrakk> \<Longrightarrow> <\<nu>x>a{b}.P \<equiv>\<^sub>s a{b}.(<\<nu>x>P)"
| TauRes: "<\<nu>x>\<tau>.(P) \<equiv>\<^sub>s \<tau>.(<\<nu>x>P)"

| BangUnfold: "!P \<equiv>\<^sub>s P \<parallel> !P"

lemma structCongBisim:
  fixes P :: pi
  and   Q :: pi

  assumes "P \<equiv>\<^sub>s Q"

  shows "P \<sim> Q"
using assms
by(induct rule: structCong.induct)
  (auto intro: reflexive symmetric transitive sumSym sumAssoc sumZero parSym parAssoc parZero
               nilRes resComm resInput resOutput resTau sumRes scopeExtPar bangSC matchId mismatchId)

end
