(* 
   Title: The Calculus of Communicating Systems   
   Author/Maintainer: Jesper Bengtson (jebe@itu.dk), 2012
*)
theory Strong_Bisim_SC
  imports Strong_Sim_SC Strong_Bisim_Pres Struct_Cong
begin

lemma resNil:
  fixes x :: name

  shows "\<lparr>\<nu>x\<rparr>\<zero> \<sim> \<zero>"
proof -
  have "(\<lparr>\<nu>x\<rparr>\<zero>, \<zero>) \<in> {(\<lparr>\<nu>x\<rparr>\<zero>, \<zero>), (\<zero>, \<lparr>\<nu>x\<rparr>\<zero>)}" by simp
  thus ?thesis
    by(coinduct rule: bisimCoinduct)
      (auto intro: resNilLeft resNilRight)
qed

lemma scopeExt:
  fixes x :: name
  and   P :: ccs
  and   Q :: ccs

  assumes "x \<sharp> P"

  shows "\<lparr>\<nu>x\<rparr>(P \<parallel> Q) \<sim> P \<parallel> \<lparr>\<nu>x\<rparr>Q"
proof -
  let ?X = "{(\<lparr>\<nu>x\<rparr>(P \<parallel> Q), P \<parallel> \<lparr>\<nu>x\<rparr>Q) | x P Q. x \<sharp> P} \<union> {(P \<parallel> \<lparr>\<nu>x\<rparr>Q, \<lparr>\<nu>x\<rparr>(P \<parallel> Q)) | x P Q. x \<sharp> P}"
  from assms have "(\<lparr>\<nu>x\<rparr>(P \<parallel> Q), P \<parallel> \<lparr>\<nu>x\<rparr>Q) \<in> ?X" by auto
  thus ?thesis
    by(coinduct rule: bisimCoinduct) (force intro: scopeExtLeft scopeExtRight)+
qed

lemma sumComm:
  fixes P :: ccs
  and   Q :: ccs

  shows "P \<oplus> Q \<sim> Q \<oplus> P"
proof -
  have "(P \<oplus> Q, Q \<oplus> P) \<in> {(P \<oplus> Q, Q \<oplus> P), (Q \<oplus> P, P \<oplus> Q)}" by simp
  thus ?thesis
    by(coinduct rule: bisimCoinduct) (auto intro: sumComm reflexive)
qed

lemma sumAssoc:
  fixes P :: ccs
  and   Q :: ccs
  and   R :: ccs

  shows "(P \<oplus> Q) \<oplus> R \<sim> P \<oplus> (Q \<oplus> R)"
proof -
  have "((P \<oplus> Q) \<oplus> R, P \<oplus> (Q \<oplus> R)) \<in> {((P \<oplus> Q) \<oplus> R, P \<oplus> (Q \<oplus> R)), (P \<oplus> (Q \<oplus> R), (P \<oplus> Q) \<oplus> R)}" by simp
  thus ?thesis
    by(coinduct rule: bisimCoinduct) (auto intro: sumAssocLeft sumAssocRight reflexive)
qed

lemma sumId:
  fixes P :: ccs

  shows "P \<oplus> \<zero> \<sim> P"
proof -
  have "(P \<oplus> \<zero>, P) \<in> {(P \<oplus> \<zero>, P), (P, P \<oplus> \<zero>)}" by simp
  thus ?thesis by(coinduct rule: bisimCoinduct) (auto intro: sumIdLeft sumIdRight reflexive) 
qed

lemma parComm:
  fixes P :: ccs
  and   Q :: ccs

  shows "P \<parallel> Q \<sim> Q \<parallel> P"
proof -
  have "(P \<parallel> Q, Q \<parallel> P) \<in> {(P \<parallel> Q, Q \<parallel> P) | P Q. True} \<union> {(Q \<parallel> P, P \<parallel> Q) | P Q. True}" by auto
  thus ?thesis
    by(coinduct rule: bisimCoinduct) (auto intro: parComm)
qed

lemma parAssoc:
  fixes P :: ccs
  and   Q :: ccs
  and   R :: ccs

  shows "(P \<parallel> Q) \<parallel> R \<sim> P \<parallel> (Q \<parallel> R)"
proof -
  have "((P \<parallel> Q) \<parallel> R, P \<parallel> (Q \<parallel> R)) \<in> {((P \<parallel> Q) \<parallel> R, P \<parallel> (Q \<parallel> R)) | P Q R. True} \<union>  
                                     {(P \<parallel> (Q \<parallel> R), (P \<parallel> Q) \<parallel> R) | P Q R. True}" by auto
  thus ?thesis
    by(coinduct rule: bisimCoinduct) (force intro: parAssocLeft parAssocRight)+
qed

lemma parId:
  fixes P :: ccs

  shows "P \<parallel> \<zero> \<sim> P"
proof -
  have "(P \<parallel> \<zero>, P) \<in> {(P \<parallel> \<zero>, P) | P. True} \<union> {(P, P \<parallel> \<zero>) | P. True}" by simp
  thus ?thesis by(coinduct rule: bisimCoinduct) (auto intro: parIdLeft parIdRight)
qed

lemma scopeFresh:
  fixes x :: name
  and   P :: ccs

  assumes "x \<sharp> P"

  shows "\<lparr>\<nu>x\<rparr>P \<sim> P"
proof -
  have "\<lparr>\<nu>x\<rparr>P \<sim> \<lparr>\<nu>x\<rparr>P \<parallel> \<zero>" by(rule parId[THEN symmetric])
  moreover have "\<lparr>\<nu>x\<rparr>P \<parallel> \<zero> \<sim> \<zero> \<parallel> \<lparr>\<nu>x\<rparr>P" by(rule parComm)
  moreover have "\<zero> \<parallel> \<lparr>\<nu>x\<rparr>P \<sim> \<lparr>\<nu>x\<rparr>(\<zero> \<parallel> P)" by(rule scopeExt[THEN symmetric]) auto
  moreover have "\<lparr>\<nu>x\<rparr>(\<zero> \<parallel> P) \<sim> \<lparr>\<nu>x\<rparr>(P \<parallel> \<zero>)" by(rule resPres[OF parComm])
  moreover from `x \<sharp> P` have "\<lparr>\<nu>x\<rparr>(P \<parallel> \<zero>) \<sim> P \<parallel> \<lparr>\<nu>x\<rparr>\<zero>" by(rule scopeExt)
  moreover have  "P \<parallel> \<lparr>\<nu>x\<rparr>\<zero> \<sim> \<lparr>\<nu>x\<rparr>\<zero> \<parallel> P" by(rule parComm)
  moreover have "\<lparr>\<nu>x\<rparr>\<zero> \<parallel> P \<sim> \<zero> \<parallel> P" by(rule parPres[OF resNil])
  moreover have "\<zero> \<parallel> P \<sim> P \<parallel> \<zero>" by(rule parComm)
  moreover have "P \<parallel> \<zero> \<sim> P" by(rule parId)
  ultimately show ?thesis by(metis transitive)
qed

lemma scopeExtSum:
  fixes x :: name
  and   P :: ccs
  and   Q :: ccs

  assumes "x \<sharp> P"

  shows "\<lparr>\<nu>x\<rparr>(P \<oplus> Q) \<sim> P \<oplus> \<lparr>\<nu>x\<rparr>Q"
proof -
  have "(\<lparr>\<nu>x\<rparr>(P \<oplus> Q), P \<oplus> \<lparr>\<nu>x\<rparr>Q) \<in> {(\<lparr>\<nu>x\<rparr>(P \<oplus> Q), P \<oplus> \<lparr>\<nu>x\<rparr>Q), (P \<oplus> \<lparr>\<nu>x\<rparr>Q, \<lparr>\<nu>x\<rparr>(P \<oplus> Q))}"
    by simp
  thus ?thesis using `x \<sharp> P`
    by(coinduct rule: bisimCoinduct) 
      (auto intro: scopeExtSumLeft scopeExtSumRight reflexive scopeFresh scopeFresh[THEN symmetric])
qed

lemma resAct:
  fixes x :: name
  and   \<alpha> :: act
  and   P :: ccs

  assumes "x \<sharp> \<alpha>"

  shows "\<lparr>\<nu>x\<rparr>(\<alpha>.(P)) \<sim> \<alpha>.(\<lparr>\<nu>x\<rparr>P)"
proof -
  have "(\<lparr>\<nu>x\<rparr>(\<alpha>.(P)), \<alpha>.(\<lparr>\<nu>x\<rparr>P)) \<in> {(\<lparr>\<nu>x\<rparr>(\<alpha>.(P)), \<alpha>.(\<lparr>\<nu>x\<rparr>P)), (\<alpha>.(\<lparr>\<nu>x\<rparr>P), \<lparr>\<nu>x\<rparr>(\<alpha>.(P)))}"
    by simp
  thus ?thesis using `x \<sharp> \<alpha>`
    by(coinduct rule: bisimCoinduct) (auto intro: resActLeft resActRight reflexive)
qed

lemma resComm:
  fixes x :: name
  and   y :: name
  and   P :: ccs

  shows "\<lparr>\<nu>x\<rparr>(\<lparr>\<nu>y\<rparr>P) \<sim> \<lparr>\<nu>y\<rparr>(\<lparr>\<nu>x\<rparr>P)"
proof -
  have "(\<lparr>\<nu>x\<rparr>(\<lparr>\<nu>y\<rparr>P), \<lparr>\<nu>y\<rparr>(\<lparr>\<nu>x\<rparr>P)) \<in> {(\<lparr>\<nu>x\<rparr>(\<lparr>\<nu>y\<rparr>P), \<lparr>\<nu>y\<rparr>(\<lparr>\<nu>x\<rparr>P)) | x y P. True}" by auto
  thus ?thesis
  by(coinduct rule: bisimCoinduct) (auto intro: resComm)
qed

lemma bangUnfold:
  fixes P

  shows "!P \<sim> P \<parallel> !P"
proof -
  have "(!P, P \<parallel> !P) \<in> {(!P, P \<parallel> !P), (P \<parallel> !P, !P)}" by auto
  thus ?thesis
    by(coinduct rule: bisimCoinduct) (auto intro: bangUnfoldLeft bangUnfoldRight reflexive)
qed

lemma bisimStructCong:
  fixes P :: ccs
  and   Q :: ccs

  assumes "P \<equiv>\<^sub>s Q"

  shows "P \<sim> Q"
using assms
apply(nominal_induct rule: Struct_Cong.strong_induct)
by(auto intro: reflexive symmetric transitive parComm parAssoc parId sumComm
   sumAssoc sumId resNil scopeExt scopeExtSum resAct resComm bangUnfold)   

end  

