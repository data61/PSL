(* 
   Title: The pi-calculus   
   Author/Maintainer: Jesper Bengtson (jebe.dk), 2012
*)
theory Weak_Late_Cong_Subst_SC
  imports Weak_Late_Cong_Subst Strong_Late_Bisim_Subst_SC
begin

(******** Structural Congruence **********)

(******** The \<nu>-operator *****************)

lemma resComm:
  fixes P :: pi
  
  shows "<\<nu>a><\<nu>b>P \<simeq>\<^sup>s <\<nu>b><\<nu>a>P"
proof -
  have "<\<nu>a><\<nu>b>P \<sim>\<^sup>s <\<nu>b><\<nu>a>P"
    by(rule Strong_Late_Bisim_Subst_SC.resComm)
  thus ?thesis by(rule strongEqWeakCong)
qed

(******** Match *********)

lemma matchId:
  fixes a :: name
  and   P :: pi

  shows "[a\<frown>a]P \<simeq>\<^sup>s P"
proof -
  have "[a\<frown>a]P \<sim>\<^sup>s P" by(rule Strong_Late_Bisim_Subst_SC.matchId)
  thus ?thesis by(rule strongEqWeakCong)
qed

(******** Mismatch *********)

lemma matchNil:
  fixes a :: name
  and   P :: pi

  shows "[a\<noteq>a]P \<simeq>\<^sup>s \<zero>"
proof -
  have "[a\<noteq>a]P \<sim>\<^sup>s \<zero>" by(rule Strong_Late_Bisim_Subst_SC.mismatchNil)
  thus ?thesis by(rule strongEqWeakCong)
qed

(******** The +-operator *********)

lemma sumSym:
  fixes P :: pi
  and   Q :: pi
  
  shows "P \<oplus> Q \<simeq>\<^sup>s Q \<oplus> P"
proof -
  have "P \<oplus> Q \<sim>\<^sup>s Q \<oplus> P" by(rule Strong_Late_Bisim_Subst_SC.sumSym)
  thus ?thesis by(rule strongEqWeakCong)
qed

lemma sumAssoc:
  fixes P :: pi
  and   Q :: pi
  and   R :: pi
  
  shows "(P \<oplus> Q) \<oplus> R \<simeq>\<^sup>s P \<oplus> (Q \<oplus> R)"
proof -
  have "(P \<oplus> Q) \<oplus> R \<sim>\<^sup>s P \<oplus> (Q \<oplus> R)" by(rule Strong_Late_Bisim_Subst_SC.sumAssoc)
  thus ?thesis by(rule strongEqWeakCong)
qed

lemma sumZero:
  fixes P :: pi
  
  shows "P \<oplus> \<zero> \<simeq>\<^sup>s P"
proof -
  have "P \<oplus> \<zero> \<sim>\<^sup>s P" by(rule Strong_Late_Bisim_Subst_SC.sumZero)
  thus ?thesis by(rule strongEqWeakCong)
qed

(******** The |-operator *********)

lemma parZero:
  fixes P :: pi

  shows "P \<parallel> \<zero> \<simeq>\<^sup>s P"
proof -
  have "P \<parallel> \<zero> \<sim>\<^sup>s P" by(rule Strong_Late_Bisim_Subst_SC.parZero)
  thus ?thesis by(rule strongEqWeakCong)
qed

lemma parSym:
  fixes P :: pi
  and   Q :: pi

  shows "P \<parallel> Q \<simeq>\<^sup>s Q \<parallel> P"
proof -
  have "P \<parallel> Q \<sim>\<^sup>s Q \<parallel> P" by(rule Strong_Late_Bisim_Subst_SC.parSym)
  thus ?thesis by(rule strongEqWeakCong)
qed

lemma scopeExtPar:
  fixes P :: pi
  and   Q :: pi
  and   x :: name

  assumes "x \<sharp> P"

  shows "<\<nu>x>(P \<parallel> Q) \<simeq>\<^sup>s P \<parallel> <\<nu>x>Q"
proof -
  from assms have "<\<nu>x>(P \<parallel> Q) \<sim>\<^sup>s P \<parallel> <\<nu>x>Q" by(rule Strong_Late_Bisim_Subst_SC.scopeExtPar)
  thus ?thesis by(rule strongEqWeakCong)
qed

lemma scopeExtPar':
  fixes P :: pi
  and   Q :: pi
  and   x :: name

  assumes xFreshQ: "x \<sharp> Q"

  shows "<\<nu>x>(P \<parallel> Q) \<simeq>\<^sup>s (<\<nu>x>P) \<parallel> Q"
proof -
  from assms have "<\<nu>x>(P \<parallel> Q) \<sim>\<^sup>s (<\<nu>x>P) \<parallel> Q" by(rule Strong_Late_Bisim_Subst_SC.scopeExtPar')
  thus ?thesis by(rule strongEqWeakCong)
qed

lemma parAssoc:
  fixes P :: pi
  and   Q :: pi
  and   R :: pi

  shows "(P \<parallel> Q) \<parallel> R \<simeq>\<^sup>s P \<parallel> (Q \<parallel> R)"
proof -
  have "(P \<parallel> Q) \<parallel> R \<sim>\<^sup>s P \<parallel> (Q \<parallel> R)" by(rule Strong_Late_Bisim_Subst_SC.parAssoc)
  thus ?thesis by(rule strongEqWeakCong)
qed

lemma scopeFresh:
  fixes P :: pi
  and   a :: name

  assumes aFreshP: "a \<sharp> P"

  shows "<\<nu>a>P \<simeq>\<^sup>s P"
proof -
  from assms have "<\<nu>a>P \<sim>\<^sup>s P" by(rule Strong_Late_Bisim_Subst_SC.scopeFresh)
  thus ?thesis by(rule strongEqWeakCong)
qed

lemma scopeExtSum:
  fixes P :: pi
  and   Q :: pi
  and   x :: name
  
  assumes "x \<sharp> P"

  shows "<\<nu>x>(P \<oplus> Q) \<simeq>\<^sup>s P \<oplus> <\<nu>x>Q"
proof -
  from assms have "<\<nu>x>(P \<oplus> Q) \<sim>\<^sup>s P \<oplus> <\<nu>x>Q" by(rule Strong_Late_Bisim_Subst_SC.scopeExtSum)
  thus ?thesis by(rule strongEqWeakCong)
qed

lemma bangSC:
  fixes P

  shows "!P \<simeq>\<^sup>s P \<parallel> !P"
proof -
  have "!P \<sim>\<^sup>s P \<parallel> !P" by(rule Strong_Late_Bisim_Subst_SC.bangSC)
  thus ?thesis by(rule strongEqWeakCong)
qed

end
