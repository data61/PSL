(* 
   Title: The pi-calculus   
   Author/Maintainer: Jesper Bengtson (jebe.dk), 2012
*)
theory Weak_Late_Cong_SC
  imports Weak_Late_Cong Strong_Late_Bisim_SC
begin

(******** Structural Congruence **********)

(******** The \<nu>-operator *****************)

lemma resComm:
  fixes P :: pi
  
  shows "<\<nu>a><\<nu>b>P \<simeq> <\<nu>b><\<nu>a>P"
proof -
  have "<\<nu>a><\<nu>b>P \<sim> <\<nu>b><\<nu>a>P" by(rule Strong_Late_Bisim_SC.resComm)
  thus ?thesis by(rule strongBisimWeakEq)
qed

(******** Match *****************)

lemma matchId:
  fixes a :: name
  and   P :: pi

  shows "[a\<frown>a]P \<simeq> P"
proof -
  have "[a\<frown>a]P \<sim> P" by(rule Strong_Late_Bisim_SC.matchId)
  thus ?thesis by(rule strongBisimWeakEq)
qed

(******** Mismatch *****************)

lemma mismatchId:
  fixes a :: name
  and   b :: name
  and   P :: pi

  assumes "a \<noteq> b"

  shows "[a\<noteq>b]P \<simeq> P"
proof -
  from \<open>a \<noteq> b\<close> have "[a\<noteq>b]P \<sim> P" by(rule Strong_Late_Bisim_SC.mismatchId)
  thus ?thesis by(rule strongBisimWeakEq)
qed

lemma mismatchNil:
  fixes a :: name
  and   P :: pi
  
  shows "[a\<noteq>a]P \<simeq> \<zero>"
proof -
  have "[a\<noteq>a]P \<sim> \<zero>" by(rule Strong_Late_Bisim_SC.mismatchNil)
  thus ?thesis by(rule strongBisimWeakEq)
qed

(******** The +-operator *********)

lemma sumSym:
  fixes P :: pi
  and   Q :: pi
  
  shows "P \<oplus> Q \<simeq> Q \<oplus> P"
proof -
  have "P \<oplus> Q \<sim> Q \<oplus> P" by(rule Strong_Late_Bisim_SC.sumSym)
  thus ?thesis by(rule strongBisimWeakEq)
qed

lemma sumAssoc:
  fixes P :: pi
  and   Q :: pi
  and   R :: pi
  
  shows "(P \<oplus> Q) \<oplus> R \<simeq> P \<oplus> (Q \<oplus> R)"
proof -
  have "(P \<oplus> Q) \<oplus> R \<sim> P \<oplus> (Q \<oplus> R)" by(rule Strong_Late_Bisim_SC.sumAssoc)
  thus ?thesis by(rule strongBisimWeakEq)
qed

lemma sumZero:
  fixes P :: pi
  
  shows "P \<oplus> \<zero> \<simeq> P"
proof -
  have "P \<oplus> \<zero> \<sim> P" by(rule Strong_Late_Bisim_SC.sumZero)
  thus ?thesis by(rule strongBisimWeakEq)
qed

(******** The |-operator *********)

lemma parZero:
  fixes P :: pi

  shows "P \<parallel> \<zero> \<simeq> P"
proof -
  have "P \<parallel> \<zero> \<sim> P" by(rule Strong_Late_Bisim_SC.parZero)
  thus ?thesis by(rule strongBisimWeakEq)
qed

lemma parSym:
  fixes P :: pi
  and   Q :: pi

  shows "P \<parallel> Q \<simeq> Q \<parallel> P"
proof -
  have "P \<parallel> Q \<sim> Q \<parallel> P" by(rule Strong_Late_Bisim_SC.parSym)
  thus ?thesis by(rule strongBisimWeakEq)
qed

lemma scopeExtPar:
  fixes P :: pi
  and   Q :: pi
  and   x :: name

  assumes "x \<sharp> P"

  shows "<\<nu>x>(P \<parallel> Q) \<simeq> P \<parallel> <\<nu>x>Q"
proof -
  from \<open>x \<sharp> P\<close> have "<\<nu>x>(P \<parallel> Q) \<sim> P \<parallel> <\<nu>x>Q" by(rule Strong_Late_Bisim_SC.scopeExtPar)
  thus ?thesis by(rule strongBisimWeakEq)
qed

lemma scopeExtPar':
  fixes P :: pi
  and   Q :: pi
  and   x :: name

  assumes "x \<sharp> Q"

  shows "<\<nu>x>(P \<parallel> Q) \<simeq> (<\<nu>x>P) \<parallel> Q"
proof -
  from \<open>x \<sharp> Q\<close> have "<\<nu>x>(P \<parallel> Q) \<sim> (<\<nu>x>P) \<parallel> Q" by(rule Strong_Late_Bisim_SC.scopeExtPar')
  thus ?thesis by(rule strongBisimWeakEq)
qed

lemma parAssoc:
  fixes P :: pi
  and   Q :: pi
  and   R :: pi

  shows "(P \<parallel> Q) \<parallel> R \<simeq> P \<parallel> (Q \<parallel> R)"
proof -
  have "(P \<parallel> Q) \<parallel> R \<sim> P \<parallel> (Q \<parallel> R)" by(rule Strong_Late_Bisim_SC.parAssoc)
  thus ?thesis by(rule strongBisimWeakEq)
qed

lemma scopeFresh:
  fixes P :: pi
  and   a :: name

  assumes "a \<sharp> P"

  shows "<\<nu>a>P \<simeq> P"
proof -
  from \<open>a \<sharp> P\<close> have "<\<nu>a>P \<sim> P" by(rule Strong_Late_Bisim_SC.scopeFresh)
  thus ?thesis by(rule strongBisimWeakEq)
qed

lemma scopeExtSum:
  fixes P :: pi
  and   Q :: pi
  and   x :: name
  
  assumes "x \<sharp> P"

  shows "<\<nu>x>(P \<oplus> Q) \<simeq> P \<oplus> <\<nu>x>Q"
proof -
  from \<open>x \<sharp> P\<close> have "<\<nu>x>(P \<oplus> Q) \<sim> P \<oplus> <\<nu>x>Q" by(rule Strong_Late_Bisim_SC.scopeExtSum)
  thus ?thesis by(rule strongBisimWeakEq)
qed

lemma bangSC:
  fixes P

  shows "!P \<simeq> P \<parallel> !P"
proof -
  have "!P \<sim> P \<parallel> !P" by(rule Strong_Late_Bisim_SC.bangSC)
  thus ?thesis by(rule strongBisimWeakEq)
qed

end
