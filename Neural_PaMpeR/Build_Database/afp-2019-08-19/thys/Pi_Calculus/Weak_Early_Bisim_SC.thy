(* 
   Title: The pi-calculus   
   Author/Maintainer: Jesper Bengtson (jebe.dk), 2012
*)
theory Weak_Early_Bisim_SC
  imports Weak_Early_Bisim Strong_Early_Bisim_SC
begin

(******** Structural Congruence **********)

lemma weakBisimStructCong:
  fixes P :: pi
  and   Q :: pi

  assumes "P \<equiv>\<^sub>s Q"

  shows "P \<approx> Q"
using assms
by(metis earlyBisimStructCong strongBisimWeakBisim)

lemma matchId:
  fixes a :: name
  and   P :: pi

  shows "[a\<frown>a]P \<approx> P"
proof -
  have "[a\<frown>a]P \<sim>\<^sub>e P" by(rule Strong_Early_Bisim_SC.matchId)
  thus ?thesis by(rule strongBisimWeakBisim)
qed

lemma mismatchId:
  fixes a :: name
  and   b :: name
  and   P :: pi

  assumes "a \<noteq> b"

  shows "[a\<noteq>b]P \<approx> P"
proof -
  from \<open>a \<noteq> b\<close> have "[a\<noteq>b]P \<sim>\<^sub>e P" by(rule Strong_Early_Bisim_SC.mismatchId)
  thus ?thesis by(rule strongBisimWeakBisim)
qed

lemma mismatchNil:
  fixes a :: name
  and   P :: pi

  shows "[a\<noteq>a]P \<approx> \<zero>"
proof -
  have "[a\<noteq>a]P \<sim>\<^sub>e \<zero>" by(rule Strong_Early_Bisim_SC.mismatchNil)
  thus ?thesis by(rule strongBisimWeakBisim)
qed

(******** The \<nu>-operator *****************)

lemma resComm:
  fixes P :: pi
  
  shows "<\<nu>a><\<nu>b>P \<approx> <\<nu>b><\<nu>a>P"
proof -
  have "<\<nu>a><\<nu>b>P \<sim>\<^sub>e <\<nu>b><\<nu>a>P" by(rule Strong_Early_Bisim_SC.resComm)
  thus ?thesis by(rule strongBisimWeakBisim)
qed

(******** The +-operator *********)

lemma sumSym:
  fixes P :: pi
  and   Q :: pi
  
  shows "P \<oplus> Q \<approx> Q \<oplus> P"
proof -
  have "P \<oplus> Q \<sim>\<^sub>e Q \<oplus> P" by(rule Strong_Early_Bisim_SC.sumSym)
  thus ?thesis by(rule strongBisimWeakBisim)
qed

lemma sumAssoc:
  fixes P :: pi
  and   Q :: pi
  and   R :: pi
  
  shows "(P \<oplus> Q) \<oplus> R \<approx> P \<oplus> (Q \<oplus> R)"
proof -
  have "(P \<oplus> Q) \<oplus> R \<sim>\<^sub>e P \<oplus> (Q \<oplus> R)" by(rule Strong_Early_Bisim_SC.sumAssoc)
  thus ?thesis by(rule strongBisimWeakBisim)
qed

lemma sumZero:
  fixes P :: pi
  
  shows "P \<oplus> \<zero> \<approx> P"
proof -
  have "P \<oplus> \<zero> \<sim>\<^sub>e P" by(rule Strong_Early_Bisim_SC.sumZero)
  thus ?thesis by(rule strongBisimWeakBisim)
qed

(******** The |-operator *********)

lemma parZero:
  fixes P :: pi

  shows "P \<parallel> \<zero> \<approx> P"
proof -
  have "P \<parallel> \<zero> \<sim>\<^sub>e P" by(rule Strong_Early_Bisim_SC.parZero)
  thus ?thesis by(rule strongBisimWeakBisim)
qed

lemma parSym:
  fixes P :: pi
  and   Q :: pi

  shows "P \<parallel> Q \<approx> Q \<parallel> P"
proof -
  have "P \<parallel> Q \<sim>\<^sub>e Q \<parallel> P" by(rule Strong_Early_Bisim_SC.parSym)
  thus ?thesis by(rule strongBisimWeakBisim)
qed

lemma scopeExtPar:
  fixes P :: pi
  and   Q :: pi
  and   x :: name

  assumes "x \<sharp> P"

  shows "<\<nu>x>(P \<parallel> Q) \<approx> P \<parallel> <\<nu>x>Q"
proof -
  from \<open>x \<sharp> P\<close> have "<\<nu>x>(P \<parallel> Q) \<sim>\<^sub>e P \<parallel> <\<nu>x>Q" by(rule Strong_Early_Bisim_SC.scopeExtPar)
  thus ?thesis by(rule strongBisimWeakBisim)
qed

lemma scopeExtPar':
  fixes P :: pi
  and   Q :: pi
  and   x :: name

  assumes "x \<sharp> Q"

  shows "<\<nu>x>(P \<parallel> Q) \<approx> (<\<nu>x>P) \<parallel> Q"
proof - 
  from \<open>x \<sharp> Q\<close> have "<\<nu>x>(P \<parallel> Q) \<sim>\<^sub>e (<\<nu>x>P) \<parallel> Q" by(rule Strong_Early_Bisim_SC.scopeExtPar')
  thus ?thesis by(rule strongBisimWeakBisim)
qed

lemma parAssoc:
  fixes P :: pi
  and   Q :: pi
  and   R :: pi

  shows "(P \<parallel> Q) \<parallel> R \<approx> P \<parallel> (Q \<parallel> R)"
proof -
  have "(P \<parallel> Q) \<parallel> R \<sim>\<^sub>e P \<parallel> (Q \<parallel> R)" by(rule Strong_Early_Bisim_SC.parAssoc)
  thus ?thesis by(rule strongBisimWeakBisim)
qed

lemma freshRes:
  fixes P :: pi
  and   a :: name

  assumes "a \<sharp> P"

  shows "<\<nu>a>P \<approx> P"
proof -
  from \<open>a \<sharp> P\<close> have "<\<nu>a>P \<sim>\<^sub>e P" by(rule Strong_Early_Bisim_SC.freshRes)
  thus ?thesis by(rule strongBisimWeakBisim)
qed

lemma scopeExtSum:
  fixes P :: pi
  and   Q :: pi
  and   x :: name
  
  assumes "x \<sharp> P"

  shows "<\<nu>x>(P \<oplus> Q) \<approx> P \<oplus> <\<nu>x>Q"
proof -
  from \<open>x \<sharp> P\<close> have "<\<nu>x>(P \<oplus> Q) \<sim>\<^sub>e P \<oplus> <\<nu>x>Q" by(rule Strong_Early_Bisim_SC.scopeExtSum)
  thus ?thesis by(rule strongBisimWeakBisim)
qed

lemma bangSC:
  fixes P

  shows "!P \<approx> P \<parallel> !P"
proof -
  have "!P \<sim>\<^sub>e P \<parallel> !P" by(rule Strong_Early_Bisim_SC.bangSC)
  thus ?thesis by(rule strongBisimWeakBisim)
qed

end
