(* 
   Title: The pi-calculus   
   Author/Maintainer: Jesper Bengtson (jebe.dk), 2012
*)
theory Strong_Early_Bisim_SC
  imports Strong_Early_Bisim Strong_Late_Bisim_SC Strong_Early_Late_Comp
begin

(******** Structural Congruence **********)

(******** The \<nu>-operator *****************)

lemma resComm:
  fixes P :: pi
  
  shows "<\<nu>a><\<nu>b>P \<sim>\<^sub>e <\<nu>b><\<nu>a>P"
proof -
  have "<\<nu>a><\<nu>b>P \<sim>\<^sub>l <\<nu>b><\<nu>a>P" by(rule Strong_Late_Bisim_SC.resComm)
  thus ?thesis by(rule lateEarlyBisim)
qed

(******** Match *********)

lemma matchId:
  fixes a :: name
  and   P :: pi

  shows "[a\<frown>a]P \<sim>\<^sub>e P"
proof -
  have "[a\<frown>a]P \<sim>\<^sub>l P" by(rule Strong_Late_Bisim_SC.matchId)
  thus ?thesis by(rule lateEarlyBisim)
qed

(******** Mismatch *********)

lemma mismatchId:
  fixes a :: name
  and   b :: name
  and   P :: pi

  assumes "a \<noteq> b"

  shows "[a\<noteq>b]P \<sim>\<^sub>e P"
proof -
  from assms have "[a\<noteq>b]P \<sim>\<^sub>l P" by(rule Strong_Late_Bisim_SC.mismatchId)
  thus ?thesis by(rule lateEarlyBisim)
qed

lemma mismatchNil:
  fixes a :: name
  and   P :: pi
  
  shows "[a\<noteq>a]P \<sim>\<^sub>e \<zero>"
proof -
  have "[a\<noteq>a]P \<sim>\<^sub>l \<zero>" by(rule Strong_Late_Bisim_SC.mismatchNil)
  thus ?thesis by(rule lateEarlyBisim)
qed

(******** The +-operator *********)

lemma sumSym:
  fixes P :: pi
  and   Q :: pi
  
  shows "P \<oplus> Q \<sim>\<^sub>e Q \<oplus> P"
proof -
  have "P \<oplus> Q \<sim>\<^sub>l Q \<oplus> P" by(rule Strong_Late_Bisim_SC.sumSym)
  thus ?thesis by(rule lateEarlyBisim)
qed

lemma sumAssoc:
  fixes P :: pi
  and   Q :: pi
  and   R :: pi
  
  shows "(P \<oplus> Q) \<oplus> R \<sim>\<^sub>e P \<oplus> (Q \<oplus> R)"
proof -
  have "(P \<oplus> Q) \<oplus> R \<sim>\<^sub>l P \<oplus> (Q \<oplus> R)" by(rule Strong_Late_Bisim_SC.sumAssoc)
  thus ?thesis by(rule lateEarlyBisim)
qed

lemma sumZero:
  fixes P :: pi
  
  shows "P \<oplus> \<zero> \<sim>\<^sub>e P"
proof -
  have "P \<oplus> \<zero> \<sim>\<^sub>l P" by(rule Strong_Late_Bisim_SC.sumZero)
  thus ?thesis by(rule lateEarlyBisim)
qed

(******** The |-operator *********)

lemma parZero:
  fixes P :: pi

  shows "P \<parallel> \<zero> \<sim>\<^sub>e P"
proof -
  have "P \<parallel> \<zero> \<sim>\<^sub>l P" by(rule Strong_Late_Bisim_SC.parZero)
  thus ?thesis by(rule lateEarlyBisim)
qed

lemma parSym:
  fixes P :: pi
  and   Q :: pi

  shows "P \<parallel> Q \<sim>\<^sub>e Q \<parallel> P"
proof -
  have "P \<parallel> Q \<sim>\<^sub>l Q \<parallel> P" by(rule Strong_Late_Bisim_SC.parSym)
  thus ?thesis by(rule lateEarlyBisim)
qed

lemma scopeExtPar:
  fixes P :: pi
  and   Q :: pi
  and   x :: name

  assumes "x \<sharp> P"

  shows "<\<nu>x>(P \<parallel> Q) \<sim>\<^sub>e P \<parallel> <\<nu>x>Q"
proof -
  from assms have "<\<nu>x>(P \<parallel> Q) \<sim>\<^sub>l P \<parallel> <\<nu>x>Q" by(rule Strong_Late_Bisim_SC.scopeExtPar)
  thus ?thesis by(rule lateEarlyBisim)
qed

lemma scopeExtPar':
  fixes P :: pi
  and   Q :: pi
  and   x :: name

  assumes xFreshQ: "x \<sharp> Q"

  shows "<\<nu>x>(P \<parallel> Q) \<sim>\<^sub>e (<\<nu>x>P) \<parallel> Q"
proof -
  from assms have "<\<nu>x>(P \<parallel> Q) \<sim>\<^sub>l (<\<nu>x>P) \<parallel> Q" by(rule Strong_Late_Bisim_SC.scopeExtPar')
  thus ?thesis by(rule lateEarlyBisim)
qed

lemma parAssoc:
  fixes P :: pi
  and   Q :: pi
  and   R :: pi

  shows "(P \<parallel> Q) \<parallel> R \<sim>\<^sub>e P \<parallel> (Q \<parallel> R)"
proof -
  have "(P \<parallel> Q) \<parallel> R \<sim>\<^sub>l P \<parallel> (Q \<parallel> R)" by(rule Strong_Late_Bisim_SC.parAssoc)
  thus ?thesis by(rule lateEarlyBisim)
qed

lemma freshRes:
  fixes P :: pi
  and   a :: name

  assumes aFreshP: "a \<sharp> P"

  shows "<\<nu>a>P \<sim>\<^sub>e P"
proof -
  from aFreshP have "<\<nu>a>P \<sim>\<^sub>l P" by(rule Strong_Late_Bisim_SC.scopeFresh)
  thus ?thesis by(rule lateEarlyBisim)
qed

lemma scopeExtSum:
  fixes P :: pi
  and   Q :: pi
  and   x :: name
  
  assumes "x \<sharp> P"

  shows "<\<nu>x>(P \<oplus> Q) \<sim>\<^sub>e P \<oplus> <\<nu>x>Q"
proof -
  from \<open>x \<sharp> P\<close>  have "<\<nu>x>(P \<oplus> Q) \<sim>\<^sub>l P \<oplus> <\<nu>x>Q" by(rule Strong_Late_Bisim_SC.scopeExtSum)
  thus ?thesis by(rule lateEarlyBisim)
qed

lemma bangSC:
  fixes P

  shows "!P \<sim>\<^sub>e P \<parallel> !P"
proof -
  have "!P \<sim>\<^sub>l P \<parallel> !P" by(rule Strong_Late_Bisim_SC.bangSC)
  thus ?thesis by(rule lateEarlyBisim)
qed

end

