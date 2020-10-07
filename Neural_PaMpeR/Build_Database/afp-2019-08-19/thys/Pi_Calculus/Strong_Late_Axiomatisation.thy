(* 
   Title: The pi-calculus   
   Author/Maintainer: Jesper Bengtson (jebe.dk), 2012
*)
theory Strong_Late_Axiomatisation
  imports Strong_Late_Expansion_Law
begin

lemma inputSuppPres:
  fixes P :: pi
  and   Q :: pi
  and   x :: name
  and   Rel  :: "(pi \<times> pi) set"

  assumes PRelQ: "\<And>y. y \<in> supp(P, Q, x) \<Longrightarrow> (P[x::=y], Q[x::=y]) \<in> Rel"
  and     Eqvt: "eqvt Rel"

  shows "a<x>.P \<leadsto>[Rel] a<x>.Q"
proof -
  from Eqvt show ?thesis
  proof(induct rule: simCasesCont[where C="(x, a, Q, P)"])
    case(Bound b y Q')
    have "x \<in> supp(P, Q, x)" by(simp add: supp_prod supp_atm)
    with PRelQ have "(P, Q) \<in> Rel" by fastforce
    have QTrans: "a<x>.Q \<longmapsto> b\<guillemotleft>y\<guillemotright> \<prec> Q'" by fact
    have "y \<sharp> (x, a, Q, P)" by fact
    hence "y \<noteq> a" and yineqx: "y \<noteq> x" and "y \<sharp> Q" and "y \<sharp> P" by(simp add: fresh_prod)+
    with QTrans show ?case
    proof(induct rule: inputCases)
      have "a<y>.([(x, y)] \<bullet> P) \<longmapsto>a<y> \<prec> ([(x, y)] \<bullet> P)" by(rule Input)
      hence "a<x>.P \<longmapsto>a<y> \<prec> ([(x, y)] \<bullet> P)" using \<open>y \<sharp> P\<close> by(simp add: alphaInput)
      moreover have "derivative ([(x, y)] \<bullet> P) ([(x, y)] \<bullet> Q) (InputS a) y Rel"
      proof(auto simp add: derivative_def)
        fix u
        have "x \<in> supp(P, Q, x)" by(simp add: supp_prod supp_atm)
        have "(P[x::=u], Q[x::=u]) \<in> Rel"
        proof(cases "u \<in> supp(P, Q, x)")
          case True
          with PRelQ show ?thesis by auto
        next
          case False
          hence "u \<sharp> P" and "u \<sharp> Q" by(auto simp add: fresh_def supp_prod)
          moreover from \<open>eqvt Rel\<close> \<open>(P, Q) \<in> Rel\<close> have "([(x, u)] \<bullet> P, [(x, u)] \<bullet> Q) \<in> Rel"
            by(rule eqvtRelI)
          ultimately show ?thesis by(simp only: injPermSubst)
        qed
        with \<open>y \<sharp> P\<close> \<open>y \<sharp> Q\<close> show "(([(x, y)] \<bullet> P)[y::=u], ([(x, y)] \<bullet> Q)[y::=u]) \<in> Rel"
          by(simp add: renaming)
      qed
      ultimately show "\<exists>P'. a<x>.P \<longmapsto> a<y> \<prec> P' \<and> derivative P' ([(x, y)] \<bullet> Q) (InputS a) y Rel"
        by blast
    qed
  next
    case(Free \<alpha> Q')
    have "a<x>.Q \<longmapsto> \<alpha> \<prec> Q'" by fact
    hence False by auto
    thus ?case by blast
  qed
qed

lemma inputSuppPresBisim:
  fixes P :: pi
  and   Q :: pi
  and   x :: name

  assumes PSimQ: "\<And>y. y \<in> supp(P, Q, x) \<Longrightarrow> P[x::=y] \<sim> Q[x::=y]"

  shows "a<x>.P \<sim> a<x>.Q"
proof -
  let ?X = "{(a<x>.P, a<x>.Q) | a x P Q. \<forall>y \<in> supp(P, Q, x). P[x::=y] \<sim> Q[x::=y]}"
  have "eqvt ?X"
    apply(auto simp add: eqvt_def)
    apply(rule_tac x="perma \<bullet> aa" in exI)
    apply(rule_tac x="perma \<bullet> x" in exI)
    apply(rule_tac x="perma \<bullet> P" in exI)
    apply auto
    apply(rule_tac x="perma \<bullet> Q" in exI)
    apply auto
    apply(drule_tac pi="rev perma" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
    apply(simp add: eqvts pt_rev_pi[OF pt_name_inst, OF at_name_inst])
    apply(erule_tac x="rev perma \<bullet> y" in ballE)
    apply auto
    apply(drule_tac p=perma in bisimClosed)
    by(simp add: eqvts pt_pi_rev[OF pt_name_inst, OF at_name_inst])
  from assms have "(a<x>.P, a<x>.Q) \<in> ?X" by fastforce
  thus ?thesis
  proof(coinduct rule: bisimCoinduct)
    case(cSim P Q)
    thus ?case using \<open>eqvt ?X\<close>
      by(fastforce intro: inputSuppPres)
  next
    case(cSym P Q)
    thus ?case by(fastforce simp add: supp_prod dest: symmetric)
  qed
qed

inductive equiv :: "pi \<Rightarrow> pi \<Rightarrow> bool" (infixr "\<equiv>\<^sub>e" 80)
where
  Refl:              "P \<equiv>\<^sub>e P"
| Sym:               "P \<equiv>\<^sub>e Q \<Longrightarrow> Q \<equiv>\<^sub>e P"
| Trans:             "\<lbrakk>P \<equiv>\<^sub>e Q; Q \<equiv>\<^sub>e R\<rbrakk> \<Longrightarrow> P \<equiv>\<^sub>e R"

| Match:             "[a\<frown>a]P \<equiv>\<^sub>e P"
| Match':            "a \<noteq> b \<Longrightarrow> [a\<frown>b]P \<equiv>\<^sub>e \<zero>"

| Mismatch:         "a \<noteq> b \<Longrightarrow> [a\<noteq>b]P \<equiv>\<^sub>e P"
| Mismatch':        "[a\<noteq>a]P \<equiv>\<^sub>e \<zero>"
 
| SumSym:            "P \<oplus> Q \<equiv>\<^sub>e Q \<oplus> P"
| SumAssoc:          "(P \<oplus> Q) \<oplus> R \<equiv>\<^sub>e P \<oplus> (Q \<oplus> R)"
| SumZero:           "P \<oplus> \<zero> \<equiv>\<^sub>e P"
| SumIdemp:          "P \<oplus> P \<equiv>\<^sub>e P"
| SumRes:            "<\<nu>x>(P \<oplus> Q) \<equiv>\<^sub>e (<\<nu>x>P) \<oplus> (<\<nu>x>Q)"

| ResNil:            "<\<nu>x>\<zero> \<equiv>\<^sub>e \<zero>"
| ResInput:          "\<lbrakk>x \<noteq> a; x \<noteq> y\<rbrakk> \<Longrightarrow> <\<nu>x>a<y>.P \<equiv>\<^sub>e a<y>.(<\<nu>x>P)"
| ResInput':         "<\<nu>x>x<y>.P \<equiv>\<^sub>e \<zero>"
| ResOutput:         "\<lbrakk>x \<noteq> a; x \<noteq> b\<rbrakk> \<Longrightarrow> <\<nu>x>a{b}.P \<equiv>\<^sub>e a{b}.(<\<nu>x>P)"
| ResOutput':        "<\<nu>x>x{b}.P \<equiv>\<^sub>e \<zero>"
| ResTau:            "<\<nu>x>\<tau>.(P) \<equiv>\<^sub>e \<tau>.(<\<nu>x>P)"
| ResComm:           "<\<nu>x><\<nu>y>P \<equiv>\<^sub>e <\<nu>y><\<nu>x>P"
| ResFresh:          "x \<sharp> P \<Longrightarrow> <\<nu>x>P \<equiv>\<^sub>e P"

| Expand:            "\<lbrakk>(R, expandSet P Q) \<in> sumComposeSet; hnf P; hnf Q\<rbrakk> \<Longrightarrow> P \<parallel> Q \<equiv>\<^sub>e R"

| SumPres:           "P \<equiv>\<^sub>e Q \<Longrightarrow> P \<oplus> R \<equiv>\<^sub>e Q \<oplus> R" 
| ParPres:           "\<lbrakk>P \<equiv>\<^sub>e P'; Q \<equiv>\<^sub>e Q'\<rbrakk> \<Longrightarrow> P \<parallel> Q \<equiv>\<^sub>e P' \<parallel> Q'"
| ResPres:           "P \<equiv>\<^sub>e Q \<Longrightarrow> <\<nu>x>P \<equiv>\<^sub>e <\<nu>x>Q"
| TauPres:           "P \<equiv>\<^sub>e Q \<Longrightarrow> \<tau>.(P) \<equiv>\<^sub>e \<tau>.(Q)"
| OutputPres:        "P \<equiv>\<^sub>e Q \<Longrightarrow> a{b}.P \<equiv>\<^sub>e a{b}.Q"
| InputPres:         "\<lbrakk>\<forall>y \<in> supp(P, Q, x). P[x::=y] \<equiv>\<^sub>e Q[x::=y]\<rbrakk> \<Longrightarrow> a<x>.P \<equiv>\<^sub>e a<x>.Q"

lemma SumIdemp':
  fixes P  :: pi
  and   P' :: pi

  assumes "P \<equiv>\<^sub>e P'"

  shows "P \<oplus> P' \<equiv>\<^sub>e P"
proof -
  have "P \<equiv>\<^sub>e P \<oplus> P" by(blast intro: Sym SumIdemp)
  moreover from assms have "P \<oplus> P \<equiv>\<^sub>e P' \<oplus> P" by(rule SumPres)
  moreover have "P' \<oplus> P \<equiv>\<^sub>e P \<oplus> P'" by(rule SumSym)
  ultimately have "P \<equiv>\<^sub>e P \<oplus> P'" by(blast intro: Trans)
  thus ?thesis by(rule Sym)
qed

lemma SumPres':
  fixes P  :: pi
  and   P' :: pi
  and   Q  :: pi
  and   Q' :: pi

  assumes PeqP': "P \<equiv>\<^sub>e P'"
  and     QeqQ': "Q \<equiv>\<^sub>e Q'"

  shows "P \<oplus> Q \<equiv>\<^sub>e P' \<oplus> Q'"
proof -
  from PeqP' have "P \<oplus> Q \<equiv>\<^sub>e P' \<oplus> Q" by(rule SumPres)
  moreover have "P' \<oplus> Q \<equiv>\<^sub>e Q \<oplus> P'" by(rule SumSym)
  moreover from QeqQ' have "Q \<oplus> P' \<equiv>\<^sub>e Q' \<oplus> P'" by(rule SumPres)
  moreover have "Q' \<oplus> P' \<equiv>\<^sub>e P' \<oplus> Q'" by(rule SumSym)
  ultimately show ?thesis by(blast intro: Trans)
qed
(*
lemma ParComm:
  fixes P :: pi
  and   Q :: pi
  and   R :: pi

  assumes "(R, expandSet P Q) \<in> sumComposeSet"

  obtains R' where "(R, expandSet Q P) \<in> sumComposeSet" and "R \<equiv>\<^sub>e R'"
using assms
apply(induct S=="expandSet P Q" rule: sumComposeSet.induct)
apply auto
apply(simp add: expandSet_def)
apply fastforce
apply auto
apply(clarify)
*)
lemma sound:
  fixes P :: pi
  and   Q :: pi

  assumes "P \<equiv>\<^sub>e Q"

  shows "P \<sim> Q"
using assms
proof(induct)
  case(Refl P)
  show ?case by(rule reflexive)
next
  case(Sym P Q)
  have "P \<sim> Q" by fact
  thus ?case by(rule symmetric)
next
  case(Trans P Q R)
  have "P \<sim> Q" and "Q \<sim> R" by fact+
  thus ?case by(rule transitive)
next
  case(Match a P)
  show ?case by(rule matchId)
next
  case(Match' a b P)
  have "a \<noteq> b" by fact
  thus ?case by(rule matchNil)
next
  case(Mismatch a b P)
  have "a \<noteq> b" by fact
  thus ?case by(rule mismatchId)
next
  case(Mismatch' a P)
  show ?case by(rule mismatchNil)
next
  case(SumSym P Q)
  show ?case by(rule sumSym)
next
  case(SumAssoc P Q R)
  show ?case by(rule sumAssoc)
next
  case(SumZero P)
  show ?case by(rule sumZero)
next
  case(SumIdemp P)
  show ?case by(rule sumIdemp)
next
  case(SumRes x P Q)
  show ?case by(rule sumRes)
next
  case(ResNil x)
  show ?case by(rule nilRes)
next
  case(ResInput x a y P)
  have "x \<noteq> a" and "x \<noteq> y" by fact+
  thus ?case by(rule resInput)
next
  case(ResInput' x y P)
  show ?case by(rule resNil)
next
  case(ResOutput x a b P)
  have "x \<noteq> a" and "x \<noteq> b" by fact+
  thus ?case by(rule resOutput)
next
  case(ResOutput' x b P)
  show ?case by(rule resNil)
next
  case(ResTau x P)
  show ?case by(rule resTau)
next
  case(ResComm x P)
  show ?case by(rule resComm)
next
  case(ResFresh x P)
  have "x \<sharp> P" by fact
  thus ?case by(rule scopeFresh)
next
  case(Expand R P Q)
  have "(R, expandSet P Q) \<in> sumComposeSet" and "hnf P" and "hnf Q" by fact+
  thus ?case by(rule expandSC)
next
  case(SumPres P Q R)
  from \<open>P \<sim> Q\<close> show ?case by(rule sumPres)
next
  case(ParPres P P' Q Q')
  have "P \<sim> P'" and "Q \<sim> Q'" by fact+
  thus ?case by(metis transitive symmetric parPres parSym)
next
  case(ResPres P Q x)
  from \<open>P \<sim> Q\<close> show ?case by(rule resPres)
next
  case(TauPres P Q)
  from \<open>P \<sim> Q\<close> show ?case by(rule tauPres)
next
  case(OutputPres P Q a b)
  from \<open>P \<sim> Q\<close> show ?case by(rule outputPres)
next
  case(InputPres P Q x a)
  have "\<forall>y \<in> supp(P, Q, x). P[x::=y] \<equiv>\<^sub>e Q[x::=y] \<and> P[x::=y] \<sim> Q[x::=y]" by fact
  hence "\<forall>y \<in> supp(P, Q, x). P[x::=y] \<sim> Q[x::=y]" by blast
  thus ?case by(rule_tac inputSuppPresBisim) auto
qed

lemma zeroDest[dest]:
  fixes a :: name
  and   b :: name
  and   x :: name
  and   P :: pi

  shows "(a{b}.P) \<equiv>\<^sub>e \<zero> \<Longrightarrow> False"
  and   "(a<x>.P) \<equiv>\<^sub>e \<zero> \<Longrightarrow> False"
  and   "(\<tau>.(P)) \<equiv>\<^sub>e \<zero> \<Longrightarrow> False"

  and   "\<zero> \<equiv>\<^sub>e a{b}.P \<Longrightarrow> False"
  and   "\<zero> \<equiv>\<^sub>e a<x>.P \<Longrightarrow> False"
  and   "\<zero> \<equiv>\<^sub>e \<tau>.(P) \<Longrightarrow> False"
by(auto dest: sound)

lemma eq_eqvt:
  fixes pi::"name prm"
  and   x::"'a::pt_name"
  shows "pi\<bullet>(x=y) = ((pi\<bullet>x)=(pi\<bullet>y))"
by(simp add: perm_bool perm_bij)
    
nominal_primrec "depth" :: "pi \<Rightarrow> nat" where
  "depth \<zero> = 0"
| "depth (\<tau>.(P)) = 1 + (depth P)"
| "a \<sharp> x \<Longrightarrow> depth (a<x>.P) = 1 + (depth P)"
| "depth (a{b}.P) = 1 + (depth P)"
| "depth ([a\<frown>b]P) = (depth P)"
| "depth ([a\<noteq>b]P) = (depth P)"
| "depth (P \<oplus> Q) = max (depth P) (depth Q)"
| "depth (P \<parallel> Q) = ((depth P) + (depth Q))"
| "depth (<\<nu>x>P) = (depth P)"
| "depth (!P) = (depth P)"
apply(auto simp add: fresh_nat)
apply(finite_guess)+
by(fresh_guess)+

lemma depthEqvt[simp]:
  fixes P :: pi
  and   p :: "name prm"
  
  shows "depth(p \<bullet> P) = depth P"
by(nominal_induct P rule: pi.strong_induct, auto simp add: name_bij)

lemma depthInput[simp]:
  fixes a :: name
  and   x :: name
  and   P :: pi

  shows "depth (a<x>.P) = 1 + (depth P)"
proof -
  obtain y where yineqa: "y \<noteq> a" and yFreshP: "y \<sharp> P"
    by(force intro: name_exists_fresh[of "(a, P)"] simp add: fresh_prod)
  from yFreshP have "a<x>.P = a<y>.([(x, y)] \<bullet> P)" by(simp add: alphaInput)
  with yineqa show ?thesis by simp
qed

nominal_primrec "valid" :: "pi \<Rightarrow> bool" where
  "valid \<zero> = True"
| "valid (\<tau>.(P)) = valid P"
| "x \<sharp> a \<Longrightarrow> valid (a<x>.P) = valid P"
| "valid (a{b}.P) = valid P"
| "valid ([a\<frown>b]P) = valid P"
| "valid ([a\<noteq>b]P) = valid P"
| "valid (P \<oplus> Q) = ((valid P) \<and> (valid Q))"
| "valid (P \<parallel> Q) = ((valid P) \<and> (valid Q))"
| "valid (<\<nu>x>P) = valid P"
| "valid (!P) = False"
apply(auto simp add: fresh_bool)
apply(finite_guess)+
by(fresh_guess)+

lemma validEqvt[simp]:
  fixes P :: pi
  and   p :: "name prm"
  
  shows "valid(p \<bullet> P) = valid P"
by(nominal_induct P rule: pi.strong_induct, auto simp add: name_bij)

lemma validInput[simp]:
  fixes a :: name
  and   x :: name
  and   P :: pi

  shows "valid (a<x>.P) = valid P"
proof -
  obtain y where yineqa: "y \<noteq> a" and yFreshP: "y \<sharp> P"
    by(force intro: name_exists_fresh[of "(a, P)"] simp add: fresh_prod)
  from yFreshP have "a<x>.P = a<y>.([(x, y)] \<bullet> P)" by(simp add: alphaInput)
  with yineqa show ?thesis by simp
qed

lemma depthMin[intro]:
  fixes P

  shows "0 \<le> depth P"
by(induct P rule: pi.induct, auto)

lemma hnfTransition:
  fixes P :: pi

  assumes "hnf P"
  and     "P \<noteq> \<zero>"

  shows "\<exists>Rs. P \<longmapsto> Rs"
using assms
by(induct rule: pi.induct, auto intro: Output Tau Input Sum1 Open)

definition "uhnf" :: "pi \<Rightarrow> bool" where
  "uhnf P \<equiv> hnf P \<and> (\<forall>R \<in> summands P. \<forall>R' \<in> summands P. R \<noteq> R' \<longrightarrow> \<not>(R \<equiv>\<^sub>e R'))"

lemma summandsIdemp:
  fixes P :: pi
  and   Q :: pi

  assumes "Q \<in> summands P"
  and     "Q \<equiv>\<^sub>e Q'"
  
  shows "P \<oplus> Q' \<equiv>\<^sub>e P"
using assms
proof(nominal_induct P arbitrary: Q rule: pi.strong_inducts)
  case(PiNil Q)
  have "Q \<in> summands \<zero>" by fact
  hence False by simp
  thus ?case by simp
next
  case(Output a b P Q)
  have "Q \<equiv>\<^sub>e Q'" by fact
  hence "a{b}.P \<oplus> Q' \<equiv>\<^sub>e a{b}.P \<oplus> Q" by(blast intro: SumPres' Refl Sym)
  moreover have "Q = a{b}.P"
  proof  -
    have "Q \<in> summands (a{b}.P)" by fact
    thus ?thesis by simp
  qed
  ultimately show ?case by(blast intro: SumIdemp Trans)
next
  case(Tau P Q)
  have "Q \<equiv>\<^sub>e Q'" by fact
  hence "\<tau>.(P) \<oplus> Q' \<equiv>\<^sub>e \<tau>.(P) \<oplus> Q" by(blast intro: SumPres' Refl Sym)
  moreover have "Q = \<tau>.(P)"
  proof  -
    have "Q \<in> summands (\<tau>.(P))" by fact
    thus ?thesis by simp
  qed
  ultimately show ?case by(blast intro: SumIdemp Trans)
next
  case(Input a x P Q)
  have "Q \<equiv>\<^sub>e Q'" by fact
  hence "a<x>.P \<oplus> Q' \<equiv>\<^sub>e a<x>.P \<oplus> Q" by(blast intro: SumPres' Refl Sym)
  moreover have "Q = a<x>.P"
  proof  -
    have "Q \<in> summands (a<x>.P)" by fact
    thus ?thesis by simp
  qed
  ultimately show ?case by(blast intro: SumIdemp Trans)
next
  case(Match a b P Q)
  have "Q \<in> summands ([a\<frown>b]P)" by fact
  hence False by simp
  thus ?case by simp
next
  case(Mismatch a b P Q)
  have "Q \<in> summands ([a\<noteq>b]P)" by fact
  hence False by simp
  thus ?case by simp
next
  case(Sum P Q R)
  have IHP: "\<And>P'. \<lbrakk>P' \<in> summands P; P' \<equiv>\<^sub>e Q'\<rbrakk> \<Longrightarrow> P \<oplus> Q' \<equiv>\<^sub>e P" by fact
  have IHQ: "\<And>Q''. \<lbrakk>Q'' \<in> summands Q; Q'' \<equiv>\<^sub>e Q'\<rbrakk> \<Longrightarrow> Q \<oplus> Q' \<equiv>\<^sub>e Q" by fact
  have ReqQ': "R \<equiv>\<^sub>e Q'" by fact
  have "R \<in> summands(P \<oplus> Q)" by fact
  hence "R \<in> summands P \<or> R \<in> summands Q" by simp
  thus ?case
  proof(rule disjE)
    assume "R \<in> summands P"
    hence PQ'eqP: "P \<oplus> Q' \<equiv>\<^sub>e P" using ReqQ' by(rule IHP)
    
    have "(P \<oplus> Q) \<oplus> Q' \<equiv>\<^sub>e P \<oplus> (Q \<oplus> Q')" by(rule SumAssoc)
    moreover have "P \<oplus> (Q \<oplus> Q') \<equiv>\<^sub>e P \<oplus> (Q' \<oplus> Q)" by(blast intro: Refl SumSym SumPres')
    moreover have "P \<oplus> (Q' \<oplus> Q) \<equiv>\<^sub>e (P \<oplus> Q') \<oplus> Q" by(blast intro: SumAssoc Sym)
    moreover from PQ'eqP have "(P \<oplus> Q') \<oplus> Q \<equiv>\<^sub>e P \<oplus> Q" by(blast intro: SumPres' Refl)
    ultimately show ?case by(blast intro: Trans)
  next
    assume "R \<in> summands Q"
    hence QQ'eqQ: "Q \<oplus> Q' \<equiv>\<^sub>e Q" using ReqQ' by(rule IHQ)
    
    have "(P \<oplus> Q) \<oplus> Q' \<equiv>\<^sub>e P \<oplus> (Q \<oplus> Q')" by(rule SumAssoc)
    moreover from QQ'eqQ have "P \<oplus> (Q \<oplus> Q') \<equiv>\<^sub>e P \<oplus> Q" by(blast intro: Refl SumPres')
    ultimately show ?case by(rule Trans)
  qed
next
  case(Par P Q R)
  have "R \<in> summands (P \<parallel> Q)" by fact
  hence False by simp
  thus ?case by simp
next
  case(Res x P Q)
  have "Q \<equiv>\<^sub>e Q'" by fact
  hence "(<\<nu>x>P) \<oplus> Q' \<equiv>\<^sub>e (<\<nu>x>P) \<oplus> Q" by(blast intro: SumPres' Refl Sym)
  moreover have "Q = <\<nu>x>P"
  proof  -
    have "Q \<in> summands (<\<nu>x>P)" by fact
    thus ?thesis by(auto simp add: if_split)
  qed
  ultimately show ?case by(blast intro: SumIdemp Trans)
next
  case(Bang P Q)
  have "Q \<in> summands(!P)" by fact
  hence False by simp
  thus ?case by simp
qed

lemma uhnfSum:
  fixes P :: pi
  and   Q :: pi

  assumes Phnf: "uhnf P"
  and     Qhnf: "uhnf Q"
  and     validP: "valid P"
  and     validQ: "valid Q"

  shows "\<exists>R. uhnf R \<and> valid R \<and> P \<oplus> Q \<equiv>\<^sub>e R \<and> (depth R) \<le> (depth (P \<oplus> Q))"
using assms
proof(nominal_induct P arbitrary: Q rule: pi.strong_inducts)
  case(PiNil Q)
  have "uhnf Q" by fact
  moreover have "valid Q" by fact
  moreover have "\<zero> \<oplus> Q \<equiv>\<^sub>e Q" by(blast intro: SumZero SumSym Trans)
  moreover have "depth Q \<le> depth(\<zero> \<oplus> Q)" by auto
  ultimately show ?case by blast
next
  case(Output a b P Q)
  show ?case
  proof(case_tac "Q = \<zero>")
    assume "Q = \<zero>"
    moreover have "uhnf (a{b}.P)" by(simp add: uhnf_def)
    moreover have "valid (a{b}.P)" by fact
    moreover have "a{b}.P \<oplus> \<zero> \<equiv>\<^sub>e a{b}.P" by(rule SumZero)
    moreover have "depth(a{b}.P) \<le> depth(a{b}.P \<oplus> \<zero>)" by simp
    ultimately show ?case by blast
  next
    assume QineqNil: "Q \<noteq> \<zero>" 
    have Qhnf: "uhnf Q" by fact
    have validQ: "valid Q" by fact
    have validP: "valid(a{b}.P)" by fact
    show ?case
    proof(case_tac "\<exists>Q' \<in> summands Q. Q' \<equiv>\<^sub>e a{b}.P")
      assume "\<exists>Q' \<in> summands Q. Q' \<equiv>\<^sub>e a{b}.P"
      then obtain Q' where "Q' \<in> summands Q" and "Q' \<equiv>\<^sub>e a{b}.P" by blast
      hence "Q \<oplus> a{b}.P \<equiv>\<^sub>e Q" by(rule summandsIdemp)
      moreover have "depth Q \<le> depth(Q \<oplus> a{b}.P)" by simp
      ultimately show ?case using Qhnf validQ by(force intro: SumSym Trans)
    next
      assume "\<not>(\<exists>Q' \<in> summands Q. Q' \<equiv>\<^sub>e a{b}.P)"
      hence "\<forall>Q' \<in> summands Q. \<not>(Q' \<equiv>\<^sub>e a{b}.P)" by simp
      with Qhnf QineqNil have "uhnf (a{b}.P \<oplus> Q)"
        by(force dest: Sym simp add: uhnf_def)
      moreover from validQ validP have "valid(a{b}.P \<oplus> Q)"  by simp
      moreover have "a{b}.P \<oplus> Q \<equiv>\<^sub>e a{b}.P \<oplus> Q" by(rule Refl)
      moreover have "depth(a{b}.P \<oplus> Q) \<le> depth(a{b}.P \<oplus> Q)" by simp
      ultimately show ?case by blast
    qed
  qed
next
  case(Tau P Q)
  show ?case
  proof(case_tac "Q = \<zero>")
    assume "Q = \<zero>"
    moreover have "uhnf (\<tau>.(P))" by(simp add: uhnf_def)
    moreover have "valid (\<tau>.(P))" by fact
    moreover have "\<tau>.(P) \<oplus> \<zero> \<equiv>\<^sub>e \<tau>.(P)" by(rule SumZero)
    moreover have "depth(\<tau>.(P)) \<le> depth(\<tau>.(P) \<oplus> \<zero>)" by simp
    ultimately show ?case by blast
  next
    assume QineqNil: "Q \<noteq> \<zero>" 
    have Qhnf: "uhnf Q" by fact
    have validP: "valid(\<tau>.(P))" and validQ: "valid Q" by fact+
    show ?case
    proof(case_tac "\<exists>Q' \<in> summands Q. Q' \<equiv>\<^sub>e \<tau>.(P)")
      assume "\<exists>Q' \<in> summands Q. Q' \<equiv>\<^sub>e \<tau>.(P)"
      then obtain Q' where "Q' \<in> summands Q" and "Q' \<equiv>\<^sub>e \<tau>.(P)" by blast
      hence "Q \<oplus> \<tau>.(P) \<equiv>\<^sub>e Q" by(rule summandsIdemp)
      moreover have "depth Q \<le> depth(Q \<oplus> \<tau>.(P))" by simp
      ultimately show ?case using Qhnf validQ by(force intro: SumSym Trans)
    next
      assume "\<not>(\<exists>Q' \<in> summands Q. Q' \<equiv>\<^sub>e \<tau>.(P))"
      hence "\<forall>Q' \<in> summands Q. \<not>(Q' \<equiv>\<^sub>e \<tau>.(P))" by simp
      with Qhnf QineqNil have "uhnf (\<tau>.(P) \<oplus> Q)"
        by(force dest: Sym simp add: uhnf_def)
      moreover from validP validQ have "valid(\<tau>.(P) \<oplus> Q)" by simp
      moreover have "\<tau>.(P) \<oplus> Q \<equiv>\<^sub>e \<tau>.(P) \<oplus> Q" by(rule Refl)
      moreover have "depth(\<tau>.(P) \<oplus> Q) \<le> depth(\<tau>.(P) \<oplus> Q)" by simp
      ultimately show ?case by blast
    qed
  qed
next
  case(Input a x P Q)
  show ?case
  proof(case_tac "Q = \<zero>")
    assume "Q = \<zero>"
    moreover have "uhnf (a<x>.P)" by(simp add: uhnf_def)
    moreover have "valid (a<x>.P)" by fact
    moreover have "a<x>.P \<oplus> \<zero> \<equiv>\<^sub>e a<x>.P" by(rule SumZero)
    moreover have "depth(a<x>.P) \<le> depth(a<x>.P \<oplus> \<zero>)" by simp
    ultimately show ?case by blast
  next
    assume QineqNil: "Q \<noteq> \<zero>" 
    have validP: "valid(a<x>.P)" and validQ: "valid Q" by fact+
    have Qhnf: "uhnf Q" by fact
    show ?case
    proof(case_tac "\<exists>Q' \<in> summands Q. Q' \<equiv>\<^sub>e a<x>.P")
      assume "\<exists>Q' \<in> summands Q. Q' \<equiv>\<^sub>e a<x>.P"
      then obtain Q' where "Q' \<in> summands Q" and "Q' \<equiv>\<^sub>e a<x>.P" by blast
      hence "Q \<oplus> a<x>.P \<equiv>\<^sub>e Q" by(rule summandsIdemp)
      moreover have "depth Q \<le> depth(Q \<oplus> a<x>.P)" by simp
      ultimately show ?case using Qhnf validQ by(force intro: SumSym Trans)
    next
      assume "\<not>(\<exists>Q' \<in> summands Q. Q' \<equiv>\<^sub>e a<x>.P)"
      hence "\<forall>Q' \<in> summands Q. \<not>(Q' \<equiv>\<^sub>e a<x>.P)" by simp
      with Qhnf QineqNil have "uhnf (a<x>.P \<oplus> Q)"
        by(force dest: Sym simp add: uhnf_def)
      moreover from validP validQ have "valid(a<x>.P \<oplus> Q)" by simp
      moreover have "a<x>.P \<oplus> Q \<equiv>\<^sub>e a<x>.P \<oplus> Q" by(rule Refl)
      moreover have "depth(a<x>.P \<oplus> Q) \<le> depth(a<x>.P \<oplus> Q)" by simp
      ultimately show ?case by blast
    qed
  qed
next
  case(Match a b P Q)
  have "uhnf ([a\<frown>b]P)" by fact
  hence False by(simp add: uhnf_def)
  thus ?case by simp
next
  case(Mismatch a b P Q)
  have "uhnf ([a\<noteq>b]P)" by fact
  hence False by(simp add: uhnf_def)
  thus ?case by simp
next
  case(Sum P Q R)
  have Rhnf: "uhnf R" by fact
  have validR: "valid R" by fact
  have PQhnf: "uhnf (P \<oplus> Q)" by fact
  have validPQ: "valid(P \<oplus> Q)" by fact
  have "\<exists>T. uhnf T \<and> valid T \<and> Q \<oplus> R \<equiv>\<^sub>e T \<and> depth T \<le> depth (Q \<oplus> R)"
  proof -
    from PQhnf have "uhnf Q" by(simp add: uhnf_def)
    moreover from validPQ have "valid Q" by simp+
    moreover have "\<And>R. \<lbrakk>uhnf Q; uhnf R; valid Q; valid R\<rbrakk> \<Longrightarrow> \<exists>T. uhnf T \<and> valid T \<and> Q \<oplus> R \<equiv>\<^sub>e T \<and> depth T \<le> depth(Q \<oplus> R)" by fact
    ultimately show ?thesis using Rhnf validR by blast
  qed
  then obtain T where Thnf: "uhnf T" and QReqT: "Q \<oplus> R \<equiv>\<^sub>e T" and validT: "valid T"
                  and Tdepth: "depth T \<le> depth(Q \<oplus> R)" by blast
  
  have "\<exists>S. uhnf S \<and> valid S \<and> P \<oplus> T \<equiv>\<^sub>e S \<and> depth S \<le> depth(P \<oplus> T)"
  proof -
    from PQhnf have "uhnf P" by(simp add: uhnf_def)
    moreover from validPQ have "valid P" by simp
    moreover have "\<And>T. \<lbrakk>uhnf P; uhnf T; valid P; valid T\<rbrakk> \<Longrightarrow> \<exists>S. uhnf S \<and> valid S \<and> P \<oplus> T \<equiv>\<^sub>e S \<and> depth S \<le> depth(P \<oplus> T)" by fact
    ultimately show ?thesis using Thnf validT by blast
  qed
  then obtain S where Shnf: "uhnf S" and PTeqS: "P \<oplus> T \<equiv>\<^sub>e S" and validS: "valid S"
                  and Sdepth: "depth S \<le> depth(P \<oplus> T)" by blast
    
  have "(P \<oplus> Q) \<oplus> R \<equiv>\<^sub>e S"
  proof -
    have "(P \<oplus> Q) \<oplus> R \<equiv>\<^sub>e P \<oplus> (Q \<oplus> R)" by(rule SumAssoc)
    moreover from QReqT have "P \<oplus> (Q \<oplus> R) \<equiv>\<^sub>e P \<oplus> T"
      by(blast intro: Refl SumPres')
    ultimately show ?thesis using PTeqS by(blast intro: Trans)
  qed
  moreover from Tdepth Sdepth have "depth S \<le> depth((P \<oplus> Q) \<oplus> R)" by auto
  
  ultimately show ?case using Shnf validS by blast
next
  case(Par P Q R)
  have "uhnf (P \<parallel> Q)" by fact
  hence False by(simp add: uhnf_def)
  thus ?case by simp
next
  case(Res x P Q)
  show ?case
  proof(case_tac "Q = \<zero>")
    assume "Q = \<zero>"
    moreover have "uhnf (<\<nu>x>P)" by fact
    moreover have "valid (<\<nu>x>P)" by fact
    moreover have "<\<nu>x>P \<oplus> \<zero> \<equiv>\<^sub>e <\<nu>x>P" by(rule SumZero)
    moreover have "depth(<\<nu>x>P) \<le> depth((<\<nu>x>P) \<oplus> \<zero>)" by simp
    ultimately show ?case by blast
  next
    assume QineqNil: "Q \<noteq> \<zero>" 
    have Qhnf: "uhnf Q" by fact
    have validP: "valid(<\<nu>x>P)" and validQ: "valid Q" by fact+
    show ?case
    proof(case_tac "\<exists>Q' \<in> summands Q. Q' \<equiv>\<^sub>e <\<nu>x>P")
      assume "\<exists>Q' \<in> summands Q. Q' \<equiv>\<^sub>e <\<nu>x>P"
      then obtain Q' where "Q' \<in> summands Q" and "Q' \<equiv>\<^sub>e <\<nu>x>P" by blast
      hence "Q \<oplus> <\<nu>x>P \<equiv>\<^sub>e Q" by(rule summandsIdemp)
      moreover have "depth Q \<le> depth(Q \<oplus> <\<nu>x>P)" by simp
      ultimately show ?case using Qhnf validQ by(force intro: SumSym Trans)
    next
      assume "\<not>(\<exists>Q' \<in> summands Q. Q' \<equiv>\<^sub>e <\<nu>x>P)"
      hence "\<forall>Q' \<in> summands Q. \<not>(Q' \<equiv>\<^sub>e <\<nu>x>P)" by simp
      moreover have "uhnf (<\<nu>x>P)" by fact
      ultimately have "uhnf (<\<nu>x>P \<oplus> Q)" using Qhnf QineqNil 
        by(force dest: Sym simp add: uhnf_def)
      moreover from validP validQ have "valid(<\<nu>x>P \<oplus> Q)" by simp
      moreover have "(<\<nu>x>P) \<oplus> Q \<equiv>\<^sub>e (<\<nu>x>P) \<oplus> Q" by(rule Refl)
      moreover have "depth((<\<nu>x>P) \<oplus> Q) \<le> depth((<\<nu>x>P) \<oplus> Q)" by simp
      ultimately show ?case by blast
    qed
  qed
next
  case(Bang P Q)
  have "uhnf (!P)" by fact
  hence False by(simp add: uhnf_def)
  thus ?case by simp
qed

lemma uhnfRes:
  fixes x :: name
  and   P :: pi

  assumes Phnf: "uhnf P"
  and     validP: "valid P"

  shows "\<exists>P'. uhnf P' \<and> valid P' \<and> <\<nu>x>P \<equiv>\<^sub>e P' \<and> depth P' \<le> depth(<\<nu>x>P)"
using assms
proof(nominal_induct P avoiding: x rule: pi.strong_inducts)
  case(PiNil x)
  have "uhnf \<zero>" by(simp add: uhnf_def)
  moreover have "valid \<zero>" by simp
  moreover have "<\<nu>x>\<zero> \<equiv>\<^sub>e \<zero>" by(rule ResNil)
  moreover have "depth \<zero> \<le> depth(<\<nu>x>\<zero>)" by simp
  ultimately show ?case by blast
next
  case(Output a b P)
  have "valid(a{b}.P)" by fact
  hence validP: "valid P" by simp
  show ?case
  proof(case_tac "x=a")
    assume "x = a"
    moreover have "uhnf \<zero>" by(simp add: uhnf_def)
    moreover have "valid \<zero>" by simp
    moreover have "\<zero> \<equiv>\<^sub>e <\<nu>x>x{b}.P" by(blast intro: ResOutput' Sym)
    moreover have "depth \<zero> \<le> depth(<\<nu>x>x{b}.P)" by simp
    ultimately show ?case by(blast intro: Sym)
  next
    assume xineqa: "x \<noteq> a"
    show ?case
    proof(case_tac "x=b")
      assume "x=b"
      moreover from xineqa have "uhnf(<\<nu>x>a{x}.P)" by(force simp add: uhnf_def)
      moreover from validP have "valid(<\<nu>x>a{x}.P)" by simp
      moreover have "<\<nu>x>a{x}.P \<equiv>\<^sub>e <\<nu>x>a{x}.P" by(rule Refl)
      moreover have "depth(<\<nu>x>a{x}.P) \<le> depth(<\<nu>x>a{x}.P)" by simp
      ultimately show ?case by blast
    next
      assume xineqb: "x \<noteq> b"
      have "uhnf(a{b}.(<\<nu>x>P))" by(simp add: uhnf_def)
      moreover from validP have "valid(a{b}.(<\<nu>x>P))" by simp
      moreover from xineqa xineqb have "a{b}.(<\<nu>x>P) \<equiv>\<^sub>e <\<nu>x>a{b}.P" by(blast intro: ResOutput Sym)
      moreover have "depth(a{b}.(<\<nu>x>P)) \<le> depth(<\<nu>x>a{b}.P)" by simp
      ultimately show ?case by(blast intro: Sym)
    qed
  qed
next
  case(Tau P)
  have "valid(\<tau>.(P))" by fact
  hence validP: "valid P" by simp
  
  have "uhnf(\<tau>.(<\<nu>x>P))" by(simp add: uhnf_def)
  moreover from validP have "valid(\<tau>.(<\<nu>x>P))" by simp
  moreover have "\<tau>.(<\<nu>x>P) \<equiv>\<^sub>e <\<nu>x>\<tau>.(P)" by(blast intro: ResTau Sym)
  moreover have "depth(\<tau>.(<\<nu>x>P)) \<le> depth(<\<nu>x>\<tau>.(P))" by simp
  ultimately show ?case by(blast intro: Sym)
next
  case(Input a y P x)
  have "valid(a<y>.P)" by fact
  hence validP: "valid P" by simp
  have "y \<sharp> x" by fact hence yineqx: "y \<noteq> x" by simp
  show ?case
  proof(case_tac "x=a")
    assume "x = a"
    moreover have "uhnf \<zero>" by(simp add: uhnf_def)
    moreover have "valid \<zero>" by simp
    moreover have "\<zero> \<equiv>\<^sub>e <\<nu>x>x<y>.P" by(blast intro: ResInput' Sym)
    moreover have "depth \<zero> \<le> depth(<\<nu>x>x<y>.P)" by simp
    ultimately show ?case by(blast intro: Sym)
  next
    assume xineqa: "x \<noteq> a"
    have "uhnf(a<y>.(<\<nu>x>P))" by(simp add: uhnf_def)
    moreover from validP have "valid(a<y>.(<\<nu>x>P))" by simp
    moreover from xineqa yineqx have "a<y>.(<\<nu>x>P) \<equiv>\<^sub>e <\<nu>x>a<y>.P" by(blast intro: ResInput Sym)
    moreover have "depth(a<y>.(<\<nu>x>P)) \<le> depth(<\<nu>x>a<y>.P)" by simp
    ultimately show ?case by(blast intro: Sym)
  qed
next
  case(Match a b P x)
  have "uhnf([a\<frown>b]P)" by fact
  hence False by(simp add: uhnf_def)
  thus ?case by simp
next
  case(Mismatch a b P x)
  have "uhnf([a\<noteq>b]P)" by fact
  hence False by(simp add: uhnf_def)
  thus ?case by simp
next
  case(Sum P Q x)
  have "valid(P \<oplus> Q)" by fact
  hence validP: "valid P" and validQ: "valid Q" by simp+
  have "uhnf(P \<oplus> Q)" by fact
  hence Phnf: "uhnf P" and Qhnf: "uhnf Q" by(auto simp add: uhnf_def)
  
  have "\<exists>P'. uhnf P' \<and> valid P' \<and> P' \<equiv>\<^sub>e <\<nu>x>P \<and> (depth P') \<le> (depth(<\<nu>x>P))"
  proof -
    have "\<lbrakk>uhnf P; valid P\<rbrakk> \<Longrightarrow> \<exists>P'. uhnf P' \<and> valid P' \<and> <\<nu>x>P \<equiv>\<^sub>e P' \<and> (depth P') \<le> (depth (<\<nu>x>P))" by fact
    with validP Phnf show ?thesis by(blast intro: Sym)
  qed
  then obtain P' where P'hnf: "uhnf P'" and P'eqP: "P' \<equiv>\<^sub>e <\<nu>x>P" and validP': "valid P'"
                   and P'depth: "(depth P') \<le> (depth(<\<nu>x>P))" by blast

  have "\<exists>Q'. uhnf Q' \<and> valid Q' \<and> Q' \<equiv>\<^sub>e <\<nu>x>Q \<and> (depth Q') \<le> (depth(<\<nu>x>Q))"
  proof -
    have "\<lbrakk>uhnf Q; valid Q\<rbrakk> \<Longrightarrow> \<exists>Q'. uhnf Q' \<and> valid Q' \<and> <\<nu>x>Q \<equiv>\<^sub>e Q' \<and> (depth Q') \<le> (depth(<\<nu>x>Q))" by fact
    with validQ Qhnf show ?thesis by(blast intro: Sym)
  qed
  
  then obtain Q' where Q'hnf: "uhnf Q'" and Q'eqQ: "Q' \<equiv>\<^sub>e <\<nu>x>Q" and validQ': "valid Q'"
                   and Q'depth: "(depth Q') \<le> (depth(<\<nu>x>Q))" by blast    
      
  from P'hnf Q'hnf validP' validQ' obtain R where Rhnf: "uhnf R" and validR: "valid R"
                                              and P'Q'eqR: "P' \<oplus> Q' \<equiv>\<^sub>e R"
                                              and Rdepth: "depth R \<le> depth(P' \<oplus> Q')"
    apply(drule_tac uhnfSum) apply assumption+ by blast
    
  from P'eqP Q'eqQ P'Q'eqR have "<\<nu>x>(P \<oplus> Q) \<equiv>\<^sub>e R" by(blast intro: Sym SumPres' SumRes Trans)
  moreover from Rdepth P'depth Q'depth have "depth R \<le> depth(<\<nu>x>(P \<oplus> Q))" by auto
  ultimately show ?case using validR Rhnf by(blast intro: Sym)
next
  case(Par P Q)
  have "uhnf(P \<parallel> Q)" by fact
  hence False by(simp add: uhnf_def)
  thus ?case by simp
next
  case(Res y P x)
  have "valid(<\<nu>y>P)" by fact hence validP: "valid P" by simp
  have "uhnf(<\<nu>y>P)" by fact
  then obtain a P' where aineqy: "a \<noteq> y" and PeqP': "P = a{y}.P'"
    by(force simp add: uhnf_def)
    
  show ?case
  proof(case_tac "x=y")
    assume "x=y"
    moreover from aineqy have "uhnf(<\<nu>y>a{y}.P')" by(force simp add: uhnf_def)
    moreover from validP PeqP' have "valid(<\<nu>y>a{y}.P')" by simp
    moreover have "<\<nu>y><\<nu>y>a{y}.P' \<equiv>\<^sub>e <\<nu>y>a{y}.P'"
    proof -
      have "y \<sharp> <\<nu>y>a{y}.P'" by(simp add: name_fresh_abs)
      hence "<\<nu>y><\<nu>y>a{y}.P' \<equiv>\<^sub>e <\<nu>y>a{y}.P'" by(rule ResFresh)
      thus ?thesis by(blast intro: Trans)
    qed
    moreover have "depth(<\<nu>y>a{y}.P') \<le> depth(<\<nu>y><\<nu>y>a{y}.P')" by simp
    ultimately show ?case using PeqP' by blast
  next
    assume xineqy: "x\<noteq>y"
    show ?case
    proof(case_tac "x=a")
      assume "x=a"
      moreover have "uhnf \<zero>" by(simp add: uhnf_def)
      moreover have "valid \<zero>" by simp
      moreover have "<\<nu>a><\<nu>y>a{y}.P' \<equiv>\<^sub>e \<zero>"
      proof -
        have "<\<nu>a><\<nu>y>a{y}.P' \<equiv>\<^sub>e <\<nu>y><\<nu>a>a{y}.P'" by(rule ResComm)
        moreover have "<\<nu>y><\<nu>a>a{y}.P' \<equiv>\<^sub>e \<zero>"
          by(blast intro: ResOutput' ResNil ResPres Trans)
        ultimately show ?thesis by(blast intro: Trans)
      qed
      moreover have "depth \<zero> \<le> depth(<\<nu>a><\<nu>y>a{y}.P')" by simp
      ultimately show ?case using PeqP' by blast
    next
      assume xineqa: "x \<noteq> a"
      from aineqy have "uhnf(<\<nu>y>a{y}.(<\<nu>x>P'))" by(force simp add: uhnf_def)
      moreover from validP PeqP' have "valid(<\<nu>y>a{y}.(<\<nu>x>P'))" by simp
      moreover have "<\<nu>x><\<nu>y>a{y}.P' \<equiv>\<^sub>e <\<nu>y>a{y}.(<\<nu>x>P')"
      proof -
        have "<\<nu>x><\<nu>y>a{y}.P' \<equiv>\<^sub>e <\<nu>y><\<nu>x>a{y}.P'" by(rule ResComm)
        moreover from xineqa xineqy have "<\<nu>y><\<nu>x>a{y}.P' \<equiv>\<^sub>e <\<nu>y>a{y}.(<\<nu>x>P')"
          by(blast intro: ResOutput ResPres Trans)
        ultimately show ?thesis by(blast intro: Trans)
      qed
      moreover have "depth(<\<nu>y>a{y}.(<\<nu>x>P')) \<le> depth(<\<nu>x><\<nu>y>a{y}.P')"
        by simp
      ultimately show ?case using PeqP' by blast
    qed
  qed
next
  case(Bang P x)
  have "valid(!P)" by fact
  hence False by simp
  thus ?case by simp
qed

lemma expandHnf:
  fixes P :: pi
  and   S :: "pi set"

  assumes "(P, S) \<in> sumComposeSet"
  and     "\<forall>P \<in> S. uhnf P \<and> valid P"

  shows "\<exists>P'. uhnf P' \<and> valid P' \<and> P \<equiv>\<^sub>e P' \<and> depth P' \<le> depth P"
using assms
proof(induct rule: sumComposeSet.induct)
  case empty
  have "uhnf \<zero>" by(simp add: uhnf_def)
  moreover have "valid \<zero>" by simp
  moreover have "\<zero> \<equiv>\<^sub>e \<zero>" by(rule Refl)
  moreover have "depth \<zero> \<le> depth \<zero>" by simp
  ultimately show ?case by blast
next
  case(insert Q S P)
  have Shnf: "\<forall>P \<in> S. uhnf P \<and> valid P" by fact
  hence "\<forall>P \<in> (S - {(Q)}). uhnf P \<and> valid P" by simp
  moreover have "\<forall>P \<in> (S - {(Q)}). uhnf P \<and> valid P \<Longrightarrow> \<exists>P'. uhnf P' \<and> valid P' \<and> P \<equiv>\<^sub>e P' \<and> depth P' \<le> depth P" by fact
  ultimately obtain P' where P'hnf: "uhnf P'" and validP': "valid P'"
                         and PeqP': "P \<equiv>\<^sub>e P'" and PP'depth: "depth P' \<le> depth P"
    by blast
  
  have "Q \<in> S" by fact
  with Shnf have "uhnf Q" and "valid Q" by simp+
  with P'hnf validP' obtain R where Rhnf: "uhnf R" and validR: "valid R"
                                and P'QeqR: "P' \<oplus> Q \<equiv>\<^sub>e R" and P'QRdepth: "depth R \<le> depth (P' \<oplus> Q)"
    by(auto dest: uhnfSum)
  
  from PeqP' P'QeqR have "P \<oplus> Q \<equiv>\<^sub>e R" by(blast intro: SumPres Trans)
  moreover from PP'depth P'QRdepth have "depth R \<le> depth(P \<oplus> Q)" by simp
  ultimately show ?case using Rhnf validR by blast
qed

lemma hnfSummandsRemove:
  fixes P :: pi
  and   Q :: pi

  assumes "P \<in> summands Q"
  and     "uhnf Q"

  shows "(summands Q) - {P' | P'. P' \<in> summands Q \<and> P' \<equiv>\<^sub>e P} = (summands Q) - {P}"
using assms
by(auto intro: Refl simp add: uhnf_def)

lemma pullSummand:
  fixes P  :: pi
  and   Q  :: pi

  assumes PsummQ: "P \<in> summands Q"
  and     Qhnf:   "uhnf Q"

  shows "\<exists>Q'. P \<oplus> Q' \<equiv>\<^sub>e Q \<and> (summands Q') = ((summands Q)  - {x. \<exists>P'. x = P' \<and> P' \<in> (summands Q) \<and> P' \<equiv>\<^sub>e P}) \<and> uhnf Q'"
proof -
  have SumGoal: "\<And>P Q R. \<lbrakk>P \<in> summands Q; uhnf(Q \<oplus> R);
                           \<And>P. \<lbrakk>P \<in> summands Q\<rbrakk> \<Longrightarrow> \<exists>Q'. P \<oplus> Q' \<equiv>\<^sub>e Q \<and> 
                                   (summands Q') = ((summands Q) - {P' |P'. P' \<in> summands Q \<and> P' \<equiv>\<^sub>e P}) \<and> uhnf Q';
                           \<And>P. \<lbrakk>P \<in> summands R\<rbrakk> \<Longrightarrow> \<exists>R'. P \<oplus> R' \<equiv>\<^sub>e R \<and> 
                                   (summands R') = ((summands R) - {P' |P'. P' \<in> summands R \<and> P' \<equiv>\<^sub>e P}) \<and> uhnf R'\<rbrakk>
    \<Longrightarrow> \<exists>Q'. P \<oplus> Q' \<equiv>\<^sub>e Q \<oplus> R \<and>
             summands Q' = summands (pi.Sum Q R) - {P' |P'. P' \<in> summands (Q \<oplus> R) \<and> P' \<equiv>\<^sub>e P} \<and> uhnf Q'"
  proof -
    fix P Q R
    assume IHR: "\<And>P. P \<in> summands R \<Longrightarrow> \<exists>R'. P \<oplus> R' \<equiv>\<^sub>e R \<and> 
                                         (summands R') = ((summands R) - {P' |P'. P' \<in> summands R \<and> P' \<equiv>\<^sub>e P}) \<and> uhnf R'"
    assume PsummQ: "P \<in> summands Q"
    moreover assume "\<And>P. P \<in> summands Q \<Longrightarrow> \<exists>Q'. P \<oplus> Q' \<equiv>\<^sub>e Q \<and> 
                                   (summands Q') = ((summands Q) - {P' |P'. P' \<in> summands Q \<and> P' \<equiv>\<^sub>e P}) \<and> uhnf Q'" 

    ultimately obtain Q' where PQ'eqQ: "P \<oplus> Q' \<equiv>\<^sub>e Q"
                           and Q'summQ: "(summands Q') = ((summands Q) - {P' |P'. P' \<in> summands Q \<and> P' \<equiv>\<^sub>e P})"
                           and Q'hnf: "uhnf Q'"
      by blast
    assume QRhnf: "uhnf(Q \<oplus> R)"

    show "\<exists>Q'. P \<oplus> Q' \<equiv>\<^sub>e Q \<oplus> R \<and>
             summands Q' = summands (pi.Sum Q R) - {P' |P'. P' \<in> summands (Q \<oplus> R) \<and> P' \<equiv>\<^sub>e P} \<and> uhnf Q'"
    proof(cases "\<exists>P' \<in> summands R. P' \<equiv>\<^sub>e P")
      assume "\<exists>P' \<in> summands R. P' \<equiv>\<^sub>e P"
      then obtain P' where P'summR: "P' \<in> summands R" and P'eqP: "P' \<equiv>\<^sub>e P" by blast
      with IHR obtain R' where PR'eqR: "P' \<oplus> R' \<equiv>\<^sub>e R"
        and R'summR: "(summands R') = ((summands R) - {P'' |P''. P'' \<in> summands R \<and> P'' \<equiv>\<^sub>e P'})"
        and R'hnf: "uhnf R'"
        by blast
      
      have L1: "P \<oplus> (Q' \<oplus> R') \<equiv>\<^sub>e Q \<oplus> R"
      proof -
        from P'eqP have "P \<oplus> (Q' \<oplus> R') \<equiv>\<^sub>e (P \<oplus> P') \<oplus> (Q' \<oplus> R')"
          by(blast intro: SumIdemp' SumPres Sym)
        moreover have "(P \<oplus> P') \<oplus> (Q' \<oplus> R') \<equiv>\<^sub>e P \<oplus> (P' \<oplus> (Q' \<oplus> R'))" by(rule SumAssoc)
        moreover have "P \<oplus> (P' \<oplus> (Q' \<oplus> R')) \<equiv>\<^sub>e P \<oplus> (P' \<oplus> (R' \<oplus> Q'))"
          by(blast intro: Refl SumPres' SumSym)
        moreover have "P \<oplus> (P' \<oplus> (R' \<oplus> Q')) \<equiv>\<^sub>e P \<oplus> (P' \<oplus> R') \<oplus> Q'"
          by(blast intro: Refl SumPres' Sym SumAssoc)
        moreover have "P \<oplus> (P' \<oplus> R') \<oplus> Q' \<equiv>\<^sub>e (P \<oplus> Q') \<oplus> (P' \<oplus> R')"
        proof -
          have "P \<oplus> (P' \<oplus> R') \<oplus> Q' \<equiv>\<^sub>e P \<oplus> Q' \<oplus> (P' \<oplus> R')"
            by(blast intro: Refl SumPres' SumSym)
          thus ?thesis by(blast intro: Sym SumAssoc Trans)
        qed
        moreover from PQ'eqQ PR'eqR have "(P \<oplus> Q') \<oplus> (P' \<oplus> R') \<equiv>\<^sub>e Q \<oplus> R" by(rule SumPres')
        ultimately show ?thesis by(blast intro!: Trans)
      qed
      
      show ?thesis
      proof(cases "Q' = \<zero>")
        assume Q'eqNil: "Q' = \<zero>"
        have "P \<oplus> R' \<equiv>\<^sub>e Q \<oplus> R"
        proof -
          have "P \<oplus> R' \<equiv>\<^sub>e P \<oplus> (R' \<oplus> \<zero>)" by(blast intro: SumZero Refl Trans SumPres' Sym)
          moreover have "P \<oplus> (R' \<oplus> \<zero>) \<equiv>\<^sub>e P \<oplus> (\<zero> \<oplus> R')"
            by(blast intro: SumSym Trans SumPres' Refl)
          ultimately show ?thesis using L1 Q'eqNil by(blast intro: Trans)
        qed
        moreover from R'summR Q'summQ P'eqP Q'eqNil have "summands (R') = (summands (Q \<oplus> R) - {P' |P'. P' \<in> summands(Q \<oplus> R) \<and> P' \<equiv>\<^sub>e P})"
          by(auto intro: Sym Trans)
        ultimately show ?thesis using R'hnf by blast
      next
        assume Q'ineqNil: "Q' \<noteq> \<zero>"
        show ?thesis
        proof(case_tac "R' = \<zero>")
          assume R'eqNil: "R' = \<zero>"
          have "P \<oplus> Q' \<equiv>\<^sub>e Q \<oplus> R"
          proof -
            have "P \<oplus> Q' \<equiv>\<^sub>e P \<oplus> (Q' \<oplus> \<zero>)" by(blast intro: SumZero Refl Trans SumPres' Sym)
            with L1 R'eqNil show ?thesis by(blast intro: Trans)
          qed
          moreover from R'summR Q'summQ P'eqP R'eqNil have "summands (Q') = (summands (Q \<oplus> R) - {P' |P'. P' \<in> summands(Q \<oplus> R) \<and> P' \<equiv>\<^sub>e P})"
            by(auto intro: Sym Trans)
          ultimately show ?thesis using Q'hnf by blast
        next
          assume R'ineqNil: "R' \<noteq> \<zero>"
          
          from R'summR Q'summQ P'eqP have "summands (Q' \<oplus> R') = (summands (Q \<oplus> R) - {P' |P'. P' \<in> summands(Q \<oplus> R) \<and> P' \<equiv>\<^sub>e P})"
            by(auto intro: Sym Trans)
          moreover from QRhnf Q'hnf R'hnf R'summR Q'summQ Q'ineqNil R'ineqNil have "uhnf(Q' \<oplus> R')"
            by(auto simp add: uhnf_def)
          
          ultimately show ?thesis using L1 by blast
        qed
      qed
    next
      assume "\<not>(\<exists>P' \<in> summands R. P' \<equiv>\<^sub>e P)"
      hence Case: "\<forall>P' \<in> summands R. \<not>(P' \<equiv>\<^sub>e P)" by simp
      show ?thesis
      proof(case_tac "Q' = \<zero>")
        assume Q'eqNil: "Q' = \<zero>"
        have "P \<oplus> R \<equiv>\<^sub>e Q \<oplus> R" 
        proof -

          have "P \<oplus> R \<equiv>\<^sub>e (P \<oplus> \<zero>) \<oplus> R" by(blast intro: SumZero Sym Trans SumPres)
          moreover from  PQ'eqQ have "P \<oplus> (Q' \<oplus> R) \<equiv>\<^sub>e Q \<oplus> R"
             by(blast intro: SumAssoc Trans Sym SumPres) 
           ultimately show ?thesis using Q'eqNil by(blast intro: SumAssoc Trans)
         qed
         
         moreover from Q'summQ Q'eqNil Case have "summands (R) = (summands (Q \<oplus> R) - {P' |P'. P' \<in> summands(Q \<oplus> R) \<and> P' \<equiv>\<^sub>e P})"
           by auto
         moreover from QRhnf have "uhnf R" by(simp add: uhnf_def)

         ultimately show ?thesis by blast       
       next
         assume Q'ineqNil: "Q' \<noteq> \<zero>"
         from PQ'eqQ have "P \<oplus> (Q' \<oplus> R) \<equiv>\<^sub>e Q \<oplus> R" 
           by(blast intro: SumAssoc Trans Sym SumPres) 
         
         moreover from Q'summQ Case have "summands (Q' \<oplus> R) = (summands (Q \<oplus> R) - {P' |P'. P' \<in> summands(Q \<oplus> R) \<and> P' \<equiv>\<^sub>e P})"
           by auto
         moreover from QRhnf Q'hnf Q'summQ Q'ineqNil have "uhnf (Q' \<oplus> R)"
           by(auto simp add: uhnf_def)
         ultimately show ?thesis by blast
       qed
     qed
   qed

   from assms show ?thesis
   proof(nominal_induct Q arbitrary: P rule: pi.strong_inducts)
     case PiNil
     have "P \<in> summands \<zero>" by fact
     hence False by auto
     thus ?case by simp
   next
     case(Output a b Q)
     have "P \<in> summands (a{b}.Q)" by fact
     hence PeqQ: "P = a{b}.Q" by simp
     have "P \<oplus> \<zero> \<equiv>\<^sub>e a{b}.Q"
     proof -
       have "P \<oplus> \<zero> \<equiv>\<^sub>e P" by(rule SumZero)
       with PeqQ show ?thesis by simp
     qed
     moreover have "(summands \<zero>) = (summands (a{b}.Q)) - {P' | P'. P' \<in> summands (a{b}.Q) \<and> P' \<equiv>\<^sub>e P}"
     proof -
       have "a{b}.Q \<equiv>\<^sub>e a{b}.Q" by(rule Refl)
       with PeqQ show ?thesis by simp
     qed
     moreover have "uhnf \<zero>" by(simp add: uhnf_def)
     ultimately show ?case by blast
   next
     case(Tau Q)
     have "P \<in> summands (\<tau>.(Q))" by fact
     hence PeqQ: "P = \<tau>.(Q)" by simp
     have "P \<oplus> \<zero> \<equiv>\<^sub>e \<tau>.(Q)"
     proof -
       have "P \<oplus> \<zero> \<equiv>\<^sub>e P" by(rule SumZero)
       with PeqQ show ?thesis by simp
     qed
     moreover have "(summands \<zero>) = (summands (\<tau>.(Q))) - {P' | P'. P' \<in> summands (\<tau>.(Q)) \<and> P' \<equiv>\<^sub>e P}"
     proof -
       have "\<tau>.(Q) \<equiv>\<^sub>e \<tau>.(Q)" by(rule Refl)
       with PeqQ show ?thesis by simp
     qed
     moreover have "uhnf \<zero>" by(simp add: uhnf_def)
     ultimately show ?case by blast
   next
     case(Input a x Q)
     have "P \<in> summands (a<x>.Q)" by fact
     hence PeqQ: "P = a<x>.Q" by simp
     have "P \<oplus> \<zero> \<equiv>\<^sub>e a<x>.Q"
     proof -
       have "P \<oplus> \<zero> \<equiv>\<^sub>e P" by(rule SumZero)
       with PeqQ show ?thesis by simp
     qed
     moreover have "(summands \<zero>) = (summands (a<x>.Q)) - {P' | P'. P' \<in> summands (a<x>.Q) \<and> P' \<equiv>\<^sub>e P}"
     proof -
       have "a<x>.Q \<equiv>\<^sub>e a<x>.Q" by(rule Refl)
       with PeqQ show ?thesis by simp
     qed
     moreover have "uhnf \<zero>" by(simp add: uhnf_def)
     ultimately show ?case by blast
   next
     case(Match a b Q)
     have "P \<in> summands ([a\<frown>b]Q)" by fact
     hence False by simp
     thus ?case by simp
   next
     case(Mismatch a b Q)
     have "P \<in> summands ([a\<noteq>b]Q)" by fact
     hence False by simp
     thus ?case by simp
   next
     case(Sum Q R)
     have QRhnf: "uhnf (Q \<oplus> R)" by fact
     hence Qhnf: "uhnf Q" and Rhnf: "uhnf R" by(simp add: uhnf_def)+
     have "\<And>P. \<lbrakk>P \<in> summands Q; uhnf Q\<rbrakk> \<Longrightarrow> \<exists>Q'. P \<oplus> Q' \<equiv>\<^sub>e Q \<and> 
                                          (summands Q') = ((summands Q) - {P' |P'. P' \<in> summands Q \<and> P' \<equiv>\<^sub>e P}) \<and> uhnf Q'"
       by fact
     with Qhnf have IHQ: "\<And>P. P \<in> summands Q \<Longrightarrow> \<exists>Q'. P \<oplus> Q' \<equiv>\<^sub>e Q \<and> 
                                  (summands Q') = ((summands Q) - {P' |P'. P' \<in> summands Q \<and> P' \<equiv>\<^sub>e P}) \<and> uhnf Q'"
       by simp
     have "\<And>P. \<lbrakk>P \<in> summands R; uhnf R\<rbrakk> \<Longrightarrow> \<exists>R'. P \<oplus> R' \<equiv>\<^sub>e R \<and> 
                                          (summands R') = ((summands R) - {P' |P'. P' \<in> summands R \<and> P' \<equiv>\<^sub>e P}) \<and> uhnf R'"
       by fact
     with Rhnf have IHR: "\<And>P. P \<in> summands R \<Longrightarrow> \<exists>R'. P \<oplus> R' \<equiv>\<^sub>e R \<and> 
                                  (summands R') = ((summands R) - {P' |P'. P' \<in> summands R \<and> P' \<equiv>\<^sub>e P}) \<and> uhnf R'"
       by simp
     have "P \<in> summands (Q \<oplus> R)" by fact
     hence "P \<in> summands Q \<or> P \<in> summands R" by simp
     thus ?case
     proof(rule disjE)
       assume "P \<in> summands Q"
       thus ?case using QRhnf IHQ IHR by(rule SumGoal)
     next
       assume "P \<in> summands R"
       moreover from QRhnf have "uhnf (R \<oplus> Q)" by(auto simp add: uhnf_def)
       ultimately have "\<exists>Q'. (pi.Sum P Q') \<equiv>\<^sub>e (pi.Sum R Q) \<and>
         summands Q' = summands (pi.Sum R Q) - {P' |P'. P' \<in> summands (pi.Sum R Q) \<and> P' \<equiv>\<^sub>e P} \<and> uhnf Q'" using IHR IHQ
         by(rule SumGoal)
       thus ?case 
         by(force intro: SumSym Trans)
     qed
   next
     case(Par Q R P)
     have "P \<in> summands (Q \<parallel> R)" by fact
     hence False by simp
     thus ?case by simp
   next
     case(Res x Q P)
     have "P \<in> summands (<\<nu>x>Q)" by fact
     hence PeqQ: "P = <\<nu>x>Q" by(simp add: if_split)
     have "P \<oplus> \<zero> \<equiv>\<^sub>e <\<nu>x>Q"
     proof -
       have "P \<oplus> \<zero> \<equiv>\<^sub>e P" by(rule SumZero)
       with PeqQ show ?thesis by simp
     qed
     moreover have "(summands \<zero>) = (summands (<\<nu>x>Q)) - {P' | P'. P' \<in> summands (<\<nu>x>Q) \<and> P' \<equiv>\<^sub>e P}"
     proof -
       have "<\<nu>x>Q \<equiv>\<^sub>e <\<nu>x>Q" by(rule Refl)
       with PeqQ show ?thesis by simp
     qed
     moreover have "uhnf \<zero>" by(simp add: uhnf_def)
     ultimately show ?case by blast
   next
     case(Bang Q P)
     have "P \<in> summands (!Q)" by fact
     hence False by simp
     thus ?case by simp
   qed
 qed
  
lemma nSym:
  fixes P :: pi
  and   Q :: pi

  assumes "\<not>(P \<equiv>\<^sub>e Q)"

  shows "\<not>(Q \<equiv>\<^sub>e P)"
using assms
by(blast dest: Sym)

lemma summandsZero:
  fixes P :: pi
  
  assumes "summands P = {}"
  and     "hnf P"

  shows "P = \<zero>"
using assms
by(nominal_induct P rule: pi.strong_inducts, auto intro: Refl SumIdemp SumPres' Trans)  

lemma summandsZero':
  fixes P :: pi
  
  assumes summP: "summands P = {}"
  and     Puhnf: "uhnf P"

  shows "P = \<zero>"
proof -
  from Puhnf have "hnf P" by(simp add: uhnf_def)
  with summP show ?thesis by(rule summandsZero)
qed

lemma summandEquiv:
  fixes P :: pi
  and   Q :: pi

  assumes Phnf: "uhnf P"
  and     Qhnf: "uhnf Q"
  and     PinQ: "\<forall>P' \<in> summands P. \<exists>Q' \<in> summands Q. P' \<equiv>\<^sub>e Q'"
  and     QinP: "\<forall>Q' \<in> summands Q. \<exists>P' \<in> summands P. Q' \<equiv>\<^sub>e P'"

  shows "P \<equiv>\<^sub>e Q"
proof -
  from finiteSummands assms show ?thesis
  proof(induct F=="summands P" arbitrary: P Q rule: finite_induct)
    case(empty P Q)
    have PEmpty: "{} = summands P" by fact
    moreover have "\<forall>Q'\<in>summands Q. \<exists>P'\<in>summands P. Q' \<equiv>\<^sub>e P'" by fact
    ultimately have QEmpty: "summands Q = {}" by simp
    
    have "P = \<zero>"
    proof -
      have "uhnf P" by fact
      with PEmpty show ?thesis by(blast intro: summandsZero')
    qed
    moreover have "Q = \<zero>"
    proof -
      have "uhnf Q" by fact
      with QEmpty show ?thesis by(blast intro: summandsZero')
    qed
    ultimately show ?case by(blast intro: Refl)
  next
    case(insert P' F P Q)
    have Phnf: "uhnf P" by fact
    have Qhnf: "uhnf Q" by fact
    
    have IH: "\<And>P Q. \<lbrakk>F = summands P; uhnf P; uhnf Q; \<forall>P' \<in> summands P. \<exists>Q' \<in> summands Q. P' \<equiv>\<^sub>e Q';
              \<forall>Q' \<in> summands Q. \<exists>P' \<in> summands P. Q' \<equiv>\<^sub>e P'\<rbrakk> \<Longrightarrow> P \<equiv>\<^sub>e Q"
      by fact
    have PeqQ: "\<forall>P' \<in> summands P. \<exists>Q' \<in> summands Q. P' \<equiv>\<^sub>e Q'" by fact
    have QeqP: "\<forall>Q' \<in> summands Q. \<exists>P' \<in> summands P. Q' \<equiv>\<^sub>e P'" by fact
  
    have PSumm: "insert P' F = summands P" by fact
    hence P'SummP: "P' \<in> summands P" by auto
    
    with Phnf obtain P'' where P'P''eqP: "P' \<oplus> P'' \<equiv>\<^sub>e P" 
                           and P''Summ: "summands P'' = summands P - {P'' |P''. P'' \<in> summands P \<and> P'' \<equiv>\<^sub>e P'}"
                           and P''hnf: "uhnf P''"
      by(blast dest: pullSummand)

    from PeqQ P'SummP obtain Q' where Q'SummQ: "Q' \<in> summands Q" and P'eqQ': "P' \<equiv>\<^sub>e Q'" by blast
    
    from Q'SummQ Qhnf obtain Q'' where Q'Q''eqQ: "Q' \<oplus> Q'' \<equiv>\<^sub>e Q" 
                                   and Q''Summ: "summands Q'' = summands Q - {Q'' |Q''. Q'' \<in> summands Q \<and> Q'' \<equiv>\<^sub>e Q'}"
                                   and Q''hnf: "uhnf Q''"
      by(blast dest: pullSummand) 
    
    have FeqP'': "F = summands P''"
    proof -
      have "P' \<notin> F" by fact
      with P''Summ PSumm hnfSummandsRemove[OF P'SummP Phnf] show ?thesis by blast
    qed

    moreover have "\<forall>P' \<in> summands P''. \<exists>Q' \<in> summands Q''. P' \<equiv>\<^sub>e Q'"
    proof(rule ballI)
      fix P'''
      assume P'''Summ: "P''' \<in> summands P''"
      with P''Summ have "P''' \<in> summands P" by simp
      with PeqQ obtain Q''' where Q'''Summ: "Q''' \<in> summands Q" and P'''eqQ''': "P''' \<equiv>\<^sub>e Q'''" by blast
      have "Q''' \<in> summands Q''"
      proof -
        from P'''Summ P''Summ have "\<not>(P''' \<equiv>\<^sub>e P')" by simp
        with P'eqQ' P'''eqQ''' have "\<not>(Q''' \<equiv>\<^sub>e Q')"  by(blast intro: Trans Sym)
        with Q''Summ Q'''Summ show ?thesis by simp
      qed
    
      with P'''eqQ''' show "\<exists>Q'\<in>summands Q''. P''' \<equiv>\<^sub>e Q'" by blast
    qed
    
    moreover have "\<forall>Q' \<in> summands Q''. \<exists>P' \<in> summands P''. Q' \<equiv>\<^sub>e P'"
    proof(rule ballI)
      fix Q'''
      assume Q'''Summ: "Q''' \<in> summands Q''"
      with Q''Summ have "Q''' \<in> summands Q" by simp
      with QeqP obtain P''' where P'''Summ: "P''' \<in> summands P"
                              and Q'''eqP''': "Q''' \<equiv>\<^sub>e P'''" by blast
      have "P''' \<in> summands P''"
      proof -
        from Q'''Summ Q''Summ have "\<not>(Q''' \<equiv>\<^sub>e Q')" by simp
        with P'eqQ' Q'''eqP''' have "\<not>(P''' \<equiv>\<^sub>e P')"  by(blast intro: Trans)
        with P''Summ P'''Summ show ?thesis by simp
      qed
      with Q'''eqP''' show "\<exists>P'\<in>summands P''. Q''' \<equiv>\<^sub>e P'" by blast
    qed
    
    ultimately have P''eqQ'': "P'' \<equiv>\<^sub>e Q''" using P''hnf Q''hnf by(rule_tac IH) 
    
    from P'P''eqP have "P \<equiv>\<^sub>e P' \<oplus> P''" by(rule Sym)
    moreover from P'eqQ' P''eqQ'' have "P' \<oplus> P'' \<equiv>\<^sub>e Q' \<oplus> Q''" by(rule SumPres')
    ultimately show ?case using Q'Q''eqQ by(blast intro: Trans)
  qed
qed


lemma validSubst[simp]:
  fixes P :: pi
  and   a :: name
  and   b :: name
  and   p :: pi
  
  shows "valid(P[a::=b]) = valid P"
by(nominal_induct P avoiding: a b rule: pi.strong_inducts, auto)

lemma validOutputTransition:
  fixes P  :: pi
  and   a  :: name
  and   b  :: name
  and   P' :: pi

  assumes "P \<longmapsto>a[b] \<prec> P'" 
  and     "valid P"

  shows "valid P'"
using assms
by(nominal_induct rule: outputInduct, auto)

lemma validInputTransition:
  fixes P  :: pi
  and   a  :: name
  and   x  :: name
  and   P' :: pi

  assumes PTrans: "P \<longmapsto>a<x> \<prec> P'" 
  and     validP: "valid P"

  shows "valid P'"
proof -
  have Goal: "\<And>P a x P'. \<lbrakk>P \<longmapsto>a<x> \<prec> P'; x \<sharp> P; valid P\<rbrakk> \<Longrightarrow> valid P'"
  proof -
    fix P a x P'
    assume "P \<longmapsto>a<x> \<prec> P'" and "x \<sharp> P" and "valid P"
    thus "valid P'"
      by(nominal_induct rule: inputInduct, auto)
  qed
  obtain y::name where yFreshP: "y \<sharp> P" and yFreshP': "y \<sharp> P'"
    by(rule_tac name_exists_fresh[of "(P, P')"], auto simp add: fresh_prod)
  from yFreshP' PTrans have "P \<longmapsto>a<y> \<prec> [(x, y)] \<bullet> P'" by(simp add: alphaBoundResidual)
  hence "valid ([(x, y)] \<bullet> P')" using yFreshP validP by(rule Goal)
  thus "valid P'" by simp
qed

lemma validBoundOutputTransition:
  fixes P  :: pi
  and   a  :: name
  and   x  :: name
  and   P' :: pi

  assumes PTrans: "P \<longmapsto>a<\<nu>x> \<prec> P'" 
  and     validP: "valid P"

  shows "valid P'"
proof -
  have Goal: "\<And>P a x P'. \<lbrakk>P \<longmapsto>a<\<nu>x> \<prec> P'; x \<sharp> P; valid P\<rbrakk> \<Longrightarrow> valid P'"
  proof -
    fix P a x P'
    assume "P \<longmapsto>a<\<nu>x> \<prec> P'" and "x \<sharp> P" and "valid P"
    thus "valid P'"
      apply(nominal_induct rule: boundOutputInduct, auto)
      proof -
        fix P a x P'
        assume "P \<longmapsto>(a::name)[x] \<prec> P'" and "valid P"
        thus "valid P'"
          by(nominal_induct rule: outputInduct, auto)
      qed
  qed
  obtain y::name where yFreshP: "y \<sharp> P" and yFreshP': "y \<sharp> P'"
    by(rule_tac name_exists_fresh[of "(P, P')"], auto simp add: fresh_prod)
  from yFreshP' PTrans have "P \<longmapsto>a<\<nu>y> \<prec> [(x, y)] \<bullet> P'" by(simp add: alphaBoundResidual)
  hence "valid ([(x, y)] \<bullet> P')" using yFreshP validP by(rule Goal)
  thus "valid P'" by simp
qed

lemma validTauTransition:
  fixes P  :: pi
  and   P' :: pi

  assumes PTrans: "P \<longmapsto>\<tau> \<prec> P'"
  and     validP: "valid P"

  shows "valid P'"
using assms
by(nominal_induct rule: tauInduct, auto dest: validOutputTransition validInputTransition validBoundOutputTransition)

lemmas validTransition = validInputTransition validOutputTransition validTauTransition validBoundOutputTransition

lemma validSummand:
  fixes P  :: pi
  and   P' :: pi
  and   a  :: name
  and   b  :: name
  and   x  :: name

  assumes "valid P"
  and     "hnf P"

  shows "\<tau>.(P') \<in> summands P \<Longrightarrow> valid P'"
  and   "a{b}.P' \<in> summands P \<Longrightarrow> valid P'"
  and   "a<x>.P' \<in> summands P \<Longrightarrow> valid P'"
  and   "\<lbrakk>a \<noteq> x; <\<nu>x>a{x}.P' \<in> summands P\<rbrakk> \<Longrightarrow> valid P'"
proof -
  assume "\<tau>.(P') \<in> summands P"
  with assms show "valid P'" by(force intro: validTauTransition simp add: summandTransition)
next
  assume "a{b}.P' \<in> summands P"
  with assms show "valid P'" by(force intro: validOutputTransition simp add: summandTransition)
next
  assume "a<x>.P' \<in> summands P"
  with assms show "valid P'" by(force intro: validInputTransition simp add: summandTransition)
next
  assume "<\<nu>x>a{x}.P' \<in> summands P" and "a \<noteq> x"
  with assms show "valid P'" 
    by(force intro: validBoundOutputTransition simp add: summandTransition[THEN sym])
qed

lemma validExpand:
  fixes P :: pi
  and   Q :: pi

  assumes "valid P"
  and     "valid Q"
  and     "uhnf P"
  and     "uhnf Q"

  shows "\<forall>R \<in> (expandSet P Q). uhnf R \<and> valid R"
proof -
  from assms have "hnf P" and "hnf Q" by(simp add: uhnf_def)+
  with assms show ?thesis
    apply(auto simp add: expandSet_def)
    apply(force dest: validSummand simp add: uhnf_def)
    apply(force dest: validSummand)
    apply(force dest: validSummand simp add: uhnf_def)
    apply(force dest: validSummand)
    apply(force dest: validSummand simp add: uhnf_def)
    apply(force dest: validSummand)
    apply(force dest: validSummand simp add: uhnf_def)
    apply(force dest: validSummand)
    apply(force dest: validSummand simp add: uhnf_def)
    apply(force dest: validSummand)
    apply(force dest: validSummand simp add: uhnf_def)
    apply(force dest: validSummand)
    apply(subgoal_tac "a\<noteq>x")
    apply(force dest: validSummand simp add: uhnf_def)
    apply blast
    apply(subgoal_tac "a\<noteq>x")
    apply(drule_tac validSummand(4)) apply assumption+
    apply blast
    apply(subgoal_tac "a\<noteq>x")
    apply(drule_tac validSummand(4)[where P=Q]) apply assumption+
    apply(force dest: validSummand simp add: uhnf_def)
    apply blast
    apply(subgoal_tac "a\<noteq>x")
    apply(drule_tac validSummand(4)[where P=Q]) apply assumption+
    apply blast
    apply(force dest: validSummand simp add: uhnf_def)
    apply(force dest: validSummand)
    apply(force dest: validSummand simp add: uhnf_def)
    apply(force simp add: uhnf_def)
    apply(force dest: validSummand)
    apply(force dest: validSummand)
    apply(force simp add: uhnf_def)
    apply(force dest: validSummand)
    apply(subgoal_tac "a\<noteq>y")
    apply(drule_tac validSummand(4)[where P=Q]) apply assumption+
    apply blast
    apply(force dest: validSummand simp add: uhnf_def)
    apply(subgoal_tac "a\<noteq>y")
    apply(drule_tac validSummand(4)) apply assumption+
    apply blast
    by(force dest: validSummand)
qed

lemma expandComplete:
  fixes F :: "pi set"

  assumes "finite F"

  shows "\<exists>P. (P, F) \<in> sumComposeSet"
using assms
proof(induct F rule: finite_induct)
  case empty
  have "(\<zero>, {}) \<in> sumComposeSet" by(rule sumComposeSet.empty)
  thus ?case by blast
next
  case(insert Q F)
  have "\<exists>P. (P, F) \<in> sumComposeSet" by fact
  then obtain P where "(P, F) \<in> sumComposeSet" by blast
  moreover have "Q \<in> insert Q F" by simp
  moreover have "Q \<notin> F" by fact
  ultimately have "(P \<oplus> Q, insert Q F) \<in> sumComposeSet"
    by(force intro: sumComposeSet.insert)
  thus ?case by blast
qed

lemma expandDepth:
  fixes F :: "pi set"
  and   P :: pi
  and   Q :: pi

  assumes "(P, F) \<in> sumComposeSet"
  and     "F \<noteq> {}"

  shows "\<exists>Q \<in> F. depth P \<le> depth Q \<and> (\<forall>R \<in> F. depth R \<le> depth Q)"
using assms
proof(induct arbitrary: Q rule: sumComposeSet.induct)
  case empty
  have "({}::pi set) \<noteq> {}" by fact
  hence False by simp
  thus ?case by simp
next
  case(insert Q S P)
  have QinS: "Q \<in> S" by fact
  show ?case
  proof(case_tac "(S - {Q}) = {}")
    assume "(S - {Q}) = {}"
    with QinS have SeqQ: "S = {Q}" by auto
    have "(P, S - {Q}) \<in> sumComposeSet" by fact
    with SeqQ have "(P, {}) \<in> sumComposeSet" by simp
    hence "P = \<zero>" apply - by(ind_cases "(P, {}) \<in> sumComposeSet", auto)
    with QinS SeqQ show ?case by simp
  next
    assume "(S - {Q}) \<noteq> {}"
    moreover have "(S - {Q}) \<noteq> {} \<Longrightarrow> \<exists>Q' \<in> (S - {Q}). depth P \<le> depth Q' \<and> (\<forall>R \<in> (S - {Q}). depth R \<le> depth Q')" by fact
    ultimately obtain Q' where Q'inS: "Q' \<in> S - {Q}" and PQ'depth: "depth P \<le> depth Q'" and All: "\<forall>R \<in> (S - {Q}). depth R \<le> depth Q'" by auto
    show ?case
    proof(case_tac "Q = Q'")
      assume "Q = Q'"
      with PQ'depth All QinS show ?case by auto
    next
      assume QineqQ': "Q \<noteq> Q'"
      show ?case
      proof(case_tac "depth Q \<le> depth Q'")
        assume "depth Q \<le> depth Q'"
        with QineqQ' PQ'depth All Q'inS show ?thesis by force
      next
        assume "\<not> depth Q \<le> depth Q'"
        with QineqQ' PQ'depth All Q'inS QinS show ?thesis apply auto
          apply(rule_tac x=Q in bexI)
          apply auto
          apply(case_tac "R=Q")
          apply auto
          apply(erule_tac x=R in ballE)
          by auto
      qed
    qed
  qed
qed

lemma depthSubst[simp]:
  fixes P :: pi
  and   a :: name
  and   b :: name

  shows "depth(P[a::=b]) = depth P"
by(nominal_induct P avoiding: a b rule: pi.strong_inducts, auto)

lemma depthTransition:
  fixes P  :: pi
  and   a  :: name
  and   b  :: name
  and   P' :: pi

  assumes Phnf: "hnf P"

  shows "P \<longmapsto>a[b] \<prec> P' \<Longrightarrow> depth P' < depth P"
  and   "P \<longmapsto>a<x> \<prec> P' \<Longrightarrow> depth P' < depth P"
  and   "P \<longmapsto>\<tau> \<prec> P' \<Longrightarrow> depth P' < depth P"
  and   "P \<longmapsto>a<\<nu>x> \<prec> P' \<Longrightarrow> depth P' < depth P"
proof -
  assume "P \<longmapsto>a[b] \<prec> P'"
  thus "depth P' < depth P" using assms
    by(nominal_induct rule: outputInduct, auto)
next
  assume Trans: "P \<longmapsto>a<x> \<prec> P'"
  have Goal: "\<And>P a x P'. \<lbrakk>P \<longmapsto>a<x> \<prec> P'; x \<sharp> P; hnf P\<rbrakk> \<Longrightarrow> depth P' < depth P"
  proof -
    fix P a x P'
    assume "P \<longmapsto>a<x> \<prec> P'" and "x \<sharp> P" and "hnf P"
    thus "depth P' < depth P"
      by(nominal_induct rule: inputInduct, auto)
  qed
  obtain y::name where yFreshP: "y \<sharp> P" and yFreshP': "y \<sharp> P'"
    by(rule_tac name_exists_fresh[of "(P, P')"], auto simp add: fresh_prod)
  from yFreshP' Trans have "P \<longmapsto>a<y> \<prec> [(x, y)] \<bullet> P'" by(simp add: alphaBoundResidual)
  hence "depth ([(x, y)] \<bullet> P') < depth P" using yFreshP Phnf by(rule Goal)
  thus "depth P' < depth P" by simp
next
  assume "P \<longmapsto>\<tau> \<prec> P'"
  thus "depth P' < depth P" using assms
    by(nominal_induct rule: tauInduct, auto simp add: uhnf_def)
next
  assume Trans: "P \<longmapsto>a<\<nu>x> \<prec> P'"
  have Goal: "\<And>P a x P'. \<lbrakk>P \<longmapsto>a<\<nu>x> \<prec> P'; x \<sharp> P; hnf P\<rbrakk> \<Longrightarrow> depth P' < depth P"
  proof -
    fix P a x P'
    assume "P \<longmapsto>a<\<nu>x> \<prec> P'" and "x \<sharp> P" and "hnf P"
    thus "depth P' < depth P"
      by(nominal_induct rule: boundOutputInduct,
         auto elim: outputCases simp add: residual.inject)
  qed
  obtain y::name where yFreshP: "y \<sharp> P" and yFreshP': "y \<sharp> P'"
    by(rule_tac name_exists_fresh[of "(P, P')"], auto simp add: fresh_prod)
  from yFreshP' Trans have "P \<longmapsto>a<\<nu>y> \<prec> [(x, y)] \<bullet> P'" by(simp add: alphaBoundResidual)
  hence "depth ([(x, y)] \<bullet> P') < depth P" using yFreshP Phnf by(rule Goal)
  thus "depth P' < depth P" by simp
qed

lemma maxExpandDepth:
  fixes P :: pi
  and   Q :: pi
  and   R :: pi
  
  assumes "R \<in> expandSet P Q"
  and     "hnf P"
  and     "hnf Q"

  shows "depth R \<le> depth(P \<parallel> Q)"
using assms
apply(auto simp add: expandSet_def summandTransition[THEN sym] dest: depthTransition)
apply(subgoal_tac "a \<noteq> x")
apply(simp add: summandTransition[THEN sym])
apply(force dest: depthTransition)
apply blast
apply(subgoal_tac "a \<noteq> x")
apply(simp add: summandTransition[THEN sym])
apply(force dest: depthTransition)
apply blast
apply(force dest: depthTransition)
apply(force dest: depthTransition)
apply(subgoal_tac "a \<noteq> y")
apply(simp add: summandTransition[THEN sym])
apply(force dest: depthTransition)
apply blast
apply(subgoal_tac "a \<noteq> y")
apply(simp add: summandTransition[THEN sym])
apply(force dest: depthTransition)
by blast

lemma expandDepth':
  fixes P :: pi
  and   Q :: pi

  assumes Phnf: "hnf P"
  and     Qhnf: "hnf Q"

  shows "\<exists>R. (R, expandSet P Q) \<in> sumComposeSet \<and> depth R \<le> depth(P \<parallel> Q)"
proof(case_tac "expandSet P Q = {}")
  assume "expandSet P Q = {}"
  with Phnf Qhnf show ?thesis by(auto intro: sumComposeSet.empty)
next
  assume "expandSet P Q \<noteq> {}"

  moreover from Phnf Qhnf finiteExpand obtain R where TSC: "(R, expandSet P Q) \<in> sumComposeSet"
    by(blast dest: expandComplete)
  ultimately obtain T where "T \<in> expandSet P Q"
                        and "depth R \<le> depth T"
    by(blast dest: expandDepth)
  with Phnf Qhnf have "depth R \<le> depth(P \<parallel> Q)"
    by(force dest: maxExpandDepth)
  with TSC show ?thesis by blast
qed

lemma validToHnf:
  fixes P :: pi

  assumes "valid P"

  shows "\<exists>Q. uhnf Q \<and> valid Q \<and> Q \<equiv>\<^sub>e P \<and> (depth Q) \<le> (depth P)"
proof -
  have MatchGoal: "\<And>a b P Q. \<lbrakk>uhnf Q; valid Q; Q \<equiv>\<^sub>e P; depth Q \<le> depth P\<rbrakk> \<Longrightarrow>
                               \<exists>Q. uhnf Q \<and> valid Q \<and> Q \<equiv>\<^sub>e [a\<frown>b]P \<and> depth Q \<le> depth ([a\<frown>b]P)"
  proof -
    fix a b P Q
    assume Qhnf: "uhnf Q" and validQ: "valid Q" and QeqP: "Q \<equiv>\<^sub>e P"
       and QPdepth: "depth Q \<le> depth P"
    show "\<exists>Q. uhnf Q \<and> valid Q \<and> Q \<equiv>\<^sub>e [a\<frown>b]P \<and> depth Q \<le> depth ([a\<frown>b]P)"
    proof(case_tac "a = b")
      assume "a = b"
      with QeqP have "Q \<equiv>\<^sub>e [a\<frown>b]P" by(blast intro: Sym Trans equiv.Match)
      with Qhnf validQ QPdepth show ?thesis by force
    next
      assume "a \<noteq> b"
      hence "\<zero> \<equiv>\<^sub>e [a\<frown>b]P" by(blast intro: Sym Match')
      moreover have "uhnf \<zero>" by(simp add: uhnf_def)
      ultimately show ?thesis by force
    qed
  qed
  
  from assms show ?thesis
  proof(nominal_induct P rule: pi.strong_inducts)
    case PiNil
    have "uhnf \<zero>" by(simp add: uhnf_def)
    moreover have "valid \<zero>" by simp
    moreover have "\<zero> \<equiv>\<^sub>e \<zero>" by(rule Refl)
    moreover have "(depth \<zero>) \<le> (depth \<zero>)" by simp
    ultimately show ?case by blast
  next
    case(Output a b P)
    have "uhnf (a{b}.P)" by(simp add: uhnf_def)
    moreover have "valid(a{b}.P)" by fact
    moreover have "a{b}.P \<equiv>\<^sub>e a{b}.P" by(rule Refl)
    moreover have "(depth (a{b}.P)) \<le> (depth (a{b}.P))" by simp
    ultimately show ?case by blast
  next
    case(Tau P)
    have "uhnf (\<tau>.(P))" by(simp add: uhnf_def)
    moreover have "valid (\<tau>.(P))" by fact
    moreover have "\<tau>.(P) \<equiv>\<^sub>e \<tau>.(P)" by(rule Refl)
    moreover have "(depth (\<tau>.(P))) \<le> (depth (\<tau>.(P)))" by simp
    ultimately show ?case by blast
  next
    case(Input a x P)
    have "uhnf (a<x>.P)" by(simp add: uhnf_def)
    moreover have "valid (a<x>.P)" by fact
    moreover have "a<x>.P \<equiv>\<^sub>e a<x>.P" by(rule Refl)
    moreover have "(depth (a<x>.P)) \<le> (depth (a<x>.P))" by simp
    ultimately show ?case by blast
  next
    case(Match a b P)
    have "valid ([a\<frown>b]P)" by fact
    hence "valid P" by simp
    moreover have "valid P \<Longrightarrow> \<exists>Q. uhnf Q \<and> valid Q \<and> Q \<equiv>\<^sub>e P \<and> depth Q \<le> depth P" by fact
    ultimately obtain Q where Qhnf: "uhnf Q" and validQ: "valid Q" and QeqP: "Q \<equiv>\<^sub>e P" 
                          and QPdepth: "depth Q \<le> depth P" by blast
    thus ?case by(rule MatchGoal)
  next
    case(Mismatch a b P)
    have "valid ([a\<noteq>b]P)" by fact
    hence "valid P" by simp
    moreover have "valid P \<Longrightarrow> \<exists>Q. uhnf Q \<and> valid Q \<and> Q \<equiv>\<^sub>e P \<and> depth Q \<le> depth P" by fact
    ultimately obtain Q where Qhnf: "uhnf Q" and validQ: "valid Q" and QeqP: "Q \<equiv>\<^sub>e P" 
                          and QPdepth: "depth Q \<le> depth P" by blast
    show ?case
    proof(case_tac "a = b")
      assume "a = b"
      hence "\<zero> \<equiv>\<^sub>e [a\<noteq>b]P" by(blast intro: Sym Mismatch')
      moreover have "uhnf \<zero>" by(simp add: uhnf_def)
      ultimately show ?case by force
    next
      assume "a \<noteq> b"
      with QeqP have "Q \<equiv>\<^sub>e [a\<noteq>b]P" by(blast intro: Sym Trans equiv.Mismatch)
      with Qhnf validQ QPdepth show ?case by force
    qed
  next
    case(Sum P Q)
    have "valid(P \<oplus> Q)" by fact
    hence validP: "valid P" and validQ: "valid Q" by simp+
    
    have "\<exists>P'. uhnf P' \<and> valid P' \<and> P' \<equiv>\<^sub>e P \<and> (depth P') \<le> (depth P)"
    proof -
      have "valid P \<Longrightarrow> \<exists>P'. uhnf P' \<and> valid P' \<and> P' \<equiv>\<^sub>e P \<and> (depth P') \<le> (depth P)" by fact
      with validP show ?thesis by simp
    qed
    then obtain P' where P'hnf: "uhnf P'" and P'eqP: "P' \<equiv>\<^sub>e P" and validP': "valid P'"
                     and P'depth: "(depth P') \<le> (depth P)" by blast

    have "\<exists>Q'. uhnf Q' \<and> valid Q' \<and> Q' \<equiv>\<^sub>e Q \<and> (depth Q') \<le> (depth Q)"
    proof -
      have "valid Q \<Longrightarrow> \<exists>Q'. uhnf Q' \<and> valid Q' \<and> Q' \<equiv>\<^sub>e Q \<and> (depth Q') \<le> (depth Q)" by fact
      with validQ show ?thesis by simp
    qed
    
    then obtain Q' where Q'hnf: "uhnf Q'" and Q'eqQ: "Q' \<equiv>\<^sub>e Q" and validQ': "valid Q'"
                     and Q'depth: "(depth Q') \<le> (depth Q)" by blast    
      
    from P'hnf Q'hnf validP' validQ' obtain R where Rhnf: "uhnf R" and validR: "valid R"
                                              and P'Q'eqR: "P' \<oplus> Q' \<equiv>\<^sub>e R"
                                              and Rdepth: "depth R \<le> depth(P' \<oplus> Q')"
      apply(drule_tac uhnfSum) apply assumption+ by blast
    
    from validP' validQ' have "valid(P' \<oplus> Q')" by simp
    from P'eqP Q'eqQ P'Q'eqR have "P \<oplus> Q \<equiv>\<^sub>e R" by(blast intro: Sym SumPres' Trans)
    moreover from Rdepth P'depth Q'depth have "depth R \<le> depth(P \<oplus> Q)" by auto
    ultimately show ?case using validR Rhnf by(blast intro: Sym)
  next
    case(Par P Q)
    have "valid(P \<parallel> Q)" by fact
    
    hence validP: "valid P" and validQ: "valid Q" by simp+
    have "\<exists>P'. uhnf P' \<and> valid P' \<and> P' \<equiv>\<^sub>e P \<and> (depth P') \<le> (depth P)"
    proof -
      have "valid P \<Longrightarrow> \<exists>P'. uhnf P' \<and> valid P' \<and> P' \<equiv>\<^sub>e P \<and> (depth P') \<le> (depth P)" by fact
      with validP show ?thesis by simp
    qed
    then obtain P' where P'hnf: "uhnf P'" and P'eqP: "P' \<equiv>\<^sub>e P" and validP': "valid P'"
                     and P'depth: "(depth P') \<le> (depth P)" by blast

    have "\<exists>Q'. uhnf Q' \<and> valid Q' \<and> Q' \<equiv>\<^sub>e Q \<and> (depth Q') \<le> (depth Q)"
    proof -
      have "valid Q \<Longrightarrow> \<exists>Q'. uhnf Q' \<and> valid Q' \<and> Q' \<equiv>\<^sub>e Q \<and> (depth Q') \<le> (depth Q)" by fact
      with validQ show ?thesis by simp
    qed
    
    then obtain Q' where Q'hnf: "uhnf Q'" and Q'eqQ: "Q' \<equiv>\<^sub>e Q" and validQ': "valid Q'"
                     and Q'depth: "(depth Q') \<le> (depth Q)" by blast

    from P'hnf Q'hnf obtain R where Exp: "(R, expandSet P' Q') \<in> sumComposeSet" and Rdepth: "depth R \<le> depth(P' \<parallel> Q')"
      by(force dest: expandDepth' simp add: uhnf_def)
    
    from Exp P'hnf Q'hnf have P'Q'eqR: "P' \<parallel> Q' \<equiv>\<^sub>e R" by(force intro: Expand simp add: uhnf_def)
    from P'hnf Q'hnf validP' validQ' have "\<forall>P \<in> (expandSet P' Q'). uhnf P \<and> valid P" by(blast dest: validExpand)
    with Exp obtain R' where R'hnf: "uhnf R'" and validR': "valid R'"
                                              and ReqR': "R \<equiv>\<^sub>e R'"
                                              and R'depth: "depth R' \<le> depth R"
      by(blast dest: expandHnf)
    from P'eqP Q'eqQ P'Q'eqR ReqR' have "P \<parallel> Q \<equiv>\<^sub>e R'" by(blast intro: Sym ParPres Trans)
    moreover from Rdepth P'depth Q'depth R'depth have "depth R' \<le> depth(P \<parallel> Q)" by auto
    ultimately show ?case using validR' R'hnf by(blast dest: Sym)
  next
    case(Res x P)
    have "valid (<\<nu>x>P)" by fact
    hence validP: "valid P" by simp
    moreover have "valid P \<Longrightarrow> \<exists>Q. uhnf Q \<and> valid Q \<and> Q \<equiv>\<^sub>e P \<and> depth Q \<le> depth P" by fact
    ultimately obtain Q where Qhnf: "uhnf Q" and validQ: "valid Q" and QeqP: "Q \<equiv>\<^sub>e P"
                          and QPDepth: "depth Q \<le> depth P" by blast
    
    from validP show ?case
    proof(nominal_induct P avoiding: x rule: pi.strong_inducts)
      case PiNil
      have "uhnf \<zero>" by(simp add: uhnf_def)
      moreover have "valid \<zero>" by simp
      moreover have "\<zero> \<equiv>\<^sub>e <\<nu>x>\<zero>"
      proof -
        have "x \<sharp> \<zero>" by simp
        thus ?thesis by(blast intro: Sym ResFresh)
      qed
      moreover have "depth \<zero> \<le> depth (<\<nu>x>\<zero>)" by simp
      ultimately show ?case by blast
    next
      case(Output a b P)
      have "valid(a{b}.P)" by fact
      hence validP: "valid P" by simp
      show ?case
      proof(case_tac "x=a")
        assume "x = a"
        moreover have "uhnf \<zero>" by(simp add: uhnf_def)
        moreover have "valid \<zero>" by simp
        moreover have "\<zero> \<equiv>\<^sub>e <\<nu>x>x{b}.P" by(blast intro: ResOutput' Sym)
        moreover have "depth \<zero> \<le> depth(<\<nu>x>x{b}.P)" by simp
        ultimately show ?case by blast
      next
        assume xineqa: "x \<noteq> a"
        show ?case
        proof(case_tac "x=b")
          assume "x=b"
          moreover from xineqa have "uhnf(<\<nu>x>a{x}.P)" by(force simp add: uhnf_def)
          moreover from validP have "valid(<\<nu>x>a{x}.P)" by simp
          moreover have "<\<nu>x>a{x}.P \<equiv>\<^sub>e <\<nu>x>a{x}.P" by(rule Refl)
          moreover have "depth(<\<nu>x>a{x}.P) \<le> depth(<\<nu>x>a{x}.P)" by simp
          ultimately show ?case by blast
        next
          assume xineqb: "x \<noteq> b"
          have "uhnf(a{b}.(<\<nu>x>P))" by(simp add: uhnf_def)
          moreover from validP have "valid(a{b}.(<\<nu>x>P))" by simp
          moreover from xineqa xineqb have "a{b}.(<\<nu>x>P) \<equiv>\<^sub>e <\<nu>x>a{b}.P" by(blast intro: ResOutput Sym)
          moreover have "depth(a{b}.(<\<nu>x>P)) \<le> depth(<\<nu>x>a{b}.P)" by simp
          ultimately show ?case by blast
        qed
      qed
    next
      case(Tau P)
      have "valid(\<tau>.(P))" by fact
      hence validP: "valid P" by simp
      
      have "uhnf(\<tau>.(<\<nu>x>P))" by(simp add: uhnf_def)
      moreover from validP have "valid(\<tau>.(<\<nu>x>P))" by simp
      moreover have "\<tau>.(<\<nu>x>P) \<equiv>\<^sub>e <\<nu>x>\<tau>.(P)" by(blast intro: ResTau Sym)
      moreover have "depth(\<tau>.(<\<nu>x>P)) \<le> depth(<\<nu>x>\<tau>.(P))" by simp
      ultimately show ?case by blast
    next
      case(Input a y P)
      have "valid(a<y>.P)" by fact
      hence validP: "valid P" by simp
      have "y \<sharp> x" by fact hence yineqx: "y \<noteq> x" by simp
      show ?case
      proof(case_tac "x=a")
        assume "x = a"
        moreover have "uhnf \<zero>" by(simp add: uhnf_def)
        moreover have "valid \<zero>" by simp
        moreover have "\<zero> \<equiv>\<^sub>e <\<nu>x>x<y>.P" by(blast intro: ResInput' Sym)
        moreover have "depth \<zero> \<le> depth(<\<nu>x>x<y>.P)" by simp
        ultimately show ?case by blast
      next
        assume xineqa: "x \<noteq> a"
        have "uhnf(a<y>.(<\<nu>x>P))" by(simp add: uhnf_def)
        moreover from validP have "valid(a<y>.(<\<nu>x>P))" by simp
        moreover from xineqa yineqx have "a<y>.(<\<nu>x>P) \<equiv>\<^sub>e <\<nu>x>a<y>.P" by(blast intro: ResInput Sym)
        moreover have "depth(a<y>.(<\<nu>x>P)) \<le> depth(<\<nu>x>a<y>.P)" by simp
        ultimately show ?case by blast
      qed
    next
      case(Match a b P x)
      have "valid([a\<frown>b]P)" by fact hence "valid P" by simp
      moreover have "\<And>x. valid P \<Longrightarrow> \<exists>Q. uhnf Q \<and> valid Q \<and> Q \<equiv>\<^sub>e <\<nu>x>P \<and> 
                                           depth Q \<le> depth(<\<nu>x>P)"
        by fact
      ultimately obtain Q where Qhnf: "uhnf Q" and validQ: "valid Q"
                            and QeqP: "Q \<equiv>\<^sub>e (<\<nu>x>P)" 
                            and QPdepth: "depth Q \<le> depth(<\<nu>x>P)"
        by blast
      show ?case
      proof(case_tac "a = b")
        assume "a=b"
        moreover have "Q \<equiv>\<^sub>e <\<nu>x>[a\<frown>a]P"
        proof -
          have "P \<equiv>\<^sub>e [a\<frown>a]P" by(blast intro: equiv.Match Sym)
          hence "<\<nu>x>P \<equiv>\<^sub>e <\<nu>x>[a\<frown>a]P" by(rule ResPres)
          with QeqP show ?thesis by(blast intro: Trans)
        qed
        moreover from QPdepth have "depth Q \<le> depth(<\<nu>x>[a\<frown>a]P)" by simp
        ultimately show ?case using Qhnf validQ by blast
      next
        assume aineqb: "a\<noteq>b"
        have "uhnf \<zero>" by(simp add: uhnf_def)
        moreover have "valid \<zero>" by simp
        moreover have "\<zero> \<equiv>\<^sub>e <\<nu>x>[a\<frown>b]P"
        proof -
          from aineqb have "\<zero> \<equiv>\<^sub>e [a\<frown>b]P" by(blast intro: Match' Sym)
          hence "<\<nu>x>\<zero> \<equiv>\<^sub>e <\<nu>x>[a\<frown>b]P" by(rule ResPres)
          thus ?thesis by(blast intro: ResNil Trans Sym)
        qed
        moreover have "depth \<zero> \<le> depth(<\<nu>x>[a\<frown>b]P)" by simp
        ultimately show ?case by blast
      qed
    next
      case(Mismatch a b P x)
      have "valid([a\<noteq>b]P)" by fact hence "valid P" by simp
      moreover have "\<And>x. valid P \<Longrightarrow> \<exists>Q. uhnf Q \<and> valid Q \<and> Q \<equiv>\<^sub>e <\<nu>x>P \<and> 
                                           depth Q \<le> depth(<\<nu>x>P)"
        by fact
      ultimately obtain Q where Qhnf: "uhnf Q" and validQ: "valid Q"
                            and QeqP: "Q \<equiv>\<^sub>e (<\<nu>x>P)" 
                            and QPdepth: "depth Q \<le> depth(<\<nu>x>P)"
        by blast
      show ?case
      proof(case_tac "a = b")
        assume "a=b"
        moreover have "uhnf \<zero>" by(simp add: uhnf_def)
        moreover have "valid \<zero>" by simp
        moreover have "\<zero> \<equiv>\<^sub>e <\<nu>x>[a\<noteq>a]P"
        proof -
          have "\<zero> \<equiv>\<^sub>e [a\<noteq>a]P" by(blast intro: Mismatch' Sym)
          hence "<\<nu>x>\<zero> \<equiv>\<^sub>e <\<nu>x>[a\<noteq>a]P" by(rule ResPres)
          thus ?thesis by(blast intro: ResNil Trans Sym)
        qed
        moreover have "depth \<zero> \<le> depth(<\<nu>x>[a\<noteq>a]P)" by simp
        ultimately show ?case by blast
      next
        assume aineqb: "a\<noteq>b"
        have "Q \<equiv>\<^sub>e <\<nu>x>[a\<noteq>b]P"
        proof -
          from aineqb have "P \<equiv>\<^sub>e [a\<noteq>b]P" by(blast intro: equiv.Mismatch Sym)
          hence "<\<nu>x>P \<equiv>\<^sub>e <\<nu>x>[a\<noteq>b]P" by(rule ResPres)
          with QeqP show ?thesis by(blast intro: Trans)
        qed
        moreover from QPdepth have "depth Q \<le> depth(<\<nu>x>[a\<noteq>b]P)" by simp
        ultimately show ?case using Qhnf validQ by blast
      qed
    next
      case(Sum P Q x)
      have "valid(P \<oplus> Q)" by fact
      hence validP: "valid P" and validQ: "valid Q" by simp+

      have "\<exists>P'. uhnf P' \<and> valid P' \<and> P' \<equiv>\<^sub>e <\<nu>x>P \<and> (depth P') \<le> (depth(<\<nu>x>P))"
      proof -
        have "valid P \<Longrightarrow> \<exists>P'. uhnf P' \<and> valid P' \<and> P' \<equiv>\<^sub>e <\<nu>x>P \<and> (depth P') \<le> (depth (<\<nu>x>P))" by fact
        with validP show ?thesis by simp
      qed
      then obtain P' where P'hnf: "uhnf P'" and P'eqP: "P' \<equiv>\<^sub>e <\<nu>x>P" and validP': "valid P'"
                       and P'depth: "(depth P') \<le> (depth(<\<nu>x>P))" by blast

      have "\<exists>Q'. uhnf Q' \<and> valid Q' \<and> Q' \<equiv>\<^sub>e <\<nu>x>Q \<and> (depth Q') \<le> (depth(<\<nu>x>Q))"
      proof -
        have "valid Q \<Longrightarrow> \<exists>Q'. uhnf Q' \<and> valid Q' \<and> Q' \<equiv>\<^sub>e <\<nu>x>Q \<and> (depth Q') \<le> (depth(<\<nu>x>Q))" by fact
        with validQ show ?thesis by simp
      qed

      then obtain Q' where Q'hnf: "uhnf Q'" and Q'eqQ: "Q' \<equiv>\<^sub>e <\<nu>x>Q" and validQ': "valid Q'"
                       and Q'depth: "(depth Q') \<le> (depth(<\<nu>x>Q))" by blast    
      
      from P'hnf Q'hnf validP' validQ' obtain R where Rhnf: "uhnf R" and validR: "valid R"
                                                and P'Q'eqR: "P' \<oplus> Q' \<equiv>\<^sub>e R"
                                                and Rdepth: "depth R \<le> depth(P' \<oplus> Q')"
        apply(drule_tac uhnfSum) apply assumption+ by blast
      
      from P'eqP Q'eqQ P'Q'eqR have "<\<nu>x>(P \<oplus> Q) \<equiv>\<^sub>e R" by(blast intro: Sym SumPres' SumRes Trans)
      moreover from Rdepth P'depth Q'depth have "depth R \<le> depth(<\<nu>x>(P \<oplus> Q))" by auto
      ultimately show ?case using validR Rhnf by(blast intro: Sym)
    next
      case(Par P Q x)
      have "valid(P \<parallel> Q)" by fact
      
      hence validP: "valid P" and validQ: "valid Q" by simp+
      have "\<exists>P'. uhnf P' \<and> valid P' \<and> P' \<equiv>\<^sub>e P \<and> (depth P') \<le> (depth P)"
      proof -
        obtain x::name where xFreshP: "x \<sharp> P" by(rule name_exists_fresh)
        moreover have "\<And>x. valid P \<Longrightarrow> \<exists>P'. uhnf P' \<and> valid P' \<and> P' \<equiv>\<^sub>e (<\<nu>x>P) \<and> (depth P') \<le> (depth(<\<nu>x>P))" by fact
        with validP obtain P' where "uhnf P'" and "valid P'" and P'eqP: "P' \<equiv>\<^sub>e (<\<nu>x>P)" and P'depth: "(depth P') \<le> (depth(<\<nu>x>P))" by blast
        moreover from xFreshP P'eqP have "P' \<equiv>\<^sub>e P" by(blast intro: Trans ResFresh)
        moreover with P'depth have "depth P' \<le> depth P" by simp
        ultimately show ?thesis by blast
      qed

      then obtain P' where P'hnf: "uhnf P'" and P'eqP: "P' \<equiv>\<^sub>e P" and validP': "valid P'"
                       and P'depth: "(depth P') \<le> (depth P)" by blast

      have "\<exists>Q'. uhnf Q' \<and> valid Q' \<and> Q' \<equiv>\<^sub>e Q \<and> (depth Q') \<le> (depth Q)"
      proof -
        obtain x::name where xFreshQ: "x \<sharp> Q" by(rule name_exists_fresh)
        moreover have "\<And>x. valid Q \<Longrightarrow> \<exists>Q'. uhnf Q' \<and> valid Q' \<and> Q' \<equiv>\<^sub>e (<\<nu>x>Q) \<and> (depth Q') \<le> (depth(<\<nu>x>Q))" by fact
        with validQ obtain Q' where "uhnf Q'" and "valid Q'" and Q'eqQ: "Q' \<equiv>\<^sub>e (<\<nu>x>Q)" and Q'depth: "(depth Q') \<le> (depth(<\<nu>x>Q))" by blast
        moreover from xFreshQ Q'eqQ have "Q' \<equiv>\<^sub>e Q" by(blast intro: Trans ResFresh)
        moreover with Q'depth have "depth Q' \<le> depth Q" by simp
        ultimately show ?thesis by blast
      qed
      
      then obtain Q' where Q'hnf: "uhnf Q'" and Q'eqQ: "Q' \<equiv>\<^sub>e Q" and validQ': "valid Q'"
                       and Q'depth: "(depth Q') \<le> (depth Q)" by blast
      
      from P'hnf Q'hnf obtain R where Exp: "(R, expandSet P' Q') \<in> sumComposeSet" and Rdepth: "depth R \<le> depth(P' \<parallel> Q')"
        by(force dest: expandDepth' simp add: uhnf_def)
    
      from Exp P'hnf Q'hnf have P'Q'eqR: "P' \<parallel> Q' \<equiv>\<^sub>e R" by(force intro: Expand simp add: uhnf_def)
      from P'hnf Q'hnf validP' validQ' have "\<forall>P \<in> (expandSet P' Q'). uhnf P \<and> valid P" by(blast dest: validExpand)
      with Exp obtain R' where R'hnf: "uhnf R'" and validR': "valid R'"
                                                and ReqR': "R \<equiv>\<^sub>e R'"
                                                and R'depth: "depth R' \<le> depth R"
        by(blast dest: expandHnf)
      
      from P'eqP Q'eqQ P'Q'eqR ReqR' have "P \<parallel> Q \<equiv>\<^sub>e R'" by(blast intro: Sym ParPres Trans)
      hence ResTrans: "<\<nu>x>(P \<parallel> Q) \<equiv>\<^sub>e <\<nu>x>R'" by(rule ResPres)
      from validR' R'hnf obtain R'' where R''hnf: "uhnf R''" and validR'': "valid R''" and R'eqR'': "<\<nu>x>R' \<equiv>\<^sub>e R''" and R''depth: "depth R'' \<le> depth(<\<nu>x>R')"
        by(force dest: uhnfRes)
      from ResTrans R'eqR'' have "<\<nu>x>(P \<parallel> Q) \<equiv>\<^sub>e R''" by(rule Trans)
      moreover from Rdepth P'depth Q'depth R'depth R''depth have "depth R'' \<le> depth(<\<nu>x>(P \<parallel> Q))" by auto
      ultimately show ?case using validR'' R''hnf by(blast dest: Sym)
    next
      case(Res y P x)
      have "valid(<\<nu>y>P)" by fact hence "valid P" by simp
      moreover have "\<And>x. valid P \<Longrightarrow> \<exists>Q. uhnf Q \<and> valid Q \<and> Q \<equiv>\<^sub>e <\<nu>x>P \<and> depth Q \<le> depth(<\<nu>x>P)"
        by fact
      ultimately obtain Q where Qhnf: "uhnf Q" and validQ: "valid Q" and QeqP: "Q \<equiv>\<^sub>e <\<nu>y>P"
                            and QPdepth: "depth Q \<le> depth(<\<nu>y>P)" by blast

      from Qhnf validQ obtain Q' where Q'hnf: "uhnf Q'" and validQ': "valid Q'" and QeqQ': "<\<nu>x>Q \<equiv>\<^sub>e Q'"
                                   and Q'Qdepth: "depth Q' \<le> depth(<\<nu>x>Q)"
        by(force dest: uhnfRes)

      from QeqP have "<\<nu>x>Q \<equiv>\<^sub>e <\<nu>x><\<nu>y>P" by(rule ResPres)
      with QeqQ' have "Q' \<equiv>\<^sub>e <\<nu>x><\<nu>y>P" by(blast intro: Trans Sym)
      moreover from Q'Qdepth QPdepth have "depth Q' \<le> depth(<\<nu>x><\<nu>y>P)" by simp
      ultimately show ?case using Q'hnf validQ' by blast
    next
      case(Bang P x)
      have "valid(!P)" by fact
      hence False by simp
      thus ?case by simp
    qed
  next
    case(Bang P)
    have "valid(!P)" by fact
    hence False by simp
    thus ?case by simp
  qed
qed

lemma depthZero:
  fixes P :: pi
  
  assumes "depth P = 0"
  and     "uhnf P"

  shows "P = \<zero>"
using assms
apply(nominal_induct P rule: pi.strong_inducts, auto simp add: uhnf_def max_def if_split) 
apply(case_tac "depth pi1 \<le> depth pi2")
by auto

lemma completeAux:
  fixes n :: nat
  and   P :: pi
  and   Q :: pi

  assumes "depth P + depth Q \<le> n"
  and     "valid P"
  and     "valid Q"
  and     "uhnf P"
  and     "uhnf Q"
  and     "P \<sim> Q"

  shows "P \<equiv>\<^sub>e Q"
using assms
proof(induct n arbitrary: P Q rule: nat.induct)
  case(zero P Q)
  have "depth P + depth Q \<le> 0" by fact
  hence Pdepth: "depth P = 0" and Qdepth: "depth Q = 0" by auto
  moreover have  "uhnf P" and "uhnf Q" by fact+
  ultimately have "P = \<zero>" and "Q = \<zero>" by(blast intro: depthZero)+
  thus ?case by(blast intro: Refl)
next
  case(Suc n P Q)
  have validP: "valid P" and validQ: "valid Q" by fact+
  have Phnf: "uhnf P" and Qhnf: "uhnf Q" by fact+
  have PBisimQ: "P \<sim> Q" by fact
  have IH: "\<And>P Q. \<lbrakk>depth P + depth Q \<le> n; valid P; valid Q; uhnf P; uhnf Q; P \<sim> Q\<rbrakk> \<Longrightarrow> P \<equiv>\<^sub>e Q"
    by fact
  have PQdepth: "depth P + depth Q \<le> Suc n" by fact
  
  have Goal: "\<And>P Q Q'. \<lbrakk>depth P + depth Q \<le> Suc n; valid P; valid Q; uhnf P; uhnf Q; 
                        P \<leadsto>[bisim] Q; Q' \<in> summands Q\<rbrakk> \<Longrightarrow> \<exists>P' \<in> summands P. Q' \<equiv>\<^sub>e P'"
  proof -
    fix P Q Q'
    assume PQdepth: "depth P + depth Q \<le> Suc n"
    assume validP: "valid P" and validQ: "valid Q"
    assume Phnf: "uhnf P" and Qhnf: "uhnf Q"
    assume PSimQ: "P \<leadsto>[bisim] Q"
    assume Q'inQ: "Q' \<in> summands Q"
    
    thus "\<exists>P' \<in> summands P. Q' \<equiv>\<^sub>e P'" using PSimQ Phnf validP PQdepth
    proof(nominal_induct Q' avoiding: P rule: pi.strong_inducts)
      case PiNil
      have "\<zero> \<in> summands Q" by fact
      hence False by(nominal_induct Q rule: pi.strong_inducts, auto simp add: if_split)
      thus ?case by simp
    next
      case(Output a b Q' P)
      have validP: "valid P" and Phnf: "uhnf P" and PSimQ: "P \<leadsto>[bisim] Q" by fact+
      have PQdepth: "depth P + depth Q \<le> Suc n" by fact
      have "a{b}.Q' \<in> summands Q" by fact
      with Qhnf have QTrans: "Q \<longmapsto>a[b] \<prec> Q'" by(simp add: summandTransition uhnf_def)
      with PSimQ obtain P' where PTrans: "P \<longmapsto>a[b] \<prec> P'" and P'BisimQ': "P' \<sim> Q'"
        by(blast dest: simE)
      
      from Phnf PTrans have "a{b}.P' \<in> summands P" by(simp add: summandTransition uhnf_def)
      moreover have "P' \<equiv>\<^sub>e Q'"
      proof -
        from validP PTrans have validP': "valid P'" by(blast intro: validTransition)
        from validQ QTrans have validQ': "valid Q'" by(blast intro: validTransition)
        
        from validP' obtain P'' where P''hnf: "uhnf P''" and validP'': "valid P''"
                                  and P''eqP': "P'' \<equiv>\<^sub>e P'" and P''depth: "depth P'' \<le> depth P'"
          by(blast dest: validToHnf)
        
        from validQ' obtain Q'' where Q''hnf: "uhnf Q''" and validQ'': "valid Q''"
                                  and Q''eqQ': "Q'' \<equiv>\<^sub>e Q'" and Q''depth: "depth Q'' \<le> depth Q'"
          by(blast dest: validToHnf)
        
        have "depth P'' + depth Q'' \<le> n"
        proof -
          from Phnf PTrans have "depth P' < depth P" 
            by(force intro: depthTransition simp add: uhnf_def)
          moreover from Qhnf QTrans have "depth Q' < depth Q"
            by(force intro: depthTransition simp add: uhnf_def)
          ultimately show ?thesis using PQdepth P''depth Q''depth by simp
        qed
        
        moreover have "P'' \<sim> Q''"
        proof -
          from P''eqP' have "P'' \<sim> P'" by(rule sound)
          moreover from Q''eqQ' have "Q'' \<sim> Q'" by(rule sound)
          ultimately show ?thesis using P'BisimQ' by(blast dest: transitive symmetric)
        qed
        ultimately have "P'' \<equiv>\<^sub>e Q''" using validP'' validQ'' P''hnf Q''hnf by(rule_tac IH)
        with P''eqP' Q''eqQ' show ?thesis by(blast intro: Sym Trans)
      qed
      ultimately show ?case by(blast intro: Sym equiv.OutputPres)
    next
      case(Tau Q' P)
      have validP: "valid P" and Phnf: "uhnf P" and PSimQ: "P \<leadsto>[bisim] Q" by fact+
      have PQdepth: "depth P + depth Q \<le> Suc n" by fact
      have "\<tau>.(Q') \<in> summands Q" by fact
      with Qhnf have QTrans: "Q \<longmapsto>\<tau> \<prec> Q'" by(simp add: summandTransition uhnf_def)
      with PSimQ obtain P' where PTrans: "P \<longmapsto>\<tau> \<prec> P'" and P'BisimQ': "P' \<sim> Q'"
        by(blast dest: simE)
      
      from Phnf PTrans have "\<tau>.(P') \<in> summands P" by(simp add: summandTransition uhnf_def)
      moreover have "P' \<equiv>\<^sub>e Q'"
      proof -
        from validP PTrans have validP': "valid P'" by(blast intro: validTransition)
        from validQ QTrans have validQ': "valid Q'" by(blast intro: validTransition)
        
        from validP' obtain P'' where P''hnf: "uhnf P''" and validP'': "valid P''"
                                  and P''eqP': "P'' \<equiv>\<^sub>e P'" and P''depth: "depth P'' \<le> depth P'"
          by(blast dest: validToHnf)
          
        from validQ' obtain Q'' where Q''hnf: "uhnf Q''" and validQ'': "valid Q''"
                                  and Q''eqQ': "Q'' \<equiv>\<^sub>e Q'" and Q''depth: "depth Q'' \<le> depth Q'"
          by(blast dest: validToHnf)
        
        have "depth P'' + depth Q'' \<le> n"
        proof -
          from Phnf PTrans have "depth P' < depth P"
            by(force intro: depthTransition simp add: uhnf_def)
          moreover from Qhnf QTrans have "depth Q' < depth Q" 
            by(force intro: depthTransition simp add: uhnf_def)
          ultimately show ?thesis using PQdepth P''depth Q''depth by simp
        qed
        
        moreover have "P'' \<sim> Q''"
        proof -
          from P''eqP' have "P'' \<sim> P'" by(rule sound)
          moreover from Q''eqQ' have "Q'' \<sim> Q'" by(rule sound)
          ultimately show ?thesis using P'BisimQ' by(blast dest: transitive symmetric)
        qed
        ultimately have "P'' \<equiv>\<^sub>e Q''" using validP'' validQ'' P''hnf Q''hnf by(rule_tac IH)
        with P''eqP' Q''eqQ' show ?thesis by(blast intro: Sym Trans)
      qed
      ultimately show ?case by(blast intro: Sym equiv.TauPres)
    next
      case(Input a x Q' P)
      have validP: "valid P" and Phnf: "uhnf P" and PSimQ: "P \<leadsto>[bisim] Q" and xFreshP: "x \<sharp> P"  by fact+
      have PQdepth: "depth P + depth Q \<le> Suc n" by fact
      have "a<x>.Q' \<in> summands Q" by fact
      with Qhnf have QTrans: "Q \<longmapsto>a<x> \<prec> Q'" by(simp add: summandTransition uhnf_def)
      with PSimQ xFreshP obtain P' where PTrans: "P \<longmapsto>a<x> \<prec> P'"
                                     and P'derQ': "derivative P' Q' (InputS a) x bisim"
        by(blast dest: simE)

      from Phnf PTrans have "a<x>.P' \<in> summands P" by(simp add: summandTransition uhnf_def)
      moreover have "\<forall>y \<in> supp(P', Q', x). P'[x::=y] \<equiv>\<^sub>e Q'[x::=y]"
      proof(rule ballI)
        fix y::name
        assume ysupp: "y \<in> supp(P', Q', x)"
        have validP': "valid(P'[x::=y])"
        proof -
          from validP PTrans have validP': "valid P'" by(blast intro: validTransition)
          thus ?thesis by simp
        qed
        have validQ': "valid(Q'[x::=y])"
        proof -
          from validQ QTrans have validQ': "valid Q'" by(blast intro: validTransition)
          thus ?thesis by simp
        qed
        
        from validP' obtain P'' where P''hnf: "uhnf P''" and validP'': "valid P''"
                                  and P''eqP': "P'' \<equiv>\<^sub>e P'[x::=y]" and P''depth: "depth P'' \<le> depth(P'[x::=y])"
          by(blast dest: validToHnf)
        
        from validQ' obtain Q'' where Q''hnf: "uhnf Q''" and validQ'': "valid Q''"
                                  and Q''eqQ': "Q'' \<equiv>\<^sub>e Q'[x::=y]" and Q''depth: "depth Q'' \<le> depth(Q'[x::=y])"
          by(blast dest: validToHnf)
        
        have "depth P'' + depth Q'' \<le> n"
        proof -
          from Phnf PTrans have "depth P' < depth P"
            by(force intro: depthTransition simp add: uhnf_def)
          moreover from Qhnf QTrans have "depth Q' < depth Q" 
            by(force intro: depthTransition simp add: uhnf_def)
          ultimately show ?thesis using PQdepth P''depth Q''depth by simp 
        qed
          
        moreover have "P'' \<sim> Q''"
        proof -
          from P'derQ' have P'BisimQ': "P'[x::=y] \<sim> Q'[x::=y]" 
            by(auto simp add: derivative_def)
          from P''eqP' have "P'' \<sim> P'[x::=y]" by(rule sound)
          moreover from Q''eqQ' have "Q'' \<sim> Q'[x::=y]" by(rule sound)
          ultimately show ?thesis using P'BisimQ' by(blast dest: transitive symmetric)
        qed
        ultimately have "P'' \<equiv>\<^sub>e Q''" using validP'' validQ'' P''hnf Q''hnf by(rule_tac IH)
        with P''eqP' Q''eqQ' show "P'[x::=y] \<equiv>\<^sub>e Q'[x::=y]" by(blast intro: Sym Trans)
      qed
      
      ultimately show ?case 
        apply -
        apply(rule_tac x="a<x>.P'" in bexI)
        apply(rule equiv.InputPres)
        apply(rule ballI)
        apply(erule_tac x=y in ballE)
        apply(blast dest: Sym)
        by(auto simp add: supp_prod)
    next
      case(Match a b P' P)
      have "[a\<frown>b]P' \<in> summands Q" by fact
      hence False by(nominal_induct Q rule: pi.strong_inducts, auto simp add: if_split)
      thus ?case by simp
    next
      case(Mismatch a b P' P)
      have "[a\<noteq>b]P' \<in> summands Q" by fact
      hence False by(nominal_induct Q rule: pi.strong_inducts, auto simp add: if_split)
      thus ?case by simp
    next
      case(Sum P' Q' P)
      have "P' \<oplus> Q' \<in> summands Q" by fact
      hence False by(nominal_induct Q rule: pi.strong_inducts, auto simp add: if_split)
      thus ?case by simp
    next
      case(Par P' Q' P)
      have "P' \<parallel> Q' \<in> summands Q" by fact
      hence False by(nominal_induct Q rule: pi.strong_inducts, auto simp add: if_split)
      thus ?case by simp
    next
      case(Res x Q'' P)
      have xFreshP: "x \<sharp> P" by fact
      have validP: "valid P" and Phnf: "uhnf P" and PSimQ: "P \<leadsto>[bisim] Q" by fact+
      have PQdepth: "depth P + depth Q \<le> Suc n" by fact
      have Q''summQ: "<\<nu>x>Q'' \<in> summands Q" by fact
      hence "\<exists>a Q'. a \<noteq> x \<and> Q'' = a{x}.Q'"
        by(nominal_induct Q rule: pi.strong_inducts, auto simp add: if_split pi.inject name_abs_eq name_calc)  
      then obtain a Q' where aineqx: "a \<noteq> x" and Q'eqQ'': "Q'' = a{x}.Q'"
        by blast
      with Qhnf  Q''summQ have QTrans: "Q \<longmapsto>a<\<nu>x> \<prec> Q'" by(simp add: summandTransition uhnf_def)
      with PSimQ xFreshP obtain P' where PTrans: "P \<longmapsto>a<\<nu>x> \<prec> P'" and P'BisimQ': "P' \<sim> Q'"
        by(force dest: simE simp add: derivative_def)
        
      from Phnf PTrans aineqx have "(<\<nu>x>a{x}.P') \<in> summands P" by(simp add: summandTransition uhnf_def)
      moreover have "a{x}.P' \<equiv>\<^sub>e a{x}.Q'"
      proof -
        have "P' \<equiv>\<^sub>e Q'"
        proof -
          from validP PTrans have validP': "valid P'" by(blast intro: validTransition)
          from validQ QTrans have validQ': "valid Q'" by(blast intro: validTransition)
        
          from validP' obtain P'' where P''hnf: "uhnf P''" and validP'': "valid P''"
                                    and P''eqP': "P'' \<equiv>\<^sub>e P'" and P''depth: "depth P'' \<le> depth P'"
            by(blast dest: validToHnf)
          
          from validQ' obtain Q'' where Q''hnf: "uhnf Q''" and validQ'': "valid Q''"
                                    and Q''eqQ': "Q'' \<equiv>\<^sub>e Q'" and Q'''depth: "depth Q'' \<le> depth Q'"
            by(blast dest: validToHnf)
            
          have "depth P'' + depth Q'' \<le> n"
          proof -
            from Phnf PTrans have "depth P' < depth P"
              by(force intro: depthTransition simp add: uhnf_def)
            moreover from Qhnf QTrans have "depth Q' < depth Q" 
              by(force intro: depthTransition simp add: uhnf_def)
            ultimately show ?thesis using PQdepth P''depth Q'''depth by simp
          qed
            
          moreover have "P'' \<sim> Q''"
          proof -
            from P''eqP' have "P'' \<sim> P'" by(rule sound)
            moreover from Q''eqQ' have "Q'' \<sim> Q'" by(rule sound)
            ultimately show ?thesis using P'BisimQ' by(blast dest: transitive symmetric)
          qed
          ultimately have "P'' \<equiv>\<^sub>e Q''" using validP'' validQ'' P''hnf Q''hnf by(rule_tac IH)
          with P''eqP' Q''eqQ' show ?thesis by(blast intro: Sym Trans)
        qed
        thus ?thesis by(rule OutputPres)
      qed
      ultimately show ?case using Q'eqQ'' by(blast intro: Sym equiv.ResPres)
    next
      case(Bang P' P)
      have "!P' \<in> summands Q" by fact
      hence False by(nominal_induct Q rule: pi.strong_inducts, auto simp add: if_split) 
      thus ?case by simp
    qed
  qed

  from Phnf Qhnf PQdepth validP validQ PBisimQ show ?case
    apply(rule_tac summandEquiv, auto)
    apply(rule Goal)
    apply auto
    apply(blast dest: bisimE symmetric)
    by(blast intro: Goal dest: bisimE)
qed

lemma complete: 
  fixes P :: pi
  and   Q :: pi

  assumes validP: "valid P"
  and     validQ: "valid Q"
  and     PBisimQ: "P \<sim> Q"

  shows "P \<equiv>\<^sub>e Q"
proof -
  from validP obtain P' where validP': "valid P'" and P'hnf: "uhnf P'" and P'eqP: "P' \<equiv>\<^sub>e P"
    by(blast dest: validToHnf)
  from validQ obtain Q' where validQ': "valid Q'" and Q'hnf: "uhnf Q'" and Q'eqQ: "Q' \<equiv>\<^sub>e Q"
    by(blast dest: validToHnf)
  
  have "\<exists>n. depth P' + depth Q' \<le> n" by auto
  then obtain n where "depth P' + depth Q' \<le> n" by blast
  moreover have "P' \<sim> Q'"
  proof -
    from P'eqP have "P' \<sim> P" by(rule sound)
    moreover from Q'eqQ have "Q' \<sim> Q" by(rule sound)
    ultimately show ?thesis using PBisimQ by(blast intro: symmetric transitive)
  qed
  ultimately have "P' \<equiv>\<^sub>e Q'" using validP' validQ' P'hnf Q'hnf by(rule_tac completeAux)
  with P'eqP Q'eqQ show ?thesis by(blast intro: Sym Trans)
qed

end
