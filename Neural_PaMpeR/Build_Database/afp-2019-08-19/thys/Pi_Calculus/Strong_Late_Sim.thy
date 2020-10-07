(* 
   Title: The pi-calculus   
   Author/Maintainer: Jesper Bengtson (jebe.dk), 2012
*)
theory Strong_Late_Sim
  imports Late_Semantics1 Rel
begin

definition derivative :: "pi \<Rightarrow> pi \<Rightarrow> subject \<Rightarrow> name \<Rightarrow> (pi \<times> pi) set \<Rightarrow> bool" where
  "derivative P Q a x Rel \<equiv> case a of InputS b \<Rightarrow> (\<forall>u. (P[x::=u], Q[x::=u]) \<in> Rel)
                                    | BoundOutputS b \<Rightarrow> (P, Q) \<in> Rel"

definition simulation :: "pi \<Rightarrow> (pi \<times> pi) set \<Rightarrow> pi \<Rightarrow> bool" ("_ \<leadsto>[_] _" [80, 80, 80] 80) where
  "P \<leadsto>[Rel] Q \<equiv> (\<forall>a x Q'. Q \<longmapsto>a\<guillemotleft>x\<guillemotright> \<prec> Q' \<and> x \<sharp> P \<longrightarrow> (\<exists>P'. P \<longmapsto>a\<guillemotleft>x\<guillemotright> \<prec> P' \<and> derivative P' Q' a x Rel)) \<and>
                 (\<forall>\<alpha> Q'. Q \<longmapsto>\<alpha> \<prec> Q' \<longrightarrow> (\<exists>P'. P \<longmapsto>\<alpha> \<prec> P' \<and> (P', Q') \<in> Rel))"

lemma monotonic: 
  fixes A  :: "(pi \<times> pi) set"
  and   B  :: "(pi \<times> pi) set"
  and   P  :: pi
  and   P' :: pi

  assumes "P \<leadsto>[A] P'"
  and     "A \<subseteq> B"

  shows "P \<leadsto>[B] P'"
using assms
apply(auto simp add: simulation_def derivative_def)
by(case_tac a) fastforce+

lemma derivativeMonotonic:
  fixes A :: "(pi \<times> pi) set"
  and   B :: "(pi \<times> pi) set"
  and   P :: pi
  and   Q :: pi
  and   a :: subject
  and   x :: name

  assumes "derivative P Q a x A"
  and     "A \<subseteq> B"
  
  shows "derivative P Q a x B"
using assms
by(case_tac a, auto simp add: derivative_def)

lemma derivativeEqvtI:
  fixes P    :: pi
  and   Q    :: pi
  and   a    :: subject
  and   x    :: name
  and   Rel  :: "(pi \<times> pi) set"
  and   perm :: "name prm"

  assumes Der: "derivative P Q a x Rel"
  and     Eqvt: "eqvt Rel"
  
  shows "derivative (perm \<bullet> P) (perm \<bullet> Q) (perm \<bullet> a) (perm \<bullet> x) Rel"
using assms
apply(case_tac a, auto simp add: derivative_def)
apply(erule_tac x="rev perm \<bullet> u" in allE)
apply(drule_tac perm=perm in eqvtRelI)
apply(blast)
apply(force simp add: eqvt_subs name_per_rev)
by(force simp add: eqvt_def)

lemma derivativeEqvtI2:
  fixes P    :: pi
  and   Q    :: pi
  and   a    :: subject
  and   x    :: name
  and   Rel  :: "(pi \<times> pi) set"
  and   perm :: "name prm"

  assumes Der: "derivative P Q a x Rel"
  and     Eqvt: "eqvt Rel"
  
  shows "derivative (perm \<bullet> P) (perm \<bullet> Q) a (perm \<bullet> x) Rel"
using assms
apply(case_tac a, auto simp add: derivative_def)
apply(erule_tac x="rev perm \<bullet> u" in allE)
apply(drule_tac perm=perm in eqvtRelI)
apply(blast)
apply(force simp add: eqvt_subs name_per_rev)
by(force simp add: eqvt_def)

lemma freshUnit[simp]:
  fixes y :: name

  shows "y \<sharp> ()"
by(auto simp add: fresh_def supp_unit)

lemma simCasesCont[consumes 1, case_names Bound Free]:
  fixes P   :: pi
  and   Q   :: pi
  and   Rel :: "(pi \<times> pi) set"
  and   C   :: "'a::fs_name"

  assumes Eqvt:  "eqvt Rel"
  and     Bound: "\<And>a x Q'. \<lbrakk>Q \<longmapsto> a\<guillemotleft>x\<guillemotright> \<prec> Q'; x \<sharp> P; x \<sharp> Q; x \<sharp> a; x \<sharp> C\<rbrakk> \<Longrightarrow> \<exists>P'. P \<longmapsto> a\<guillemotleft>x\<guillemotright> \<prec> P' \<and> derivative P' Q' a x Rel"
  and     Free:  "\<And>\<alpha> Q'. Q \<longmapsto> \<alpha> \<prec> Q' \<Longrightarrow> \<exists>P'. P \<longmapsto> \<alpha> \<prec> P' \<and> (P', Q') \<in> Rel"

  shows "P \<leadsto>[Rel] Q"
using Free
proof(auto simp add: simulation_def)
  fix a x Q'
  assume "(x::name) \<sharp> P"
  assume Trans: "Q \<longmapsto> a\<guillemotleft>x\<guillemotright> \<prec> Q'"
  
  obtain y::name where "y \<sharp> P" and "y \<sharp> Q" and "y \<sharp> a" and "y \<sharp> C" and "y \<sharp> Q'" and "y \<noteq> x"
    by(generate_fresh "name") auto

  from Trans \<open>y \<sharp> Q'\<close> have "Q \<longmapsto> a\<guillemotleft>y\<guillemotright> \<prec> [(x, y)] \<bullet> Q'" by(simp add: alphaBoundResidual)
  hence "\<exists>P'. P \<longmapsto> a\<guillemotleft>y\<guillemotright> \<prec> P' \<and> derivative P' ([(x, y)] \<bullet> Q') a y Rel" 
    using \<open>y \<sharp> P\<close> \<open>y \<sharp> Q\<close> \<open>y \<sharp> a\<close> \<open>y \<sharp> C\<close>
    by(rule Bound)
  then obtain P' where PTrans: "P \<longmapsto> a\<guillemotleft>y\<guillemotright> \<prec> P'" and PDer: "derivative P' ([(x, y)] \<bullet> Q') a y Rel"
    by blast
  
  from PTrans \<open>x \<sharp> P\<close> \<open>y \<noteq> x\<close> have "x \<sharp> P'" by(force intro: freshBoundDerivative)
  with PTrans have "P \<longmapsto> a\<guillemotleft>x\<guillemotright> \<prec> [(x, y)] \<bullet> P'" by(simp add: alphaBoundResidual name_swap)
  moreover have "derivative ([(x, y)] \<bullet> P') Q' a x Rel"
  proof -
    from PDer Eqvt have "derivative ([(x, y)] \<bullet> P') ([(x, y)] \<bullet> [(x, y)] \<bullet> Q') a ([(x, y)] \<bullet> y) Rel"
      by(rule derivativeEqvtI2)
    with \<open>y \<noteq> x\<close> show ?thesis by(simp add: name_calc)
  qed
  ultimately show "\<exists>P'. P \<longmapsto>a\<guillemotleft>x\<guillemotright> \<prec> P' \<and> derivative P' Q' a x Rel" by blast
qed

lemma simCases[case_names Bound Free]:
  fixes P   :: pi
  and   Q   :: pi
  and   Rel :: "(pi \<times> pi) set"

  assumes Bound: "\<And>a y Q'. \<lbrakk>Q \<longmapsto> a\<guillemotleft>y\<guillemotright> \<prec> Q'; y \<sharp> P\<rbrakk> \<Longrightarrow> \<exists>P'. P \<longmapsto> a\<guillemotleft>y\<guillemotright> \<prec> P' \<and> derivative P' Q' a y Rel"
  and     Free:  "\<And>\<alpha> Q'. Q \<longmapsto> \<alpha> \<prec> Q' \<Longrightarrow> \<exists>P'. P \<longmapsto> \<alpha> \<prec> P' \<and> (P', Q') \<in> Rel"

  shows "P \<leadsto>[Rel] Q"
using assms
by(auto simp add: simulation_def)

lemma resSimCases[consumes 1, case_names BoundOutput BoundR FreeR]:
  fixes x   :: name
  and   P   :: pi
  and   Rel :: "(pi \<times> pi) set"
  and   Q   :: pi
  and   C   :: "'a::fs_name"

  assumes Eqvt:    "eqvt Rel"
  and     BoundO:  "\<And>Q' a. \<lbrakk>Q \<longmapsto>a[x] \<prec> Q'; a \<noteq> x\<rbrakk> \<Longrightarrow> \<exists>P'. P \<longmapsto>a<\<nu>x> \<prec> P' \<and> (P', Q') \<in> Rel"
  and     BR:      "\<And>Q' a y. \<lbrakk>Q \<longmapsto>a\<guillemotleft>y\<guillemotright> \<prec> Q'; x \<sharp> a; x \<noteq> y; y \<sharp> C\<rbrakk> \<Longrightarrow> \<exists>P'. P \<longmapsto>a\<guillemotleft>y\<guillemotright> \<prec> P' \<and> derivative P' (<\<nu>x>Q') a y Rel"
  and     BF:      "\<And>Q' \<alpha>. \<lbrakk>Q \<longmapsto>\<alpha> \<prec> Q'; x \<sharp> \<alpha>\<rbrakk> \<Longrightarrow> \<exists>P'. P \<longmapsto>\<alpha> \<prec> P' \<and> (P', <\<nu>x>Q') \<in> Rel"

  shows "P \<leadsto>[Rel] <\<nu>x>Q"
using Eqvt
proof(induct rule: simCasesCont[where C="(C, x, Q)"])
  case(Bound a y Q')
  have "y \<sharp> (C, x, Q)" by fact
  hence yFreshC: "y \<sharp> C" and yineqx: "y \<noteq> x" and "y \<sharp> Q"
    by(simp add: fresh_prod)+
  have "<\<nu>x>Q \<longmapsto>a\<guillemotleft>y\<guillemotright> \<prec> Q'" by fact
  thus ?case using yineqx \<open>y \<sharp> Q\<close>
  proof(induct rule: resCasesB)
    case(cOpen a' Q')
    have "Q \<longmapsto>a'[x] \<prec> Q'" and "a' \<noteq> x" by fact+
    then obtain P' where PTrans: "P \<longmapsto>a'<\<nu>x> \<prec> P'" and P'RelQ': "(P', Q') \<in> Rel" by(force dest: BoundO)
    
    from PTrans \<open>y \<sharp> P\<close> yineqx have "y \<sharp> P'" by(force dest: freshBoundDerivative)
    with PTrans have "P \<longmapsto>a'<\<nu>y> \<prec> ([(x, y)] \<bullet> P')" by(simp add: alphaBoundResidual)
    moreover from P'RelQ' Eqvt have "([(x, y)] \<bullet> P', [(x, y)] \<bullet> Q') \<in> Rel" by(auto simp add: eqvt_def)
    ultimately show ?case by(force simp add: derivative_def name_swap) 
  next
    case(cRes Q')
    have "Q \<longmapsto>a\<guillemotleft>y\<guillemotright> \<prec> Q'" and "x \<sharp> a" by fact+
    with yineqx yFreshC show ?case by(force dest: BR)
  qed
next
  case(Free \<alpha> Q')
  have "<\<nu>x>Q \<longmapsto>\<alpha> \<prec> Q'" by fact
  thus ?case
  proof(induct rule: resCasesF)
    case(cRes Q')
    have "Q \<longmapsto>\<alpha> \<prec> Q'" and "x \<sharp> \<alpha>" by fact+
    thus ?case by(rule BF)
  qed
qed

lemma simE:
  fixes P   :: pi
  and   Rel :: "(pi \<times> pi) set"
  and   Q   :: pi
  and   a   :: subject
  and   x   :: name
  and   Q'  :: pi

  assumes "P \<leadsto>[Rel] Q"

  shows "Q \<longmapsto> a\<guillemotleft>x\<guillemotright> \<prec> Q' \<Longrightarrow> x \<sharp> P \<Longrightarrow> \<exists>P'. P \<longmapsto> a\<guillemotleft>x\<guillemotright> \<prec> P' \<and> (derivative P' Q' a x Rel)"
  and   "Q \<longmapsto> \<alpha> \<prec> Q' \<Longrightarrow> \<exists>P'. P \<longmapsto> \<alpha> \<prec> P' \<and> (P', Q') \<in> Rel"
using assms by(simp add: simulation_def)+

lemma eqvtI:
  fixes P    :: pi
  and   Q    :: pi
  and   Rel  :: "(pi \<times> pi) set"
  and   perm :: "name prm"

  assumes Sim: "P \<leadsto>[Rel] Q"
  and     RelRel': "Rel \<subseteq> Rel'"
  and     EqvtRel': "eqvt Rel'"

  shows "(perm \<bullet> P) \<leadsto>[Rel'] (perm \<bullet> Q)"
proof(induct rule: simCases)
  case(Bound a y Q')
  have QTrans: "(perm \<bullet> Q) \<longmapsto> a\<guillemotleft>y\<guillemotright> \<prec> Q'" and yFreshP: "y \<sharp> perm \<bullet> P" by fact+
  
  from QTrans have "(rev perm \<bullet> (perm \<bullet> Q)) \<longmapsto> rev perm \<bullet> (a\<guillemotleft>y\<guillemotright> \<prec> Q')"
    by(rule transitions.eqvt)
  hence "Q \<longmapsto> (rev perm \<bullet> a)\<guillemotleft>(rev perm \<bullet> y)\<guillemotright> \<prec> (rev perm \<bullet> Q')" 
    by(simp add: name_rev_per)
  moreover from yFreshP have "(rev perm \<bullet> y) \<sharp> P" by(simp add: name_fresh_left)
  ultimately have "\<exists>P'. P \<longmapsto> (rev perm \<bullet> a)\<guillemotleft>rev perm \<bullet> y\<guillemotright> \<prec> P' \<and> derivative P' (rev perm \<bullet> Q') (rev perm \<bullet> a) (rev perm \<bullet> y) Rel" using Sim
    by(force intro: simE)
  then obtain P' where PTrans: "P \<longmapsto> (rev perm \<bullet> a)\<guillemotleft>rev perm \<bullet> y\<guillemotright> \<prec> P'" and Pderivative: "derivative P' (rev perm \<bullet> Q') (rev perm \<bullet> a) (rev perm \<bullet> y) Rel" by blast
  
  from PTrans have "(perm \<bullet> P) \<longmapsto> perm \<bullet> ((rev perm \<bullet> a)\<guillemotleft>rev perm \<bullet> y\<guillemotright> \<prec> P')" by(rule transitions.eqvt)
  hence L1: "(perm \<bullet> P) \<longmapsto> a\<guillemotleft>y\<guillemotright> \<prec> (perm \<bullet> P')" by(simp add: name_per_rev)
  from Pderivative RelRel' have "derivative P' (rev perm \<bullet> Q') (rev perm \<bullet> a) (rev perm \<bullet> y) Rel'"
    by(rule derivativeMonotonic)
  hence "derivative (perm \<bullet> P') (perm \<bullet> (rev perm \<bullet> Q')) (perm \<bullet> (rev perm \<bullet> a)) (perm \<bullet> (rev perm \<bullet> y)) Rel'" using EqvtRel'
    by(rule derivativeEqvtI)
  hence "derivative (perm \<bullet> P') Q' a y Rel'" by(simp add: name_per_rev)
  with L1 show ?case by blast
next
  case(Free \<alpha> Q')
  have "(perm \<bullet> Q) \<longmapsto> \<alpha> \<prec> Q'" by fact

  hence "(rev perm \<bullet> (perm \<bullet> Q)) \<longmapsto> rev perm \<bullet> (\<alpha> \<prec> Q')"
    by(rule transitions.eqvt)
  hence "Q \<longmapsto> (rev perm \<bullet> \<alpha>) \<prec> (rev perm \<bullet> Q')" 
    by(simp add: name_rev_per)
  with Sim have "\<exists>P'. P \<longmapsto> (rev perm \<bullet> \<alpha>) \<prec> P' \<and> (P', (rev perm \<bullet> Q')) \<in> Rel"
    by(force intro: simE)
  then obtain P' where PTrans: "P \<longmapsto> (rev perm \<bullet> \<alpha>) \<prec> P'" and PRel: "(P', (rev perm \<bullet> Q')) \<in> Rel"
    by blast
    
  from PTrans have "(perm \<bullet> P) \<longmapsto> perm \<bullet> ((rev perm \<bullet> \<alpha>)\<prec> P')" by(rule transitions.eqvt)
  hence L1: "(perm \<bullet> P) \<longmapsto> \<alpha> \<prec> (perm \<bullet> P')" by(simp add: name_per_rev)
  from PRel EqvtRel' RelRel'  have "((perm \<bullet> P'), (perm \<bullet> (rev perm \<bullet> Q'))) \<in> Rel'"
    by(force intro: eqvtRelI)
  hence "((perm \<bullet> P'), Q') \<in> Rel'" by(simp add: name_per_rev)
  with L1 show "\<exists>P'. (perm \<bullet> P) \<longmapsto>\<alpha> \<prec> P' \<and> (P', Q') \<in> Rel'" by blast
qed

lemma derivativeReflexive:
  fixes P   :: pi
  and   a   :: subject
  and   x   :: name
  and   Rel :: "(pi \<times> pi) set"
  
  assumes "Id \<subseteq> Rel"

  shows "derivative P P a x Rel"
using assms
apply(cases a)
by(auto simp add: derivative_def)
(*
lemma simActFreeCases[consumes 0, case_names Der]:
  fixes P   :: pi
  and   \<alpha>   :: freeRes
  and   Q'  :: pi
  and   Rel :: "(pi \<times> pi) set"

  assumes "\<exists>P'. P \<longmapsto>\<alpha> \<prec> P' \<and> (P', Q') \<in> Rel"

  shows "simAct P (\<alpha> \<prec> Q') P Rel"
using assms
by(simp add: simAct_def residualInject)
*)
(*****************Reflexivity and transitivity*********************)

lemma reflexive:
  fixes P   :: pi
  and   Rel :: "(pi \<times> pi) set"

  assumes "Id \<subseteq> Rel"

  shows "P \<leadsto>[Rel] P"
using assms
by(auto simp add: simulation_def derivativeReflexive)

lemma transitive:
  fixes P     :: pi
  and   Q     :: pi
  and   R     :: pi
  and   Rel   :: "(pi \<times> pi) set"
  and   Rel'  :: "(pi \<times> pi) set"
  and   Rel'' :: "(pi \<times> pi) set"

  assumes PSimQ: "P \<leadsto>[Rel] Q"
  and     QSimR: "Q \<leadsto>[Rel'] R"
  and     Eqvt': "eqvt Rel''"
  and     Trans: "Rel O Rel' \<subseteq> Rel''"

  shows "P \<leadsto>[Rel''] R"
using Eqvt'
proof(induct rule: simCasesCont[where C=Q])
  case(Bound a x R')
  have RTrans: "R \<longmapsto> a\<guillemotleft>x\<guillemotright> \<prec> R'" by fact

  from \<open>x \<sharp> Q\<close> QSimR RTrans obtain Q' where QTrans: "Q \<longmapsto> a\<guillemotleft>x\<guillemotright> \<prec> Q'"
                                        and QDer: "derivative Q' R' a x Rel'" 
    by(blast dest: simE)
  with QTrans \<open>x \<sharp> P\<close> PSimQ obtain P' where PTrans: "P \<longmapsto> a\<guillemotleft>x\<guillemotright> \<prec> P'"
                                        and PDer: "derivative P' Q' a x Rel"
    by(blast dest: simE)
  moreover from PDer QDer Trans have "derivative P' R' a x Rel''"
    by(cases a) (auto simp add: derivative_def)
  ultimately show ?case by blast
next
  case(Free \<alpha> R')
  have RTrans: "R \<longmapsto> \<alpha> \<prec> R'" by fact
  with QSimR obtain Q' where QTrans: "Q \<longmapsto> \<alpha> \<prec> Q'" 
                         and Q'RelR': "(Q', R') \<in> Rel'"
    by(blast dest: simE)
  from QTrans PSimQ obtain P' where PTrans: "P \<longmapsto> \<alpha> \<prec> P'"
                                and P'RelQ': "(P', Q') \<in> Rel"
    by(blast dest: simE)
  from P'RelQ' Q'RelR' Trans have "(P', R') \<in> Rel''" by blast
  with PTrans show ?case by blast
qed

end
