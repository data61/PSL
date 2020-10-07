(* 
   Title: The pi-calculus   
   Author/Maintainer: Jesper Bengtson (jebe.dk), 2012
*)
theory Weak_Early_Late_Comp
  imports Weak_Early_Cong Weak_Late_Cong Strong_Early_Late_Comp
begin

(*************** Transitions *********************)

abbreviation earlyTauChain_judge ("_ \<Longrightarrow>\<^sub>\<tau>\<^sub>e _" [80, 80] 80) where "P \<Longrightarrow>\<^sub>\<tau>\<^sub>e Q \<equiv> Early_Tau_Chain.tauChain P Q"
abbreviation lateTauChain_judge ("_ \<Longrightarrow>\<^sub>\<tau>\<^sub>l _" [80, 80] 80) where "P \<Longrightarrow>\<^sub>\<tau>\<^sub>l Q \<equiv> Late_Tau_Chain.tauChain_judge P Q"

(************** Tau Chains *******************)

lemma lateEarlyTauChain:
  fixes P :: pi
  and   Q :: pi

  assumes "P \<Longrightarrow>\<^sub>\<tau>\<^sub>l Q"

  shows "P \<Longrightarrow>\<^sub>\<tau>\<^sub>e Q"
using assms
proof(induct rule: Late_Tau_Chain.tauChainInduct)
  case id
  show ?case by simp
next
  case(ih P' P'')
  have "P \<Longrightarrow>\<^sub>\<tau>\<^sub>e P'" by fact
  moreover have "P' \<longmapsto>\<^sub>e\<tau> \<prec>\<^sub>e P''"
  proof -
    have "P' \<longmapsto>\<^sub>l\<tau> \<prec>\<^sub>l P''" by fact
    thus ?thesis by(rule lateEarlyTau)
  qed
  ultimately show ?case by blast
qed

lemma earlyLateTauChain:
  fixes P :: pi
  and   Q :: pi

  assumes "P \<Longrightarrow>\<^sub>\<tau>\<^sub>e Q"

  shows "P \<Longrightarrow>\<^sub>\<tau>\<^sub>l Q"
using assms
proof(induct rule: Early_Tau_Chain.tauChainInduct)
  case id
  show ?case by simp
next
  case(ih P' P'')
  have "P \<Longrightarrow>\<^sub>\<tau>\<^sub>l P'" by fact
  moreover have "P' \<longmapsto>\<^sub>l\<tau> \<prec>\<^sub>l P''"
  proof -
    have "P' \<longmapsto>\<^sub>e\<tau> \<prec>\<^sub>e P''" by fact
    thus ?thesis by(rule earlyLateTau)
  qed
  ultimately show ?case by blast
qed

lemma tauChainEq:
  fixes P :: pi
  and   Q :: pi

  shows "P \<Longrightarrow>\<^sub>\<tau>\<^sub>l Q = P \<Longrightarrow>\<^sub>\<tau>\<^sub>e Q"
by(blast intro: lateEarlyTauChain earlyLateTauChain)

(***************** Step semantics ****************)
  
lemma lateEarlyStepOutput:
  fixes P  :: pi
  and   a  :: name
  and   b  :: name
  and   P' :: pi

  assumes "P \<Longrightarrow>\<^sub>l(a[b] \<prec>\<^sub>l P')"

  shows "P \<Longrightarrow>\<^sub>e(a[b] \<prec>\<^sub>e P')"
proof -
  from assms obtain P'' P''' where PChain: "P \<Longrightarrow>\<^sub>\<tau>\<^sub>l P'''"
                               and P'''Trans: "P''' \<longmapsto>\<^sub>la[b] \<prec>\<^sub>l P''"
                               and P''Chain: "P'' \<Longrightarrow>\<^sub>\<tau>\<^sub>l P'"
    by(blast dest: Weak_Late_Step_Semantics.transitionE)

  from PChain have "P \<Longrightarrow>\<^sub>\<tau>\<^sub>e P'''" by(rule lateEarlyTauChain)
  moreover from P'''Trans have "P''' \<longmapsto>\<^sub>ea[b] \<prec>\<^sub>e P''" by(rule lateEarlyOutput)
  moreover from P''Chain have "P'' \<Longrightarrow>\<^sub>\<tau>\<^sub>e P'" by(rule lateEarlyTauChain)
  ultimately show ?thesis by(rule Weak_Early_Step_Semantics.transitionI)
qed
  
lemma earlyLateStepOutput:
  fixes P  :: pi
  and   a  :: name
  and   b  :: name
  and   P' :: pi

  assumes "P \<Longrightarrow>\<^sub>e(a[b] \<prec>\<^sub>e P')"

  shows "P \<Longrightarrow>\<^sub>l(a[b] \<prec>\<^sub>l P')"
proof -
  from assms obtain P'' P''' where PChain: "P \<Longrightarrow>\<^sub>\<tau>\<^sub>e P'''"
                               and P'''Trans: "P''' \<longmapsto>\<^sub>ea[b] \<prec>\<^sub>e P''"
                               and P''Chain: "P'' \<Longrightarrow>\<^sub>\<tau>\<^sub>e P'"
    by(blast dest: Weak_Early_Step_Semantics.transitionE)

  from PChain have "P \<Longrightarrow>\<^sub>\<tau>\<^sub>l P'''" by(rule earlyLateTauChain)
  moreover from P'''Trans have "P''' \<longmapsto>\<^sub>la[b] \<prec>\<^sub>l P''" by(rule earlyLateOutput)
  moreover from P''Chain have "P'' \<Longrightarrow>\<^sub>\<tau>\<^sub>l P'" by(rule earlyLateTauChain)
  ultimately show ?thesis by(rule Weak_Late_Step_Semantics.transitionI)
qed
  
lemma stepOutputEq:
  fixes P  :: pi
  and   a  :: name
  and   b  :: name
  and   P' :: pi

  shows "P \<Longrightarrow>\<^sub>e(a[b] \<prec>\<^sub>e P') = P \<Longrightarrow>\<^sub>l(a[b] \<prec>\<^sub>l P')"
by(auto intro: lateEarlyStepOutput earlyLateStepOutput)

lemma lateEarlyStepBoundOutput:
  fixes P  :: pi
  and   a  :: name
  and   x  :: name
  and   P' :: pi

  assumes "P \<Longrightarrow>\<^sub>l(a<\<nu>x> \<prec>\<^sub>l P')"

  shows "P \<Longrightarrow>\<^sub>e(a<\<nu>x> \<prec>\<^sub>e P')"
proof -
  have Goal: "\<And>P a x P'. \<lbrakk>P \<Longrightarrow>\<^sub>l(a<\<nu>x> \<prec>\<^sub>l P'); x \<sharp> P\<rbrakk> \<Longrightarrow> P \<Longrightarrow>\<^sub>e(a<\<nu>x> \<prec>\<^sub>e P')"
  proof -
    fix P a x P'
    assume "P \<Longrightarrow>\<^sub>l(a<\<nu>x> \<prec>\<^sub>l P')" and "x \<sharp> P"
    then obtain P'' P''' where PChain: "P \<Longrightarrow>\<^sub>\<tau>\<^sub>l P'''"
                           and P'''Trans: "P''' \<longmapsto>\<^sub>la<\<nu>x> \<prec>\<^sub>l P''"
                           and P''Chain: "P'' \<Longrightarrow>\<^sub>\<tau>\<^sub>l P'"
      by(blast dest: Weak_Late_Step_Semantics.transitionE)

    from PChain have "P \<Longrightarrow>\<^sub>\<tau>\<^sub>e P'''" by(rule lateEarlyTauChain)
    moreover from P'''Trans have "P''' \<longmapsto>\<^sub>ea<\<nu>x> \<prec>\<^sub>e P''" by(rule lateEarlyBoundOutput)
    moreover from P''Chain have "P'' \<Longrightarrow>\<^sub>\<tau>\<^sub>e P'" by(rule lateEarlyTauChain)
    ultimately show "P \<Longrightarrow>\<^sub>e(a<\<nu>x> \<prec>\<^sub>e P')" by(rule Weak_Early_Step_Semantics.transitionI)
  qed
  have "\<exists>c::name. c \<sharp> (P, P')" by(blast intro: name_exists_fresh)
  then obtain c::name where cFreshP: "c \<sharp> P" and cFreshP': "c \<sharp> P'"
    by(force simp add: fresh_prod)
  from assms cFreshP' have "P \<Longrightarrow>\<^sub>la<\<nu>c> \<prec>\<^sub>l ([(x, c)] \<bullet> P')" by(simp add: alphaBoundResidual)
  hence "P \<Longrightarrow>\<^sub>ea<\<nu>c> \<prec>\<^sub>e ([(x, c)] \<bullet> P')" using cFreshP by(rule Goal)
  with cFreshP' show ?thesis by(simp add: alphaBoundOutput)
qed
  
lemma earlyLateStepBoundOutput:
  fixes P  :: pi
  and   a  :: name
  and   x  :: name
  and   P' :: pi

  assumes "P \<Longrightarrow>\<^sub>e(a<\<nu>x> \<prec>\<^sub>e P')"

  shows "P \<Longrightarrow>\<^sub>l(a<\<nu>x> \<prec>\<^sub>l P')"
proof -
  have Goal: "\<And>P a x P'. \<lbrakk>P \<Longrightarrow>\<^sub>e(a<\<nu>x> \<prec>\<^sub>e P'); x \<sharp> P\<rbrakk> \<Longrightarrow> P \<Longrightarrow>\<^sub>l(a<\<nu>x> \<prec>\<^sub>l P')"
  proof -
    fix P a x P'
    assume "P \<Longrightarrow>\<^sub>e(a<\<nu>x> \<prec>\<^sub>e P')" and "x \<sharp> P"
    then obtain P'' P''' where PChain: "P \<Longrightarrow>\<^sub>\<tau>\<^sub>e P'''"
                           and P'''Trans: "P''' \<longmapsto>\<^sub>ea<\<nu>x> \<prec>\<^sub>e P''"
                           and P''Chain: "P'' \<Longrightarrow>\<^sub>\<tau>\<^sub>e P'"
      by(blast dest: Weak_Early_Step_Semantics.transitionE)

    from PChain have "P \<Longrightarrow>\<^sub>\<tau>\<^sub>l P'''" by(rule earlyLateTauChain)
    moreover from P'''Trans have "P''' \<longmapsto>\<^sub>la<\<nu>x> \<prec>\<^sub>l P''" by(rule earlyLateBoundOutput)
    moreover from P''Chain have "P'' \<Longrightarrow>\<^sub>\<tau>\<^sub>l P'" by(rule earlyLateTauChain)
    ultimately show "P \<Longrightarrow>\<^sub>l(a<\<nu>x> \<prec>\<^sub>l P')" by(rule Weak_Late_Step_Semantics.transitionI)
  qed
  have "\<exists>c::name. c \<sharp> (P, P')" by(blast intro: name_exists_fresh)
  then obtain c::name where cFreshP: "c \<sharp> P" and cFreshP': "c \<sharp> P'"
    by(force simp add: fresh_prod)
  from assms cFreshP' have "P \<Longrightarrow>\<^sub>ea<\<nu>c> \<prec>\<^sub>e ([(x, c)] \<bullet> P')" by(simp add: alphaBoundOutput)
  hence "P \<Longrightarrow>\<^sub>la<\<nu>c> \<prec>\<^sub>l ([(x, c)] \<bullet> P')" using cFreshP by(rule Goal)
  with cFreshP' show ?thesis by(simp add: alphaBoundResidual)
qed
  
lemma stepBoundOutputEq:
  fixes P  :: pi
  and   a  :: name
  and   x  :: name
  and   P' :: pi

  shows "P \<Longrightarrow>\<^sub>e(a<\<nu>x> \<prec>\<^sub>e P') = P \<Longrightarrow>\<^sub>l(a<\<nu>x> \<prec>\<^sub>l P')"
by(auto intro: lateEarlyStepBoundOutput earlyLateStepBoundOutput)

lemma earlyLateStepInput:
  fixes P  :: pi
  and   a  :: name
  and   u  :: name
  and   P' :: pi
  and   C  :: "'a::fs_name"

  assumes "P \<Longrightarrow>\<^sub>e(a<u> \<prec>\<^sub>e P')"

  shows "\<exists>P'' x. P \<Longrightarrow>\<^sub>lu in P'' \<rightarrow>a<x> \<prec> P' \<and> x \<sharp> C"
proof -
  from assms obtain P'' P''' where PChain: "P \<Longrightarrow>\<^sub>\<tau>\<^sub>e P'''"
                              and P'''Trans: "P''' \<longmapsto>\<^sub>ea<u> \<prec>\<^sub>e P''"
                              and P''Chain: "P'' \<Longrightarrow>\<^sub>\<tau>\<^sub>e P'"
    by(blast dest: Weak_Early_Step_Semantics.transitionE)

  from PChain have "P \<Longrightarrow>\<^sub>\<tau>\<^sub>l P'''" by(rule earlyLateTauChain)
  moreover from P'''Trans obtain P'''' x where P'''Trans: "P''' \<longmapsto>\<^sub>la<x> \<prec>\<^sub>l P''''" 
                                           and P''eqP'''': "P'' = P''''[x::=u]"
                                           and xFreshC: "x \<sharp> C"
    by(blast dest: earlyLateInput)
  moreover from P''Chain have "P'' \<Longrightarrow>\<^sub>\<tau>\<^sub>l P'" by(rule earlyLateTauChain)
  ultimately show "\<exists>P'' x. P \<Longrightarrow>\<^sub>lu in P'' \<rightarrow> a<x> \<prec> P' \<and> x \<sharp> C"
    by(blast intro: Weak_Late_Step_Semantics.transitionI)
qed
  
lemma lateEarlyStepInput:
  fixes P   :: pi
  and   u   :: name
  and   P'' :: pi
  and   a   :: name
  and   x   :: name
  and   P'  :: pi

  assumes "P \<Longrightarrow>\<^sub>lu in P'' \<rightarrow> a<x> \<prec> P'"

  shows "P \<Longrightarrow>\<^sub>e(a<u> \<prec>\<^sub>e P')"
proof -
  from assms obtain P''' where PChain: "P \<Longrightarrow>\<^sub>\<tau>\<^sub>l P'''"
                           and P'''Trans: "P''' \<longmapsto>\<^sub>la<x> \<prec>\<^sub>l P''"
                           and P''Chain: "P''[x::=u] \<Longrightarrow>\<^sub>\<tau>\<^sub>l P'"
    by(blast dest: Weak_Late_Step_Semantics.transitionE)

  from PChain have "P \<Longrightarrow>\<^sub>\<tau>\<^sub>e P'''" by(rule lateEarlyTauChain)
  moreover from P'''Trans have "P''' \<longmapsto>\<^sub>ea<u> \<prec>\<^sub>e P''[x::=u]" by(rule lateEarlyInput)
  moreover from P''Chain have "P''[x::=u] \<Longrightarrow>\<^sub>\<tau>\<^sub>e P'" by(rule lateEarlyTauChain)
  ultimately show "P \<Longrightarrow>\<^sub>e(a<u> \<prec>\<^sub>e P')" by(rule Weak_Early_Step_Semantics.transitionI)
qed

lemma lateEarlyStepTau:
  fixes P  :: pi
  and   a  :: name
  and   b  :: name
  and   P' :: pi

  assumes "P \<Longrightarrow>\<^sub>l(\<tau> \<prec>\<^sub>l P')"

  shows "P \<Longrightarrow>\<^sub>e(\<tau> \<prec>\<^sub>e P')"
proof -
  from assms obtain P'' P''' where PChain: "P \<Longrightarrow>\<^sub>\<tau>\<^sub>l P'''"
                               and P'''Trans: "P''' \<longmapsto>\<^sub>l\<tau> \<prec>\<^sub>l P''"
                               and P''Chain: "P'' \<Longrightarrow>\<^sub>\<tau>\<^sub>l P'"
    by(blast dest: Weak_Late_Step_Semantics.transitionE)

  from PChain have "P \<Longrightarrow>\<^sub>\<tau>\<^sub>e P'''" by(rule lateEarlyTauChain)
  moreover from P'''Trans have "P''' \<longmapsto>\<^sub>e\<tau> \<prec>\<^sub>e P''" by(rule lateEarlyTau)
  moreover from P''Chain have "P'' \<Longrightarrow>\<^sub>\<tau>\<^sub>e P'" by(rule lateEarlyTauChain)
  ultimately show ?thesis by(rule Weak_Early_Step_Semantics.transitionI)
qed

lemma earlyLateStepTau:
  fixes P  :: pi
  and   a  :: name
  and   b  :: name
  and   P' :: pi

  assumes "P \<Longrightarrow>\<^sub>e(\<tau> \<prec>\<^sub>e P')"

  shows "P \<Longrightarrow>\<^sub>l(\<tau> \<prec>\<^sub>l P')"
proof -
  from assms obtain P'' P''' where PChain: "P \<Longrightarrow>\<^sub>\<tau>\<^sub>e P'''"
                               and P'''Trans: "P''' \<longmapsto>\<^sub>e\<tau> \<prec>\<^sub>e P''"
                               and P''Chain: "P'' \<Longrightarrow>\<^sub>\<tau>\<^sub>e P'"
    by(blast dest: Weak_Early_Step_Semantics.transitionE)

  from PChain have "P \<Longrightarrow>\<^sub>\<tau>\<^sub>l P'''" by(rule earlyLateTauChain)
  moreover from P'''Trans have "P''' \<longmapsto>\<^sub>l\<tau> \<prec>\<^sub>l P''" by(rule earlyLateTau)
  moreover from P''Chain have "P'' \<Longrightarrow>\<^sub>\<tau>\<^sub>l P'" by(rule earlyLateTauChain)
  ultimately show ?thesis by(rule Weak_Late_Step_Semantics.transitionI)
qed

lemma stepTauEq:
  fixes P  :: pi
  and   P' :: pi
  
  shows "P \<Longrightarrow>\<^sub>e\<tau> \<prec>\<^sub>e P' = P \<Longrightarrow>\<^sub>l\<tau> \<prec>\<^sub>l P'"
by(blast intro: earlyLateStepTau lateEarlyStepTau)

(****************** Weak Semantics *************)

lemma lateEarlyOutput:
  fixes P  :: pi
  and   a  :: name
  and   b  :: name
  and   P' :: pi

  assumes "P \<Longrightarrow>\<^sub>l\<^sup>^(a[b] \<prec>\<^sub>l P')"

  shows "P \<Longrightarrow>\<^sub>e\<^sup>^(a[b] \<prec>\<^sub>e P')"
proof -
  from assms have "P \<Longrightarrow>\<^sub>l(a[b] \<prec>\<^sub>l P')"
    by(simp add: Weak_Late_Semantics.weakTransition_def Late_Semantics.residual.inject)
  hence "P \<Longrightarrow>\<^sub>e(a[b] \<prec>\<^sub>e P')" by(rule lateEarlyStepOutput)
  thus ?thesis
    by(simp add: Weak_Early_Semantics.weakTransition_def Early_Semantics.residual.inject)
qed
  
lemma earlyLateOutput:
  fixes P  :: pi
  and   a  :: name
  and   b  :: name
  and   P' :: pi

  assumes "P \<Longrightarrow>\<^sub>e\<^sup>^(a[b] \<prec>\<^sub>e P')"

  shows "P \<Longrightarrow>\<^sub>l\<^sup>^(a[b] \<prec>\<^sub>l P')"
proof -
  from assms have "P \<Longrightarrow>\<^sub>e(a[b] \<prec>\<^sub>e P')"
    by(simp add: Weak_Early_Semantics.weakTransition_def Early_Semantics.residual.inject)
  hence "P \<Longrightarrow>\<^sub>l(a[b] \<prec>\<^sub>l P')" by(rule earlyLateStepOutput)
  thus ?thesis
    by(simp add: Weak_Late_Semantics.weakTransition_def Late_Semantics.residual.inject)
qed

lemma outputEq:
  fixes P  :: pi
  and   a  :: name
  and   b  :: name
  and   P' :: pi

  shows "P \<Longrightarrow>\<^sub>e\<^sup>^(a[b] \<prec>\<^sub>e P') = P \<Longrightarrow>\<^sub>l\<^sup>^(a[b] \<prec>\<^sub>l P')"
by(auto intro: lateEarlyOutput earlyLateOutput)

lemma lateEarlyBoundOutput:
  fixes P  :: pi
  and   a  :: name
  and   x  :: name
  and   P' :: pi

  assumes "P \<Longrightarrow>\<^sub>l\<^sup>^(a<\<nu>x> \<prec>\<^sub>l P')"

  shows "P \<Longrightarrow>\<^sub>e\<^sup>^(a<\<nu>x> \<prec>\<^sub>e P')"
proof -
  from assms have "P \<Longrightarrow>\<^sub>l(a<\<nu>x> \<prec>\<^sub>l P')"
    by(simp add: Weak_Late_Semantics.weakTransition_def Late_Semantics.residual.inject)
  hence "P \<Longrightarrow>\<^sub>e(a<\<nu>x> \<prec>\<^sub>e P')" by(rule lateEarlyStepBoundOutput)
  thus ?thesis
    by(simp add: Weak_Early_Semantics.weakTransition_def Early_Semantics.residual.inject)
qed
  
lemma earlyLateBoundOutput:
  fixes P  :: pi
  and   a  :: name
  and   x  :: name
  and   P' :: pi

  assumes "P \<Longrightarrow>\<^sub>e\<^sup>^(a<\<nu>x> \<prec>\<^sub>e P')"

  shows "P \<Longrightarrow>\<^sub>l\<^sup>^(a<\<nu>x> \<prec>\<^sub>l P')"
proof -
  from assms have "P \<Longrightarrow>\<^sub>e(a<\<nu>x> \<prec>\<^sub>e P')"
    by(simp add: Weak_Early_Semantics.weakTransition_def Early_Semantics.residual.inject)
  hence "P \<Longrightarrow>\<^sub>l(a<\<nu>x> \<prec>\<^sub>l P')" by(rule earlyLateStepBoundOutput)
  thus ?thesis
    by(simp add: Weak_Late_Semantics.weakTransition_def Late_Semantics.residual.inject)
qed

lemma boundOutputEq:
  fixes P  :: pi
  and   a  :: name
  and   b  :: name
  and   P' :: pi

  shows "P \<Longrightarrow>\<^sub>e\<^sup>^(a<\<nu>x> \<prec>\<^sub>e P') = P \<Longrightarrow>\<^sub>l\<^sup>^(a<\<nu>x> \<prec>\<^sub>l P')"
by(auto intro: lateEarlyBoundOutput earlyLateBoundOutput)

lemma earlyLateInput:
  fixes P  :: pi
  and   a  :: name
  and   u  :: name
  and   P' :: pi
  and   C  :: "'a::fs_name"

  assumes "P \<Longrightarrow>\<^sub>e\<^sup>^(a<u> \<prec>\<^sub>e P')"

  shows "\<exists>P'' x. P \<Longrightarrow>\<^sub>lu in P'' \<rightarrow>a<x> \<prec> P' \<and> x \<sharp> C"
proof -
  from assms have "P \<Longrightarrow>\<^sub>e(a<u> \<prec>\<^sub>e P')"
    by(simp add: Weak_Early_Semantics.weakTransition_def Early_Semantics.residual.inject)
  thus ?thesis by(rule earlyLateStepInput)
qed
  
lemma lateEarlyInput:
  fixes P   :: pi
  and   u   :: name
  and   P'' :: pi
  and   a   :: name
  and   x   :: name
  and   P'  :: pi

  assumes "P \<Longrightarrow>\<^sub>lu in P'' \<rightarrow> a<x> \<prec> P'"

  shows "P \<Longrightarrow>\<^sub>e\<^sup>^(a<u> \<prec>\<^sub>e P')"
proof -
  from assms have "P \<Longrightarrow>\<^sub>e(a<u> \<prec>\<^sub>e P')" by(rule lateEarlyStepInput)
  thus ?thesis by(simp add: Weak_Early_Semantics.weakTransition_def Early_Semantics.residual.inject)
qed

lemma lateEarlyTau:
  fixes P  :: pi
  and   P' :: pi

  assumes "P \<Longrightarrow>\<^sub>l\<^sup>^(\<tau> \<prec>\<^sub>l P')"

  shows "P \<Longrightarrow>\<^sub>e\<^sup>^(\<tau> \<prec>\<^sub>e P')"
proof -
  from assms show ?thesis
  proof(induct rule: Weak_Late_Semantics.transitionCases)
    case Stay
    thus ?case
      by(auto simp add: Late_Semantics.residual.inject Weak_Early_Semantics.weakTransition_def)
  next
    case Step
    have "P \<Longrightarrow>\<^sub>l\<tau> \<prec>\<^sub>l P'" by fact
    hence "P \<Longrightarrow>\<^sub>e\<tau> \<prec>\<^sub>e P'" by(rule lateEarlyStepTau)
    thus ?case by(simp add: Weak_Early_Semantics.weakTransition_def)
  qed
qed

lemma earlyLateTau:
  fixes P  :: pi
  and   P' :: pi

  assumes "P \<Longrightarrow>\<^sub>e\<^sup>^(\<tau> \<prec>\<^sub>e P')"

  shows "P \<Longrightarrow>\<^sub>l\<^sup>^(\<tau> \<prec>\<^sub>l P')"
proof -
  from assms show ?thesis
  proof(induct rule: Weak_Early_Semantics.transitionCases)
    case Stay
    thus ?case
      by(auto simp add: Early_Semantics.residual.inject Weak_Late_Semantics.weakTransition_def)
  next
    case Step
    have "P \<Longrightarrow>\<^sub>e\<tau> \<prec>\<^sub>e P'" by fact
    hence "P \<Longrightarrow>\<^sub>l\<tau> \<prec>\<^sub>l P'" by(rule earlyLateStepTau)
    thus ?case by(simp add: Weak_Late_Semantics.weakTransition_def)
  qed
qed

lemma tauEq:
  fixes P  :: pi
  and   P' :: pi
  
  shows "P \<Longrightarrow>\<^sub>e\<^sup>^\<tau> \<prec>\<^sub>e P' = P \<Longrightarrow>\<^sub>l\<^sup>^\<tau> \<prec>\<^sub>l P'"
by(blast intro: earlyLateTau lateEarlyTau)

(****************** Weak Simulation ******************)

abbreviation weakSimStepLate_judge ("_ \<leadsto>\<^sub>l<_> _" [80, 80, 80] 80) where "P \<leadsto>\<^sub>l<Rel> Q \<equiv> Weak_Late_Step_Sim.weakStepSim P Rel Q"
abbreviation weakSimStepEarly_judge ("_ \<leadsto>\<^sub>e<_> _" [80, 80, 80] 80) where "P \<leadsto>\<^sub>e<Rel> Q \<equiv> Weak_Early_Step_Sim.weakStepSimulation P Rel Q"
abbreviation weakSimLate_judge ("_ \<leadsto>\<^sub>l\<^sup>^<_> _" [80, 80, 80] 80) where "P \<leadsto>\<^sub>l\<^sup>^<Rel> Q \<equiv> Weak_Late_Sim.weakSimulation P Rel Q"
abbreviation weakSimEarly_judge ("_ \<leadsto>\<^sub>e\<^sup>^<_> _" [80, 80, 80] 80) where "P \<leadsto>\<^sub>e\<^sup>^<Rel> Q \<equiv> Weak_Early_Sim.weakSimulation P Rel Q"

lemma lateEarlyStepSim:
  fixes P   :: pi
  and   Q   :: pi
  and   Rel :: "(pi \<times> pi) set"

  assumes PSimQ: "P \<leadsto>\<^sub>l<Rel> Q"

  shows "P \<leadsto>\<^sub>e<Rel> Q"
proof(induct rule: Weak_Early_Step_Sim.simCases)
  case(Bound Q' a x)
  have "Q \<longmapsto>\<^sub>ea<\<nu>x> \<prec>\<^sub>e Q'" by fact
  hence "Q \<longmapsto>\<^sub>la<\<nu>x> \<prec>\<^sub>l Q'" by(rule Strong_Early_Late_Comp.earlyLateBoundOutput)
  moreover have "x \<sharp> P" by fact
  ultimately obtain P' where PTrans: "P \<Longrightarrow>\<^sub>la<\<nu>x> \<prec>\<^sub>l P'" and P'RelQ': "(P', Q') \<in> Rel" using PSimQ
    by(blast dest: Weak_Late_Step_Sim.simE)
  from PTrans have "P \<Longrightarrow>\<^sub>ea<\<nu>x> \<prec>\<^sub>e P'" by(rule lateEarlyStepBoundOutput)
  with P'RelQ' show ?case by blast
next
  case(Free Q' \<alpha>)
  have "Q \<longmapsto>\<^sub>e Early_Semantics.residual.FreeR \<alpha> Q'" by fact
  thus ?case
  proof(cases \<alpha>, auto)
    fix a u
    assume "Q \<longmapsto>\<^sub>ea<u> \<prec>\<^sub>e Q'"
    then obtain Q'' x where QTrans: "Q \<longmapsto>\<^sub>la<x> \<prec>\<^sub>l Q''" and Q'eqQ'': "Q' = Q''[x::=u]"
                        and xFreshP: "x \<sharp> P"
      by(blast dest: Strong_Early_Late_Comp.earlyLateInput[of _ _ _ _ P])
    from PSimQ QTrans xFreshP obtain P' P'' where PTrans: "P \<Longrightarrow>\<^sub>lu in P'' \<rightarrow> a<x> \<prec> P'"
                                              and P'RelQ': "(P', Q''[x::=u]) \<in> Rel"
      by(blast dest: Weak_Late_Step_Sim.simE)
    from PTrans have "P \<Longrightarrow>\<^sub>ea<u> \<prec>\<^sub>e P'" by(rule lateEarlyStepInput)
    with P'RelQ' Q'eqQ'' show "\<exists>P'. P \<Longrightarrow>\<^sub>ea<u> \<prec>\<^sub>e P' \<and> (P', Q') \<in> Rel" by blast
  next
    fix a b
    assume "Q \<longmapsto>\<^sub>ea[b] \<prec>\<^sub>e Q'"
    hence "Q \<longmapsto>\<^sub>la[b] \<prec>\<^sub>l Q'" by(rule Strong_Early_Late_Comp.earlyLateOutput)
    with PSimQ obtain P' where PTrans: "P \<Longrightarrow>\<^sub>la[b] \<prec>\<^sub>l P'" and P'RelQ': "(P', Q') \<in> Rel"
      by(blast dest: Weak_Late_Step_Sim.simE)
    from PTrans have "P \<Longrightarrow>\<^sub>ea[b] \<prec>\<^sub>e P'" by(rule lateEarlyStepOutput)
    with P'RelQ' show "\<exists>P'. P \<Longrightarrow>\<^sub>ea[b] \<prec>\<^sub>e P' \<and> (P', Q') \<in> Rel"  by blast
  next
    assume "Q \<longmapsto>\<^sub>e\<tau> \<prec>\<^sub>e Q'"
    hence "Q \<longmapsto>\<^sub>l\<tau> \<prec>\<^sub>l Q'" by(rule Strong_Early_Late_Comp.earlyLateTau)
    with PSimQ obtain P' where PTrans: "P \<Longrightarrow>\<^sub>l\<tau> \<prec>\<^sub>l P'" and P'RelQ': "(P', Q') \<in> Rel"
      by(blast dest: Weak_Late_Step_Sim.simE)
    from PTrans have "P \<Longrightarrow>\<^sub>e\<tau> \<prec>\<^sub>e P'" by(rule lateEarlyStepTau)
    with P'RelQ' show "\<exists>P'. P \<Longrightarrow>\<^sub>e\<tau> \<prec>\<^sub>e P' \<and> (P', Q') \<in> Rel"  by blast
  qed
qed

lemma lateEarlySim:
  fixes P   :: pi
  and   Q   :: pi
  and   Rel :: "(pi \<times> pi) set"

  assumes PSimQ: "P \<leadsto>\<^sub>l\<^sup>^<Rel> Q"

  shows "P \<leadsto>\<^sub>e\<^sup>^<Rel> Q"
proof(induct rule: Weak_Early_Sim.simCases)
  case(Bound Q' a x)
  have "Q \<longmapsto>\<^sub>ea<\<nu>x> \<prec>\<^sub>e Q'" by fact
  hence "Q \<longmapsto>\<^sub>la<\<nu>x> \<prec>\<^sub>l Q'" by(rule Strong_Early_Late_Comp.earlyLateBoundOutput)
  moreover have "x \<sharp> P" by fact
  ultimately obtain P' where PTrans: "P \<Longrightarrow>\<^sub>l\<^sup>^a<\<nu>x> \<prec>\<^sub>l P'" and P'RelQ': "(P', Q') \<in> Rel" using PSimQ
    by(blast dest: Weak_Late_Sim.simE)
  from PTrans have "P \<Longrightarrow>\<^sub>e\<^sup>^a<\<nu>x> \<prec>\<^sub>e P'" by(rule lateEarlyBoundOutput)
  with P'RelQ' show ?case by blast
next
  case(Free Q' \<alpha>)
  have "Q \<longmapsto>\<^sub>e Early_Semantics.residual.FreeR \<alpha> Q'" by fact
  thus ?case
  proof(cases \<alpha>, auto)
    fix a u
    assume "Q \<longmapsto>\<^sub>ea<u> \<prec>\<^sub>e Q'"
    then obtain Q'' x where QTrans: "Q \<longmapsto>\<^sub>la<x> \<prec>\<^sub>l Q''" and Q'eqQ'': "Q' = Q''[x::=u]"
                        and xFreshP: "x \<sharp> P"
      by(blast dest: Strong_Early_Late_Comp.earlyLateInput[of _ _ _ _ P])
    from PSimQ QTrans xFreshP obtain P' P'' where PTrans: "P \<Longrightarrow>\<^sub>lu in P'' \<rightarrow> a<x> \<prec> P'"
                                              and P'RelQ': "(P', Q''[x::=u]) \<in> Rel"
      by(blast dest: Weak_Late_Sim.simE)
    from PTrans have "P \<Longrightarrow>\<^sub>e\<^sup>^a<u> \<prec>\<^sub>e P'" by(rule lateEarlyInput)
    with P'RelQ' Q'eqQ'' show "\<exists>P'. P \<Longrightarrow>\<^sub>e\<^sup>^a<u> \<prec>\<^sub>e P' \<and> (P', Q') \<in> Rel" by blast
  next
    fix a b
    assume "Q \<longmapsto>\<^sub>ea[b] \<prec>\<^sub>e Q'"
    hence "Q \<longmapsto>\<^sub>la[b] \<prec>\<^sub>l Q'" by(rule Strong_Early_Late_Comp.earlyLateOutput)
    with PSimQ obtain P' where PTrans: "P \<Longrightarrow>\<^sub>l\<^sup>^a[b] \<prec>\<^sub>l P'" and P'RelQ': "(P', Q') \<in> Rel"
      by(blast dest: Weak_Late_Sim.simE)
    from PTrans have "P \<Longrightarrow>\<^sub>e\<^sup>^a[b] \<prec>\<^sub>e P'" by(rule lateEarlyOutput)
    with P'RelQ' show "\<exists>P'. P \<Longrightarrow>\<^sub>e\<^sup>^a[b] \<prec>\<^sub>e P' \<and> (P', Q') \<in> Rel"  by blast
  next
    assume "Q \<longmapsto>\<^sub>e\<tau> \<prec>\<^sub>e Q'"
    hence "Q \<longmapsto>\<^sub>l\<tau> \<prec>\<^sub>l Q'" by(rule Strong_Early_Late_Comp.earlyLateTau)
    with PSimQ obtain P' where PTrans: "P \<Longrightarrow>\<^sub>l\<^sup>^\<tau> \<prec>\<^sub>l P'" and P'RelQ': "(P', Q') \<in> Rel"
      by(blast dest: Weak_Late_Sim.simE)
    from PTrans have "P \<Longrightarrow>\<^sub>e\<^sup>^\<tau> \<prec>\<^sub>e P'" by(rule lateEarlyTau)
    with P'RelQ' show "\<exists>P'. P \<Longrightarrow>\<^sub>e\<^sup>^\<tau> \<prec>\<^sub>e P' \<and> (P', Q') \<in> Rel"  by blast
  qed
qed

(*************** Bisimulation ***************)

abbreviation weakBisimLate_judge (infixl "\<approx>\<^sub>l" 80) where "P \<approx>\<^sub>l Q \<equiv> (P, Q) \<in> Weak_Late_Bisim.weakBisim"
abbreviation weakBisimEarly_judge (infixl "\<approx>\<^sub>e" 80) where "P \<approx>\<^sub>e Q \<equiv> (P, Q) \<in> Weak_Early_Bisim.weakBisim"
abbreviation weakCongLate_judge (infixl "\<simeq>\<^sub>l" 80) where "P \<simeq>\<^sub>l Q \<equiv> (P, Q) \<in> Weak_Late_Cong.congruence"
abbreviation weakCongEarly_judge (infixl "\<simeq>\<^sub>e" 80) where "P \<simeq>\<^sub>e Q \<equiv> (P, Q) \<in> Weak_Early_Cong.congruence"

lemma lateEarlyBisim:
  fixes P :: pi
  and   Q :: pi

  assumes "P \<approx>\<^sub>l Q"

  shows "P \<approx>\<^sub>e Q"
proof -
  from assms show ?thesis
  by(coinduct rule: Weak_Early_Bisim.weak_coinduct,
     auto dest: Weak_Late_Bisim.unfoldE intro: lateEarlySim)
qed

lemma lateEarlyCong:
  fixes P :: pi
  and   Q :: pi

  assumes "P \<simeq>\<^sub>l Q"

  shows "P \<simeq>\<^sub>e Q"
proof -
  from lateEarlyBisim have "\<And>P Q. P \<leadsto>\<^sub>l<(Weak_Late_Bisim.weakBisim)> Q \<Longrightarrow> P \<leadsto>\<^sub>l<(Weak_Early_Bisim.weakBisim)> Q"
    by(auto intro: Weak_Late_Step_Sim.monotonic)
  with assms show ?thesis
    by(auto simp add: Weak_Late_Cong.congruence_def Weak_Early_Cong.congruence_def intro: lateEarlyStepSim)
qed

abbreviation weakLateBisimSubst_judge (infixl "\<approx>\<^sup>s\<^sub>l" 80) where "P \<approx>\<^sup>s\<^sub>l Q \<equiv> (P, Q) \<in> (substClosed Weak_Late_Bisim.weakBisim)"
abbreviation weakEarlyBisimSubst_judge (infixl "\<approx>\<^sup>s\<^sub>e" 80) where "P \<approx>\<^sup>s\<^sub>e Q \<equiv> (P, Q) \<in> (substClosed Weak_Early_Bisim.weakBisim)"

abbreviation weakLateCongSubst_judge (infixl "\<simeq>\<^sup>s\<^sub>l" 80) where "P \<simeq>\<^sup>s\<^sub>l Q \<equiv> (P, Q) \<in> (substClosed Weak_Late_Cong.congruence)"
abbreviation weakEarlyTongSubst_judge (infixl "\<simeq>\<^sup>s\<^sub>e" 80) where "P \<simeq>\<^sup>s\<^sub>e Q \<equiv> (P, Q) \<in> (substClosed Weak_Early_Cong.congruence)"

lemma lateEarlyBisimSubst:
  fixes P :: pi
  and   Q :: pi

  assumes "P \<approx>\<^sup>s\<^sub>l Q"

  shows "P \<approx>\<^sup>s\<^sub>e Q"
using assms
by(auto simp add: substClosed_def intro: lateEarlyBisim)

lemma lateEarlyBisimSubst:
  fixes P :: pi
  and   Q :: pi

  assumes "P \<simeq>\<^sup>s\<^sub>l Q"

  shows "P \<simeq>\<^sup>s\<^sub>e Q"
using assms
by(auto simp add: substClosed_def intro: lateEarlyCong)

end
