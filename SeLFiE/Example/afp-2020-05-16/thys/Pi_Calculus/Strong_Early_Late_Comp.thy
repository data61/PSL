(* 
   Title: The pi-calculus   
   Author/Maintainer: Jesper Bengtson (jebe.dk), 2012
*)
theory Strong_Early_Late_Comp
  imports Strong_Late_Bisim_Subst_SC Strong_Early_Bisim_Subst
begin

abbreviation TransitionsLate_judge ("_ \<longmapsto>\<^sub>l _" [80, 80] 80) where "P \<longmapsto>\<^sub>l Rs \<equiv> transitions P Rs"
abbreviation TransitionsEarly_judge ("_ \<longmapsto>\<^sub>e _" [80, 80] 80) where "P \<longmapsto>\<^sub>e Rs \<equiv> TransitionsEarly P Rs"

abbreviation Transitions_InputjudgeLate ("_<_> \<prec>\<^sub>l _" [80, 80] 80) where "a<x> \<prec>\<^sub>l P' \<equiv> (Late_Semantics.BoundR (Late_Semantics.InputS a) x P')"
abbreviation Transitions_OutputjudgeLate ("_[_] \<prec>\<^sub>l _" [80, 80] 80) where "a[b] \<prec>\<^sub>l P' \<equiv> (Late_Semantics.FreeR (Late_Semantics.OutputR a b) P')"
abbreviation Transitions_BoundOutputjudgeLate ("_<\<nu>_> \<prec>\<^sub>l _" [80, 80] 80) where "a<\<nu>x> \<prec>\<^sub>l P' \<equiv> (Late_Semantics.BoundR (Late_Semantics.BoundOutputS a) x P')"
abbreviation Transitions_TaujudgeLate ("\<tau> \<prec>\<^sub>l _" 80) where "\<tau> \<prec>\<^sub>l P' \<equiv> (Late_Semantics.FreeR Late_Semantics.TauR P')"

abbreviation Transitions_InputjudgeEarly ("_<_> \<prec>\<^sub>e _" [80, 80] 80) where "a<x> \<prec>\<^sub>e P' \<equiv> (Early_Semantics.FreeR (Early_Semantics.InputR a x) P')"
abbreviation Transitions_OutputjudgeEarly ("_[_] \<prec>\<^sub>e _" [80, 80] 80) where "a[b] \<prec>\<^sub>e P' \<equiv> (Early_Semantics.FreeR (Early_Semantics.OutputR a b) P')"
abbreviation Transitions_BoundOutputjudgeEarly ("_<\<nu>_> \<prec>\<^sub>e _" [80, 80] 80) where "a<\<nu>x> \<prec>\<^sub>e P' \<equiv>(Early_Semantics.BoundOutputR a x P')"
abbreviation Transitions_TaujudgeEarly ("\<tau> \<prec>\<^sub>e _" 80) where "\<tau> \<prec>\<^sub>e P' \<equiv> (Early_Semantics.FreeR Early_Semantics.TauR P')"

lemma earlyLateOutput:
  fixes P  :: pi
  and   a  :: name
  and   b  :: name
  and   P' :: pi

  assumes "P \<longmapsto>\<^sub>ea[b] \<prec>\<^sub>e P'"

  shows "P \<longmapsto>\<^sub>la[b] \<prec>\<^sub>l P'"
using assms
proof(nominal_induct rule: Early_Semantics.outputInduct)
  case(Output a b P)
  show ?case by(rule Late_Semantics.Output)
next
  case(Match P a b P' c)
  have "P \<longmapsto>\<^sub>la[b] \<prec>\<^sub>l P'" by fact
  thus ?case by(rule Late_Semantics.Match)
next
  case(Mismatch P a b P' c d)
  from \<open>P \<longmapsto>\<^sub>la[b] \<prec>\<^sub>l P'\<close> \<open>c \<noteq> d\<close>
  show ?case by(rule Late_Semantics.Mismatch)
next
  case(Sum1 P a b P' Q)
  have "P \<longmapsto>\<^sub>la[b] \<prec>\<^sub>l P'" by fact
  thus ?case by(rule Late_Semantics.Sum1)
next
  case(Sum2 Q a b Q' P)
  have "Q \<longmapsto>\<^sub>la[b] \<prec>\<^sub>l Q'" by fact
  thus ?case by(rule Late_Semantics.Sum2)
next
  case(Par1 P a b P' Q)
  have "P \<longmapsto>\<^sub>la[b] \<prec>\<^sub>l P'" by fact
  thus ?case by(rule Late_Semantics.Par1F)
next
  case(Par2 Q a b Q' P)
  have "Q \<longmapsto>\<^sub>la[b] \<prec>\<^sub>l Q'" by fact
  thus ?case by(rule Late_Semantics.Par2F)
next
  case(Res P a b P' x)
  have "P \<longmapsto>\<^sub>la[b] \<prec>\<^sub>l P'" and "x \<noteq> a" and "x \<noteq> b" by fact+
  thus ?case by(force intro: Late_Semantics.ResF)
next
  case(Bang P a b P')
  have "P \<parallel> !P \<longmapsto>\<^sub>la[b] \<prec>\<^sub>l P'" by fact
  thus ?case by(rule Late_Semantics.Bang)
qed

lemma lateEarlyOutput:
  fixes P  :: pi
  and   a  :: name
  and   b  :: name
  and   P' :: pi

  assumes "P \<longmapsto>\<^sub>la[b] \<prec>\<^sub>l P'"

  shows "P \<longmapsto>\<^sub>ea[b] \<prec>\<^sub>e P'"
using assms
proof(nominal_induct rule: Late_Semantics.outputInduct)
  case(Output a b P)
  thus ?case by(rule Early_Semantics.Output)
next
  case(Match P a b P' c)
  have "P \<longmapsto>\<^sub>ea[b] \<prec>\<^sub>e P'" by fact
  thus ?case by(rule Early_Semantics.Match)
next
  case(Mismatch P a b P' c d)
  have "P \<longmapsto>\<^sub>ea[b] \<prec>\<^sub>e P'" and "c \<noteq> d" by fact+
  thus ?case by(rule Early_Semantics.Mismatch)
next
  case(Sum1 P a b P' Q)
  have "P \<longmapsto>\<^sub>ea[b] \<prec>\<^sub>e P'" by fact
  thus ?case by(rule Early_Semantics.Sum1)
next
  case(Sum2 Q a b Q' P)
  have "Q \<longmapsto>\<^sub>ea[b] \<prec>\<^sub>e Q'" by fact
  thus ?case by(rule Early_Semantics.Sum2)
next
  case(Par1 P a b P' Q)
  have "P \<longmapsto>\<^sub>ea[b] \<prec>\<^sub>e P'" by fact
  thus ?case by(rule Early_Semantics.Par1F)
next
  case(Par2 Q a b Q' P)
  have "Q \<longmapsto>\<^sub>ea[b] \<prec>\<^sub>e Q'" by fact
  thus ?case by(rule Early_Semantics.Par2F)
next
  case(Res P a b P' x)
  have "P \<longmapsto>\<^sub>ea[b] \<prec>\<^sub>e P'" and "x \<noteq> a" and "x \<noteq> b" by fact+
  thus ?case by(force intro: Early_Semantics.ResF)
next
  case(Bang P a b P')
  have "P \<parallel> !P \<longmapsto>\<^sub>ea[b] \<prec>\<^sub>e P'" by fact
  thus ?case by(rule Early_Semantics.Bang)
qed

lemma outputEq:
  fixes P  :: pi
  and   a  :: name
  and   b  :: name
  and   P' :: pi

  shows "P \<longmapsto>\<^sub>ea[b] \<prec>\<^sub>e P' = P \<longmapsto>\<^sub>la[b] \<prec>\<^sub>l P'"
by(auto intro: lateEarlyOutput earlyLateOutput)

lemma lateEarlyBoundOutput:
  fixes P  :: pi
  and   a  :: name
  and   x  :: name
  and   P' :: pi

  assumes "P \<longmapsto>\<^sub>la<\<nu>x> \<prec>\<^sub>l P'"

  shows "P \<longmapsto>\<^sub>ea<\<nu>x> \<prec>\<^sub>e P'"
proof -
  have Goal: "\<And>P a x P'. \<lbrakk>P \<longmapsto>\<^sub>la<\<nu>x> \<prec>\<^sub>l P'; x \<sharp> P\<rbrakk> \<Longrightarrow> P \<longmapsto>\<^sub>ea<\<nu>x> \<prec>\<^sub>e P'"
  proof -
    fix P a x P'
    assume "P \<longmapsto>\<^sub>l a<\<nu>x> \<prec>\<^sub>l P'" and "x \<sharp> P"
    thus "P \<longmapsto>\<^sub>ea<\<nu>x> \<prec>\<^sub>e P'"
    proof(nominal_induct rule: Late_Semantics.boundOutputInduct)
      case(Match P a x P' b)
      have "P \<longmapsto>\<^sub>e a<\<nu>x> \<prec>\<^sub>e P'" by fact
      thus ?case by(rule Early_Semantics.Match)
    next
      case(Mismatch P a x P' b c)
      have "P \<longmapsto>\<^sub>e a<\<nu>x> \<prec>\<^sub>e P'" and "b \<noteq> c" by fact+
      thus ?case by(rule Early_Semantics.Mismatch)
    next
      case(Open P a x P')
      have "P \<longmapsto>\<^sub>la[x] \<prec>\<^sub>l P'" by fact
      hence "P \<longmapsto>\<^sub>ea[x] \<prec>\<^sub>e P'" by(rule lateEarlyOutput)
      moreover have "a \<noteq> x" by fact
      ultimately show ?case by(rule Early_Semantics.Open)
    next
      case(Sum1 P Q a x P')
      have "P \<longmapsto>\<^sub>e a<\<nu>x> \<prec>\<^sub>e P'" by fact
      thus ?case by(rule Early_Semantics.Sum1)
    next
      case(Sum2 P Q a x Q')
      have "Q \<longmapsto>\<^sub>e a<\<nu>x> \<prec>\<^sub>e Q'" by fact
      thus ?case by(rule Early_Semantics.Sum2)
    next
      case(Par1 P P' Q a x)
      have "P \<longmapsto>\<^sub>e a<\<nu>x> \<prec>\<^sub>e P'" and "x \<sharp> Q" by fact+
      thus ?case by(rule Early_Semantics.Par1B)
    next
      case(Par2 P Q Q' a x)
      have "Q \<longmapsto>\<^sub>e a<\<nu>x> \<prec>\<^sub>e Q'" and "x \<sharp> P" by fact+
      thus ?case by(rule Early_Semantics.Par2B)
    next
      case(Res P P' a x y)
      have "P \<longmapsto>\<^sub>e a<\<nu>x> \<prec>\<^sub>e P'" and "y \<noteq> a" and "y \<noteq> x" by fact+
      thus ?case by(force intro: Early_Semantics.ResB)
    next
      case(Bang P a x P')
      have "P \<parallel> !P \<longmapsto>\<^sub>e a<\<nu>x> \<prec>\<^sub>e P'" by fact
      thus ?case by(rule Early_Semantics.Bang)
    qed
  qed

  have "\<exists>c::name. c \<sharp> (P, P', x)" by(blast intro: name_exists_fresh)
  then obtain c::name where cFreshP: "c \<sharp> P" and cFreshP': "c \<sharp> P'" and "c \<noteq> x"
    by(force simp add: fresh_prod)
  from assms cFreshP' have "P \<longmapsto>\<^sub>la<\<nu>c> \<prec>\<^sub>l ([(x, c)] \<bullet> P')"
    by(simp add: Late_Semantics.alphaBoundResidual)
  hence "P \<longmapsto>\<^sub>e a<\<nu>c> \<prec>\<^sub>e ([(x, c)] \<bullet> P')" using cFreshP
    by(rule Goal)
  moreover from cFreshP' \<open>c \<noteq> x\<close> have "x \<sharp> [(x, c)] \<bullet> P'" by(simp add: name_fresh_left name_calc)
  ultimately show ?thesis by(simp add: Early_Semantics.alphaBoundOutput name_swap)
qed

lemma earlyLateBoundOutput:
  fixes P  :: pi
  and   a  :: name
  and   x  :: name
  and   P' :: pi

  assumes "P \<longmapsto>\<^sub>ea<\<nu>x> \<prec>\<^sub>e P'"

  shows "P \<longmapsto>\<^sub>la<\<nu>x> \<prec>\<^sub>l P'"
proof -
  have Goal: "\<And>P a x P'. \<lbrakk>P \<longmapsto>\<^sub>ea<\<nu>x> \<prec>\<^sub>e P'; x \<sharp> P\<rbrakk> \<Longrightarrow> P \<longmapsto>\<^sub>la<\<nu>x> \<prec>\<^sub>l P'"
  proof -
    fix P a x P'
    assume "P \<longmapsto>\<^sub>e a<\<nu>x> \<prec> P'" and "x \<sharp> P"
    thus "P \<longmapsto>\<^sub>la<\<nu>x> \<prec>\<^sub>l P'"
    proof(nominal_induct rule: Early_Semantics.boundOutputInduct)
      case(Match P a x P' b)
      have "P \<longmapsto>\<^sub>l a<\<nu>x> \<prec> P'" by fact
      thus ?case by(rule Late_Semantics.Match)
    next
      case(Mismatch P a x P' b c)
      have "P \<longmapsto>\<^sub>l a<\<nu>x> \<prec> P'" and "b \<noteq> c" by fact+
      thus ?case by(rule Late_Semantics.Mismatch)
    next
      case(Open P a x P')
      have "P \<longmapsto>\<^sub>ea[x] \<prec>\<^sub>e P'" by fact
      hence "P \<longmapsto>\<^sub>la[x] \<prec>\<^sub>l P'" by(rule earlyLateOutput)
      moreover have "a \<noteq> x" by fact
      ultimately show ?case by(rule Late_Semantics.Open)
    next
      case(Sum1 P Q a x P')
      have "P \<longmapsto>\<^sub>l a<\<nu>x> \<prec>\<^sub>l P'" by fact
      thus ?case by(rule Late_Semantics.Sum1)
    next
      case(Sum2 P Q a x Q')
      have "Q \<longmapsto>\<^sub>l a<\<nu>x> \<prec>\<^sub>l Q'" by fact
      thus ?case by(rule Late_Semantics.Sum2)
    next
      case(Par1 P P' Q a x)
      have "P \<longmapsto>\<^sub>l a<\<nu>x> \<prec>\<^sub>l P'" and "x \<sharp> Q" by fact+
      thus ?case by(rule Late_Semantics.Par1B)
    next
      case(Par2 P Q Q' a x)
      have "Q \<longmapsto>\<^sub>l a<\<nu>x> \<prec>\<^sub>l Q'" and "x \<sharp> P" by fact+
      thus ?case by(rule Late_Semantics.Par2B)
    next
      case(Res P P' a x y)
      have "P \<longmapsto>\<^sub>l a<\<nu>x> \<prec>\<^sub>l P'" and "y \<noteq> a" and "y \<noteq> x" by fact+
      thus ?case by(force intro: Late_Semantics.ResB)
    next
      case(Bang P a x P')
      have "P \<parallel> !P \<longmapsto>\<^sub>l a<\<nu>x> \<prec> P'" by fact
      thus ?case by(rule Late_Semantics.Bang)
    qed
  qed

  have "\<exists>c::name. c \<sharp> (P, P', x)" by(blast intro: name_exists_fresh)
  then obtain c::name where cFreshP: "c \<sharp> P" and cFreshP': "c \<sharp> P'" and "c \<noteq> x"
    by(force simp add: fresh_prod)
  from assms cFreshP' have "P \<longmapsto>\<^sub>ea<\<nu>c> \<prec>\<^sub>e ([(x, c)] \<bullet> P')"
    by(simp add: Early_Semantics.alphaBoundOutput)
  hence "P \<longmapsto>\<^sub>l a<\<nu>c> \<prec>\<^sub>l ([(x, c)] \<bullet> P')" using cFreshP
    by(rule Goal)
  moreover from cFreshP' \<open>c \<noteq> x\<close> have "x \<sharp> [(x, c)] \<bullet> P'" by(simp add: name_fresh_left name_calc)
  ultimately show ?thesis by(simp add: Late_Semantics.alphaBoundResidual name_swap)
qed

lemma BoundOutputEq:
  fixes P  :: pi
  and   a  :: name
  and   x  :: name
  and   P' :: pi

  shows "P \<longmapsto>\<^sub>ea<\<nu>x> \<prec>\<^sub>e P' = P \<longmapsto>\<^sub>la<\<nu>x> \<prec>\<^sub>l P'"
by(auto intro: earlyLateBoundOutput lateEarlyBoundOutput)

lemma lateEarlyInput:
  fixes P  :: pi
  and   a  :: name
  and   x  :: name
  and   P' :: pi
  and   u  :: name

  assumes PTrans: "P \<longmapsto>\<^sub>l a<x> \<prec>\<^sub>l P'"

  shows "P \<longmapsto>\<^sub>ea<u> \<prec>\<^sub>e (P'[x::=u])"
proof -
  have Goal: "\<And>P a x P' u. \<lbrakk>P \<longmapsto>\<^sub>l a<x> \<prec>\<^sub>l P'; x \<sharp> P\<rbrakk> \<Longrightarrow> P \<longmapsto>\<^sub>e a<u> \<prec>\<^sub>e (P'[x::=u])"
  proof -
    fix P a x P' u
    assume "P \<longmapsto>\<^sub>l a<x> \<prec>\<^sub>l P'" and "x \<sharp> P"
    thus "P \<longmapsto>\<^sub>e a<u> \<prec>\<^sub>e (P'[x::=u])"
    proof(nominal_induct avoiding: u rule: Late_Semantics.inputInduct)
      case(Input a x P)
      thus ?case by(rule Early_Semantics.Input)
    next
      case(Match P a x P' b u)
      have "P \<longmapsto>\<^sub>ea<u> \<prec>\<^sub>e (P'[x::=u])" by fact
      thus ?case by(rule Early_Semantics.Match)
    next
      case(Mismatch P a x P' b c u)
      have "P \<longmapsto>\<^sub>ea<u> \<prec>\<^sub>e (P'[x::=u])" by fact
      moreover have "b\<noteq>c" by fact
      ultimately show ?case by(rule Early_Semantics.Mismatch)
    next
      case(Sum1 P Q a x P')
      have "P \<longmapsto>\<^sub>ea<u> \<prec>\<^sub>e (P'[x::=u])" by fact
      thus ?case by(rule Early_Semantics.Sum1)
    next
      case(Sum2 P Q a x Q')
      have "Q \<longmapsto>\<^sub>ea<u> \<prec>\<^sub>e (Q'[x::=u])" by fact
      thus ?case by(rule Early_Semantics.Sum2)
    next
      case(Par1 P P' Q a x)
      have "P \<longmapsto>\<^sub>ea<u> \<prec>\<^sub>e (P'[x::=u])" by fact
      hence "P \<parallel> Q \<longmapsto>\<^sub>ea<u> \<prec>\<^sub>e (P'[x::=u] \<parallel> Q)" by(rule Early_Semantics.Par1F)
      moreover have "x \<sharp> Q" by fact
      ultimately show ?case by(simp add: forget)
    next
      case(Par2 P Q Q' a x)
      have "Q \<longmapsto>\<^sub>ea<u> \<prec>\<^sub>e (Q'[x::=u])" by fact
      hence "P \<parallel> Q \<longmapsto>\<^sub>ea<u> \<prec>\<^sub>e (P \<parallel> Q'[x::=u])" by(rule Early_Semantics.Par2F)
      moreover have "x \<sharp> P" by fact
      ultimately show ?case by(simp add: forget)
    next
      case(Res P P' a x y u)
      have "P \<longmapsto>\<^sub>ea<u> \<prec>\<^sub>e (P'[x::=u])" and "y \<noteq> a" and yinequ: "y \<sharp> u" by fact+
      hence "<\<nu>y>P \<longmapsto>\<^sub>ea<u> \<prec>\<^sub>e <\<nu>y>(P'[x::=u])" by(force intro: Early_Semantics.ResF)
      moreover have "y \<noteq> x" by fact
      ultimately show ?case using yinequ by simp
    next
      case(Bang P a x P' u)
      have "P \<parallel> !P \<longmapsto>\<^sub>ea<u> \<prec>\<^sub>e (P'[x::=u])" by fact
      thus ?case by(rule Early_Semantics.Bang)
    qed
  qed

  have "\<exists>c::name. c \<sharp> (P, P')" by(blast intro: name_exists_fresh)
  then obtain c::name where cFreshP: "c \<sharp> P" and cFreshP': "c \<sharp> P'"
    by(force simp add: fresh_prod)
  from assms cFreshP' have "P \<longmapsto>\<^sub>la<c> \<prec>\<^sub>l ([(x, c)] \<bullet> P')"
    by(simp add: Late_Semantics.alphaBoundResidual)
  hence "P \<longmapsto>\<^sub>e a<u> \<prec>\<^sub>e ([(x, c)] \<bullet> P')[c::=u]" using cFreshP
    by(rule Goal)
  with cFreshP' show ?thesis by(simp add: renaming name_swap)
qed

lemma earlyLateInput:
  fixes P  :: pi
  and   a  :: name
  and   x  :: name
  and   P' :: pi
  and   u  :: name
  and   C  :: "'a::fs_name"

  assumes "P \<longmapsto>\<^sub>ea<u> \<prec>\<^sub>e P'"
  and     "x \<sharp> P"

  shows "\<exists>P''. P \<longmapsto>\<^sub>la<x> \<prec>\<^sub>l P'' \<and> P' = P''[x::=u]"
proof -
  {
    fix P a u P'
    assume "P \<longmapsto>\<^sub>ea<u> \<prec>\<^sub>e P'"
    hence "\<exists>P'' x. P \<longmapsto>\<^sub>la<x> \<prec>\<^sub>l P'' \<and> P' = P''[x::=u]"
    proof(nominal_induct rule: Early_Semantics.inputInduct)
      case(cInput a x P u)
      have "a<x>.P \<longmapsto>\<^sub>la<x> \<prec> P" by(rule Late_Semantics.Input)
      thus ?case by blast
    next
      case(cMatch P a u P' b)
      have "\<exists>P'' x. P \<longmapsto>\<^sub>la<x> \<prec> P'' \<and> P' = P''[x::=u]" by fact
      then obtain P'' x where PTrans: "P \<longmapsto>\<^sub>la<x> \<prec> P''" and P'eqP'': "P' = P''[x::=u]" by blast
      from PTrans have "[b\<frown>b]P \<longmapsto>\<^sub>la<x> \<prec> P''" by(rule Late_Semantics.Match)
      with P'eqP'' show ?case by blast
    next
      case(cMismatch P a u P' b c)
      have "\<exists>P'' x. P \<longmapsto>\<^sub>la<x> \<prec> P'' \<and> P' = P''[x::=u]" by fact
      then obtain P'' x where PTrans: "P \<longmapsto>\<^sub>la<x> \<prec> P''" and P'eqP'': "P' = P''[x::=u]" by blast
      have "b \<noteq> c" by fact
      with PTrans have "[b\<noteq>c]P \<longmapsto>\<^sub>la<x> \<prec> P''" by(rule Late_Semantics.Mismatch)
      with P'eqP'' show ?case by blast
    next
      case(cSum1 P a u P' Q)
      have "\<exists>P'' x. P \<longmapsto>\<^sub>la<x> \<prec> P'' \<and> P' = P''[x::=u]" by fact
      then obtain P'' x where PTrans: "P \<longmapsto>\<^sub>la<x> \<prec> P''" and P'eqP'': "P' = P''[x::=u]" by blast
      from PTrans have "P \<oplus> Q \<longmapsto>\<^sub>la<x> \<prec> P''" by(rule Late_Semantics.Sum1)
      with P'eqP'' show ?case by blast
    next
      case(cSum2 Q a u Q' P)
      have "\<exists>Q'' x. Q \<longmapsto>\<^sub>la<x> \<prec> Q'' \<and> Q' = Q''[x::=u]" by fact
      then obtain Q'' x where QTrans: "Q \<longmapsto>\<^sub>la<x> \<prec> Q''" and Q'eqQ'': "Q' = Q''[x::=u]" by blast
      from QTrans have "P \<oplus> Q \<longmapsto>\<^sub>la<x> \<prec> Q''" by(rule Late_Semantics.Sum2)
      with Q'eqQ'' show ?case by blast
    next
      case(cPar1 P a u P' Q)
      have "\<exists>P'' x. P \<longmapsto>\<^sub>la<x> \<prec> P'' \<and> P' = P''[x::=u]" by fact
      then obtain P'' x where PTrans: "P \<longmapsto>\<^sub>la<x> \<prec> P''" and P'eqP'': "P' = P''[x::=u]" by blast
      have "\<exists>c::name. c \<sharp> (Q, P'')" by(blast intro: name_exists_fresh)
      then obtain c::name where cFreshQ: "c \<sharp> Q" and cFreshP'': "c \<sharp> P''" by(force simp add: fresh_prod)
      from PTrans cFreshP'' have "P \<longmapsto>\<^sub>la<c> \<prec> [(x, c)] \<bullet> P''" by(simp add: Late_Semantics.alphaBoundResidual)
      hence "P \<parallel> Q \<longmapsto>\<^sub>la<c> \<prec> ([(x, c)] \<bullet> P'') \<parallel> Q" using \<open>c \<sharp> Q\<close> by(rule Late_Semantics.Par1B)
      moreover from cFreshQ cFreshP'' P'eqP'' have "P' \<parallel> Q = (([(x, c)] \<bullet> P'') \<parallel> Q)[c::=u]"
        by(simp add: forget renaming name_swap)
      ultimately show ?case by blast
    next
      case(cPar2 Q a u Q' P)
      have "\<exists>Q'' x. Q \<longmapsto>\<^sub>la<x> \<prec> Q'' \<and> Q' = Q''[x::=u]" by fact
      then obtain Q'' x where QTrans: "Q \<longmapsto>\<^sub>la<x> \<prec> Q''" and Q'eqQ'': "Q' = Q''[x::=u]" by blast
      have "\<exists>c::name. c \<sharp> (P, Q'')" by(blast intro: name_exists_fresh)
      then obtain c::name where cFreshP: "c \<sharp> P" and cFreshQ'': "c \<sharp> Q''" by(force simp add: fresh_prod)
      from QTrans cFreshQ'' have "Q \<longmapsto>\<^sub>la<c> \<prec> [(x, c)] \<bullet> Q''" by(simp add: Late_Semantics.alphaBoundResidual)
      hence "P \<parallel> Q \<longmapsto>\<^sub>la<c> \<prec> P \<parallel> ([(x, c)] \<bullet> Q'')" using \<open>c \<sharp> P\<close> by(rule Late_Semantics.Par2B)
      moreover from cFreshP cFreshQ'' Q'eqQ'' have "P \<parallel> Q' = (P \<parallel> ([(x, c)] \<bullet> Q''))[c::=u]"
        by(simp add: forget renaming name_swap)
      ultimately show ?case by blast
    next
      case(cRes P a u P' y)
      have "\<exists>P'' x. P \<longmapsto>\<^sub>la<x> \<prec> P'' \<and> P' = P''[x::=u]" by fact
      then obtain P'' x where PTrans: "P \<longmapsto>\<^sub>la<x> \<prec> P''" and P'eqP'': "P' = P''[x::=u]" by blast
      have yinequ: "y \<noteq> u" by fact
      have "\<exists>c::name. c \<sharp> (y, P'')" by(blast intro: name_exists_fresh)
      then obtain c::name where cineqy: "c \<noteq> y" and cFreshP'': "c \<sharp> P''" by(force simp add: fresh_prod)
      from PTrans cFreshP'' have "P \<longmapsto>\<^sub>la<c> \<prec> [(x, c)] \<bullet> P''" by(simp add: Late_Semantics.alphaBoundResidual)
      moreover have "y \<noteq> a" by fact
      ultimately have "<\<nu>y>P \<longmapsto>\<^sub>la<c> \<prec> <\<nu>y>(([(x, c)] \<bullet> P''))" using cineqy
        by(force intro: Late_Semantics.ResB)
      moreover from cineqy cFreshP'' P'eqP'' yinequ have "<\<nu>y>P' = (<\<nu>y>([(x, c)] \<bullet> P''))[c::=u]"
        by(simp add: renaming name_swap)
      ultimately show ?case by blast
    next
      case(cBang P a u P')
      have "\<exists>P'' x. P \<parallel> !P \<longmapsto>\<^sub>la<x> \<prec> P'' \<and> P' = P''[x::=u]" by fact
      then obtain P'' x where PTrans: "P \<parallel> !P \<longmapsto>\<^sub>la<x> \<prec> P''" and P'eqP'': "P' = P''[x::=u]" by blast
      from PTrans have "!P \<longmapsto>\<^sub>la<x> \<prec> P''" by(rule Late_Semantics.Bang)
      with P'eqP'' show ?case by blast
    qed
  }
  with assms obtain P'' y where PTrans: "P \<longmapsto>\<^sub>la<y> \<prec> P''" and P'eqP'': "P' = P''[y::=u]" by blast
  show ?thesis
  proof(cases "x=y")
    case True
    from PTrans P'eqP'' \<open>x = y\<close> show ?thesis by blast
  next
    case False
    from PTrans \<open>x \<noteq> y\<close> \<open>x \<sharp> P\<close> have "x \<sharp> P''" by(fastforce dest: freshBoundDerivative simp add: residual.inject)
    with PTrans have "P \<longmapsto>\<^sub>la<x> \<prec>\<^sub>l ([(x, y)] \<bullet> P'')"
      by(simp add: Late_Semantics.alphaBoundResidual)
    moreover from \<open>x \<sharp> P''\<close> have "P''[y::=u] = ([(x, y)] \<bullet> P'')[x::=u]" by(simp add: renaming name_swap)
    ultimately show ?thesis using P'eqP'' by blast
  qed
qed
(*
lemma earlyLateInput:
  fixes P  :: pi
  and   a  :: name
  and   x  :: name
  and   P' :: pi
  and   u  :: name
  and   C  :: "'a::fs_name"

  assumes PTrans: "P \<longmapsto>\<^sub>ea<u> \<prec>\<^sub>e P'"

  shows "\<exists>P'' x. P \<longmapsto>\<^sub>la<x> \<prec>\<^sub>l P'' \<and> P' = P''[x::=u] \<and> x \<sharp> C"
proof -
  have "\<And>P a u P'. P \<longmapsto>\<^sub>ea<u> \<prec>\<^sub>e P' \<Longrightarrow> \<exists>P'' x. P \<longmapsto>\<^sub>la<x> \<prec>\<^sub>l P'' \<and> P' = P''[x::=u]"
  proof -
    fix P a u P'
    assume "P \<longmapsto>\<^sub>ea<u> \<prec>\<^sub>e P'"
    thus "\<exists>P'' x. P \<longmapsto>\<^sub>la<x> \<prec>\<^sub>l P'' \<and> P' = P''[x::=u]"
    proof(nominal_induct rule: Early_Semantics.inputInduct)
      case(cInput a x P u)
      have "a<x>.P \<longmapsto>\<^sub>la<x> \<prec> P" by(rule Late_Semantics.Input)
      thus ?case by blast
    next
      case(cMatch P a u P' b)
      have "\<exists>P'' x. P \<longmapsto>\<^sub>la<x> \<prec> P'' \<and> P' = P''[x::=u]" by fact
      then obtain P'' x where PTrans: "P \<longmapsto>\<^sub>la<x> \<prec> P''" and P'eqP'': "P' = P''[x::=u]" by blast
      from PTrans have "[b\<frown>b]P \<longmapsto>\<^sub>la<x> \<prec> P''" by(rule Late_Semantics.Match)
      with P'eqP'' show ?case by blast
    next
      case(cMismatch P a u P' b c)
      have "\<exists>P'' x. P \<longmapsto>\<^sub>la<x> \<prec> P'' \<and> P' = P''[x::=u]" by fact
      then obtain P'' x where PTrans: "P \<longmapsto>\<^sub>la<x> \<prec> P''" and P'eqP'': "P' = P''[x::=u]" by blast
      have "b \<noteq> c" by fact
      with PTrans have "[b\<noteq>c]P \<longmapsto>\<^sub>la<x> \<prec> P''" by(rule Late_Semantics.Mismatch)
      with P'eqP'' show ?case by blast
    next
      case(cSum1 P a u P' Q)
      have "\<exists>P'' x. P \<longmapsto>\<^sub>la<x> \<prec> P'' \<and> P' = P''[x::=u]" by fact
      then obtain P'' x where PTrans: "P \<longmapsto>\<^sub>la<x> \<prec> P''" and P'eqP'': "P' = P''[x::=u]" by blast
      from PTrans have "P \<oplus> Q \<longmapsto>\<^sub>la<x> \<prec> P''" by(rule Late_Semantics.Sum1)
      with P'eqP'' show ?case by blast
    next
      case(cSum2 Q a u Q' P)
      have "\<exists>Q'' x. Q \<longmapsto>\<^sub>la<x> \<prec> Q'' \<and> Q' = Q''[x::=u]" by fact
      then obtain Q'' x where QTrans: "Q \<longmapsto>\<^sub>la<x> \<prec> Q''" and Q'eqQ'': "Q' = Q''[x::=u]" by blast
      from QTrans have "P \<oplus> Q \<longmapsto>\<^sub>la<x> \<prec> Q''" by(rule Late_Semantics.Sum2)
      with Q'eqQ'' show ?case by blast
    next
      case(cPar1 P a u P' Q)
      have "\<exists>P'' x. P \<longmapsto>\<^sub>la<x> \<prec> P'' \<and> P' = P''[x::=u]" by fact
      then obtain P'' x where PTrans: "P \<longmapsto>\<^sub>la<x> \<prec> P''" and P'eqP'': "P' = P''[x::=u]" by blast
      have "\<exists>c::name. c \<sharp> (Q, P'')" by(blast intro: name_exists_fresh)
      then obtain c::name where cFreshQ: "c \<sharp> Q" and cFreshP'': "c \<sharp> P''" by(force simp add: fresh_prod)
      from PTrans cFreshP'' have "P \<longmapsto>\<^sub>la<c> \<prec> [(x, c)] \<bullet> P''" by(simp add: Late_Semantics.alphaBoundResidual)
      hence "P \<parallel> Q \<longmapsto>\<^sub>la<c> \<prec> ([(x, c)] \<bullet> P'') \<parallel> Q" using `c \<sharp> Q` by(rule Late_Semantics.Par1B)
      moreover from cFreshQ cFreshP'' P'eqP'' have "P' \<parallel> Q = (([(x, c)] \<bullet> P'') \<parallel> Q)[c::=u]"
        by(simp add: forget renaming name_swap)
      ultimately show ?case by blast
    next
      case(cPar2 Q a u Q' P)
      have "\<exists>Q'' x. Q \<longmapsto>\<^sub>la<x> \<prec> Q'' \<and> Q' = Q''[x::=u]" by fact
      then obtain Q'' x where QTrans: "Q \<longmapsto>\<^sub>la<x> \<prec> Q''" and Q'eqQ'': "Q' = Q''[x::=u]" by blast
      have "\<exists>c::name. c \<sharp> (P, Q'')" by(blast intro: name_exists_fresh)
      then obtain c::name where cFreshP: "c \<sharp> P" and cFreshQ'': "c \<sharp> Q''" by(force simp add: fresh_prod)
      from QTrans cFreshQ'' have "Q \<longmapsto>\<^sub>la<c> \<prec> [(x, c)] \<bullet> Q''" by(simp add: Late_Semantics.alphaBoundResidual)
      hence "P \<parallel> Q \<longmapsto>\<^sub>la<c> \<prec> P \<parallel> ([(x, c)] \<bullet> Q'')" using `c \<sharp> P` by(rule Late_Semantics.Par2B)
      moreover from cFreshP cFreshQ'' Q'eqQ'' have "P \<parallel> Q' = (P \<parallel> ([(x, c)] \<bullet> Q''))[c::=u]"
        by(simp add: forget renaming name_swap)
      ultimately show ?case by blast
    next
      case(cRes P a u P' y)
      have "\<exists>P'' x. P \<longmapsto>\<^sub>la<x> \<prec> P'' \<and> P' = P''[x::=u]" by fact
      then obtain P'' x where PTrans: "P \<longmapsto>\<^sub>la<x> \<prec> P''" and P'eqP'': "P' = P''[x::=u]" by blast
      have yinequ: "y \<noteq> u" by fact
      have "\<exists>c::name. c \<sharp> (y, P'')" by(blast intro: name_exists_fresh)
      then obtain c::name where cineqy: "c \<noteq> y" and cFreshP'': "c \<sharp> P''" by(force simp add: fresh_prod)
      from PTrans cFreshP'' have "P \<longmapsto>\<^sub>la<c> \<prec> [(x, c)] \<bullet> P''" by(simp add: Late_Semantics.alphaBoundResidual)
      moreover have "y \<noteq> a" by fact
      ultimately have "<\<nu>y>P \<longmapsto>\<^sub>la<c> \<prec> <\<nu>y>(([(x, c)] \<bullet> P''))" using cineqy
        by(force intro: Late_Semantics.ResB)
      moreover from cineqy cFreshP'' P'eqP'' yinequ have "<\<nu>y>P' = (<\<nu>y>([(x, c)] \<bullet> P''))[c::=u]"
        by(simp add: renaming name_swap)
      ultimately show ?case by blast
    next
      case(cBang P a u P')
      have "\<exists>P'' x. P \<parallel> !P \<longmapsto>\<^sub>la<x> \<prec> P'' \<and> P' = P''[x::=u]" by fact
      then obtain P'' x where PTrans: "P \<parallel> !P \<longmapsto>\<^sub>la<x> \<prec> P''" and P'eqP'': "P' = P''[x::=u]" by blast
      from PTrans have "!P \<longmapsto>\<^sub>la<x> \<prec> P''" by(rule Late_Semantics.Bang)
      with P'eqP'' show ?case by blast
    qed
  qed
  with PTrans obtain P'' x where PTrans: "P \<longmapsto>\<^sub>la<x> \<prec> P''" and P'eqP'': "P' = P''[x::=u]" by blast
  have "\<exists>c::name. c \<sharp> (P'', C)" by(blast intro: name_exists_fresh)
  then obtain c::name where cFreshP'': "c \<sharp> P''" and cFreshC: "c \<sharp> C" by force
  from cFreshP'' PTrans have "P \<longmapsto>\<^sub>la<c> \<prec>\<^sub>l ([(x, c)] \<bullet> P'')"
    by(simp add: Late_Semantics.alphaBoundResidual)
  moreover from cFreshP'' have "P''[x::=u] = ([(x, c)] \<bullet> P'')[c::=u]" by(simp add: renaming name_swap)
  ultimately show ?thesis using P'eqP'' cFreshC by blast
qed
*)
lemma lateEarlyTau:
  fixes P  :: pi
  and   P' :: pi

  assumes "P \<longmapsto>\<^sub>l\<tau> \<prec>\<^sub>l P'"

  shows "P \<longmapsto>\<^sub>e\<tau> \<prec>\<^sub>e P'"
using assms
proof(nominal_induct rule: Late_Semantics.tauInduct)
  case(Tau P)
  thus ?case by(rule Early_Semantics.Tau)
next
  case(Match P P' a)
  have "P \<longmapsto>\<^sub>e\<tau> \<prec>\<^sub>e P'" by fact
  thus "[a\<frown>a]P \<longmapsto>\<^sub>e\<tau> \<prec>\<^sub>e P'" by(rule Early_Semantics.Match)
next
  case(Mismatch P P' a b)
  have "P \<longmapsto>\<^sub>e\<tau> \<prec>\<^sub>e P'" by fact
  moreover have "a \<noteq> b" by fact
  ultimately show "[a\<noteq>b]P \<longmapsto>\<^sub>e\<tau> \<prec>\<^sub>e P'" by(rule Early_Semantics.Mismatch)
next
  case(Sum1 P P' Q)
  have "P \<longmapsto>\<^sub>e\<tau> \<prec>\<^sub>e P'" by fact
  thus "P \<oplus> Q \<longmapsto>\<^sub>e\<tau> \<prec>\<^sub>e P'" by(rule Early_Semantics.Sum1)
next
  case(Sum2 Q Q' P)
  have "Q \<longmapsto>\<^sub>e\<tau> \<prec>\<^sub>e Q'" by fact
  thus "P \<oplus> Q \<longmapsto>\<^sub>e\<tau> \<prec>\<^sub>e Q'" by(rule Early_Semantics.Sum2)
next
  case(Par1 P P' Q)
  have "P \<longmapsto>\<^sub>e\<tau> \<prec>\<^sub>e P'" by fact
  thus "P \<parallel> Q \<longmapsto>\<^sub>e\<tau> \<prec>\<^sub>e P' \<parallel> Q" by(rule Early_Semantics.Par1F)
next
  case(Par2 Q Q' P)
  have "Q \<longmapsto>\<^sub>e\<tau> \<prec>\<^sub>e Q'" by fact
  thus "P \<parallel> Q \<longmapsto>\<^sub>e\<tau> \<prec>\<^sub>e P \<parallel> Q'" by(rule Early_Semantics.Par2F)
next
  case(Comm1 P a x P' Q b Q')
  have "P \<longmapsto>\<^sub>ea<b> \<prec>\<^sub>e P'[x::=b]"
  proof -
    have "P \<longmapsto>\<^sub>l a<x> \<prec> P'" by fact
    thus ?thesis by(rule lateEarlyInput)
  qed
  moreover have "Q \<longmapsto>\<^sub>ea[b] \<prec>\<^sub>e Q'"
  proof -
    have "Q \<longmapsto>\<^sub>la[b] \<prec>\<^sub>l Q'" by fact
    thus ?thesis by(rule lateEarlyOutput)
  qed
  ultimately show ?case by(rule Early_Semantics.Comm1)
next
  case(Comm2 P a b P' Q x Q')
  have "P \<longmapsto>\<^sub>ea[b] \<prec>\<^sub>e P'"
  proof -
    have "P \<longmapsto>\<^sub>la[b] \<prec>\<^sub>l P'" by fact
    thus ?thesis by(rule lateEarlyOutput)
  qed
  moreover have "Q \<longmapsto>\<^sub>ea<b> \<prec>\<^sub>e Q'[x::=b]"
  proof -
    have "Q \<longmapsto>\<^sub>la<x> \<prec>\<^sub>l Q'" by fact
    thus ?thesis by(rule lateEarlyInput)
  qed
  ultimately show ?case by(rule Early_Semantics.Comm2)
next
  case(Close1 P a x P' Q y Q')
  have "P \<longmapsto>\<^sub>ea<y> \<prec>\<^sub>e P'[x::=y]"
  proof -
    have "P \<longmapsto>\<^sub>l a<x> \<prec> P'" by fact
    thus ?thesis by(rule lateEarlyInput)
  qed
  moreover have "Q \<longmapsto>\<^sub>ea<\<nu>y> \<prec> Q'"
  proof -
    have "Q \<longmapsto>\<^sub>la<\<nu>y> \<prec>\<^sub>l Q'" by fact
    thus ?thesis by(rule lateEarlyBoundOutput)
  qed
  moreover have "y \<sharp> P" by fact
  ultimately show ?case by(rule Early_Semantics.Close1)
next
  case(Close2 P a y P' Q x Q')
  have "P \<longmapsto>\<^sub>ea<\<nu>y> \<prec> P'"
  proof -
    have "P \<longmapsto>\<^sub>la<\<nu>y> \<prec>\<^sub>l P'" by fact
    thus ?thesis by(rule lateEarlyBoundOutput)
  qed
  moreover have "Q \<longmapsto>\<^sub>ea<y> \<prec>\<^sub>e Q'[x::=y]"
  proof -
    have "Q \<longmapsto>\<^sub>la<x> \<prec>\<^sub>l Q'" by fact
    thus ?thesis by(rule lateEarlyInput)
  qed
  moreover have "y \<sharp> Q" by fact
  ultimately show ?case by(rule Early_Semantics.Close2)
next
  case(Res P P' x)
  have "P \<longmapsto>\<^sub>e\<tau> \<prec>\<^sub>e P'" by fact
  thus ?case by(force intro: Early_Semantics.ResF)
next
  case(Bang P P')
  have "P \<parallel> !P \<longmapsto>\<^sub>e\<tau> \<prec>\<^sub>e P'" by fact
  thus ?case by(rule Early_Semantics.Bang)
qed

lemma earlyLateTau:
  fixes P  :: pi
  and   P' :: pi

  assumes "P \<longmapsto>\<^sub>e\<tau> \<prec>\<^sub>e P'"

  shows "P \<longmapsto>\<^sub>l\<tau> \<prec>\<^sub>l P'"
using assms
proof(nominal_induct rule: Early_Semantics.tauInduct)
  case(Tau P)
  thus ?case by(rule Late_Semantics.Tau)
next
  case(Match P P' a)
  have "P \<longmapsto>\<^sub>l\<tau> \<prec>\<^sub>l P'" by fact
  thus ?case by(rule Late_Semantics.Match)
next
  case(Mismatch P P' a b)
  have "P \<longmapsto>\<^sub>l\<tau> \<prec>\<^sub>l P'" by fact
  moreover have "a \<noteq> b" by fact
  ultimately show ?case by(rule Late_Semantics.Mismatch)
next
  case(Sum1 P P' Q)
  have "P \<longmapsto>\<^sub>l\<tau> \<prec>\<^sub>l P'" by fact
  thus ?case by(rule Late_Semantics.Sum1)
next
  case(Sum2 Q Q' P)
  have "Q \<longmapsto>\<^sub>l\<tau> \<prec>\<^sub>l Q'" by fact
  thus ?case by(rule Late_Semantics.Sum2)
next
  case(Par1 P P' Q)
  have "P \<longmapsto>\<^sub>l\<tau> \<prec>\<^sub>l P'" by fact
  thus ?case by(rule Late_Semantics.Par1F)
next
  case(Par2 Q Q' P)
  have "Q \<longmapsto>\<^sub>l\<tau> \<prec>\<^sub>l Q'" by fact
  thus ?case by(rule Late_Semantics.Par2F)
next
  case(Comm1 P a b P' Q Q')
  have "P \<longmapsto>\<^sub>ea<b> \<prec>\<^sub>e P'" by fact
  moreover obtain x::name  where "x \<sharp> P" by(generate_fresh "name") auto
  ultimately obtain P'' where PTrans: "P \<longmapsto>\<^sub>la<x> \<prec> P''" and P'eqP'': "P' = P''[x::=b]"
    by(blast dest: earlyLateInput)
  have "Q \<longmapsto>\<^sub>ea[b] \<prec>\<^sub>e Q'" by fact
  hence "Q \<longmapsto>\<^sub>la[b] \<prec>\<^sub>l Q'" by(rule earlyLateOutput)
  with PTrans P'eqP'' show ?case
    by(blast intro: Late_Semantics.Comm1)
next
  case(Comm2 P a b P' Q Q')
  have "P \<longmapsto>\<^sub>ea[b] \<prec>\<^sub>e P'" by fact
  hence QTrans: "P \<longmapsto>\<^sub>la[b] \<prec>\<^sub>l P'" by(rule earlyLateOutput)
  have "Q \<longmapsto>\<^sub>ea<b> \<prec>\<^sub>e Q'" by fact
  moreover obtain x::name  where "x \<sharp> Q" by(generate_fresh "name") auto
  ultimately obtain Q'' x where "Q \<longmapsto>\<^sub>la<x> \<prec> Q''" and "Q' = Q''[x::=b]"
    by(blast dest: earlyLateInput)
  with QTrans show ?case
    by(blast intro: Late_Semantics.Comm2)
next
  case(Close1 P a x P' Q Q')
  have  "P \<longmapsto>\<^sub>ea<x> \<prec>\<^sub>e P'" and "x \<sharp> P" by fact+
  then obtain P'' where "P \<longmapsto>\<^sub>la<x> \<prec> P''" and "P' = P''[x::=x]"
    by(blast dest: earlyLateInput)
  
  moreover have "Q \<longmapsto>\<^sub>ea<\<nu>x> \<prec>\<^sub>e Q'" by fact
  hence "Q \<longmapsto>\<^sub>la<\<nu>x> \<prec>\<^sub>l Q'" by(rule earlyLateBoundOutput)
  moreover have "x \<sharp> P" by fact
  ultimately show ?case
    by(blast intro: Late_Semantics.Close1)
next
  case(Close2 P a x P' Q Q')
  have  "P \<longmapsto>\<^sub>ea<\<nu>x> \<prec>\<^sub>e P'" by fact
  hence PTrans: "P \<longmapsto>\<^sub>la<\<nu>x> \<prec>\<^sub>l P'" by(rule earlyLateBoundOutput)

  have "Q \<longmapsto>\<^sub>ea<x> \<prec>\<^sub>e Q'" and "x \<sharp> Q" by fact+
  then obtain Q'' y where "Q \<longmapsto>\<^sub>la<x> \<prec> Q''" and "Q' = Q''[x::=x]"
    by(blast dest: earlyLateInput)
  moreover have "x \<sharp> Q" by fact
  ultimately show ?case using PTrans
    by(blast intro: Late_Semantics.Close2)
next
  case(Res P P' x)
  have  "P \<longmapsto>\<^sub>l\<tau> \<prec>\<^sub>l P'" by fact
  thus ?case by(force intro: Late_Semantics.ResF)
next
  case(Bang P P')
  have  "P \<parallel> !P \<longmapsto>\<^sub>l\<tau> \<prec>\<^sub>l P'" by fact
  thus ?case by(force intro: Late_Semantics.Bang)
qed

lemma tauEq:
  fixes P  :: pi
  and   P' :: pi

  shows "P \<longmapsto>\<^sub>e(Early_Semantics.FreeR Early_Semantics.TauR P') = P \<longmapsto>\<tau> \<prec>\<^sub>l P'"
by(auto intro: earlyLateTau lateEarlyTau)

(****************** Simulation ******************)

abbreviation simLate_judge ("_ \<leadsto>\<^sub>l[_] _" [80, 80, 80] 80) where "P \<leadsto>\<^sub>l[Rel] Q \<equiv> Strong_Late_Sim.simulation P Rel Q"
abbreviation simEarly_judge ("_ \<leadsto>\<^sub>e[_] _" [80, 80, 80] 80) where "P \<leadsto>\<^sub>e[Rel] Q \<equiv> Strong_Early_Sim.strongSimEarly P Rel Q"

lemma lateEarlySim:
  fixes P   :: pi
  and   Q   :: pi
  and   Rel :: "(pi \<times> pi) set"

  assumes PSimQ: "P \<leadsto>\<^sub>l[Rel] Q"

  shows "P \<leadsto>\<^sub>e[Rel] Q"
proof(induct rule: Strong_Early_Sim.simCases)
  case(Bound a x Q')
  have "Q \<longmapsto>\<^sub>ea<\<nu>x> \<prec>\<^sub>e Q'" by fact
  hence "Q \<longmapsto>\<^sub>la<\<nu>x> \<prec>\<^sub>l Q'" by(rule earlyLateBoundOutput)
  moreover have "x \<sharp> P" by fact
  ultimately obtain P' where PTrans: "P \<longmapsto>\<^sub>la<\<nu>x> \<prec>\<^sub>l P'" and P'RelQ': "(P', Q') \<in> Rel" using PSimQ
    by(force dest: Strong_Late_Sim.simE simp add: derivative_def)
  from PTrans have "P \<longmapsto>\<^sub>ea<\<nu>x> \<prec>\<^sub>e P'" by(rule lateEarlyBoundOutput)
  with P'RelQ' show ?case by blast
next
  case(Free \<alpha> Q')
  have "Q \<longmapsto>\<^sub>e Early_Semantics.residual.FreeR \<alpha> Q'" by fact
  thus ?case
  proof(nominal_induct \<alpha> rule: freeRes.strong_induct)
    case(InputR a u)
    obtain x::name where "x \<sharp> Q" and "x \<sharp> P" by(generate_fresh "name") auto
    with \<open>Q \<longmapsto>\<^sub>ea<u> \<prec>\<^sub>e Q'\<close> obtain Q'' where QTrans: "Q \<longmapsto>\<^sub>la<x> \<prec>\<^sub>l Q''" and Q'eqQ'': "Q' = Q''[x::=u]"
      by(blast dest: earlyLateInput)
    from PSimQ QTrans \<open>x \<sharp> P\<close>  obtain P' where PTrans: "P \<longmapsto>\<^sub>la<x> \<prec> P'"
                                          and P'RelQ': "(P'[x::=u], Q''[x::=u]) \<in> Rel"
      by(force dest: Strong_Late_Sim.simE simp add: derivative_def)
    from PTrans have "P \<longmapsto>\<^sub>ea<u> \<prec>\<^sub>e P'[x::=u]" by(rule lateEarlyInput)
    with P'RelQ' Q'eqQ'' show "\<exists>P'. P \<longmapsto>\<^sub>ea<u> \<prec>\<^sub>e P' \<and> (P', Q') \<in> Rel" by blast
  next
    case(OutputR a b)
    from \<open>Q \<longmapsto>\<^sub>ea[b] \<prec>\<^sub>e Q'\<close> have "Q \<longmapsto>\<^sub>la[b] \<prec>\<^sub>l Q'" by(rule earlyLateOutput)
    with PSimQ obtain P' where PTrans: "P \<longmapsto>\<^sub>la[b] \<prec>\<^sub>l P'" and P'RelQ': "(P', Q') \<in> Rel"
      by(blast dest: Strong_Late_Sim.simE)
    from PTrans have "P \<longmapsto>\<^sub>ea[b] \<prec>\<^sub>e P'" by(rule lateEarlyOutput)
    with P'RelQ' show "\<exists>P'. P \<longmapsto>\<^sub>ea[b] \<prec>\<^sub>e P' \<and> (P', Q') \<in> Rel"  by blast
  next
    case TauR
    from \<open>Q \<longmapsto>\<^sub>e\<tau> \<prec>\<^sub>e Q'\<close> have "Q \<longmapsto>\<^sub>l\<tau> \<prec>\<^sub>l Q'" by(rule earlyLateTau)
    with PSimQ obtain P' where PTrans: "P \<longmapsto>\<^sub>l\<tau> \<prec>\<^sub>l P'" and P'RelQ': "(P', Q') \<in> Rel"
      by(blast dest: Strong_Late_Sim.simE)
    from PTrans have "P \<longmapsto>\<^sub>e\<tau> \<prec>\<^sub>e P'" by(rule lateEarlyTau)
    with P'RelQ' show "\<exists>P'. P \<longmapsto>\<^sub>e\<tau> \<prec>\<^sub>e P' \<and> (P', Q') \<in> Rel"  by blast
  qed
qed

(*************** Bisimulation ***************)

abbreviation bisimLate_judge ("_ \<sim>\<^sub>l _" [80, 80] 80) where "P \<sim>\<^sub>l Q \<equiv> (P, Q) \<in> Strong_Late_Bisim.bisim"
abbreviation bisimEarly_judge ("_ \<sim>\<^sub>e _" [80, 80] 80) where "P \<sim>\<^sub>e Q \<equiv> (P, Q) \<in> Strong_Early_Bisim.bisim"

lemma lateEarlyBisim:
  fixes P :: pi
  and   Q :: pi

  assumes "P \<sim>\<^sub>l Q"

  shows "P \<sim>\<^sub>e Q"
using assms
by(coinduct rule: Strong_Early_Bisim.weak_coinduct)
  (auto dest: Strong_Late_Bisim.bisimE Strong_Late_Bisim.symmetric intro: lateEarlySim)


(*************** Congruence ***************)

abbreviation congLate_judge ("_ \<sim>\<^sup>s\<^sub>l _" [80, 80] 80) where "P \<sim>\<^sup>s\<^sub>l Q \<equiv> (P, Q) \<in> (substClosed Strong_Late_Bisim.bisim)"
abbreviation congEarly_judge ("_ \<sim>\<^sup>s\<^sub>e _" [80, 80] 80) where "P \<sim>\<^sup>s\<^sub>e Q \<equiv> (P, Q) \<in> (substClosed Strong_Early_Bisim.bisim)"

lemma lateEarlyCong:
  fixes P :: pi
  and   Q :: pi

  assumes "P \<sim>\<^sup>s\<^sub>l Q"

  shows "P \<sim>\<^sup>s\<^sub>e Q"
using assms
by(auto simp add: substClosed_def intro: lateEarlyBisim)

lemma earlyCongStructCong:
  fixes P :: pi
  and   Q :: pi

  assumes "P \<equiv>\<^sub>s Q"

  shows "P \<sim>\<^sup>s\<^sub>e Q"
using assms lateEarlyCong bisimSubstStructCong
by blast


lemma earlyBisimStructCong:
  fixes P :: pi
  and   Q :: pi

  assumes "P \<equiv>\<^sub>s Q"

  shows "P \<sim>\<^sub>e Q"
using assms lateEarlyBisim structCongBisim
by blast

end
