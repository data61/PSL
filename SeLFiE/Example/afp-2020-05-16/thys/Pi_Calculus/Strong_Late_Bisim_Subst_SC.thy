(* 
   Title: The pi-calculus   
   Author/Maintainer: Jesper Bengtson (jebe.dk), 2012
*)
theory Strong_Late_Bisim_Subst_SC
  imports Strong_Late_Bisim_Subst_Pres Strong_Late_Bisim_SC
begin

lemma matchId:
  fixes a :: name
  and   P :: pi

  shows "[a\<frown>a]P \<sim>\<^sup>s P"
by(auto simp add: substClosed_def intro: Strong_Late_Bisim_SC.matchId)

lemma mismatchNil:
  fixes a :: name
  and   P :: pi
  
  shows "[a\<noteq>a]P \<sim>\<^sup>s \<zero>"
by(auto simp add: substClosed_def intro: Strong_Late_Bisim_SC.mismatchNil)

lemma scopeFresh:
  fixes P :: pi
  and   x :: name

  assumes xFreshP: "x \<sharp> P"

  shows "<\<nu>x>P \<sim>\<^sup>s P"
proof(auto simp add: substClosed_def)
  fix s :: "(name \<times> name) list"

  have "\<exists>c::name. c \<sharp> (P, s)" by(blast intro: name_exists_fresh)
  then obtain c::name where cFreshP: "c \<sharp> P" and cFreshs: "c \<sharp> s" by(force simp add: fresh_prod)

  have "<\<nu>x>P = <\<nu>c>P"
  proof -
    from cFreshP have "<\<nu>x>P = <\<nu>c>([(x, c)] \<bullet> P)" by(simp add: alphaRes)
    with cFreshP xFreshP show ?thesis by(simp add: name_fresh_fresh)
  qed

  with cFreshP cFreshs show "(<\<nu>x>P)[<s>] \<sim> P[<s>]"
    by(force intro: Strong_Late_Bisim_SC.scopeFresh)
qed

lemma resComm:
  fixes P :: pi
  and   x :: name
  and   y :: name

  shows "<\<nu>x><\<nu>y>P \<sim>\<^sup>s <\<nu>y><\<nu>x>P"
proof(cases "x=y")
  assume xeqy: "x=y"
  have "P \<sim>\<^sup>s P" by(rule Strong_Late_Bisim_Subst.reflexive)
  hence "<\<nu>x>P \<sim>\<^sup>s <\<nu>x>P" by(rule resPres)
  hence "<\<nu>x><\<nu>x>P \<sim>\<^sup>s <\<nu>x><\<nu>x>P" by(rule resPres)
  with xeqy show ?thesis by simp
next
  assume xineqy: "x \<noteq> y"
  show ?thesis
  proof(auto simp add: substClosed_def)
    fix s::"(name \<times> name) list"
    
    have "\<exists>c::name. c \<sharp> (P, s, y)" by(blast intro: name_exists_fresh)
    then obtain c::name where cFreshP: "c \<sharp> P" and cFreshs: "c \<sharp> s" and cineqy: "c \<noteq> y"
      by(force simp add: fresh_prod)
    
    have "\<exists>d::name. d \<sharp> (P, s, c, x, y)" by (blast intro: name_exists_fresh)
    then obtain d::name where dFreshP: "d \<sharp> P" and dFreshs: "d \<sharp> s" and dineqc: "d \<noteq> c"
                          and dineqx: "d \<noteq> x" and dineqy: "d \<noteq> y"
      by(force simp add: fresh_prod)

    have "<\<nu>x><\<nu>y>P = <\<nu>c><\<nu>d>([(x, c)] \<bullet> [(y, d)] \<bullet> P)"
    proof -
      from cineqy cFreshP have cFreshyP: "c \<sharp> <\<nu>y>P" by(simp add: name_fresh_abs)
      from dFreshP have "<\<nu>y>P = <\<nu>d>([(y, d)] \<bullet> P)" by(rule alphaRes)
      moreover from cFreshyP have "<\<nu>x><\<nu>y>P = <\<nu>c>([(x, c)] \<bullet> (<\<nu>y>P))" by(rule alphaRes)
      ultimately show ?thesis using dineqc dineqx by(simp add: name_calc)
    qed
    moreover have "<\<nu>y><\<nu>x>P = <\<nu>d><\<nu>c>([(x, c)] \<bullet> [(y, d)] \<bullet> P)"
    proof -
      from dineqx dFreshP have dFreshxP: "d \<sharp> <\<nu>x>P" by(simp add: name_fresh_abs)
      from cFreshP have "<\<nu>x>P = <\<nu>c>([(x, c)] \<bullet> P)" by(rule alphaRes)
      moreover from dFreshxP have "<\<nu>y><\<nu>x>P = <\<nu>d>([(y, d)] \<bullet> (<\<nu>x>P))" by(rule alphaRes)
      ultimately have "<\<nu>y><\<nu>x>P = <\<nu>d><\<nu>c>([(y, d)] \<bullet> [(x, c)] \<bullet> P)" using dineqc cineqy
        by(simp add: name_calc)
      thus ?thesis using dineqx dineqc cineqy xineqy
        by(subst name_perm_compose, simp add: name_calc)
    qed

    ultimately show "(<\<nu>x><\<nu>y>P)[<s>] \<sim> (<\<nu>y><\<nu>x>P)[<s>]" using cFreshs dFreshs
      by(force intro: Strong_Late_Bisim_SC.resComm)
  qed
qed

lemma sumZero:
  fixes P :: pi
  
  shows "P \<oplus> \<zero> \<sim>\<^sup>s P"
by(force simp add: substClosed_def intro: Strong_Late_Bisim_SC.sumZero)
    
lemma sumSym:
  fixes P :: pi
  and   Q :: pi

  shows "P \<oplus> Q \<sim>\<^sup>s Q \<oplus> P"
by(force simp add: substClosed_def intro: Strong_Late_Bisim_SC.sumSym)

lemma sumAssoc:
  fixes P :: pi
  and   Q :: pi
  and   R :: pi
  
  shows "(P \<oplus> Q) \<oplus> R \<sim>\<^sup>s P \<oplus> (Q \<oplus> R)"
by(force simp add: substClosed_def intro: Strong_Late_Bisim_SC.sumAssoc)

lemma sumRes:
  fixes P :: pi
  and   Q :: pi
  and   x :: name

  shows "<\<nu>x>(P \<oplus> Q) \<sim>\<^sup>s <\<nu>x>P \<oplus> <\<nu>x>Q"
proof(auto simp add: substClosed_def)
  fix s :: "(name \<times> name) list"

  have "\<exists>c::name. c \<sharp> (P, Q, s)" by(blast intro: name_exists_fresh)
  then obtain c::name where cFreshP: "c \<sharp> P" and cFreshQ: "c \<sharp> Q" and cFreshs: "c \<sharp> s"
    by(force simp add: fresh_prod)

  have "<\<nu>x>(P \<oplus> Q) = <\<nu>c>(([(x, c)] \<bullet> P) \<oplus> ([(x, c)] \<bullet> Q))"
  proof -
    from cFreshP cFreshQ have "c \<sharp> P \<oplus> Q" by simp
    hence "<\<nu>x>(P \<oplus> Q) = <\<nu>c>([(x, c)] \<bullet> (P \<oplus> Q))" by(simp add: alphaRes)
    thus ?thesis by(simp add: name_fresh_fresh)
  qed

  moreover from cFreshP have "<\<nu>x>P = <\<nu>c>([(x, c)] \<bullet> P)" by(simp add: alphaRes)
  moreover from cFreshQ have "<\<nu>x>Q = <\<nu>c>([(x, c)] \<bullet> Q)" by(simp add: alphaRes)
  
  ultimately show "(<\<nu>x>(P \<oplus> Q))[<s>] \<sim> (<\<nu>x>P)[<s>] \<oplus> (<\<nu>x>Q)[<s>]" using cFreshs
    by(force intro: Strong_Late_Bisim_SC.sumRes)
qed

lemma scopeExtSum:
  fixes P :: pi
  and   Q :: pi
  and   x :: name

  assumes xFreshP: "x \<sharp> P"

  shows "<\<nu>x>(P \<oplus> Q) \<sim>\<^sup>s P \<oplus> <\<nu>x>Q"
proof(auto simp add: substClosed_def)
  fix s :: "(name \<times> name) list"

  have "\<exists>c::name. c \<sharp> (P, Q, s)" by(blast intro: name_exists_fresh)
  then obtain c::name where cFreshP: "c \<sharp> P" and cFreshQ: "c \<sharp> Q" and cFreshs: "c \<sharp> s"
    by(force simp add: fresh_prod)

  have "<\<nu>x>(P \<oplus> Q) = <\<nu>c>(P \<oplus> ([(x, c)] \<bullet> Q))"
  proof -
    from cFreshP cFreshQ have "c \<sharp> P \<oplus> Q" by simp
    hence "<\<nu>x>(P \<oplus> Q) = <\<nu>c>([(x, c)] \<bullet> (P \<oplus> Q))" by(simp add: alphaRes)
    with xFreshP cFreshP show ?thesis by(simp add: name_fresh_fresh)
  qed

  moreover from cFreshQ have "<\<nu>x>Q = <\<nu>c>([(x, c)] \<bullet> Q)" by(simp add: alphaRes)
  
  ultimately show "(<\<nu>x>(P \<oplus> Q))[<s>] \<sim> P[<s>] \<oplus> (<\<nu>x>Q)[<s>]" using cFreshs cFreshP
    by(force intro: Strong_Late_Bisim_SC.scopeExtSum)
qed

lemma parZero:
  fixes P :: pi
  
  shows "P \<parallel> \<zero> \<sim>\<^sup>s P"
by(force simp add: substClosed_def intro: Strong_Late_Bisim_SC.parZero)

lemma parSym:
  fixes P :: pi
  and   Q :: pi

  shows "P \<parallel> Q \<sim>\<^sup>s Q \<parallel> P"
by(force simp add: substClosed_def intro: Strong_Late_Bisim_SC.parSym)

lemma parAssoc:
  fixes P :: pi
  and   Q :: pi
  and   R :: pi
  
  shows "(P \<parallel> Q) \<parallel> R \<sim>\<^sup>s P \<parallel> (Q \<parallel> R)"
  by(force simp add: substClosed_def intro: Strong_Late_Bisim_SC.parAssoc)

lemma scopeExtPar:
  fixes P :: pi
  and   Q :: pi
  and   x :: name

  assumes xFreshP: "x \<sharp> P"

  shows "<\<nu>x>(P \<parallel> Q) \<sim>\<^sup>s P \<parallel> <\<nu>x>Q"
proof(auto simp add: substClosed_def)
  fix s :: "(name \<times> name) list"

  have "\<exists>c::name. c \<sharp> (P, Q, s)" by(blast intro: name_exists_fresh)
  then obtain c::name where cFreshP: "c \<sharp> P" and cFreshQ: "c \<sharp> Q" and cFreshs: "c \<sharp> s"
    by(force simp add: fresh_prod)

  have "<\<nu>x>(P \<parallel> Q) = <\<nu>c>(P \<parallel> ([(x, c)] \<bullet> Q))"
  proof -
    from cFreshP cFreshQ have "c \<sharp> P \<parallel> Q" by simp
    hence "<\<nu>x>(P \<parallel> Q) = <\<nu>c>([(x, c)] \<bullet> (P \<parallel> Q))" by(simp add: alphaRes)
    with xFreshP cFreshP show ?thesis by(simp add: name_fresh_fresh)
  qed

  moreover from cFreshQ have "<\<nu>x>Q = <\<nu>c>([(x, c)] \<bullet> Q)" by(simp add: alphaRes)
  
  ultimately show "(<\<nu>x>(P \<parallel> Q))[<s>] \<sim> P[<s>] \<parallel> (<\<nu>x>Q)[<s>]" using cFreshs cFreshP
    by(force intro: Strong_Late_Bisim_SC.scopeExtPar)
qed

lemma scopeExtPar':
  fixes P :: pi
  and   Q :: pi
  and   x :: name

  assumes xFreshP: "x \<sharp> Q"

  shows "<\<nu>x>(P \<parallel> Q) \<sim>\<^sup>s (<\<nu>x>P) \<parallel> Q"
proof -
  have "<\<nu>x>(P \<parallel> Q) \<sim>\<^sup>s <\<nu>x>(Q \<parallel> P)" by(blast intro: parSym resPres)
  moreover from xFreshP have "<\<nu>x>(Q \<parallel> P) \<sim>\<^sup>s Q \<parallel> <\<nu>x>P" by(rule scopeExtPar)
  moreover have "Q \<parallel> <\<nu>x>P \<sim>\<^sup>s (<\<nu>x>P) \<parallel> Q" by(rule parSym)
  ultimately show ?thesis by (blast intro: transitive)
qed

lemma bangSC:
  fixes P :: pi

  shows "!P \<sim>\<^sup>s P \<parallel> !P"
by(auto simp add: substClosed_def intro: Strong_Late_Bisim_SC.bangSC)

lemma nilRes:
  fixes x :: name
  
  shows "<\<nu>x>\<zero> \<sim>\<^sup>s \<zero>"
proof(auto simp add: substClosed_def)
  fix \<sigma>::"(name \<times> name) list"
  obtain y::name where "y \<sharp> \<sigma>"
    by(generate_fresh "name") auto
  have "<\<nu>y>\<zero> \<sim> \<zero>" by (rule Strong_Late_Bisim_SC.nilRes)
  with \<open>y \<sharp> \<sigma>\<close> have "(<\<nu>y>\<zero>)[<\<sigma>>] \<sim> \<zero>" by simp
  thus "(<\<nu>x>\<zero>)[<\<sigma>>] \<sim> \<zero>"
    by(subst alphaRes[where c=y]) auto
qed

lemma resTau:
  fixes x :: name
  and   P :: pi

  shows "<\<nu>x>(\<tau>.(P)) \<sim>\<^sup>s \<tau>.(<\<nu>x>P)"
proof(auto simp add: substClosed_def)
  fix \<sigma>::"(name \<times> name) list"
  obtain y::name where "y \<sharp> P" and "y \<sharp> \<sigma>"
    by(generate_fresh "name", auto)
  have "<\<nu>y>(\<tau>.(([(x, y)] \<bullet> P)[<\<sigma>>])) \<sim> \<tau>.(<\<nu>y>(([(x, y)] \<bullet> P)[<\<sigma>>]))"
    by(rule resTau)
  with \<open>y \<sharp> \<sigma>\<close> have "(<\<nu>y>(\<tau>.([(x, y)] \<bullet> P)))[<\<sigma>>] \<sim> (\<tau>.(<\<nu>y>([(x, y)] \<bullet> P)))[<\<sigma>>]"
    by simp
  with \<open>y \<sharp> P\<close> show "(<\<nu>x>\<tau>.(P))[<\<sigma>>] \<sim> \<tau>.((<\<nu>x>P)[<\<sigma>>])"
    apply(subst alphaRes[where c=y])
    apply simp
    apply(subst alphaRes[where c=y and a=x])
    by simp+
qed

lemma resOutput:
  fixes x :: name
  and   a :: name
  and   b :: name
  and   P :: pi

  assumes "x \<noteq> a"
  and     "x \<noteq> b"

  shows "<\<nu>x>(a{b}.(P)) \<sim>\<^sup>s a{b}.(<\<nu>x>P)"
proof(auto simp add: substClosed_def)
  fix \<sigma>::"(name \<times> name) list"
  obtain y::name where "y \<sharp> P" and "y \<sharp> \<sigma>" and "y \<noteq> a" and "y \<noteq> b"
    by(generate_fresh "name", auto)
  have "<\<nu>y>((seq_subst_name a \<sigma>){seq_subst_name b \<sigma>}.(([(x, y)] \<bullet> P)[<\<sigma>>])) \<sim> seq_subst_name a \<sigma>{seq_subst_name b \<sigma>}.(<\<nu>y>(([(x, y)] \<bullet> P)[<\<sigma>>]))"
    using \<open>y \<noteq> a\<close> \<open>y \<noteq> b\<close> \<open>y \<sharp> \<sigma>\<close> freshSeqSubstName
    by(rule_tac resOutput) auto
  with \<open>y \<sharp> \<sigma>\<close> have "(<\<nu>y>(a{b}.([(x, y)] \<bullet> P)))[<\<sigma>>] \<sim> (a{b}.(<\<nu>y>([(x, y)] \<bullet> P)))[<\<sigma>>]"
    by simp
  with \<open>y \<sharp> P\<close> \<open>y \<noteq> a\<close> \<open>y \<noteq> b\<close> \<open>x \<noteq> a\<close> \<open>x \<noteq> b\<close> show "(<\<nu>x>a{b}.(P))[<\<sigma>>] \<sim> seq_subst_name a \<sigma>{seq_subst_name b \<sigma>}.((<\<nu>x>P)[<\<sigma>>])"
    apply(subst alphaRes[where c=y])
    apply simp
    apply(subst alphaRes[where c=y and a=x])
    by simp+
qed

lemma resInput:
  fixes x :: name
  and   a :: name
  and   b :: name
  and   P :: pi

  assumes "x \<noteq> a"
  and     "x \<noteq> y"

  shows "<\<nu>x>(a<y>.(P)) \<sim>\<^sup>s a<y>.(<\<nu>x>P)"
proof(auto simp add: substClosed_def)
  fix \<sigma>::"(name \<times> name) list"
  obtain x'::name where "x' \<sharp> P" and "x' \<sharp> \<sigma>" and "x' \<noteq> a" and "x' \<noteq> x" and "x' \<noteq> y"
    by(generate_fresh "name", auto)
  obtain y'::name where "y' \<sharp> P" and "y' \<sharp> \<sigma>" and "y' \<noteq> a" and "y' \<noteq> x" and "y' \<noteq> y" and "x' \<noteq> y'"
    by(generate_fresh "name", auto)
  have "<\<nu>x'>((seq_subst_name a \<sigma>)<y'>.(([(y, y')] \<bullet> [(x, x')] \<bullet> P)[<\<sigma>>])) \<sim> seq_subst_name a \<sigma><y'>.(<\<nu>x'>(([(y, y')] \<bullet> [(x, x')] \<bullet> P)[<\<sigma>>]))"
    using \<open>x' \<noteq> a\<close> \<open>x' \<noteq> y'\<close> \<open>x' \<sharp> \<sigma>\<close> \<open>y' \<sharp> \<sigma>\<close> freshSeqSubstName
    by(rule_tac resInput) auto
  with \<open>x' \<sharp> \<sigma>\<close> \<open>y' \<sharp> \<sigma>\<close> have "(<\<nu>x'>(a<y'>.([(y, y')] \<bullet> [(x, x')] \<bullet> P)))[<\<sigma>>] \<sim> (a<y'>.(<\<nu>x'>([(y, y')] \<bullet> [(x, x')] \<bullet> P)))[<\<sigma>>]"
    by simp
  with \<open>x' \<sharp> P\<close> \<open>y' \<noteq> x\<close> \<open>x' \<noteq> y\<close> \<open>y' \<sharp> P\<close> \<open>x' \<noteq> y'\<close> \<open>x' \<noteq> a\<close> \<open>y' \<noteq> a\<close> \<open>x \<noteq> a\<close> \<open>x \<noteq> y\<close> show "(<\<nu>x>a<y>.(P))[<\<sigma>>] \<sim> a<y>.(<\<nu>x>P)[<\<sigma>>]"
    apply(subst alphaInput[where c=y'])
    apply simp
    apply(subst alphaRes[where c=x'])
    apply(simp add: abs_fresh fresh_left calc_atm)
    apply(simp add: eqvts calc_atm)
    apply(subst alphaRes[where c=x' and a=x])
    apply simp
    apply(subst alphaInput[where c=y' and x=y])
    apply(simp add: abs_fresh fresh_left calc_atm)
    apply(simp add: eqvts calc_atm)
    apply(subst perm_compose)
    by(simp add: eqvts calc_atm)
qed

lemma bisimSubstStructCong:
  fixes P :: pi
  and   Q :: pi

  assumes "P \<equiv>\<^sub>s Q"
  shows "P \<sim>\<^sup>s Q"

using assms
apply(induct rule: structCong.induct)
by(auto intro: reflexive symmetric transitive sumSym sumAssoc sumZero parSym parAssoc parZero
               nilRes resComm resInput resOutput resTau sumRes scopeExtPar bangSC matchId mismatchId)


end

