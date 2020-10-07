(* 
   Title: Psi-calculi   
   Author/Maintainer: Jesper Bengtson (jebe@itu.dk), 2012
*)
theory Bisim_Struct_Cong
  imports Bisim_Pres Sim_Struct_Cong Structural_Congruence
begin

context env begin

lemma bisimParComm:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"
  
  shows "\<Psi> \<rhd> P \<parallel> Q \<sim> Q \<parallel> P"
proof -
  let ?X = "{((\<Psi>::'b), \<lparr>\<nu>*xvec\<rparr>((P::('a, 'b, 'c) psi) \<parallel> Q), \<lparr>\<nu>*xvec\<rparr>(Q \<parallel> P)) | xvec \<Psi> P Q. xvec \<sharp>* \<Psi>}"
  
  have "eqvt ?X"
    by(force simp add: eqvt_def pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst] eqvts)

  have "(\<Psi>, P \<parallel> Q, Q \<parallel> P) \<in> ?X"
    apply auto by(rule_tac x="[]" in exI) auto
  thus ?thesis
  proof(coinduct rule: bisimWeakCoinduct)
    case(cStatEq \<Psi> PQ QP)
    from \<open>(\<Psi>, PQ, QP) \<in> ?X\<close>
    obtain xvec P Q where PFrQ: "PQ = \<lparr>\<nu>*xvec\<rparr>(P \<parallel> Q)" and QFrP: "QP = \<lparr>\<nu>*xvec\<rparr>(Q \<parallel> P)" and "xvec \<sharp>* \<Psi>"
      by auto

    obtain A\<^sub>P \<Psi>\<^sub>P where FrP: "extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" and "A\<^sub>P \<sharp>* \<Psi>" and "A\<^sub>P \<sharp>* Q"
      by(rule_tac C="(\<Psi>, Q)" in freshFrame) auto
    obtain A\<^sub>Q \<Psi>\<^sub>Q where FrQ: "extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" and "A\<^sub>Q \<sharp>* \<Psi>" and "A\<^sub>Q \<sharp>* A\<^sub>P" and "A\<^sub>Q \<sharp>* \<Psi>\<^sub>P"
      by(rule_tac C="(\<Psi>, A\<^sub>P, \<Psi>\<^sub>P)" in freshFrame) auto
    from FrQ \<open>A\<^sub>Q \<sharp>* A\<^sub>P\<close> \<open>A\<^sub>P \<sharp>* Q\<close> have "A\<^sub>P \<sharp>* \<Psi>\<^sub>Q" by(force dest: extractFrameFreshChain)
    have "\<langle>(xvec@A\<^sub>P@A\<^sub>Q), \<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q\<rangle> \<simeq>\<^sub>F \<langle>(xvec@A\<^sub>Q@A\<^sub>P), \<Psi> \<otimes> \<Psi>\<^sub>Q \<otimes> \<Psi>\<^sub>P\<rangle>"
      by(simp add: frameChainAppend)
        (metis frameResChainPres frameResChainComm frameNilStatEq compositionSym Associativity Commutativity FrameStatEqTrans)
    with FrP FrQ PFrQ QFrP \<open>A\<^sub>P \<sharp>* \<Psi>\<^sub>Q\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<^sub>P\<close> \<open>A\<^sub>Q \<sharp>* A\<^sub>P\<close> \<open>xvec \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<close>
    show ?case by(auto simp add: frameChainAppend)
  next
    case(cSim \<Psi> PQ QP)
    from \<open>(\<Psi>, PQ, QP) \<in> ?X\<close>    
    obtain xvec P Q where PFrQ: "PQ = \<lparr>\<nu>*xvec\<rparr>(P \<parallel> Q)" and QFrP: "QP = \<lparr>\<nu>*xvec\<rparr>(Q \<parallel> P)"
                      and "xvec \<sharp>* \<Psi>"
      by auto
    moreover have "\<Psi> \<rhd> \<lparr>\<nu>*xvec\<rparr>(P \<parallel> Q) \<leadsto>[?X] \<lparr>\<nu>*xvec\<rparr>(Q \<parallel> P)"
    proof -
      have "\<Psi> \<rhd> P \<parallel> Q \<leadsto>[?X] Q \<parallel> P"
      proof -
        note \<open>eqvt ?X\<close>
        moreover have "\<And>\<Psi> P Q. (\<Psi>, P \<parallel> Q, Q \<parallel> P) \<in> ?X"
          apply auto by(rule_tac x="[]" in exI) auto
        moreover have "\<And>\<Psi> P Q xvec. \<lbrakk>(\<Psi>, P, Q) \<in> ?X; xvec \<sharp>* \<Psi>\<rbrakk> \<Longrightarrow> (\<Psi>, \<lparr>\<nu>*xvec\<rparr>P, \<lparr>\<nu>*xvec\<rparr>Q) \<in> ?X"
          apply(induct xvec, auto)
          by(rule_tac x="xvec@xveca" in exI) (auto simp add: resChainAppend)
        ultimately show ?thesis by(rule simParComm) 
      qed
      moreover note \<open>eqvt ?X\<close> \<open>xvec \<sharp>* \<Psi>\<close>
      moreover have "\<And>\<Psi> P Q x. \<lbrakk>(\<Psi>, P, Q) \<in> ?X; x \<sharp> \<Psi>\<rbrakk> \<Longrightarrow> (\<Psi>, \<lparr>\<nu>x\<rparr>P, \<lparr>\<nu>x\<rparr>Q) \<in> ?X"
        apply auto
        by(rule_tac x="x#xvec" in exI) auto
      ultimately show ?thesis by(rule resChainPres) 
    qed
    ultimately show ?case by simp
  next
    case(cExt \<Psi> PQ QP \<Psi>')
    from \<open>(\<Psi>, PQ, QP) \<in> ?X\<close>
    obtain xvec P Q where PFrQ: "PQ = \<lparr>\<nu>*xvec\<rparr>(P \<parallel> Q)" and QFrP: "QP = \<lparr>\<nu>*xvec\<rparr>(Q \<parallel> P)"
                      and "xvec \<sharp>* \<Psi>"
      by auto
    
    obtain p where "(p \<bullet> xvec) \<sharp>* \<Psi>"
               and "(p \<bullet> xvec) \<sharp>* P"
               and "(p \<bullet> xvec) \<sharp>* Q"
               and "(p \<bullet> xvec) \<sharp>* \<Psi>'"
               and S: "(set p) \<subseteq> (set xvec) \<times> (set(p \<bullet> xvec))" and "distinctPerm p"
      by(rule_tac c="(\<Psi>, P, Q, \<Psi>')" in name_list_avoiding) auto

    from \<open>(p \<bullet> xvec) \<sharp>* P\<close> \<open>(p \<bullet> xvec) \<sharp>* Q\<close> S have "\<lparr>\<nu>*xvec\<rparr>(P \<parallel> Q) = \<lparr>\<nu>*(p \<bullet> xvec)\<rparr>(p \<bullet> (P \<parallel> Q))"
      by(subst resChainAlpha) auto
    hence PQAlpha: "\<lparr>\<nu>*xvec\<rparr>(P \<parallel> Q) = \<lparr>\<nu>*(p \<bullet> xvec)\<rparr>((p \<bullet> P) \<parallel> (p \<bullet> Q))"
      by(simp add: eqvts)

    from \<open>(p \<bullet> xvec) \<sharp>* P\<close> \<open>(p \<bullet> xvec) \<sharp>* Q\<close> S have "\<lparr>\<nu>*xvec\<rparr>(Q \<parallel> P) = \<lparr>\<nu>*(p \<bullet> xvec)\<rparr>(p \<bullet> (Q \<parallel> P))"
      by(subst resChainAlpha) auto
    hence QPAlpha: "\<lparr>\<nu>*xvec\<rparr>(Q \<parallel> P) = \<lparr>\<nu>*(p \<bullet> xvec)\<rparr>((p \<bullet> Q) \<parallel> (p \<bullet> P))"
      by(simp add: eqvts)

    from \<open>(p \<bullet> xvec) \<sharp>* \<Psi>\<close> \<open>(p \<bullet> xvec) \<sharp>* \<Psi>'\<close> have "(\<Psi> \<otimes> \<Psi>', \<lparr>\<nu>*(p \<bullet> xvec)\<rparr>((p \<bullet> P) \<parallel> (p \<bullet> Q)), \<lparr>\<nu>*(p \<bullet> xvec)\<rparr>((p \<bullet> Q) \<parallel> (p \<bullet> P))) \<in> ?X"
      by auto
    with PFrQ QFrP PQAlpha QPAlpha show ?case by simp
  next
    case(cSym \<Psi> PR QR)
    thus ?case by blast
  qed
qed

lemma bisimResComm:
  fixes x :: name
  and   \<Psi> :: 'b
  and   y :: name
  and   P :: "('a, 'b, 'c) psi"

  shows "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>y\<rparr>P) \<sim> \<lparr>\<nu>y\<rparr>(\<lparr>\<nu>x\<rparr>P)"
proof(cases "x=y")
  case True
  thus ?thesis by(blast intro: bisimReflexive)
next
  case False
  {
    fix x::name and y::name and P::"('a, 'b, 'c) psi"
    assume "x \<sharp> \<Psi>" and "y \<sharp> \<Psi>"
    let ?X = "{((\<Psi>::'b), \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>y\<rparr>(P::('a, 'b, 'c) psi)), \<lparr>\<nu>y\<rparr>(\<lparr>\<nu>x\<rparr>P)) | \<Psi> x y P. x \<sharp> \<Psi> \<and> y \<sharp> \<Psi>}"
    from \<open>x \<sharp> \<Psi>\<close> \<open>y \<sharp> \<Psi>\<close> have "(\<Psi>, \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>y\<rparr>P), \<lparr>\<nu>y\<rparr>(\<lparr>\<nu>x\<rparr>P)) \<in> ?X" by auto
    hence "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>y\<rparr>P) \<sim> \<lparr>\<nu>y\<rparr>(\<lparr>\<nu>x\<rparr>P)"
    proof(coinduct rule: bisimCoinduct)
      case(cStatEq \<Psi> xyP yxP)
      from \<open>(\<Psi>, xyP, yxP) \<in> ?X\<close> obtain x y P where "x \<sharp> \<Psi>" and "y \<sharp> \<Psi>" and "xyP = \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>y\<rparr>P)" and "yxP = \<lparr>\<nu>y\<rparr>(\<lparr>\<nu>x\<rparr>P)" by auto
      moreover obtain A\<^sub>P \<Psi>\<^sub>P where "extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" and "A\<^sub>P \<sharp>* \<Psi>" and "x \<sharp> A\<^sub>P" and "y \<sharp> A\<^sub>P"
        by(rule_tac C="(x, y, \<Psi>)" in freshFrame) auto
      ultimately show ?case by(force intro: frameResComm FrameStatEqTrans)
    next
      case(cSim \<Psi> xyP yxP)
      from \<open>(\<Psi>, xyP, yxP) \<in> ?X\<close> obtain x y P where "x \<sharp> \<Psi>" and "y \<sharp> \<Psi>" and "xyP = \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>y\<rparr>P)" and "yxP = \<lparr>\<nu>y\<rparr>(\<lparr>\<nu>x\<rparr>P)" by auto
      note \<open>x \<sharp> \<Psi>\<close> \<open>y \<sharp> \<Psi>\<close>
      moreover have "eqvt ?X" by(force simp add: eqvt_def pt_fresh_bij[OF pt_name_inst, OF at_name_inst])
      hence "eqvt(?X \<union> bisim)" by auto
      moreover have "\<And>\<Psi> P. (\<Psi>, P, P) \<in> ?X \<union> bisim" by(blast intro: bisimReflexive)
      moreover have "\<And>\<Psi> x y P. \<lbrakk>x \<sharp> \<Psi>; y \<sharp> \<Psi>\<rbrakk> \<Longrightarrow> (\<Psi>, \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>y\<rparr>P), \<lparr>\<nu>y\<rparr>(\<lparr>\<nu>x\<rparr>P)) \<in> ?X \<union> bisim" by auto
      ultimately have "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>y\<rparr>P) \<leadsto>[(?X \<union> bisim)] \<lparr>\<nu>y\<rparr>(\<lparr>\<nu>x\<rparr>P)" by(rule resComm)
      with \<open>xyP = \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>y\<rparr>P)\<close> \<open>yxP = \<lparr>\<nu>y\<rparr>(\<lparr>\<nu>x\<rparr>P)\<close> show ?case
        by simp
    next
      case(cExt \<Psi> xyP yxP \<Psi>')
      from \<open>(\<Psi>, xyP, yxP) \<in> ?X\<close> obtain x y P where "x \<sharp> \<Psi>" and "y \<sharp> \<Psi>" and xyPeq: "xyP = \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>y\<rparr>P)" and yxPeq: "yxP = \<lparr>\<nu>y\<rparr>(\<lparr>\<nu>x\<rparr>P)" by auto
      show ?case
      proof(case_tac "x=y")
        assume "x = y"
        with xyPeq yxPeq show ?case
          by(blast intro: bisimReflexive)
      next
        assume "x \<noteq> y"
        obtain x' where "x' \<sharp> \<Psi>" and "x' \<sharp> \<Psi>'" and "x' \<noteq> x" and "x' \<noteq> y" and "x' \<sharp> P" by(generate_fresh "name") (auto simp add: fresh_prod)
        obtain y' where "y' \<sharp> \<Psi>" and "y' \<sharp> \<Psi>'" and "y' \<noteq> x" and "x' \<noteq> y'" and "y' \<noteq> y" and "y' \<sharp> P" by(generate_fresh "name") (auto simp add: fresh_prod)
        with xyPeq \<open>y' \<sharp> P\<close> \<open>x' \<sharp> P\<close> \<open>x \<noteq> y\<close> \<open>x' \<noteq> y\<close> \<open>y' \<noteq> x\<close> have "\<lparr>\<nu>x\<rparr>(\<lparr>\<nu>y\<rparr>P) = \<lparr>\<nu>x'\<rparr>(\<lparr>\<nu>y'\<rparr>([(x, x')] \<bullet> [(y, y')] \<bullet> P))"
          apply(subst alphaRes[of x']) apply(simp add: abs_fresh) by(subst alphaRes[of y' _ y]) (auto simp add: eqvts calc_atm)
        moreover with yxPeq \<open>y' \<sharp> P\<close> \<open>x' \<sharp> P\<close> \<open>x \<noteq> y\<close> \<open>x' \<noteq> y\<close> \<open>y' \<noteq> x\<close> \<open>x' \<noteq> y'\<close> have "\<lparr>\<nu>y\<rparr>(\<lparr>\<nu>x\<rparr>P) = \<lparr>\<nu>y'\<rparr>(\<lparr>\<nu>x'\<rparr>([(y, y')] \<bullet> [(x, x')] \<bullet> P))"
          apply(subst alphaRes[of y']) apply(simp add: abs_fresh) by(subst alphaRes[of x' _ x]) (auto simp add: eqvts calc_atm)
        with \<open>x \<noteq> y\<close> \<open>x' \<noteq> y\<close> \<open>y' \<noteq> y\<close> \<open>x' \<noteq> x\<close> \<open>y' \<noteq> x\<close> \<open>x' \<noteq> y'\<close> have "\<lparr>\<nu>y\<rparr>(\<lparr>\<nu>x\<rparr>P) = \<lparr>\<nu>y'\<rparr>(\<lparr>\<nu>x'\<rparr>([(x, x')] \<bullet> [(y, y')] \<bullet> P))"
          by(subst perm_compose) (simp add: calc_atm)
        moreover from \<open>x' \<sharp> \<Psi>\<close> \<open>x' \<sharp> \<Psi>'\<close> \<open>y' \<sharp> \<Psi>\<close> \<open>y' \<sharp> \<Psi>'\<close> have "(\<Psi> \<otimes> \<Psi>', \<lparr>\<nu>x'\<rparr>(\<lparr>\<nu>y'\<rparr>([(x, x')] \<bullet> [(y, y')] \<bullet> P)), \<lparr>\<nu>y'\<rparr>(\<lparr>\<nu>x'\<rparr>([(x, x')] \<bullet> [(y, y')] \<bullet> P))) \<in> ?X"
          by auto
        ultimately show ?case using xyPeq yxPeq by simp
      qed
    next
      case(cSym \<Psi> xyP yxP)
      thus ?case by auto
    qed
  }
  moreover obtain x'::name where "x' \<sharp> \<Psi>" and "x' \<sharp> P" and "x' \<noteq> x" and "x' \<noteq> y"
    by(generate_fresh "name") auto
  moreover obtain y'::name where "y' \<sharp> \<Psi>" and "y' \<sharp> P" and "y' \<noteq> x" and "y' \<noteq> y" and "y' \<noteq> x'"
    by(generate_fresh "name") auto
  ultimately have "\<Psi> \<rhd> \<lparr>\<nu>x'\<rparr>(\<lparr>\<nu>y'\<rparr>([(y, y'), (x, x')] \<bullet> P)) \<sim> \<lparr>\<nu>y'\<rparr>(\<lparr>\<nu>x'\<rparr>([(y, y'), (x, x')] \<bullet> P))" by auto
  thus ?thesis using \<open>x' \<sharp> P\<close> \<open>x' \<noteq> x\<close> \<open>x' \<noteq> y\<close> \<open>y' \<sharp> P\<close> \<open>y' \<noteq> x\<close> \<open>y' \<noteq> y\<close> \<open>y' \<noteq> x'\<close> \<open>x \<noteq> y\<close>
    apply(subst alphaRes[where x=x and y=x' and P=P], auto)
    apply(subst alphaRes[where x=y and y=y' and P=P], auto)
    apply(subst alphaRes[where x=x and y=x' and P="\<lparr>\<nu>y'\<rparr>([(y, y')] \<bullet> P)"], auto simp add: abs_fresh fresh_left)
    apply(subst alphaRes[where x=y and y=y' and P="\<lparr>\<nu>x'\<rparr>([(x, x')] \<bullet> P)"], auto simp add: abs_fresh fresh_left)
    by(subst perm_compose) (simp add: eqvts calc_atm)
qed

lemma bisimResComm':
  fixes x    :: name
  and   \<Psi>   :: 'b
  and   xvec :: "name list"
  and   P    :: "('a, 'b, 'c) psi"

  assumes "x \<sharp> \<Psi>"
  and     "xvec \<sharp>* \<Psi>"

  shows "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*xvec\<rparr>P) \<sim> \<lparr>\<nu>*xvec\<rparr>(\<lparr>\<nu>x\<rparr>P)"
using assms
by(induct xvec) (auto intro: bisimResComm bisimReflexive bisimResPres bisimTransitive)

lemma bisimScopeExt:
  fixes x :: name
  and   \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"

  assumes "x \<sharp> P"

  shows "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(P \<parallel> Q) \<sim> P \<parallel> \<lparr>\<nu>x\<rparr>Q"
proof -
  {
    fix x::name and Q :: "('a, 'b, 'c) psi"
    assume "x \<sharp> \<Psi>" and "x \<sharp> P"
    let ?X1 = "{((\<Psi>::'b), \<lparr>\<nu>*xvec\<rparr>(\<lparr>\<nu>x\<rparr>((P::('a, 'b, 'c) psi) \<parallel> Q)), \<lparr>\<nu>*xvec\<rparr>(P \<parallel> \<lparr>\<nu>x\<rparr>Q)) | \<Psi> xvec x P Q. x \<sharp> \<Psi> \<and> x \<sharp> P \<and> xvec \<sharp>* \<Psi>}"
    let ?X2 = "{((\<Psi>::'b), \<lparr>\<nu>*xvec\<rparr>((P::('a, 'b, 'c) psi) \<parallel> \<lparr>\<nu>x\<rparr>Q), \<lparr>\<nu>*xvec\<rparr>(\<lparr>\<nu>x\<rparr>(P \<parallel> Q))) | \<Psi> xvec x P Q. x \<sharp> \<Psi> \<and> x \<sharp> P \<and> xvec \<sharp>* \<Psi>}"
    let ?X = "?X1 \<union> ?X2"

    from \<open>x \<sharp> \<Psi>\<close> \<open>x \<sharp> P\<close> have "(\<Psi>, \<lparr>\<nu>x\<rparr>(P \<parallel> Q), P \<parallel> \<lparr>\<nu>x\<rparr>Q) \<in> ?X"
      by(auto, rule_tac x="[]" in exI) (auto simp add: fresh_list_nil)
    moreover have "eqvt ?X"
      by(rule eqvtUnion)
    (fastforce simp add: eqvt_def eqvts pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst] pt_fresh_bij[OF pt_name_inst, OF at_name_inst])+
    ultimately have "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(P \<parallel> Q) \<sim> P \<parallel> \<lparr>\<nu>x\<rparr>Q"
    proof(coinduct rule: transitiveCoinduct)
      case(cStatEq \<Psi> R T)
      show ?case
      proof(case_tac "(\<Psi>, R, T) \<in> ?X1")
        assume "(\<Psi>, R, T) \<in> ?X1"
        then obtain xvec x P Q where "R = \<lparr>\<nu>*xvec\<rparr>(\<lparr>\<nu>x\<rparr>(P \<parallel> Q))" and "T = \<lparr>\<nu>*xvec\<rparr>(P \<parallel> \<lparr>\<nu>x\<rparr>Q)" and "xvec \<sharp>* \<Psi>" and "x \<sharp> P" and "x \<sharp> \<Psi>"
          by auto
        moreover obtain A\<^sub>P \<Psi>\<^sub>P where FrP: "extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" and "A\<^sub>P \<sharp>* \<Psi>" and "x \<sharp> A\<^sub>P" and "A\<^sub>P \<sharp>* Q"
          by(rule_tac C="(\<Psi>, x, Q)" in freshFrame) auto
        moreover obtain A\<^sub>Q \<Psi>\<^sub>Q where FrQ: "extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" and "A\<^sub>Q \<sharp>* \<Psi>" and "x \<sharp> A\<^sub>Q" and "A\<^sub>Q \<sharp>* A\<^sub>P" and "A\<^sub>Q \<sharp>* \<Psi>\<^sub>P"
          by(rule_tac C="(\<Psi>, x, A\<^sub>P, \<Psi>\<^sub>P)" in freshFrame) auto
        moreover from FrQ \<open>A\<^sub>P \<sharp>* Q\<close> \<open>A\<^sub>Q \<sharp>* A\<^sub>P\<close> have "A\<^sub>P \<sharp>* \<Psi>\<^sub>Q"
          by(drule_tac extractFrameFreshChain) auto
        moreover from \<open>x \<sharp> P\<close> \<open>x \<sharp> A\<^sub>P\<close> FrP have "x \<sharp> \<Psi>\<^sub>P" by(drule_tac extractFrameFresh) auto
        ultimately show ?case
          by(force simp add: frameChainAppend intro: frameResComm' FrameStatEqTrans frameResChainPres)
      next
        assume "(\<Psi>, R, T) \<notin> ?X1"
        with \<open>(\<Psi>, R, T) \<in> ?X\<close> have "(\<Psi>, R, T) \<in> ?X2" by blast
        then obtain xvec x P Q where "T = \<lparr>\<nu>*xvec\<rparr>(\<lparr>\<nu>x\<rparr>(P \<parallel> Q))" and "R = \<lparr>\<nu>*xvec\<rparr>(P \<parallel> \<lparr>\<nu>x\<rparr>Q)" and "xvec \<sharp>* \<Psi>" and "x \<sharp> P" and "x \<sharp> \<Psi>"
          by auto
        moreover obtain A\<^sub>P \<Psi>\<^sub>P where FrP: "extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" and "A\<^sub>P \<sharp>* \<Psi>" and "x \<sharp> A\<^sub>P" and "A\<^sub>P \<sharp>* Q"
          by(rule_tac C="(\<Psi>, x, Q)" in freshFrame) auto
        moreover obtain A\<^sub>Q \<Psi>\<^sub>Q where FrQ: "extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" and "A\<^sub>Q \<sharp>* \<Psi>" and "x \<sharp> A\<^sub>Q" and "A\<^sub>Q \<sharp>* A\<^sub>P" and "A\<^sub>Q \<sharp>* \<Psi>\<^sub>P"
          by(rule_tac C="(\<Psi>, x, A\<^sub>P, \<Psi>\<^sub>P)" in freshFrame) auto
        moreover from FrQ \<open>A\<^sub>P \<sharp>* Q\<close> \<open>A\<^sub>Q \<sharp>* A\<^sub>P\<close> have "A\<^sub>P \<sharp>* \<Psi>\<^sub>Q"
          by(drule_tac extractFrameFreshChain) auto
        moreover from \<open>x \<sharp> P\<close> \<open>x \<sharp> A\<^sub>P\<close> FrP have "x \<sharp> \<Psi>\<^sub>P" by(drule_tac extractFrameFresh) auto
        ultimately show ?case
          apply auto
          by(force simp add: frameChainAppend intro: frameResComm' FrameStatEqTrans frameResChainPres FrameStatEqSym)
      qed
    next
      case(cSim \<Psi> R T)
      let ?Y = "{(\<Psi>, P, Q) | \<Psi> P P' Q' Q. \<Psi> \<rhd> P \<sim> P' \<and> ((\<Psi>, P', Q') \<in> ?X \<or> \<Psi> \<rhd> P' \<sim> Q') \<and> \<Psi> \<rhd> Q' \<sim> Q}"
      from \<open>eqvt ?X\<close> have "eqvt ?Y" by blast
      have C1: "\<And>\<Psi> R T y. \<lbrakk>(\<Psi>, R, T) \<in> ?Y; (y::name) \<sharp> \<Psi>\<rbrakk> \<Longrightarrow> (\<Psi>, \<lparr>\<nu>y\<rparr>R, \<lparr>\<nu>y\<rparr>T) \<in> ?Y"
      proof -
        fix \<Psi> R T y
        assume "(\<Psi>, R, T) \<in> ?Y"
        then obtain R' T' where "\<Psi> \<rhd> R \<sim> R'" and "(\<Psi>, R', T') \<in> (?X \<union> bisim)" and "\<Psi> \<rhd> T' \<sim> T" by fastforce
        assume "(y::name) \<sharp> \<Psi>" 
        show "(\<Psi>, \<lparr>\<nu>y\<rparr>R, \<lparr>\<nu>y\<rparr>T) \<in> ?Y"
        proof(case_tac "(\<Psi>, R', T') \<in> ?X")
          assume "(\<Psi>, R', T') \<in> ?X"
          show ?thesis
          proof(case_tac "(\<Psi>, R', T') \<in> ?X1")
            assume "(\<Psi>, R', T') \<in> ?X1"
            then obtain xvec x P Q where R'eq: "R' = \<lparr>\<nu>*xvec\<rparr>(\<lparr>\<nu>x\<rparr>(P \<parallel> Q))" and T'eq: "T' = \<lparr>\<nu>*xvec\<rparr>(P \<parallel> \<lparr>\<nu>x\<rparr>Q)"
                                     and "xvec \<sharp>* \<Psi>" and "x \<sharp> P" and "x \<sharp> \<Psi>"
              by auto
            from \<open>\<Psi> \<rhd> R \<sim> R'\<close> \<open>y \<sharp> \<Psi>\<close> have "\<Psi> \<rhd> \<lparr>\<nu>y\<rparr>R \<sim> \<lparr>\<nu>y\<rparr>R'" by(rule bisimResPres)
            moreover from \<open>xvec \<sharp>* \<Psi>\<close> \<open>y \<sharp> \<Psi>\<close> \<open>x \<sharp> P\<close> \<open>x \<sharp> \<Psi>\<close> have "(\<Psi>, \<lparr>\<nu>*(y#xvec)\<rparr>\<lparr>\<nu>x\<rparr>(P \<parallel> Q), \<lparr>\<nu>*(y#xvec)\<rparr>(P \<parallel> \<lparr>\<nu>x\<rparr>Q)) \<in> ?X1"
              by(force simp del: resChain.simps)
            with R'eq T'eq have "(\<Psi>, \<lparr>\<nu>y\<rparr>R', \<lparr>\<nu>y\<rparr>T') \<in> ?X \<union> bisim" by simp
            moreover from \<open>\<Psi> \<rhd> T' \<sim> T\<close> \<open>y \<sharp> \<Psi>\<close> have "\<Psi> \<rhd> \<lparr>\<nu>y\<rparr>T' \<sim> \<lparr>\<nu>y\<rparr>T" by(rule bisimResPres)
            ultimately show ?thesis by blast
          next
            assume "(\<Psi>, R', T') \<notin> ?X1"
            with \<open>(\<Psi>, R', T') \<in> ?X\<close> have "(\<Psi>, R', T') \<in> ?X2" by blast
            then obtain xvec x P Q where T'eq: "T' = \<lparr>\<nu>*xvec\<rparr>(\<lparr>\<nu>x\<rparr>(P \<parallel> Q))" and R'eq: "R' = \<lparr>\<nu>*xvec\<rparr>(P \<parallel> \<lparr>\<nu>x\<rparr>Q)" and "xvec \<sharp>* \<Psi>" and "x \<sharp> P" and "x \<sharp> \<Psi>"
              by auto
            from \<open>\<Psi> \<rhd> R \<sim> R'\<close> \<open>y \<sharp> \<Psi>\<close> have "\<Psi> \<rhd> \<lparr>\<nu>y\<rparr>R \<sim> \<lparr>\<nu>y\<rparr>R'" by(rule bisimResPres)
            moreover from \<open>xvec \<sharp>* \<Psi>\<close> \<open>y \<sharp> \<Psi>\<close> \<open>x \<sharp> P\<close> \<open>x \<sharp> \<Psi>\<close> have "(\<Psi>, \<lparr>\<nu>*(y#xvec)\<rparr>(P \<parallel> \<lparr>\<nu>x\<rparr>Q), \<lparr>\<nu>*(y#xvec)\<rparr>(\<lparr>\<nu>x\<rparr>(P \<parallel> Q))) \<in> ?X2"
              by(force simp del: resChain.simps)
            with R'eq T'eq have "(\<Psi>, \<lparr>\<nu>y\<rparr>R', \<lparr>\<nu>y\<rparr>T') \<in> ?X \<union> bisim" by simp
            moreover from \<open>\<Psi> \<rhd> T' \<sim> T\<close> \<open>y \<sharp> \<Psi>\<close> have "\<Psi> \<rhd> \<lparr>\<nu>y\<rparr>T' \<sim> \<lparr>\<nu>y\<rparr>T" by(rule bisimResPres)
            ultimately show ?thesis by blast
          qed
        next
          assume "(\<Psi>, R', T') \<notin> ?X"
          with \<open>(\<Psi>, R', T') \<in> ?X \<union> bisim\<close> have "\<Psi> \<rhd> R' \<sim> T'" by blast
          with \<open>\<Psi> \<rhd> R \<sim> R'\<close> \<open>\<Psi> \<rhd> T' \<sim> T\<close> \<open>y \<sharp> \<Psi>\<close> show ?thesis
            by(blast dest: bisimResPres)
        qed
      qed
      
      show ?case
      proof(case_tac "(\<Psi>, R, T) \<in> ?X1")
        assume "(\<Psi>, R, T) \<in> ?X1"
        then obtain xvec x P Q where Req: "R = \<lparr>\<nu>*xvec\<rparr>(\<lparr>\<nu>x\<rparr>(P \<parallel> Q))" and Teq: "T = \<lparr>\<nu>*xvec\<rparr>(P \<parallel> \<lparr>\<nu>x\<rparr>Q)" and "xvec \<sharp>* \<Psi>" and "x \<sharp> P" and "x \<sharp> \<Psi>"
          by auto
        have "\<Psi> \<rhd> \<lparr>\<nu>*xvec\<rparr>(\<lparr>\<nu>x\<rparr>(P \<parallel> Q)) \<leadsto>[?Y] \<lparr>\<nu>*xvec\<rparr>(P \<parallel> \<lparr>\<nu>x\<rparr>Q)"
        proof -
          have "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(P \<parallel> Q) \<leadsto>[?Y] P \<parallel> \<lparr>\<nu>x\<rparr>Q"
          proof -
            note \<open>x \<sharp> P\<close> \<open>x \<sharp> \<Psi>\<close> \<open>eqvt ?Y\<close>
            moreover have "\<And>\<Psi> P. (\<Psi>, P, P) \<in> ?Y" by(blast intro: bisimReflexive)
            moreover have "\<And>x \<Psi> P Q xvec. \<lbrakk>x \<sharp> \<Psi>; x \<sharp> P; xvec \<sharp>* \<Psi>\<rbrakk> \<Longrightarrow> (\<Psi>, \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*xvec\<rparr>(P \<parallel> Q)), \<lparr>\<nu>*xvec\<rparr>(P \<parallel> \<lparr>\<nu>x\<rparr>Q)) \<in> ?Y"
            proof -
              fix x \<Psi> P Q xvec
              assume "(x::name) \<sharp> (\<Psi>::'b)" and "x \<sharp> (P::('a, 'b, 'c) psi)" and "(xvec::name list) \<sharp>* \<Psi>"
              from \<open>x \<sharp> \<Psi>\<close> \<open>xvec \<sharp>* \<Psi>\<close> have "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*xvec\<rparr>(P \<parallel> Q)) \<sim> \<lparr>\<nu>*xvec\<rparr>(\<lparr>\<nu>x\<rparr>(P \<parallel> Q))"
                by(rule bisimResComm')
              moreover from \<open>xvec \<sharp>* \<Psi>\<close> \<open>x \<sharp> \<Psi>\<close> \<open>x \<sharp> P\<close> have "(\<Psi>, \<lparr>\<nu>*xvec\<rparr>(\<lparr>\<nu>x\<rparr>(P \<parallel> Q)), \<lparr>\<nu>*xvec\<rparr>(P \<parallel> \<lparr>\<nu>x\<rparr>Q)) \<in> ?X \<union> bisim"
                by blast
              ultimately show "(\<Psi>, \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*xvec\<rparr>(P \<parallel> Q)), \<lparr>\<nu>*xvec\<rparr>(P \<parallel> \<lparr>\<nu>x\<rparr>Q)) \<in> ?Y" 
                by(blast intro: bisimReflexive)
            qed
            moreover have "\<And>\<Psi> xvec P x. \<lbrakk>x \<sharp> \<Psi>; xvec \<sharp>* \<Psi>\<rbrakk> \<Longrightarrow> (\<Psi>, \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*xvec\<rparr>P), \<lparr>\<nu>*xvec\<rparr>(\<lparr>\<nu>x\<rparr>P)) \<in> ?Y"
              by(blast intro: bisimResComm' bisimReflexive)
            ultimately show ?thesis by(rule scopeExtLeft)
          qed
          thus ?thesis using \<open>eqvt ?Y\<close> \<open>xvec \<sharp>* \<Psi>\<close> C1 
            by(rule resChainPres)
        qed
        with Req Teq show ?case by simp
      next
        assume "(\<Psi>, R, T) \<notin> ?X1"
        with \<open>(\<Psi>, R, T) \<in> ?X\<close> have "(\<Psi>, R, T) \<in> ?X2" by blast
        then obtain xvec x P Q where Teq: "T = \<lparr>\<nu>*xvec\<rparr>(\<lparr>\<nu>x\<rparr>(P \<parallel> Q))" and Req: "R = \<lparr>\<nu>*xvec\<rparr>(P \<parallel> \<lparr>\<nu>x\<rparr>Q)" and "xvec \<sharp>* \<Psi>" and "x \<sharp> P" and "x \<sharp> \<Psi>"
          by auto
        have "\<Psi> \<rhd> \<lparr>\<nu>*xvec\<rparr>(P \<parallel> \<lparr>\<nu>x\<rparr>Q) \<leadsto>[?Y] \<lparr>\<nu>*xvec\<rparr>(\<lparr>\<nu>x\<rparr>(P \<parallel> Q))"
        proof -
          have "\<Psi> \<rhd> P \<parallel> \<lparr>\<nu>x\<rparr>Q \<leadsto>[?Y] \<lparr>\<nu>x\<rparr>(P \<parallel> Q)"
          proof -
            note \<open>x \<sharp> P\<close> \<open>x \<sharp> \<Psi>\<close> \<open>eqvt ?Y\<close>
            moreover have "\<And>\<Psi> P. (\<Psi>, P, P) \<in> ?Y" by(blast intro: bisimReflexive)
            moreover have "\<And>x \<Psi> P Q xvec. \<lbrakk>x \<sharp> \<Psi>; x \<sharp> P; xvec \<sharp>* \<Psi>\<rbrakk> \<Longrightarrow> (\<Psi>, \<lparr>\<nu>*xvec\<rparr>(P \<parallel> \<lparr>\<nu>x\<rparr>Q), \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*xvec\<rparr>(P \<parallel> Q))) \<in> ?Y"
            proof -
              fix x \<Psi> P Q xvec
              assume "(x::name) \<sharp> (\<Psi>::'b)" and "x \<sharp> (P::('a, 'b, 'c) psi)" and "(xvec::name list) \<sharp>* \<Psi>"
              from \<open>xvec \<sharp>* \<Psi>\<close> \<open>x \<sharp> \<Psi>\<close> \<open>x \<sharp> P\<close> have "(\<Psi>, \<lparr>\<nu>*xvec\<rparr>(P \<parallel> \<lparr>\<nu>x\<rparr>Q), \<lparr>\<nu>*xvec\<rparr>(\<lparr>\<nu>x\<rparr>(P \<parallel> Q))) \<in> ?X \<union> bisim"
                by blast
              moreover from \<open>x \<sharp> \<Psi>\<close> \<open>xvec \<sharp>* \<Psi>\<close> have "\<Psi> \<rhd> \<lparr>\<nu>*xvec\<rparr>(\<lparr>\<nu>x\<rparr>(P \<parallel> Q)) \<sim> \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*xvec\<rparr>(P \<parallel> Q))"
                by(blast intro: bisimResComm' bisimE)
              ultimately show "(\<Psi>, \<lparr>\<nu>*xvec\<rparr>(P \<parallel> \<lparr>\<nu>x\<rparr>Q), \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*xvec\<rparr>(P \<parallel> Q))) \<in> ?Y" 
                by(blast intro: bisimReflexive)
            qed
            ultimately show ?thesis by(rule scopeExtRight)
          qed
          thus ?thesis using \<open>eqvt ?Y\<close> \<open>xvec \<sharp>* \<Psi>\<close> C1 
            by(rule resChainPres)
        qed
        with Req Teq show ?case by simp
      qed
    next
      case(cExt \<Psi> R T \<Psi>')
      show ?case
      proof(case_tac "(\<Psi>, R, T) \<in> ?X1")
        assume "(\<Psi>, R, T) \<in> ?X1"
        then obtain xvec x P Q where Req: "R = \<lparr>\<nu>*xvec\<rparr>(\<lparr>\<nu>x\<rparr>(P \<parallel> Q))" and Teq: "T = \<lparr>\<nu>*xvec\<rparr>(P \<parallel> \<lparr>\<nu>x\<rparr>Q)" and "xvec \<sharp>* \<Psi>" and "x \<sharp> P" and "x \<sharp> \<Psi>"
          by auto
        obtain y::name where "y \<sharp> P" and "y \<sharp> Q" and "y \<sharp> xvec" and "y \<sharp> \<Psi>" and "y \<sharp> \<Psi>'"
          by(generate_fresh "name", auto simp add: fresh_prod)

        obtain p where "(p \<bullet> xvec) \<sharp>* \<Psi>" and "(p \<bullet> xvec) \<sharp>* P" and "(p \<bullet> xvec) \<sharp>* Q" and "(p \<bullet> xvec) \<sharp>* \<Psi>'"
                  and "x \<sharp> (p \<bullet> xvec)" and "y \<sharp> (p \<bullet> xvec)"
                   and S: "(set p) \<subseteq> (set xvec) \<times> (set(p \<bullet> xvec))" and "distinctPerm p"
          by(rule_tac c="(\<Psi>, P, Q, x, y, \<Psi>')" in name_list_avoiding) auto
        
        
        from \<open>y \<sharp> P\<close> have "(p \<bullet> y) \<sharp> (p \<bullet> P)" by(simp add: pt_fresh_bij[OF pt_name_inst, OF at_name_inst])
        with S \<open>y \<sharp> xvec\<close> \<open>y \<sharp> (p \<bullet> xvec)\<close> have "y \<sharp> (p \<bullet> P)" by simp
        with \<open>(p \<bullet> xvec) \<sharp>* \<Psi>\<close> \<open>y \<sharp> \<Psi>\<close> \<open>(p \<bullet> xvec) \<sharp>* \<Psi>'\<close> \<open>y \<sharp> \<Psi>'\<close>
        have "(\<Psi> \<otimes> \<Psi>', \<lparr>\<nu>*(p \<bullet> xvec)\<rparr>(\<lparr>\<nu>y\<rparr>((p \<bullet> P) \<parallel> (p \<bullet> [(x, y)] \<bullet> Q))), \<lparr>\<nu>*(p \<bullet> xvec)\<rparr>((p \<bullet> P) \<parallel> (\<lparr>\<nu>y\<rparr>(p \<bullet> [(x, y)] \<bullet> Q)))) \<in> ?X"
          by auto
        moreover from Req \<open>(p \<bullet> xvec) \<sharp>* P\<close> \<open>(p \<bullet> xvec) \<sharp>* Q\<close> \<open>y \<sharp> xvec\<close> \<open>y \<sharp> (p \<bullet> xvec)\<close> \<open>x \<sharp> (p \<bullet> xvec)\<close> \<open>y \<sharp> P\<close> \<open>y \<sharp> Q\<close> \<open>x \<sharp> P\<close> S
        have "R = \<lparr>\<nu>*(p \<bullet> xvec)\<rparr>(\<lparr>\<nu>y\<rparr>((p \<bullet> P) \<parallel> (p \<bullet> [(x, y)] \<bullet> Q)))"
          apply(erule_tac rev_mp)
          apply(subst alphaRes[of y])
          apply(clarsimp simp add: eqvts)
          apply(subst resChainAlpha[of p])
          by(auto simp add: eqvts)
        moreover from Teq \<open>(p \<bullet> xvec) \<sharp>* P\<close> \<open>(p \<bullet> xvec) \<sharp>* Q\<close> \<open>y \<sharp> xvec\<close> \<open>y \<sharp> (p \<bullet> xvec)\<close> \<open>x \<sharp> (p \<bullet> xvec)\<close> \<open>y \<sharp> P\<close> \<open>y \<sharp> Q\<close> \<open>x \<sharp> P\<close> S
        have "T = \<lparr>\<nu>*(p \<bullet> xvec)\<rparr>((p \<bullet> P) \<parallel> \<lparr>\<nu>y\<rparr>(p \<bullet> [(x, y)] \<bullet> Q))"
          apply(erule_tac rev_mp)
          apply(subst alphaRes[of y])
          apply(clarsimp simp add: eqvts)
          apply(subst resChainAlpha[of p])
          by(auto simp add: eqvts)
        ultimately show ?case
          by blast
      next
        assume "(\<Psi>, R, T) \<notin> ?X1"
        with \<open>(\<Psi>, R, T) \<in> ?X\<close> have "(\<Psi>, R, T) \<in> ?X2" by blast
        then obtain xvec x P Q where Teq: "T = \<lparr>\<nu>*xvec\<rparr>(\<lparr>\<nu>x\<rparr>(P \<parallel> Q))" and Req: "R = \<lparr>\<nu>*xvec\<rparr>(P \<parallel> \<lparr>\<nu>x\<rparr>Q)" and "xvec \<sharp>* \<Psi>" and "x \<sharp> P" and "x \<sharp> \<Psi>"
          by auto
        obtain y::name where "y \<sharp> P" and "y \<sharp> Q" and "y \<sharp> xvec" and "y \<sharp> \<Psi>" and "y \<sharp> \<Psi>'"
          by(generate_fresh "name", auto simp add: fresh_prod)

        obtain p where "(p \<bullet> xvec) \<sharp>* \<Psi>" and "(p \<bullet> xvec) \<sharp>* P" and "(p \<bullet> xvec) \<sharp>* Q" and "(p \<bullet> xvec) \<sharp>* \<Psi>'"
                   and "x \<sharp> (p \<bullet> xvec)" and "y \<sharp> (p \<bullet> xvec)"
                   and S: "(set p) \<subseteq> (set xvec) \<times> (set(p \<bullet> xvec))" and "distinctPerm p"
          by(rule_tac c="(\<Psi>, P, Q, x, y, \<Psi>')" in name_list_avoiding) auto
        
        from \<open>y \<sharp> P\<close> have "(p \<bullet> y) \<sharp> (p \<bullet> P)" by(simp add: pt_fresh_bij[OF pt_name_inst, OF at_name_inst])
        with S \<open>y \<sharp> xvec\<close> \<open>y \<sharp> (p \<bullet> xvec)\<close> have "y \<sharp> (p \<bullet> P)" by simp
        with \<open>(p \<bullet> xvec) \<sharp>* \<Psi>\<close> \<open>y \<sharp> \<Psi>\<close> \<open>(p \<bullet> xvec) \<sharp>* \<Psi>'\<close> \<open>y \<sharp> \<Psi>'\<close>
        have "(\<Psi> \<otimes> \<Psi>', \<lparr>\<nu>*(p \<bullet> xvec)\<rparr>((p \<bullet> P) \<parallel> \<lparr>\<nu>y\<rparr>(p \<bullet> [(x, y)] \<bullet> Q)), \<lparr>\<nu>*(p \<bullet> xvec)\<rparr>(\<lparr>\<nu>y\<rparr>((p \<bullet> P) \<parallel> (p \<bullet> [(x, y)] \<bullet> Q)))) \<in> ?X2"
          by auto
        moreover from Teq \<open>(p \<bullet> xvec) \<sharp>* P\<close> \<open>(p \<bullet> xvec) \<sharp>* Q\<close> \<open>y \<sharp> xvec\<close> \<open>y \<sharp> (p \<bullet> xvec)\<close> \<open>x \<sharp> (p \<bullet> xvec)\<close> \<open>y \<sharp> P\<close> \<open>y \<sharp> Q\<close> \<open>x \<sharp> P\<close> S
        have "T = \<lparr>\<nu>*(p \<bullet> xvec)\<rparr>(\<lparr>\<nu>y\<rparr>((p \<bullet> P) \<parallel> (p \<bullet> [(x, y)] \<bullet> Q)))"
          apply(erule_tac rev_mp)
          apply(subst alphaRes[of y])
          apply(clarsimp simp add: eqvts)
          apply(subst resChainAlpha[of p])
          by(auto simp add: eqvts)
        moreover from Req \<open>(p \<bullet> xvec) \<sharp>* P\<close> \<open>(p \<bullet> xvec) \<sharp>* Q\<close> \<open>y \<sharp> xvec\<close> \<open>y \<sharp> (p \<bullet> xvec)\<close> \<open>x \<sharp> (p \<bullet> xvec)\<close> \<open>y \<sharp> P\<close> \<open>y \<sharp> Q\<close> \<open>x \<sharp> P\<close> S
        have "R = \<lparr>\<nu>*(p \<bullet> xvec)\<rparr>((p \<bullet> P) \<parallel> \<lparr>\<nu>y\<rparr>(p \<bullet> [(x, y)] \<bullet> Q))"
          apply(erule_tac rev_mp)
          apply(subst alphaRes[of y])
          apply(clarsimp simp add: eqvts)
          apply(subst resChainAlpha[of p])
          by(auto simp add: eqvts)
        ultimately show ?case
          by blast
      qed
    next
      case(cSym \<Psi> P Q)
      thus ?case
        by(blast dest: bisimE)
    qed
  }
  moreover obtain y::name where "y \<sharp> \<Psi>" and "y \<sharp> P" "y \<sharp> Q"
    by(generate_fresh "name") auto
  ultimately have "\<Psi> \<rhd> \<lparr>\<nu>y\<rparr>(P \<parallel> ([(x, y)] \<bullet> Q)) \<sim> P \<parallel> \<lparr>\<nu>y\<rparr>([(x, y)] \<bullet> Q)" by auto
  thus ?thesis using assms \<open>y \<sharp> P\<close> \<open>y \<sharp> Q\<close>
    apply(subst alphaRes[where x=x and y=y and P=Q], auto)
    by(subst alphaRes[where x=x and y=y and P="P \<parallel> Q"]) auto
qed

lemma bisimScopeExtChain:
  fixes xvec :: "name list"
  and   \<Psi>    :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"

  assumes "xvec \<sharp>* \<Psi>"
  and     "xvec \<sharp>* P"

  shows "\<Psi> \<rhd> \<lparr>\<nu>*xvec\<rparr>(P \<parallel> Q) \<sim> P \<parallel> (\<lparr>\<nu>*xvec\<rparr>Q)"
using assms
by(induct xvec) (auto intro: bisimScopeExt bisimReflexive bisimTransitive bisimResPres) 

lemma bisimParAssoc:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"
  and   R :: "('a, 'b, 'c) psi"

  shows "\<Psi> \<rhd> (P \<parallel> Q) \<parallel> R \<sim> P \<parallel> (Q \<parallel> R)"
proof -
  let ?X = "{(\<Psi>, \<lparr>\<nu>*xvec\<rparr>((P \<parallel> Q) \<parallel> R), \<lparr>\<nu>*xvec\<rparr>(P \<parallel> (Q \<parallel> R))) | \<Psi> xvec P Q R. xvec \<sharp>* \<Psi>}"
  let ?Y = "{(\<Psi>, P, Q) | \<Psi> P P' Q' Q. \<Psi> \<rhd> P \<sim> P' \<and> (\<Psi>, P', Q') \<in> ?X \<and> \<Psi> \<rhd> Q' \<sim> Q}"

  have "(\<Psi>, (P \<parallel> Q) \<parallel> R, P \<parallel> (Q \<parallel> R)) \<in> ?X"
    by(auto, rule_tac x="[]" in exI) auto
  moreover have "eqvt ?X" by(force simp add: eqvt_def simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst] eqvts)
  ultimately show ?thesis
  proof(coinduct rule: weakTransitiveCoinduct')
    case(cStatEq \<Psi> PQR PQR')
    from \<open>(\<Psi>, PQR, PQR') \<in> ?X\<close> obtain xvec P Q R where "xvec \<sharp>* \<Psi>" and "PQR = \<lparr>\<nu>*xvec\<rparr>((P \<parallel> Q) \<parallel> R)" and "PQR' = \<lparr>\<nu>*xvec\<rparr>(P \<parallel> (Q \<parallel> R))"
      by auto
    moreover obtain A\<^sub>P \<Psi>\<^sub>P where FrP: "extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" and "A\<^sub>P \<sharp>* \<Psi>" and "A\<^sub>P \<sharp>* Q" and "A\<^sub>P \<sharp>* R"
      by(rule_tac C="(\<Psi>, Q, R)" in freshFrame) auto
    moreover obtain A\<^sub>Q \<Psi>\<^sub>Q where FrQ: "extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" and "A\<^sub>Q \<sharp>* \<Psi>" and "A\<^sub>Q \<sharp>* A\<^sub>P" and "A\<^sub>Q \<sharp>* \<Psi>\<^sub>P" and "A\<^sub>Q \<sharp>* R"
      by(rule_tac C="(\<Psi>, A\<^sub>P, \<Psi>\<^sub>P, R)" in freshFrame) auto
    moreover obtain A\<^sub>R \<Psi>\<^sub>R where FrR: "extractFrame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>" and "A\<^sub>R \<sharp>* \<Psi>" and "A\<^sub>R \<sharp>* A\<^sub>P" and "A\<^sub>R \<sharp>* \<Psi>\<^sub>P" and "A\<^sub>R \<sharp>* A\<^sub>Q" and "A\<^sub>R \<sharp>* \<Psi>\<^sub>Q"
      by(rule_tac C="(\<Psi>, A\<^sub>P, \<Psi>\<^sub>P, A\<^sub>Q, \<Psi>\<^sub>Q)" in freshFrame) auto
    moreover from FrQ \<open>A\<^sub>P \<sharp>* Q\<close> \<open>A\<^sub>Q \<sharp>* A\<^sub>P\<close> have "A\<^sub>P \<sharp>* \<Psi>\<^sub>Q"
      by(drule_tac extractFrameFreshChain) auto
    moreover from FrR \<open>A\<^sub>P \<sharp>* R\<close> \<open>A\<^sub>R \<sharp>* A\<^sub>P\<close> have "A\<^sub>P \<sharp>* \<Psi>\<^sub>R"
      by(drule_tac extractFrameFreshChain) auto
    moreover from FrR \<open>A\<^sub>Q \<sharp>* R\<close> \<open>A\<^sub>R \<sharp>* A\<^sub>Q\<close> have "A\<^sub>Q \<sharp>* \<Psi>\<^sub>R"
      by(drule_tac extractFrameFreshChain) auto
    ultimately show ?case using freshCompChain
      by auto (metis frameChainAppend compositionSym Associativity frameNilStatEq frameResChainPres)
  next
    case(cSim \<Psi> T S)
    from \<open>(\<Psi>, T, S) \<in> ?X\<close> obtain xvec P Q R where "xvec \<sharp>* \<Psi>" and TEq: "T = \<lparr>\<nu>*xvec\<rparr>((P \<parallel> Q) \<parallel> R)"
                                               and SEq: "S = \<lparr>\<nu>*xvec\<rparr>(P \<parallel> (Q \<parallel> R))"
      by auto
    from \<open>eqvt ?X\<close>have "eqvt ?Y" by blast
    have C1: "\<And>\<Psi> T S yvec. \<lbrakk>(\<Psi>, T, S) \<in> ?Y; yvec \<sharp>* \<Psi>\<rbrakk> \<Longrightarrow> (\<Psi>, \<lparr>\<nu>*yvec\<rparr>T, \<lparr>\<nu>*yvec\<rparr>S) \<in> ?Y"
    proof -
      fix \<Psi> T S yvec
      assume "(\<Psi>, T, S) \<in> ?Y"
      then obtain T' S' where "\<Psi> \<rhd> T \<sim> T'" and "(\<Psi>, T', S') \<in> ?X" and "\<Psi> \<rhd> S' \<sim> S" by fastforce
      assume "(yvec::name list) \<sharp>* \<Psi>" 
      from \<open>(\<Psi>, T', S') \<in> ?X\<close> obtain xvec P Q R where T'eq: "T' = \<lparr>\<nu>*xvec\<rparr>((P \<parallel> Q) \<parallel> R)" and S'eq: "S' = \<lparr>\<nu>*xvec\<rparr>(P \<parallel> (Q \<parallel> R))"
                                                  and "xvec \<sharp>* \<Psi>"
        by auto
      from \<open>\<Psi> \<rhd> T \<sim> T'\<close> \<open>yvec \<sharp>* \<Psi>\<close> have "\<Psi> \<rhd> \<lparr>\<nu>*yvec\<rparr>T \<sim> \<lparr>\<nu>*yvec\<rparr>T'" by(rule bisimResChainPres)
      moreover from \<open>xvec \<sharp>* \<Psi>\<close> \<open>yvec \<sharp>* \<Psi>\<close> have "(\<Psi>, \<lparr>\<nu>*(yvec@xvec)\<rparr>((P \<parallel> Q) \<parallel> R), \<lparr>\<nu>*(yvec@xvec)\<rparr>(P \<parallel> (Q \<parallel> R))) \<in> ?X"
        by force
      with T'eq S'eq have "(\<Psi>, \<lparr>\<nu>*yvec\<rparr>T', \<lparr>\<nu>*yvec\<rparr>S') \<in> ?X" by(simp add: resChainAppend)
      moreover from \<open>\<Psi> \<rhd> S' \<sim> S\<close> \<open>yvec \<sharp>* \<Psi>\<close> have "\<Psi> \<rhd> \<lparr>\<nu>*yvec\<rparr>S' \<sim> \<lparr>\<nu>*yvec\<rparr>S" by(rule bisimResChainPres)
      ultimately show "(\<Psi>, \<lparr>\<nu>*yvec\<rparr>T, \<lparr>\<nu>*yvec\<rparr>S) \<in> ?Y" by blast
    qed
    have C2: "\<And>\<Psi> T S y. \<lbrakk>(\<Psi>, T, S) \<in> ?Y; y \<sharp> \<Psi>\<rbrakk> \<Longrightarrow> (\<Psi>, \<lparr>\<nu>y\<rparr>T, \<lparr>\<nu>y\<rparr>S) \<in> ?Y"
      by(drule_tac yvec2="[y]" in C1) auto

    have "\<Psi> \<rhd> \<lparr>\<nu>*xvec\<rparr>((P \<parallel> Q) \<parallel> R) \<leadsto>[?Y] \<lparr>\<nu>*xvec\<rparr>(P \<parallel> (Q \<parallel> R))"
    proof -
      have "\<Psi> \<rhd> (P \<parallel> Q) \<parallel> R \<leadsto>[?Y] P \<parallel> (Q \<parallel> R)" 
      proof -
        note \<open>eqvt ?Y\<close>
        moreover have "\<And>\<Psi> P Q R. (\<Psi>, (P \<parallel> Q) \<parallel> R, P \<parallel> (Q \<parallel> R)) \<in> ?Y"
        proof -
          fix \<Psi> P Q R
          have "(\<Psi>::'b, ((P::('a, 'b, 'c) psi) \<parallel> Q) \<parallel> R, P \<parallel> (Q \<parallel> R)) \<in> ?X"
            by(auto, rule_tac x="[]" in exI) auto
          thus "(\<Psi>, (P \<parallel> Q) \<parallel> R, P \<parallel> (Q \<parallel> R)) \<in> ?Y"
            by(blast intro: bisimReflexive)
        qed
        moreover have "\<And>xvec \<Psi> P Q R. \<lbrakk>xvec \<sharp>* \<Psi>; xvec \<sharp>* P\<rbrakk> \<Longrightarrow> (\<Psi>, \<lparr>\<nu>*xvec\<rparr>((P \<parallel> Q) \<parallel> R), P \<parallel> (\<lparr>\<nu>*xvec\<rparr>(Q \<parallel> R))) \<in> ?Y"
        proof -
          fix xvec \<Psi> P Q R
          assume "(xvec::name list) \<sharp>* (\<Psi>::'b)" and "xvec \<sharp>* (P::('a, 'b, 'c) psi)"
          from \<open>xvec \<sharp>* \<Psi>\<close> have "(\<Psi>, \<lparr>\<nu>*xvec\<rparr>((P \<parallel> Q) \<parallel> R), \<lparr>\<nu>*xvec\<rparr>(P \<parallel> (Q \<parallel> R))) \<in> ?X" by blast
          moreover from \<open>xvec \<sharp>* \<Psi>\<close> \<open>xvec \<sharp>* P\<close> have "\<Psi> \<rhd> \<lparr>\<nu>*xvec\<rparr>(P \<parallel> (Q \<parallel> R)) \<sim> P \<parallel> (\<lparr>\<nu>*xvec\<rparr>(Q \<parallel> R))"
            by(rule bisimScopeExtChain)
          ultimately show "(\<Psi>, \<lparr>\<nu>*xvec\<rparr>((P \<parallel> Q) \<parallel> R), P \<parallel> (\<lparr>\<nu>*xvec\<rparr>(Q \<parallel> R))) \<in> ?Y"
            by(blast intro: bisimReflexive)
        qed
        moreover have "\<And>xvec \<Psi> P Q R. \<lbrakk>xvec \<sharp>* \<Psi>; xvec \<sharp>* R\<rbrakk> \<Longrightarrow> (\<Psi>, (\<lparr>\<nu>*xvec\<rparr>(P \<parallel> Q)) \<parallel> R, \<lparr>\<nu>*xvec\<rparr>(P \<parallel> (Q \<parallel> R))) \<in> ?Y"
        proof -
          fix xvec \<Psi> P Q R
          assume "(xvec::name list) \<sharp>* (\<Psi>::'b)" and "xvec \<sharp>* (R::('a, 'b, 'c) psi)"
          have "\<Psi> \<rhd> (\<lparr>\<nu>*xvec\<rparr>(P \<parallel> Q)) \<parallel> R \<sim> R \<parallel> (\<lparr>\<nu>*xvec\<rparr>(P \<parallel> Q))" by(rule bisimParComm)
          moreover from \<open>xvec \<sharp>* \<Psi>\<close> \<open>xvec \<sharp>* R\<close> have "\<Psi> \<rhd> \<lparr>\<nu>*xvec\<rparr>(R \<parallel> (P \<parallel> Q)) \<sim> R \<parallel> (\<lparr>\<nu>*xvec\<rparr>(P \<parallel> Q))" by(rule bisimScopeExtChain)
          hence "\<Psi> \<rhd> R \<parallel> (\<lparr>\<nu>*xvec\<rparr>(P \<parallel> Q)) \<sim> \<lparr>\<nu>*xvec\<rparr>(R \<parallel> (P \<parallel> Q))" by(rule bisimE)
          moreover from \<open>xvec \<sharp>* \<Psi>\<close> have "\<Psi> \<rhd> \<lparr>\<nu>*xvec\<rparr>(R \<parallel> (P \<parallel> Q)) \<sim> \<lparr>\<nu>*xvec\<rparr>((P \<parallel> Q) \<parallel> R)"
            by(metis bisimResChainPres bisimParComm)
          moreover from \<open>xvec \<sharp>* \<Psi>\<close> have "(\<Psi>, \<lparr>\<nu>*xvec\<rparr>((P \<parallel> Q) \<parallel> R), \<lparr>\<nu>*xvec\<rparr>(P \<parallel> (Q \<parallel> R))) \<in> ?X" by blast
          ultimately show "(\<Psi>, (\<lparr>\<nu>*xvec\<rparr>(P \<parallel> Q)) \<parallel> R, \<lparr>\<nu>*xvec\<rparr>(P \<parallel> (Q \<parallel> R))) \<in> ?Y"  by(blast dest: bisimTransitive intro: bisimReflexive)
        qed
        ultimately show ?thesis using C1
          by(rule parAssocLeft)
      qed
      thus ?thesis using \<open>eqvt ?Y\<close> \<open>xvec \<sharp>* \<Psi>\<close> C2
        by(rule resChainPres)
    qed
    with TEq SEq show ?case by simp
  next
    case(cExt \<Psi> T S \<Psi>')
    from \<open>(\<Psi>, T, S) \<in> ?X\<close> obtain xvec P Q R where "xvec \<sharp>* \<Psi>" and TEq: "T = \<lparr>\<nu>*xvec\<rparr>((P \<parallel> Q) \<parallel> R)"
                                               and SEq: "S = \<lparr>\<nu>*xvec\<rparr>(P \<parallel> (Q \<parallel> R))"
      by auto
    obtain p where "(p \<bullet> xvec) \<sharp>* \<Psi>" and "(p \<bullet> xvec) \<sharp>* P" and "(p \<bullet> xvec) \<sharp>* Q" and "(p \<bullet> xvec) \<sharp>* R" and "(p \<bullet> xvec) \<sharp>* \<Psi>'"
               and S: "(set p) \<subseteq> (set xvec) \<times> (set(p \<bullet> xvec))" and "distinctPerm p"
      by(rule_tac c="(\<Psi>, P, Q, R, \<Psi>')" in name_list_avoiding) auto

    from \<open>(p \<bullet> xvec) \<sharp>* \<Psi>\<close> \<open>(p \<bullet> xvec) \<sharp>* \<Psi>'\<close> have "(\<Psi> \<otimes> \<Psi>', \<lparr>\<nu>*(p \<bullet> xvec)\<rparr>(((p \<bullet> P) \<parallel> (p \<bullet> Q)) \<parallel> (p \<bullet> R)), \<lparr>\<nu>*(p \<bullet> xvec)\<rparr>((p \<bullet> P) \<parallel> ((p \<bullet> Q) \<parallel> (p \<bullet> R)))) \<in> ?X"
      by auto
    moreover from TEq \<open>(p \<bullet> xvec) \<sharp>* P\<close> \<open>(p \<bullet> xvec) \<sharp>* Q\<close> \<open>(p \<bullet> xvec) \<sharp>* R\<close> S have "T = \<lparr>\<nu>*(p \<bullet> xvec)\<rparr>(((p \<bullet> P) \<parallel> (p \<bullet> Q)) \<parallel> (p \<bullet> R))"
      apply auto by(subst resChainAlpha[of p]) auto
    moreover from SEq \<open>(p \<bullet> xvec) \<sharp>* P\<close> \<open>(p \<bullet> xvec) \<sharp>* Q\<close> \<open>(p \<bullet> xvec) \<sharp>* R\<close> S have "S = \<lparr>\<nu>*(p \<bullet> xvec)\<rparr>((p \<bullet> P) \<parallel> ((p \<bullet> Q) \<parallel> (p \<bullet> R)))"
      apply auto by(subst resChainAlpha[of p]) auto
    ultimately show ?case by simp
  next
    case(cSym \<Psi> T S)
    from \<open>(\<Psi>, T, S) \<in> ?X\<close> obtain xvec P Q R where "xvec \<sharp>* \<Psi>" and TEq: "T = \<lparr>\<nu>*xvec\<rparr>((P \<parallel> Q) \<parallel> R)"
                                               and SEq: "\<lparr>\<nu>*xvec\<rparr>(P \<parallel> (Q \<parallel> R)) = S"
      by auto
    
    from \<open>xvec \<sharp>* \<Psi>\<close> have "\<Psi> \<rhd> \<lparr>\<nu>*xvec\<rparr>(P \<parallel> (Q \<parallel> R)) \<sim> \<lparr>\<nu>*xvec\<rparr>((R \<parallel> Q) \<parallel> P)"
      by(metis bisimParComm bisimParPres bisimTransitive bisimResChainPres)
    moreover from \<open>xvec \<sharp>* \<Psi>\<close> have "(\<Psi>, \<lparr>\<nu>*xvec\<rparr>((R \<parallel> Q) \<parallel> P), \<lparr>\<nu>*xvec\<rparr>(R \<parallel> (Q \<parallel> P))) \<in> ?X" by blast
    moreover from \<open>xvec \<sharp>* \<Psi>\<close> have "\<Psi> \<rhd> \<lparr>\<nu>*xvec\<rparr>(R \<parallel> (Q \<parallel> P)) \<sim> \<lparr>\<nu>*xvec\<rparr>((P \<parallel> Q) \<parallel> R)"
      by(metis bisimParComm bisimParPres bisimTransitive bisimResChainPres)
    ultimately show ?case using TEq SEq by(blast dest: bisimTransitive)
  qed
qed    

lemma bisimParNil:
  fixes P :: "('a, 'b, 'c) psi"

  shows "\<Psi> \<rhd> P \<parallel> \<zero> \<sim> P"
proof -
  let ?X1 = "{(\<Psi>, P \<parallel> \<zero>, P) | \<Psi> P. True}"
  let ?X2 = "{(\<Psi>, P, P \<parallel> \<zero>) | \<Psi> P. True}"
  let ?X = "?X1 \<union> ?X2"
  have "eqvt ?X" by(auto simp add: eqvt_def)
  have "(\<Psi>, P \<parallel> \<zero>, P) \<in> ?X" by simp
  thus ?thesis
  proof(coinduct rule: bisimWeakCoinduct)
    case(cStatEq \<Psi> Q R)
    show ?case
    proof(case_tac "(\<Psi>, Q, R) \<in> ?X1")
      assume "(\<Psi>, Q, R) \<in> ?X1"
      then obtain P where "Q = P \<parallel> \<zero>" and "R = P" by auto
      moreover obtain A\<^sub>P \<Psi>\<^sub>P where "extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" and "A\<^sub>P \<sharp>* \<Psi>"
        by(rule freshFrame)
      ultimately show ?case
        apply auto by(metis frameResChainPres frameNilStatEq Identity Associativity AssertionStatEqTrans Commutativity)
    next
      assume "(\<Psi>, Q, R) \<notin> ?X1"
      with \<open>(\<Psi>, Q, R) \<in> ?X\<close> have "(\<Psi>, Q, R) \<in> ?X2" by blast
      then obtain P where "Q = P" and "R = P \<parallel> \<zero>" by auto
      moreover obtain A\<^sub>P \<Psi>\<^sub>P where "extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" and "A\<^sub>P \<sharp>* \<Psi>"
        by(rule freshFrame)
      ultimately show ?case
        apply auto by(metis frameResChainPres frameNilStatEq Identity Associativity AssertionStatEqTrans AssertionStatEqSym Commutativity)
    qed
  next
    case(cSim \<Psi> Q R)
    thus ?case using \<open>eqvt ?X\<close>
      by(auto intro: parNilLeft parNilRight)
  next
    case(cExt \<Psi> Q R \<Psi>')
    thus ?case by auto
  next
    case(cSym \<Psi> Q R)
    thus ?case by auto
  qed
qed

lemma bisimResNil:
  fixes x :: name
  and   \<Psi> :: 'b
  
  shows "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>\<zero> \<sim> \<zero>"
proof -
  {
    fix x::name
    assume "x \<sharp> \<Psi>"
    have "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>\<zero> \<sim> \<zero>"
    proof -
      let ?X1 = "{(\<Psi>, \<lparr>\<nu>x\<rparr>\<zero>, \<zero>) | \<Psi> x. x \<sharp> \<Psi>}"
      let ?X2 = "{(\<Psi>, \<zero>, \<lparr>\<nu>x\<rparr>\<zero>) | \<Psi> x. x \<sharp> \<Psi>}"
      let ?X = "?X1 \<union> ?X2"

      from \<open>x \<sharp> \<Psi>\<close> have "(\<Psi>, \<lparr>\<nu>x\<rparr>\<zero>, \<zero>) \<in> ?X" by auto
      thus ?thesis
      proof(coinduct rule: bisimWeakCoinduct)
        case(cStatEq \<Psi> P Q)
        thus ?case using freshComp by(force intro: frameResFresh FrameStatEqSym)
      next
        case(cSim \<Psi> P Q)
        thus ?case
          by(force intro: resNilLeft resNilRight)
      next
        case(cExt \<Psi> P Q \<Psi>')
        obtain y where "y \<sharp> \<Psi>" and "y \<sharp> \<Psi>'" and "y \<noteq> x"
          by(generate_fresh "name") (auto simp add: fresh_prod)
        show ?case
        proof(case_tac "(\<Psi>, P, Q) \<in> ?X1")
          assume "(\<Psi>, P, Q) \<in> ?X1"
          then obtain x where "P = \<lparr>\<nu>x\<rparr>\<zero>" and "Q = \<zero>" by auto
          moreover have "\<lparr>\<nu>x\<rparr>\<zero> = \<lparr>\<nu>y\<rparr> \<zero>" by(subst alphaRes) auto
          ultimately show ?case using \<open>y \<sharp> \<Psi>\<close> \<open>y \<sharp> \<Psi>'\<close> by auto
        next
          assume "(\<Psi>, P, Q) \<notin> ?X1"
          with \<open>(\<Psi>, P, Q) \<in> ?X\<close> have "(\<Psi>, P, Q) \<in> ?X2" by auto
          then obtain x where "Q = \<lparr>\<nu>x\<rparr>\<zero>" and "P = \<zero>" by auto
          moreover have "\<lparr>\<nu>x\<rparr>\<zero> = \<lparr>\<nu>y\<rparr> \<zero>" by(subst alphaRes) auto
          ultimately show ?case using \<open>y \<sharp> \<Psi>\<close> \<open>y \<sharp> \<Psi>'\<close> by auto
        qed
      next
        case(cSym \<Psi> P Q)
        thus ?case by auto
      qed
    qed
  }
  moreover obtain y::name where "y \<sharp> \<Psi>" by(generate_fresh "name") auto
  ultimately have "\<Psi> \<rhd> \<lparr>\<nu>y\<rparr>\<zero> \<sim> \<zero>" by auto
  thus ?thesis by(subst alphaRes[where x=x and y=y]) auto
qed

lemma bisimOutputPushRes:
  fixes x :: name
  and   \<Psi> :: 'b
  and   M :: 'a
  and   N :: 'a
  and   P :: "('a, 'b, 'c) psi"

  assumes "x \<sharp> M"
  and     "x \<sharp> N"

  shows "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(M\<langle>N\<rangle>.P) \<sim> M\<langle>N\<rangle>.\<lparr>\<nu>x\<rparr>P"
proof -
  {
    fix x::name and P::"('a, 'b, 'c) psi"
    assume "x \<sharp> \<Psi>" and "x \<sharp> M" and "x \<sharp> N"
    let ?X1 = "{(\<Psi>, \<lparr>\<nu>x\<rparr>(M\<langle>N\<rangle>.P), M\<langle>N\<rangle>.\<lparr>\<nu>x\<rparr>P) | \<Psi> x M N P. x \<sharp> \<Psi> \<and> x \<sharp> M \<and> x \<sharp> N}"
    let ?X2 = "{(\<Psi>, M\<langle>N\<rangle>.\<lparr>\<nu>x\<rparr>P, \<lparr>\<nu>x\<rparr>(M\<langle>N\<rangle>.P)) | \<Psi> x M N P. x \<sharp> \<Psi> \<and> x \<sharp> M \<and> x \<sharp> N}"
    let ?X = "?X1 \<union> ?X2"
  
    have "eqvt ?X" by(rule_tac eqvtUnion) (force simp add: eqvt_def pt_fresh_bij[OF pt_name_inst, OF at_name_inst] eqvts)+
    from \<open>x \<sharp> \<Psi>\<close> \<open>x \<sharp> M\<close> \<open>x \<sharp> N\<close>  have "(\<Psi>, \<lparr>\<nu>x\<rparr>(M\<langle>N\<rangle>.P), M\<langle>N\<rangle>.\<lparr>\<nu>x\<rparr>P) \<in> ?X" by auto
    hence "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(M\<langle>N\<rangle>.P) \<sim> M\<langle>N\<rangle>.\<lparr>\<nu>x\<rparr>P"
    proof(coinduct rule: bisimCoinduct)
      case(cStatEq \<Psi> Q R)
      thus ?case using freshComp by(force intro: frameResFresh FrameStatEqSym)
    next
      case(cSim \<Psi> Q R)
      thus ?case using \<open>eqvt ?X\<close>
        by(fastforce intro: outputPushResLeft outputPushResRight bisimReflexive)
    next
      case(cExt \<Psi> Q R \<Psi>')
      show ?case
      proof(case_tac "(\<Psi>, Q, R) \<in> ?X1")
        assume "(\<Psi>, Q, R) \<in> ?X1"
        then obtain x M N P where Qeq: "Q = \<lparr>\<nu>x\<rparr>(M\<langle>N\<rangle>.P)" and Req: "R = M\<langle>N\<rangle>.\<lparr>\<nu>x\<rparr>P" and "x \<sharp> \<Psi>" and "x \<sharp> M" and "x \<sharp> N" by auto
        obtain y::name where "y \<sharp> \<Psi>" and "y \<sharp> \<Psi>'" and "y \<sharp> M" and "y \<sharp> N" and "y \<sharp> P"
          by(generate_fresh "name") (auto simp add: fresh_prod)
        
        moreover hence "(\<Psi> \<otimes> \<Psi>', \<lparr>\<nu>y\<rparr>(M\<langle>N\<rangle>.([(x, y)] \<bullet> P)), M\<langle>N\<rangle>.\<lparr>\<nu>y\<rparr>([(x, y)] \<bullet> P)) \<in> ?X" by auto
        moreover from Qeq \<open>x \<sharp> M\<close> \<open>y \<sharp> M\<close> \<open>x \<sharp> N\<close> \<open>y \<sharp> N\<close> \<open>y \<sharp> P\<close> have "Q = \<lparr>\<nu>y\<rparr>(M\<langle>N\<rangle>.([(x, y)] \<bullet> P))"
          apply auto by(subst alphaRes[of y]) (auto simp add: eqvts)
        moreover from Req \<open>y \<sharp> P\<close> have "R = M\<langle>N\<rangle>.\<lparr>\<nu>y\<rparr>([(x, y)] \<bullet> P)"
          apply auto by(subst alphaRes[of y]) (auto simp add: eqvts)
        ultimately show ?case by blast
      next
        assume "(\<Psi>, Q, R) \<notin> ?X1"
        with \<open>(\<Psi>, Q, R) \<in> ?X\<close> have "(\<Psi>, Q, R) \<in> ?X2" by blast
        then obtain x M N P where Req: "R = \<lparr>\<nu>x\<rparr>(M\<langle>N\<rangle>.P)" and Qeq: "Q = M\<langle>N\<rangle>.\<lparr>\<nu>x\<rparr>P" and "x \<sharp> \<Psi>" and "x \<sharp> M" and "x \<sharp> N" by auto
        obtain y::name where "y \<sharp> \<Psi>" and "y \<sharp> \<Psi>'" and "y \<sharp> M" and "y \<sharp> N" and "y \<sharp> P"
          by(generate_fresh "name") (auto simp add: fresh_prod)
        
        moreover hence "(\<Psi> \<otimes> \<Psi>', \<lparr>\<nu>y\<rparr>(M\<langle>N\<rangle>.([(x, y)] \<bullet> P)), M\<langle>N\<rangle>.\<lparr>\<nu>y\<rparr>([(x, y)] \<bullet> P)) \<in> ?X" by auto
        moreover from Req \<open>x \<sharp> M\<close> \<open>y \<sharp> M\<close> \<open>x \<sharp> N\<close> \<open>y \<sharp> N\<close> \<open>y \<sharp> P\<close> have "R = \<lparr>\<nu>y\<rparr>(M\<langle>N\<rangle>.([(x, y)] \<bullet> P))"
          apply auto by(subst alphaRes[of y]) (auto simp add: eqvts)
        moreover from Qeq \<open>y \<sharp> P\<close> have "Q = M\<langle>N\<rangle>.\<lparr>\<nu>y\<rparr>([(x, y)] \<bullet> P)"
          apply auto by(subst alphaRes[of y]) (auto simp add: eqvts)
        ultimately show ?case by blast
      qed
    next
      case(cSym \<Psi> R Q)
      thus ?case by blast
    qed
  }
  moreover obtain y::name where "y \<sharp> \<Psi>" and "y \<sharp> M" and "y \<sharp> N" "y \<sharp> P"
    by(generate_fresh "name") auto
  ultimately have "\<Psi> \<rhd> \<lparr>\<nu>y\<rparr>(M\<langle>N\<rangle>.([(x, y)] \<bullet> P)) \<sim> M\<langle>N\<rangle>.\<lparr>\<nu>y\<rparr>([(x, y)] \<bullet> P)" by auto
  thus ?thesis using assms \<open>y \<sharp> P\<close> \<open>y \<sharp> M\<close> \<open>y \<sharp> N\<close>
    apply(subst alphaRes[where x=x and y=y and P=P], auto)
    by(subst alphaRes[where x=x and y=y and P="M\<langle>N\<rangle>.P"]) auto
qed

lemma bisimInputPushRes:
  fixes x    :: name
  and   \<Psi>    :: 'b
  and   M    :: 'a
  and   xvec :: "name list"
  and   N    :: 'a
  and   P    :: "('a, 'b, 'c) psi"

  assumes "x \<sharp> M"
  and     "x \<sharp> xvec"
  and     "x \<sharp> N"

  shows "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(M\<lparr>\<lambda>*xvec N\<rparr>.P) \<sim> M\<lparr>\<lambda>*xvec N\<rparr>.\<lparr>\<nu>x\<rparr>P"
proof -
  {
    fix x::name and P::"('a, 'b, 'c) psi"
    assume "x \<sharp> \<Psi>" and "x \<sharp> M" and "x \<sharp> N" and "x \<sharp> xvec"
    let ?X1 = "{(\<Psi>, \<lparr>\<nu>x\<rparr>(M\<lparr>\<lambda>*xvec N\<rparr>.P), M\<lparr>\<lambda>*xvec N\<rparr>.\<lparr>\<nu>x\<rparr>P) | \<Psi> x M xvec N P. x \<sharp> \<Psi> \<and> x \<sharp> M \<and> x \<sharp> xvec \<and> x \<sharp> N}"
    let ?X2 = "{(\<Psi>, M\<lparr>\<lambda>*xvec N\<rparr>.\<lparr>\<nu>x\<rparr>P, \<lparr>\<nu>x\<rparr>(M\<lparr>\<lambda>*xvec N\<rparr>.P)) | \<Psi> x M xvec N P. x \<sharp> \<Psi> \<and> x \<sharp> M \<and> x \<sharp> xvec \<and> x \<sharp> N}"
    let ?X = "?X1 \<union> ?X2"
  
    have "eqvt ?X" by(rule_tac eqvtUnion) (force simp add: eqvt_def pt_fresh_bij[OF pt_name_inst, OF at_name_inst] eqvts)+

    from \<open>x \<sharp> \<Psi>\<close> \<open>x \<sharp> M\<close> \<open>x \<sharp> xvec\<close> \<open>x \<sharp> N\<close> have "(\<Psi>, \<lparr>\<nu>x\<rparr>(M\<lparr>\<lambda>*xvec N\<rparr>.P), M\<lparr>\<lambda>*xvec N\<rparr>.\<lparr>\<nu>x\<rparr>P) \<in> ?X" by blast
    hence "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(M\<lparr>\<lambda>*xvec N\<rparr>.P) \<sim> M\<lparr>\<lambda>*xvec N\<rparr>.\<lparr>\<nu>x\<rparr>P"
    proof(coinduct rule: bisimCoinduct)
      case(cStatEq \<Psi> Q R)
      thus ?case using freshComp by(force intro: frameResFresh FrameStatEqSym)
    next
      case(cSim \<Psi> Q R)
      thus ?case using \<open>eqvt ?X\<close>
        by(fastforce intro: inputPushResLeft inputPushResRight bisimReflexive)
    next
      case(cExt \<Psi> Q R \<Psi>')
      show ?case
      proof(case_tac "(\<Psi>, Q, R) \<in> ?X1")
        assume "(\<Psi>, Q, R) \<in> ?X1"
        then obtain x M xvec N P where Qeq: "Q = \<lparr>\<nu>x\<rparr>(M\<lparr>\<lambda>*xvec N\<rparr>.P)" and Req: "R = M\<lparr>\<lambda>*xvec N\<rparr>.\<lparr>\<nu>x\<rparr>P" and "x \<sharp> \<Psi>"
                                   and "x \<sharp> M" and "x \<sharp> xvec" and "x \<sharp> N" by auto
        obtain y::name where "y \<sharp> \<Psi>" and "y \<sharp> \<Psi>'" and "y \<sharp> M" and "y \<sharp> N" and "y \<sharp> P" and "y \<sharp> xvec"
          by(generate_fresh "name") (auto simp add: fresh_prod)
        
        moreover hence "(\<Psi> \<otimes> \<Psi>', \<lparr>\<nu>y\<rparr>(M\<lparr>\<lambda>*xvec N\<rparr>.([(x, y)] \<bullet> P)), M\<lparr>\<lambda>*xvec N\<rparr>.\<lparr>\<nu>y\<rparr>([(x, y)] \<bullet> P)) \<in> ?X" by fastforce
        moreover from Qeq \<open>x \<sharp> M\<close> \<open>y \<sharp> M\<close> \<open>x \<sharp> xvec\<close> \<open>y \<sharp> xvec\<close> \<open>x \<sharp> N\<close> \<open>y \<sharp> N\<close> \<open>y \<sharp> P\<close> have "Q = \<lparr>\<nu>y\<rparr>(M\<lparr>\<lambda>*xvec N\<rparr>.([(x, y)] \<bullet> P))"
          apply auto by(subst alphaRes[of y]) (auto simp add: eqvts inputChainFresh)
        moreover from Req \<open>y \<sharp> P\<close> have "R = M\<lparr>\<lambda>*xvec N \<rparr>.\<lparr>\<nu>y\<rparr>([(x, y)] \<bullet> P)"
          apply auto by(subst alphaRes[of y]) (auto simp add: eqvts)
        ultimately show ?case by blast
      next
        assume "(\<Psi>, Q, R) \<notin> ?X1"
        with \<open>(\<Psi>, Q, R) \<in> ?X\<close> have "(\<Psi>, Q, R) \<in> ?X2" by blast
        then obtain x M xvec N P where Req: "R = \<lparr>\<nu>x\<rparr>(M\<lparr>\<lambda>*xvec N\<rparr>.P)" and Qeq: "Q = M\<lparr>\<lambda>*xvec N\<rparr>.\<lparr>\<nu>x\<rparr>P" and "x \<sharp> \<Psi>"
                                   and "x \<sharp> M" and "x \<sharp> xvec" and "x \<sharp> N" by auto
        obtain y::name where "y \<sharp> \<Psi>" and "y \<sharp> \<Psi>'" and "y \<sharp> M" and "y \<sharp> N" and "y \<sharp> P" and "y \<sharp> xvec"
          by(generate_fresh "name") (auto simp add: fresh_prod)

        moreover hence "(\<Psi> \<otimes> \<Psi>', \<lparr>\<nu>y\<rparr>(M\<lparr>\<lambda>*xvec N\<rparr>.([(x, y)] \<bullet> P)), M\<lparr>\<lambda>*xvec N\<rparr>.\<lparr>\<nu>y\<rparr>([(x, y)] \<bullet> P)) \<in> ?X" by fastforce
        moreover from Req \<open>x \<sharp> M\<close> \<open>y \<sharp> M\<close> \<open>x \<sharp> xvec\<close> \<open>y \<sharp> xvec\<close> \<open>x \<sharp> N\<close> \<open>y \<sharp> N\<close> \<open>y \<sharp> P\<close> have "R = \<lparr>\<nu>y\<rparr>(M\<lparr>\<lambda>*xvec N\<rparr>.([(x, y)] \<bullet> P))"
          apply auto by(subst alphaRes[of y]) (auto simp add: eqvts inputChainFresh)
        moreover from Qeq \<open>y \<sharp> P\<close> have "Q = M\<lparr>\<lambda>*xvec N \<rparr>.\<lparr>\<nu>y\<rparr>([(x, y)] \<bullet> P)"
          apply auto by(subst alphaRes[of y]) (auto simp add: eqvts)
        ultimately show ?case by blast
      qed
    next
      case(cSym \<Psi> R Q)
      thus ?case by blast
    qed
  }
  moreover obtain y::name where "y \<sharp> \<Psi>" and "y \<sharp> M" and "y \<sharp> N" and "y \<sharp> P" and "y \<sharp> xvec"
    by(generate_fresh "name") auto
  ultimately have "\<Psi> \<rhd> \<lparr>\<nu>y\<rparr>(M\<lparr>\<lambda>*xvec N\<rparr>.([(x, y)] \<bullet> P)) \<sim> M\<lparr>\<lambda>*xvec N\<rparr>.\<lparr>\<nu>y\<rparr>([(x, y)] \<bullet> P)" by auto
  thus ?thesis using assms \<open>y \<sharp> P\<close> \<open>y \<sharp> M\<close> \<open>y \<sharp> N\<close> \<open>y \<sharp> xvec\<close>
    apply(subst alphaRes[where x=x and y=y and P=P], auto)
    by(subst alphaRes[where x=x and y=y and P="M\<lparr>\<lambda>*xvec N\<rparr>.P"]) (auto simp add: inputChainFresh eqvts)
qed

lemma bisimCasePushRes:
  fixes x  :: name
  and   \<Psi>  :: 'b
  and   Cs :: "('c \<times> ('a, 'b, 'c) psi) list"

  assumes "x \<sharp> (map fst Cs)"

  shows "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(Cases Cs) \<sim> Cases(map (\<lambda>(\<phi>, P). (\<phi>, \<lparr>\<nu>x\<rparr>P)) Cs)"
proof -
  {
    fix x::name and Cs::"('c \<times> ('a, 'b, 'c) psi) list"
    assume "x \<sharp> \<Psi>" and "x \<sharp> (map fst Cs)"
    let ?X1 = "{(\<Psi>, \<lparr>\<nu>x\<rparr>(Cases Cs), Cases(map (\<lambda>(\<phi>, P). (\<phi>, \<lparr>\<nu>x\<rparr>P)) Cs)) | \<Psi> x Cs. x \<sharp> \<Psi> \<and> x \<sharp> (map fst Cs)}"
    let ?X2 = "{(\<Psi>, Cases(map (\<lambda>(\<phi>, P). (\<phi>, \<lparr>\<nu>x\<rparr>P)) Cs), \<lparr>\<nu>x\<rparr>(Cases Cs)) | \<Psi> x Cs. x \<sharp> \<Psi> \<and> x \<sharp> (map fst Cs)}"
    let ?X = "?X1 \<union> ?X2"
  
    have "eqvt ?X" apply(rule_tac eqvtUnion) 
      apply(auto simp add: eqvt_def eqvts)
      apply(rule_tac x="p \<bullet> x" in exI)
      apply(rule_tac x="p \<bullet> Cs" in exI)
      apply(perm_extend_simp)
      apply(auto simp add: eqvts)
      apply(simp add: pt_fresh_bij[OF pt_name_inst, OF at_name_inst])
      apply(drule_tac pi=p in pt_fresh_bij1[OF pt_name_inst, OF at_name_inst])
      apply(drule_tac pi=p in pt_fresh_bij1[OF pt_name_inst, OF at_name_inst])
      apply(simp add: eqvts)
      apply(perm_extend_simp)
      apply(simp add: eqvts)
      apply(rule_tac x="p \<bullet> x" in exI)
      apply(rule_tac x="p \<bullet> Cs" in exI)
      apply auto
      apply(perm_extend_simp)
      apply(simp add: pt_fresh_bij[OF pt_name_inst, OF at_name_inst])
      apply(drule_tac pi=p in pt_fresh_bij1[OF pt_name_inst, OF at_name_inst])
      apply(drule_tac pi=p in pt_fresh_bij1[OF pt_name_inst, OF at_name_inst])
      apply(simp add: eqvts)
      apply(perm_extend_simp)
      by(simp add: eqvts)    
    
    from \<open>x \<sharp> \<Psi>\<close> \<open>x \<sharp> map fst Cs\<close> have "(\<Psi>, \<lparr>\<nu>x\<rparr>(Cases Cs), Cases(map (\<lambda>(\<phi>, P). (\<phi>, \<lparr>\<nu>x\<rparr>P)) Cs)) \<in> ?X" by auto
    hence "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(Cases Cs) \<sim> Cases(map (\<lambda>(\<phi>, P). (\<phi>, \<lparr>\<nu>x\<rparr>P)) Cs)"
    proof(coinduct rule: bisimCoinduct)
      case(cStatEq \<Psi> Q R)
      thus ?case using freshComp by(force intro: frameResFresh FrameStatEqSym)
    next
      case(cSim \<Psi> Q R)
      thus ?case using \<open>eqvt ?X\<close>
        by(fastforce intro: casePushResLeft casePushResRight bisimReflexive)
    next
      case(cExt \<Psi> Q R \<Psi>')
      show ?case
      proof(case_tac "(\<Psi>, Q, R) \<in> ?X1")
        assume "(\<Psi>, Q, R) \<in> ?X1"
        then obtain x Cs where Qeq: "Q = \<lparr>\<nu>x\<rparr>(Cases Cs)" and Req: "R = Cases(map (\<lambda>(\<phi>, P). (\<phi>, \<lparr>\<nu>x\<rparr>P)) Cs)"
                           and "x \<sharp> \<Psi>" and "x \<sharp> (map fst Cs)" by blast
        obtain y::name where "y \<sharp> \<Psi>" and "y \<sharp> \<Psi>'" and "y \<sharp> Cs"
          by(generate_fresh "name") (auto simp add: fresh_prod)
        from \<open>y \<sharp> Cs\<close> \<open>x \<sharp> (map fst Cs)\<close> have "y \<sharp> map fst ([(x, y)] \<bullet> Cs)" by(induct Cs) (auto simp add: fresh_list_cons fresh_list_nil)

        moreover with \<open>y \<sharp> \<Psi>\<close> \<open>y \<sharp> \<Psi>'\<close> have "(\<Psi> \<otimes> \<Psi>', \<lparr>\<nu>y\<rparr>(Cases ([(x, y)] \<bullet> Cs)), Cases(map (\<lambda>(\<phi>, P). (\<phi>, \<lparr>\<nu>y\<rparr>P)) ([(x, y)] \<bullet> Cs))) \<in> ?X"
          by auto
        moreover from Qeq \<open>y \<sharp> Cs\<close> have "Q = \<lparr>\<nu>y\<rparr>(Cases([(x, y)] \<bullet> Cs))"
          apply auto by(subst alphaRes[of y]) (auto simp add: eqvts)
        moreover from Req \<open>y \<sharp> Cs\<close> \<open>x \<sharp> (map fst Cs)\<close> have "R = Cases(map (\<lambda>(\<phi>, P). (\<phi>, \<lparr>\<nu>y\<rparr>P)) ([(x, y)] \<bullet> Cs))" 
          by(induct Cs arbitrary: R) (auto simp add: fresh_list_cons fresh_prod alphaRes)
        ultimately show ?case by blast
      next
        assume "(\<Psi>, Q, R) \<notin> ?X1"
        with \<open>(\<Psi>, Q, R) \<in> ?X\<close> have "(\<Psi>, Q, R) \<in> ?X2" by blast
        then obtain x Cs where Req: "R = \<lparr>\<nu>x\<rparr>(Cases Cs)" and Qeq: "Q = Cases(map (\<lambda>(\<phi>, P). (\<phi>, \<lparr>\<nu>x\<rparr>P)) Cs)"
                           and "x \<sharp> \<Psi>" and "x \<sharp> (map fst Cs)" by blast
        obtain y::name where "y \<sharp> \<Psi>" and "y \<sharp> \<Psi>'" and "y \<sharp> Cs"
          by(generate_fresh "name") (auto simp add: fresh_prod)
        from \<open>y \<sharp> Cs\<close> \<open>x \<sharp> (map fst Cs)\<close> have "y \<sharp> map fst ([(x, y)] \<bullet> Cs)" by(induct Cs) (auto simp add: fresh_list_cons fresh_list_nil)
        
        moreover with \<open>y \<sharp> \<Psi>\<close> \<open>y \<sharp> \<Psi>'\<close> have "(\<Psi> \<otimes> \<Psi>', \<lparr>\<nu>y\<rparr>(Cases ([(x, y)] \<bullet> Cs)), Cases(map (\<lambda>(\<phi>, P). (\<phi>, \<lparr>\<nu>y\<rparr>P)) ([(x, y)] \<bullet> Cs))) \<in> ?X"
          by auto
        moreover from Req \<open>y \<sharp> Cs\<close> have "R = \<lparr>\<nu>y\<rparr>(Cases([(x, y)] \<bullet> Cs))"
          apply auto by(subst alphaRes[of y]) (auto simp add: eqvts)
        moreover from Qeq \<open>y \<sharp> Cs\<close> \<open>x \<sharp> (map fst Cs)\<close> have "Q = Cases(map (\<lambda>(\<phi>, P). (\<phi>, \<lparr>\<nu>y\<rparr>P)) ([(x, y)] \<bullet> Cs))" 
          by(induct Cs arbitrary: Q) (auto simp add: fresh_list_cons fresh_prod alphaRes)
        ultimately show ?case by blast
      qed
    next
      case(cSym \<Psi> R Q)
      thus ?case by blast
    qed
  }
  moreover obtain y::name where "y \<sharp> \<Psi>" and "y \<sharp> Cs" by(generate_fresh "name") auto
  moreover from \<open>x \<sharp> map fst Cs\<close> have "y \<sharp> map fst([(x, y)] \<bullet> Cs)" 
    by(induct Cs) (auto simp add: fresh_left calc_atm)
  ultimately have "\<Psi> \<rhd> \<lparr>\<nu>y\<rparr>(Cases ([(x, y)] \<bullet> Cs)) \<sim> Cases(map (\<lambda>(\<phi>, P). (\<phi>, \<lparr>\<nu>y\<rparr>P)) ([(x, y)] \<bullet> Cs))"
    by auto
  moreover from \<open>y \<sharp> Cs\<close> have "\<lparr>\<nu>y\<rparr>(Cases ([(x, y)] \<bullet> Cs)) =  \<lparr>\<nu>x\<rparr>(Cases Cs)"
    by(simp add: alphaRes eqvts)
  moreover from \<open>x \<sharp> map fst Cs\<close> \<open>y \<sharp> Cs\<close> have "Cases(map (\<lambda>(\<phi>, P). (\<phi>, \<lparr>\<nu>y\<rparr>P)) ([(x, y)] \<bullet> Cs)) = Cases(map (\<lambda>(\<phi>, P). (\<phi>, \<lparr>\<nu>x\<rparr>P)) Cs)"
    by(induct Cs) (auto simp add: alphaRes)
  ultimately show ?thesis by auto
qed

lemma bangExt:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  
  assumes "guarded P"

  shows "\<Psi> \<rhd> !P \<sim> P \<parallel> !P"
proof -
  let ?X = "{(\<Psi>, !P, P \<parallel> !P) | \<Psi> P. guarded P} \<union> {(\<Psi>, P \<parallel> !P, !P) | \<Psi> P. guarded P}"
  from \<open>guarded P\<close> have "(\<Psi>, !P, P \<parallel> !P) \<in> ?X" by auto
  thus ?thesis
  proof(coinduct rule: bisimCoinduct)
    case(cStatEq \<Psi> Q R)
    from \<open>(\<Psi>, Q, R) \<in> ?X\<close> obtain P where Eq: "(Q = !P \<and> R = P \<parallel> !P) \<or> (Q = P \<parallel> !P \<and> R = !P)" and "guarded P"
      by auto
    obtain A\<^sub>P \<Psi>\<^sub>P where FrP: "extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" and "A\<^sub>P \<sharp>* \<Psi>" by(rule freshFrame)
    from FrP \<open>guarded P\<close> have "\<Psi>\<^sub>P \<simeq> SBottom'" by(blast dest: guardedStatEq)
    from \<open>\<Psi>\<^sub>P \<simeq> SBottom'\<close> have "\<Psi> \<otimes> SBottom' \<simeq> \<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> SBottom'" by(metis Identity Composition AssertionStatEqTrans Commutativity AssertionStatEqSym)
    hence "\<langle>A\<^sub>P, \<Psi> \<otimes> SBottom'\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>P, \<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> SBottom'\<rangle>"
      by(force intro: frameResChainPres)
    moreover from \<open>A\<^sub>P \<sharp>* \<Psi>\<close> have "\<langle>\<epsilon>, \<Psi> \<otimes> SBottom'\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>P, \<Psi> \<otimes> SBottom'\<rangle>"
      by(rule_tac FrameStatEqSym) (fastforce intro: frameResFreshChain)
    ultimately show ?case using Eq \<open>A\<^sub>P \<sharp>* \<Psi>\<close> FrP
      by auto (blast dest: FrameStatEqTrans FrameStatEqSym)+
  next
    case(cSim \<Psi> Q R)
    thus ?case by(auto intro: bangExtLeft bangExtRight bisimReflexive)
  next
    case(cExt \<Psi> Q R)
    thus ?case by auto
  next
    case(cSym \<Psi> Q R)
    thus ?case by auto
  qed
qed
  
lemma bisimParPresSym:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"
  and   R :: "('a, 'b, 'c) psi"

  assumes "\<Psi> \<rhd> P \<sim> Q"

  shows "\<Psi> \<rhd> R \<parallel> P \<sim> R \<parallel> Q"
using assms
by(metis bisimParComm bisimParPres bisimTransitive)

lemma bisimScopeExtSym:
  fixes x :: name
  and   Q :: "('a, 'b, 'c) psi"
  and   P :: "('a, 'b, 'c) psi"

  assumes "x \<sharp> \<Psi>"
  and     "x \<sharp> Q"

  shows "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(P \<parallel> Q) \<sim> (\<lparr>\<nu>x\<rparr>P) \<parallel> Q"
using assms
by(metis bisimScopeExt bisimTransitive bisimParComm bisimSymmetric bisimResPres)

lemma bisimScopeExtChainSym:
  fixes xvec :: "name list"
  and   Q    :: "('a, 'b, 'c) psi"
  and   P    :: "('a, 'b, 'c) psi"

  assumes "xvec \<sharp>* \<Psi>"
  and     "xvec \<sharp>* Q"

  shows "\<Psi> \<rhd> \<lparr>\<nu>*xvec\<rparr>(P \<parallel> Q) \<sim> (\<lparr>\<nu>*xvec\<rparr>P) \<parallel> Q"
using assms
by(induct xvec) (auto intro: bisimScopeExtSym bisimReflexive bisimTransitive bisimResPres)

lemma bisimParPresAuxSym:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"
  and   R :: "('a, 'b, 'c) psi"

  assumes "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> P \<sim> Q"
  and     "extractFrame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>"
  and     "A\<^sub>R \<sharp>* \<Psi>"
  and     "A\<^sub>R \<sharp>* P"
  and     "A\<^sub>R \<sharp>* Q"

  shows "\<Psi> \<rhd> R \<parallel> P \<sim> R \<parallel> Q"
using assms
by(metis bisimParComm bisimParPresAux bisimTransitive)

lemma bangDerivative:
  fixes \<Psi>   :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   \<alpha>    :: "'a action"
  and   P'   :: "('a, 'b, 'c) psi"

  assumes "\<Psi> \<rhd> !P \<longmapsto>\<alpha> \<prec> P'"
  and     "\<Psi> \<rhd> P \<sim> Q"
  and     "bn \<alpha> \<sharp>* \<Psi>"
  and     "bn \<alpha> \<sharp>* P"
  and     "bn \<alpha> \<sharp>* Q"
  and     "bn \<alpha> \<sharp>* subject \<alpha>"
  and     "guarded Q"

  obtains Q' R T where "\<Psi> \<rhd> !Q \<longmapsto>\<alpha> \<prec> Q'" and "\<Psi> \<rhd> P' \<sim> R \<parallel> !P" and "\<Psi> \<rhd> Q' \<sim> T \<parallel> !Q" and "\<Psi> \<rhd> R \<sim> T"
                   and "((supp R)::name set) \<subseteq> supp P'" and "((supp T)::name set) \<subseteq> supp Q'"
proof -
  from \<open>\<Psi> \<rhd> !P \<longmapsto>\<alpha> \<prec> P'\<close> have "guarded P" apply - by(ind_cases "\<Psi> \<rhd> !P \<longmapsto>\<alpha> \<prec> P'") (auto simp add: psi.inject)
  assume "\<And>Q' R T. \<lbrakk>\<Psi> \<rhd> !Q \<longmapsto>\<alpha> \<prec> Q'; \<Psi> \<rhd> P' \<sim> R \<parallel> !P; \<Psi> \<rhd> Q' \<sim> T \<parallel> !Q; \<Psi> \<rhd> R \<sim> T; ((supp R)::name set) \<subseteq> supp P';
                    ((supp T)::name set) \<subseteq> supp Q'\<rbrakk> \<Longrightarrow> thesis"
  moreover from \<open>\<Psi> \<rhd> !P \<longmapsto>\<alpha> \<prec> P'\<close> \<open>bn \<alpha> \<sharp>* subject \<alpha>\<close> \<open>bn \<alpha> \<sharp>* \<Psi>\<close> \<open>bn \<alpha> \<sharp>* P\<close> \<open>bn \<alpha> \<sharp>* Q\<close> \<open>\<Psi> \<rhd> P \<sim> Q\<close> \<open>guarded Q\<close> 
  have "\<exists>Q' T R . \<Psi> \<rhd> !Q \<longmapsto>\<alpha>  \<prec> Q' \<and> \<Psi> \<rhd> P' \<sim> R \<parallel> !P \<and> \<Psi> \<rhd> Q' \<sim> T \<parallel> !Q \<and> \<Psi> \<rhd> R \<sim> T \<and>
                  ((supp R)::name set) \<subseteq> supp P' \<and> ((supp T)::name set) \<subseteq> supp Q'"
  proof(nominal_induct avoiding: Q rule: bangInduct')
    case(cAlpha \<alpha> P' p Q)
    then obtain Q' T R where QTrans: "\<Psi> \<rhd> !Q \<longmapsto>\<alpha> \<prec> Q'" and "\<Psi> \<rhd> P' \<sim> R \<parallel> (P \<parallel> !P)" and "\<Psi> \<rhd> Q' \<sim> T \<parallel> !Q" and "\<Psi> \<rhd> R \<sim> T"
                         and suppR: "((supp R)::name set) \<subseteq> supp P'" and suppT: "((supp T)::name set) \<subseteq> supp Q'"
      by blast
    from QTrans have "distinct(bn \<alpha>)" by(rule boundOutputDistinct)
    have S: "set p \<subseteq> set(bn \<alpha>) \<times> set(bn(p \<bullet> \<alpha>))" by fact
    from QTrans \<open>bn(p \<bullet> \<alpha>) \<sharp>* Q\<close> \<open>bn(p \<bullet> \<alpha>) \<sharp>* \<alpha>\<close> \<open>bn \<alpha> \<sharp>* subject \<alpha>\<close> \<open>distinct(bn \<alpha>)\<close> have "bn(p \<bullet> \<alpha>) \<sharp>* Q'"
      by(drule_tac freeFreshChainDerivative) simp+
    with QTrans \<open>bn(p \<bullet> \<alpha>) \<sharp>* \<alpha>\<close> S \<open>bn \<alpha> \<sharp>* subject \<alpha>\<close> have "\<Psi> \<rhd> !Q \<longmapsto>(p \<bullet> \<alpha>) \<prec> (p \<bullet> Q')"
      by(force simp add: residualAlpha)
    moreover from \<open>\<Psi> \<rhd> P' \<sim> R \<parallel> (P \<parallel> !P)\<close> have "(p \<bullet> \<Psi>) \<rhd> (p \<bullet> P') \<sim> (p \<bullet> (R \<parallel> (P \<parallel> !P)))"
      by(rule bisimClosed)
    with \<open>bn \<alpha> \<sharp>* \<Psi>\<close> \<open>bn \<alpha> \<sharp>* P\<close> \<open>bn(p \<bullet> \<alpha>) \<sharp>* \<Psi>\<close> \<open>bn(p \<bullet> \<alpha>) \<sharp>* P\<close> S have "\<Psi> \<rhd> (p \<bullet> P') \<sim> (p \<bullet> R) \<parallel> (P \<parallel> !P)"
      by(simp add: eqvts)
    moreover from \<open>\<Psi> \<rhd> Q' \<sim> T \<parallel> !Q\<close> have "(p \<bullet> \<Psi>) \<rhd> (p \<bullet> Q') \<sim> (p \<bullet> (T \<parallel> !Q))"
      by(rule bisimClosed)
    with \<open>bn \<alpha> \<sharp>* \<Psi>\<close> \<open>bn \<alpha> \<sharp>* Q\<close> \<open>bn(p \<bullet> \<alpha>) \<sharp>* \<Psi>\<close> \<open>bn(p \<bullet> \<alpha>) \<sharp>* Q\<close> S have "\<Psi> \<rhd> (p \<bullet> Q') \<sim> (p \<bullet> T) \<parallel> !Q"
      by(simp add: eqvts)
    moreover from \<open>\<Psi> \<rhd> R \<sim> T\<close> have "(p \<bullet> \<Psi>) \<rhd> (p \<bullet> R) \<sim> (p \<bullet> T)"
      by(rule bisimClosed)
    with \<open>bn \<alpha> \<sharp>* \<Psi>\<close> \<open>bn(p \<bullet> \<alpha>) \<sharp>* \<Psi>\<close> S have "\<Psi> \<rhd> (p \<bullet> R) \<sim> (p \<bullet> T)"
      by(simp add: eqvts)
    moreover from suppR have "((supp(p \<bullet> R))::name set) \<subseteq> supp(p \<bullet> P')"
      apply(erule_tac rev_mp)
      by(subst subsetClosed[of p, symmetric]) (simp add: eqvts)
    moreover from suppT have "((supp(p \<bullet> T))::name set) \<subseteq> supp(p \<bullet> Q')"
      apply(erule_tac rev_mp)
      by(subst subsetClosed[of p, symmetric]) (simp add: eqvts)
    ultimately show ?case by blast
  next
    case(cPar1 \<alpha> P' Q)
    from \<open>\<Psi> \<rhd> P \<sim> Q\<close> \<open>\<Psi> \<rhd> P \<longmapsto>\<alpha> \<prec> P'\<close> \<open>bn \<alpha> \<sharp>* \<Psi>\<close> \<open>bn \<alpha> \<sharp>* Q\<close> 
    obtain Q' where QTrans: "\<Psi> \<rhd> Q \<longmapsto>\<alpha> \<prec> Q'" and "\<Psi> \<rhd> P' \<sim> Q'"
      by(blast dest: bisimE simE)
    from QTrans have "\<Psi> \<otimes> SBottom' \<rhd> Q \<longmapsto>\<alpha> \<prec> Q'" by(metis statEqTransition Identity AssertionStatEqSym)
    hence "\<Psi> \<rhd> Q \<parallel> !Q \<longmapsto>\<alpha> \<prec> (Q' \<parallel> !Q)" using \<open>bn \<alpha> \<sharp>* Q\<close> by(rule_tac Par1) (assumption | simp)+
    hence "\<Psi> \<rhd> !Q \<longmapsto>\<alpha> \<prec> (Q' \<parallel> !Q)" using \<open>guarded Q\<close> by(rule Bang)
    moreover from \<open>guarded P\<close> have "\<Psi> \<rhd> P' \<parallel> !P \<sim> P' \<parallel> (P \<parallel> !P)" by(metis bangExt bisimParPresSym)
    moreover have "\<Psi> \<rhd> Q' \<parallel> !Q \<sim> Q' \<parallel> !Q" by(rule bisimReflexive)
    ultimately show ?case using \<open>\<Psi> \<rhd> P' \<sim> Q'\<close> by(force simp add: psi.supp)
  next
    case(cPar2 \<alpha> P' Q)
    then obtain Q' T R where QTrans: "\<Psi> \<rhd> !Q \<longmapsto>\<alpha> \<prec> Q'" and "\<Psi> \<rhd> P' \<sim> R \<parallel> !P" and "\<Psi> \<rhd> Q' \<sim> T \<parallel> !Q" and "\<Psi> \<rhd> R \<sim> T"
                         and suppR: "((supp R)::name set) \<subseteq> supp P'" and suppT: "((supp T)::name set) \<subseteq> supp Q'"
      by blast
    note QTrans
    from \<open>\<Psi> \<rhd> P' \<sim> R \<parallel> !P\<close> have "\<Psi> \<rhd> P \<parallel> P' \<sim> R \<parallel> (P \<parallel> !P)"
      by(metis bisimParPresSym bisimParComm bisimTransitive bisimParAssoc)
    with QTrans show ?case using \<open>\<Psi> \<rhd> Q' \<sim> T \<parallel> !Q\<close> \<open>\<Psi> \<rhd> R \<sim> T\<close> suppR suppT
      by(force simp add: psi.supp)
  next
    case(cComm1 M N P' K xvec P'' Q)
    from \<open>\<Psi> \<rhd> P \<sim> Q\<close> have "\<Psi> \<rhd> Q \<leadsto>[bisim] P" by(metis bisimE)
    with \<open>\<Psi> \<rhd> P \<longmapsto>M\<lparr>N\<rparr> \<prec> P'\<close> obtain Q' where QTrans: "\<Psi> \<rhd> Q \<longmapsto>M\<lparr>N\<rparr> \<prec> Q'" and "\<Psi> \<rhd> Q' \<sim> P'"
      by(force dest: simE)
    from QTrans have "\<Psi> \<otimes> SBottom' \<rhd> Q \<longmapsto>M\<lparr>N\<rparr> \<prec> Q'" by(metis statEqTransition Identity AssertionStatEqSym)
    moreover obtain A\<^sub>Q \<Psi>\<^sub>Q where FrQ: "extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" and "A\<^sub>Q \<sharp>* \<Psi>" and "A\<^sub>Q \<sharp>* Q" and "A\<^sub>Q \<sharp>* M" 
      by(rule_tac C="(\<Psi>, Q, M)" in freshFrame) auto
    note FrQ
    moreover from FrQ \<open>guarded Q\<close> have "\<Psi>\<^sub>Q \<simeq> SBottom'" by(blast dest: guardedStatEq)
    from \<open>\<Psi> \<rhd> !P \<longmapsto>K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P''\<close> \<open>xvec \<sharp>* K\<close> \<open>\<Psi> \<rhd> P \<sim> Q\<close> \<open>xvec \<sharp>* \<Psi>\<close> \<open>xvec \<sharp>* P\<close> \<open>xvec \<sharp>* Q\<close> \<open>guarded Q\<close>
    obtain Q'' T R where QTrans': "\<Psi> \<rhd> !Q \<longmapsto>K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q''" and "\<Psi> \<rhd> P'' \<sim> R \<parallel> !P" and "\<Psi> \<rhd> Q'' \<sim> T \<parallel> !Q" and "\<Psi> \<rhd> R \<sim> T"
                     and suppR: "((supp R)::name set) \<subseteq> supp P''" and suppT: "((supp T)::name set) \<subseteq> supp Q''" using cComm1
      by fastforce
    from QTrans' \<open>\<Psi>\<^sub>Q \<simeq> SBottom'\<close> have "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> !Q \<longmapsto>K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q''" 
      by(metis statEqTransition Identity compositionSym AssertionStatEqSym)
    moreover from \<open>\<Psi> \<turnstile> M \<leftrightarrow> K\<close> \<open>\<Psi>\<^sub>Q \<simeq> SBottom'\<close> have "\<Psi> \<otimes> \<Psi>\<^sub>Q \<otimes> SBottom' \<turnstile> M \<leftrightarrow> K" by(metis statEqEnt Identity compositionSym AssertionStatEqSym)
    ultimately have "\<Psi> \<rhd> Q \<parallel> !Q \<longmapsto>\<tau> \<prec> (\<lparr>\<nu>*xvec\<rparr>(Q' \<parallel> Q''))" using \<open>A\<^sub>Q \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q \<sharp>* Q\<close> \<open>A\<^sub>Q \<sharp>* M\<close> \<open>xvec \<sharp>* Q\<close>
      by(rule_tac Comm1) (assumption | simp)+
    hence "\<Psi> \<rhd> !Q \<longmapsto>\<tau> \<prec> (\<lparr>\<nu>*xvec\<rparr>(Q' \<parallel> Q''))" using \<open>guarded Q\<close> by(rule Bang)
    moreover from \<open>\<Psi> \<rhd> P'' \<sim> R \<parallel> !P\<close> \<open>guarded P\<close> \<open>xvec \<sharp>* \<Psi>\<close> have "\<Psi> \<rhd> \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> P'') \<sim> \<lparr>\<nu>*xvec\<rparr>((P' \<parallel> R) \<parallel> (P \<parallel> !P))"
      by(metis bisimParPresSym bangExt bisimTransitive bisimParAssoc bisimSymmetric bisimResChainPres)
    with \<open>xvec \<sharp>* \<Psi>\<close> \<open>xvec \<sharp>* P\<close> have "\<Psi> \<rhd> \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> P'') \<sim> (\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> R)) \<parallel> (P \<parallel> !P)"
      by(metis bisimScopeExtChainSym bisimTransitive psiFreshVec)
    moreover from \<open>\<Psi> \<rhd> Q'' \<sim> T \<parallel> !Q\<close> \<open>xvec \<sharp>* \<Psi>\<close> \<open>xvec \<sharp>* Q\<close> have "\<Psi> \<rhd> \<lparr>\<nu>*xvec\<rparr>(Q' \<parallel> Q'') \<sim> (\<lparr>\<nu>*xvec\<rparr>(Q' \<parallel> T)) \<parallel> !Q"
      by(metis bisimParPresSym bisimTransitive bisimParAssoc bisimSymmetric bisimResChainPres bisimScopeExtChainSym psiFreshVec)
    moreover from \<open>\<Psi> \<rhd> R \<sim> T\<close> \<open>\<Psi> \<rhd> Q' \<sim> P'\<close> \<open>xvec \<sharp>* \<Psi>\<close> have "\<Psi> \<rhd> \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> R) \<sim> \<lparr>\<nu>*xvec\<rparr>(Q' \<parallel> T)"
      by(metis bisimParPresSym bisimTransitive bisimResChainPres bisimParComm bisimE(4))
    moreover from suppR have "((supp(\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> R)))::name set) \<subseteq>  supp((\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> P'')))"
      by(auto simp add: psi.supp resChainSupp)
    moreover from suppT have "((supp(\<lparr>\<nu>*xvec\<rparr>(Q' \<parallel> T)))::name set) \<subseteq>  supp((\<lparr>\<nu>*xvec\<rparr>(Q' \<parallel> Q'')))"
      by(auto simp add: psi.supp resChainSupp)
    ultimately show ?case by blast
  next
    case(cComm2 M xvec N P' K P'' Q)
    from \<open>\<Psi> \<rhd> P \<sim> Q\<close> \<open>\<Psi> \<rhd> P \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'\<close> \<open>xvec \<sharp>* \<Psi>\<close> \<open>xvec \<sharp>* Q\<close> 
    obtain Q' where QTrans: "\<Psi> \<rhd> Q \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'" and "\<Psi> \<rhd> P' \<sim> Q'"
      by(metis bisimE simE bn.simps)
    from QTrans have "\<Psi> \<otimes> SBottom' \<rhd> Q \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'" by(metis statEqTransition Identity AssertionStatEqSym)
    moreover obtain A\<^sub>Q \<Psi>\<^sub>Q where FrQ: "extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" and "A\<^sub>Q \<sharp>* \<Psi>" and "A\<^sub>Q \<sharp>* Q" and "A\<^sub>Q \<sharp>* M" 
      by(rule_tac C="(\<Psi>, Q, M)" in freshFrame) auto
    note FrQ
    moreover from FrQ \<open>guarded Q\<close> have "\<Psi>\<^sub>Q \<simeq> SBottom'" by(blast dest: guardedStatEq)
    from \<open>\<Psi> \<rhd> !P \<longmapsto>K\<lparr>N\<rparr> \<prec> P''\<close> \<open>\<Psi> \<rhd> P \<sim> Q\<close> \<open>guarded Q\<close>
   obtain Q'' T R where QTrans': "\<Psi> \<rhd> !Q \<longmapsto>K\<lparr>N\<rparr> \<prec> Q''" and "\<Psi> \<rhd> P'' \<sim> R \<parallel> !P" and "\<Psi> \<rhd> Q'' \<sim> T \<parallel> !Q" and "\<Psi> \<rhd> R \<sim> T"
                    and suppR: "((supp R)::name set) \<subseteq> supp P''" and suppT: "((supp T)::name set) \<subseteq> supp Q''" using cComm2
     by fastforce
    from QTrans' \<open>\<Psi>\<^sub>Q \<simeq> SBottom'\<close> have "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> !Q \<longmapsto>K\<lparr>N\<rparr> \<prec> Q''" 
      by(metis statEqTransition Identity compositionSym AssertionStatEqSym)
    moreover from \<open>\<Psi> \<turnstile> M \<leftrightarrow> K\<close> \<open>\<Psi>\<^sub>Q \<simeq> SBottom'\<close> have "\<Psi> \<otimes> \<Psi>\<^sub>Q \<otimes> SBottom' \<turnstile> M \<leftrightarrow> K" by(metis statEqEnt Identity compositionSym AssertionStatEqSym)
    ultimately have "\<Psi> \<rhd> Q \<parallel> !Q \<longmapsto>\<tau> \<prec> (\<lparr>\<nu>*xvec\<rparr>(Q' \<parallel> Q''))" using \<open>A\<^sub>Q \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q \<sharp>* Q\<close> \<open>A\<^sub>Q \<sharp>* M\<close> \<open>xvec \<sharp>* Q\<close>
      by(rule_tac Comm2) (assumption | simp)+
    hence "\<Psi> \<rhd> !Q \<longmapsto>\<tau> \<prec> (\<lparr>\<nu>*xvec\<rparr>(Q' \<parallel> Q''))" using \<open>guarded Q\<close> by(rule Bang)
    moreover from \<open>\<Psi> \<rhd> P'' \<sim> R \<parallel> !P\<close> \<open>guarded P\<close> \<open>xvec \<sharp>* \<Psi>\<close> have "\<Psi> \<rhd> \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> P'') \<sim> \<lparr>\<nu>*xvec\<rparr>((P' \<parallel> R) \<parallel> (P \<parallel> !P))"
      by(metis bisimParPresSym bangExt bisimTransitive bisimParAssoc bisimSymmetric bisimResChainPres)
    with \<open>xvec \<sharp>* \<Psi>\<close> \<open>xvec \<sharp>* P\<close> have "\<Psi> \<rhd> \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> P'') \<sim> (\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> R)) \<parallel> (P \<parallel> !P)"
      by(metis bisimScopeExtChainSym bisimTransitive psiFreshVec)
    moreover from \<open>\<Psi> \<rhd> Q'' \<sim> T \<parallel> !Q\<close> \<open>xvec \<sharp>* \<Psi>\<close> \<open>xvec \<sharp>* Q\<close> have "\<Psi> \<rhd> \<lparr>\<nu>*xvec\<rparr>(Q' \<parallel> Q'') \<sim> (\<lparr>\<nu>*xvec\<rparr>(Q' \<parallel> T)) \<parallel> !Q"
      by(metis bisimParPresSym bisimTransitive bisimParAssoc bisimSymmetric bisimResChainPres bisimScopeExtChainSym psiFreshVec)
    moreover from \<open>\<Psi> \<rhd> R \<sim> T\<close> \<open>\<Psi> \<rhd> P' \<sim> Q'\<close> \<open>xvec \<sharp>* \<Psi>\<close> have "\<Psi> \<rhd> \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> R) \<sim> \<lparr>\<nu>*xvec\<rparr>(Q' \<parallel> T)"
      by(metis bisimParPresSym bisimTransitive bisimResChainPres bisimParComm)
    moreover from suppR have "((supp(\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> R)))::name set) \<subseteq>  supp((\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> P'')))"
      by(auto simp add: psi.supp resChainSupp)
    moreover from suppT have "((supp(\<lparr>\<nu>*xvec\<rparr>(Q' \<parallel> T)))::name set) \<subseteq>  supp((\<lparr>\<nu>*xvec\<rparr>(Q' \<parallel> Q'')))"
      by(auto simp add: psi.supp resChainSupp)
    ultimately show ?case by blast
  next
    case(cBang \<alpha> P' Q)
    then obtain Q' T R where QTrans: "\<Psi> \<rhd> !Q \<longmapsto>\<alpha> \<prec> Q'" and "\<Psi> \<rhd> P' \<sim> R \<parallel> (P \<parallel> !P)" and "\<Psi> \<rhd> Q' \<sim> T \<parallel> !Q" and "\<Psi> \<rhd> R \<sim> T"
                         and suppR: "((supp R)::name set) \<subseteq> supp P'" and suppT: "((supp T)::name set) \<subseteq> supp Q'"
      by blast
    from \<open>\<Psi> \<rhd> P' \<sim> R \<parallel> (P \<parallel> !P)\<close> \<open>guarded P\<close> have "\<Psi> \<rhd> P' \<sim> R \<parallel> !P" by(metis bangExt bisimParPresSym bisimTransitive bisimSymmetric)
    with QTrans show ?case using \<open>\<Psi> \<rhd> Q' \<sim> T \<parallel> !Q\<close> \<open>\<Psi> \<rhd> R \<sim> T\<close> suppR suppT
      by blast
  qed
  ultimately show ?thesis by blast
qed

lemma structCongBisim:
  fixes P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"

  assumes "P \<equiv>\<^sub>s Q"

  shows "P \<sim> Q"
using assms
by(induct rule: structCong.induct)
  (auto intro: bisimReflexive bisimSymmetric bisimTransitive bisimParComm bisimParAssoc bisimParNil bisimResNil bisimResComm bisimScopeExt bisimCasePushRes bisimInputPushRes bisimOutputPushRes bangExt)

lemma bisimBangPres:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"

  assumes "\<Psi> \<rhd> P \<sim> Q"
  and     "guarded P"
  and     "guarded Q"

  shows "\<Psi> \<rhd> !P \<sim> !Q"
proof -
  let ?X = "{(\<Psi>, R \<parallel> !P, R \<parallel> !Q) | \<Psi> P Q R. \<Psi> \<rhd> P \<sim> Q \<and> guarded P \<and> guarded Q}"
  let ?Y = "{(\<Psi>, P, Q) | \<Psi> P P' Q' Q. \<Psi> \<rhd> P \<sim> P' \<and> (\<Psi>, P', Q') \<in> ?X \<and> \<Psi> \<rhd> Q' \<sim> Q}"
  from assms have "(\<Psi>, \<zero> \<parallel> !P, \<zero> \<parallel> !Q) \<in> ?X" by(blast intro: bisimReflexive)

  moreover have "eqvt ?X" 
    apply(auto simp add: eqvt_def)
    apply(drule_tac p=p in bisimClosed)
    by fastforce
  ultimately have "\<Psi> \<rhd> \<zero> \<parallel> !P \<sim> \<zero> \<parallel> !Q"
  proof(coinduct rule: weakTransitiveCoinduct)
    case(cStatEq \<Psi> P Q)
    thus ?case by auto
  next
    case(cSim \<Psi> RP RQ)
    from \<open>(\<Psi>, RP, RQ) \<in> ?X\<close> obtain P Q R where "\<Psi> \<rhd> P \<sim> Q" and "guarded P" and "guarded Q"
                                           and "RP = R \<parallel> !P" and "RQ = R \<parallel> !Q"
      by auto
    note \<open>\<Psi> \<rhd> P \<sim> Q\<close> 
    moreover from \<open>eqvt ?X\<close> have "eqvt ?Y" by blast
    moreover note \<open>guarded P\<close> \<open>guarded Q\<close> bisimE(2) bisimE(3) bisimE(4) statEqBisim bisimClosed bisimParAssoc[THEN bisimSymmetric] 
                  bisimParPres bisimParPresAuxSym bisimResChainPres bisimScopeExtChainSym bisimTransitive
    moreover have "\<And>\<Psi> P Q R T. \<lbrakk>\<Psi> \<rhd> P \<sim> Q; (\<Psi>, Q, R) \<in> ?Y; \<Psi> \<rhd> R \<sim> T\<rbrakk> \<Longrightarrow> (\<Psi>, P, T) \<in> ?Y"
      by auto (metis bisimTransitive)
    moreover have "\<And>\<Psi> P Q R. \<lbrakk>\<Psi> \<rhd> P \<sim> Q; guarded P; guarded Q\<rbrakk> \<Longrightarrow> (\<Psi>, R \<parallel> !P, R \<parallel> !Q) \<in> ?Y" by(blast intro: bisimReflexive)
    moreover have "\<And>\<Psi> P \<alpha> P' Q. \<lbrakk>\<Psi> \<rhd> !P \<longmapsto>\<alpha> \<prec> P'; \<Psi> \<rhd> P \<sim> Q; bn \<alpha> \<sharp>* \<Psi>;  bn \<alpha> \<sharp>* P;  bn \<alpha> \<sharp>* Q; guarded Q; bn \<alpha> \<sharp>* subject \<alpha>\<rbrakk> \<Longrightarrow>
                                         \<exists>Q' R T.  \<Psi> \<rhd> !Q \<longmapsto>\<alpha> \<prec> Q' \<and> \<Psi> \<rhd> P' \<sim> R \<parallel> !P \<and>  \<Psi> \<rhd> Q' \<sim> T \<parallel> !Q \<and>
                                                   \<Psi> \<rhd> R \<sim> T \<and> ((supp R)::name set) \<subseteq> supp P' \<and> 
                                                   ((supp T)::name set) \<subseteq> supp Q'"
      by(blast elim: bangDerivative)
    ultimately have "\<Psi> \<rhd> R \<parallel> !P \<leadsto>[?Y] R \<parallel> !Q"
      by(rule bangPres)
    with \<open>RP = R \<parallel> !P\<close> \<open>RQ = R \<parallel> !Q\<close> show ?case
      by blast
  next
    case(cExt \<Psi> RP RQ \<Psi>')
    thus ?case by(blast dest: bisimE)
  next
    case(cSym \<Psi> RP RQ)
    thus ?case by(blast dest: bisimE)
  qed
  thus ?thesis
    by(metis bisimTransitive bisimParNil bisimSymmetric bisimParComm)
qed

end

end
