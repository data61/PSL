(* 
   Title: Psi-calculi   
   Author/Maintainer: Jesper Bengtson (jebe@itu.dk), 2012
*)
theory Sim_Struct_Cong
  imports Simulation
begin

lemma partitionListLeft:
  assumes "xs@ys=xs'@y#ys'"
  and     "y mem xs"
  and     "distinct(xs@ys)"

  obtains zs where "xs = xs'@y#zs" and "ys'=zs@ys"
using assms
by(auto simp add: append_eq_append_conv2 append_eq_Cons_conv)

lemma partitionListRight: 
  assumes "xs@ys=xs'@y#ys'"
  and     "y mem ys"
  and     "distinct(xs@ys)"

  obtains zs where "xs' = xs@zs" and "ys=zs@y#ys'"
using assms
by(force simp add: append_eq_append_conv2 append_eq_Cons_conv)

context env begin

lemma resComm:
  fixes \<Psi>   :: 'b
  and   x   :: name
  and   y   :: name
  and   Rel :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
  and   P   :: "('a, 'b, 'c) psi"
  
  assumes "x \<sharp> \<Psi>"
  and     "y \<sharp> \<Psi>"
  and     "eqvt Rel"
  and     R1: "\<And>\<Psi>' Q. (\<Psi>', Q, Q) \<in> Rel"
  and     R2: "\<And>\<Psi>' a b Q. \<lbrakk>a \<sharp> \<Psi>'; b \<sharp> \<Psi>'\<rbrakk> \<Longrightarrow> (\<Psi>', \<lparr>\<nu>a\<rparr>(\<lparr>\<nu>b\<rparr>Q), \<lparr>\<nu>b\<rparr>(\<lparr>\<nu>a\<rparr>Q)) \<in> Rel"

  shows "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>y\<rparr>P) \<leadsto>[Rel] \<lparr>\<nu>y\<rparr>(\<lparr>\<nu>x\<rparr>P)"
proof(case_tac "x=y")
  assume "x = y"
  thus ?thesis using R1
    by(force intro: reflexive)
next
  assume "x \<noteq> y"
  note \<open>eqvt Rel\<close>
  moreover from \<open>x \<sharp> \<Psi>\<close> \<open>y \<sharp> \<Psi>\<close> have "[x, y] \<sharp>* \<Psi>" by(simp add: fresh_star_def)
  moreover have "[x, y] \<sharp>* \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>y\<rparr>P)" by(simp add: abs_fresh)
  moreover have "[x, y] \<sharp>* \<lparr>\<nu>y\<rparr>(\<lparr>\<nu>x\<rparr>P)" by(simp add: abs_fresh)
  ultimately show ?thesis
  proof(induct rule: simIChainFresh[where C="(x, y)"])
    case(cSim \<alpha> P')
    from \<open>bn \<alpha> \<sharp>* (x, y)\<close> \<open>bn \<alpha> \<sharp>* (\<lparr>\<nu>x\<rparr>(\<lparr>\<nu>y\<rparr>P))\<close> have "x \<sharp> bn \<alpha>" and "y \<sharp> bn \<alpha>" and "bn \<alpha> \<sharp>* P" by simp+
    from \<open>[x, y] \<sharp>* \<alpha>\<close> have "x \<sharp> \<alpha>" and "y \<sharp> \<alpha>" by simp+
    from \<open>[x, y] \<sharp>* P'\<close> have "x \<sharp> P'" and "y \<sharp> P'" by simp+
    from \<open>bn \<alpha> \<sharp>* P\<close> \<open>x \<sharp> \<alpha>\<close> have "bn \<alpha> \<sharp>* \<lparr>\<nu>x\<rparr>P" by(simp add: abs_fresh)
    with \<open>\<Psi> \<rhd> \<lparr>\<nu>y\<rparr>(\<lparr>\<nu>x\<rparr>P) \<longmapsto>\<alpha> \<prec> P'\<close> \<open>y \<sharp> \<Psi>\<close> \<open>y \<sharp> \<alpha>\<close> \<open>y \<sharp> P'\<close> \<open>bn \<alpha> \<sharp>* \<Psi>\<close>
    show ?case using \<open>bn \<alpha> \<sharp>* subject \<alpha>\<close> \<open>x \<sharp> \<alpha>\<close> \<open>x \<sharp> P'\<close> \<open>bn \<alpha> \<sharp>* \<Psi>\<close> \<open>bn \<alpha> \<sharp>* P\<close> \<open>bn \<alpha> \<sharp>* subject \<alpha>\<close> \<open>y \<sharp> \<alpha>\<close>
    proof(induct rule: resCases')
      case(cOpen M yvec1 yvec2 y' N P')
      from \<open>yvec1 \<sharp>* yvec2\<close> \<open>distinct yvec1\<close> \<open>distinct yvec2\<close> have "distinct(yvec1@yvec2)" by auto
      from \<open>x \<sharp> M\<lparr>\<nu>*(yvec1 @ y' # yvec2)\<rparr>\<langle>N\<rangle>\<close> have "x \<sharp> M" and "x \<sharp> yvec1" and "x \<noteq> y'" and "x \<sharp> yvec2" and "x \<sharp> N"
        by simp+
      from \<open>y \<sharp> M\<lparr>\<nu>*(yvec1 @ y' # yvec2)\<rparr>\<langle>N\<rangle>\<close> have "y \<sharp> M" and "y \<sharp> yvec1" and "y \<sharp> yvec2"
        by simp+
      from \<open>\<Psi> \<rhd> ([(y, y')] \<bullet> \<lparr>\<nu>x\<rparr>P) \<longmapsto>M\<lparr>\<nu>*(yvec1@yvec2)\<rparr>\<langle>N\<rangle> \<prec> P'\<close> \<open>x \<noteq> y\<close> \<open>x \<noteq> y'\<close>
      have "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>([(y, y')] \<bullet> P) \<longmapsto>M\<lparr>\<nu>*(yvec1@yvec2)\<rparr>\<langle>N\<rangle> \<prec> P'" by(simp add: eqvts)
      moreover note \<open>x \<sharp> \<Psi>\<close>
      moreover from \<open>x \<sharp> N\<close> \<open>x \<sharp> yvec1\<close> \<open>x \<sharp> yvec2\<close> \<open>x \<sharp> M\<close> have "x \<sharp> M\<lparr>\<nu>*(yvec1@yvec2)\<rparr>\<langle>N\<rangle>" by simp
      moreover note \<open>x \<sharp> P'\<close>
      moreover from \<open>yvec1 \<sharp>* \<Psi>\<close> \<open>yvec2 \<sharp>* \<Psi>\<close> have "bn(M\<lparr>\<nu>*(yvec1@yvec2)\<rparr>\<langle>N\<rangle>) \<sharp>* \<Psi>" by simp
      moreover from \<open>yvec1 \<sharp>* \<lparr>\<nu>x\<rparr>P\<close> \<open>yvec2 \<sharp>* \<lparr>\<nu>x\<rparr>P\<close> \<open>y \<sharp> yvec1\<close> \<open>y' \<sharp> yvec1\<close> \<open>y \<sharp> yvec2\<close> \<open>y' \<sharp> yvec2\<close> \<open>x \<sharp> yvec1\<close> \<open>x \<sharp> yvec2\<close>
      have "bn(M\<lparr>\<nu>*(yvec1@yvec2)\<rparr>\<langle>N\<rangle>) \<sharp>* ([(y, y')] \<bullet> P)" by simp
      moreover from \<open>yvec1 \<sharp>* M\<close> \<open>yvec2 \<sharp>* M\<close> have "bn(M\<lparr>\<nu>*(yvec1 @ yvec2)\<rparr>\<langle>N\<rangle>) \<sharp>* subject(M\<lparr>\<nu>*(yvec1 @ yvec2)\<rparr>\<langle>N\<rangle>)"
        by simp
      moreover have "bn(M\<lparr>\<nu>*(yvec1 @ yvec2)\<rparr>\<langle>N\<rangle>) = yvec1@yvec2" by simp
      moreover have "subject(M\<lparr>\<nu>*(yvec1 @ yvec2)\<rparr>\<langle>N\<rangle>) = Some M" by simp
      moreover have "object(M\<lparr>\<nu>*(yvec1 @ yvec2)\<rparr>\<langle>N\<rangle>) = Some N" by simp
      ultimately show ?case 
      proof(induct rule: resCases')
        case(cOpen M' xvec1 xvec2 x' N' P')
        from \<open>bn(M'\<lparr>\<nu>*(xvec1 @ x' # xvec2)\<rparr>\<langle>N'\<rangle>) = yvec1 @ yvec2\<close> have "yvec1@yvec2 = xvec1@x'#xvec2" by simp
        from \<open>subject(M'\<lparr>\<nu>*(xvec1 @ x' # xvec2)\<rparr>\<langle>N'\<rangle>) = Some M\<close> have "M = M'" by simp
        from \<open>object(M'\<lparr>\<nu>*(xvec1 @ x' # xvec2)\<rparr>\<langle>N'\<rangle>) = Some N\<close> have "N = N'" by simp
        from \<open>x \<sharp> yvec1\<close> \<open>x \<sharp> yvec2\<close> \<open>y' \<sharp> yvec1\<close> \<open>y' \<sharp> yvec2\<close> \<open>y \<sharp> yvec1\<close> \<open>y \<sharp> yvec2\<close>
        have "x \<sharp> (yvec1@yvec2)" and "y \<sharp> (yvec1@yvec2)" and "y' \<sharp> (yvec1@yvec2)" by simp+
        with \<open>yvec1@yvec2 = xvec1@x'#xvec2\<close>
        have "x \<sharp> xvec1" and "x \<noteq> x'" and "x \<sharp> xvec2" and "y \<sharp> xvec1" and "y \<noteq> x'" and "y \<sharp> xvec2"
          and "y' \<sharp> xvec1" and "x' \<noteq> y'" and "y' \<sharp> xvec2"
          by auto

        show ?case
        proof(case_tac "x' mem yvec1")
          assume "x' mem yvec1"
        
          with \<open>yvec1@yvec2 = xvec1@x'#xvec2\<close> \<open>distinct (yvec1@yvec2)\<close>
          obtain xvec2' where Eq1: "yvec1=xvec1@x'#xvec2'"
                          and Eq: "xvec2=xvec2'@yvec2"
            by(rule_tac partitionListLeft)
          from \<open>\<Psi> \<rhd> ([(x, x')] \<bullet> [(y, y')] \<bullet> P) \<longmapsto>M'\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>N'\<rangle> \<prec> P'\<close> \<open>y' \<in> supp N\<close> \<open>y' \<sharp> \<Psi>\<close> \<open>y' \<sharp> M\<close> \<open>y' \<sharp> xvec1\<close> \<open>y' \<sharp> xvec2\<close> Eq \<open>M=M'\<close> \<open>N = N'\<close>
          have "\<Psi> \<rhd> \<lparr>\<nu>y'\<rparr>([(x, x')] \<bullet> [(y, y')] \<bullet> P) \<longmapsto>M'\<lparr>\<nu>*((xvec1@xvec2')@y'#yvec2)\<rparr>\<langle>N'\<rangle> \<prec> P'" 
            by(rule_tac Open) auto
          then have "\<Psi> \<rhd> \<lparr>\<nu>x'\<rparr>(\<lparr>\<nu>y'\<rparr>([(x, x')] \<bullet> [(y, y')] \<bullet> P)) \<longmapsto>M\<lparr>\<nu>*(xvec1@x'#xvec2'@y'#yvec2)\<rparr>\<langle>N\<rangle> \<prec> P'" 
            using \<open>x' \<in> supp N'\<close> \<open>x' \<sharp> \<Psi>\<close> \<open>x' \<sharp> M'\<close> \<open>x' \<sharp> xvec1\<close> \<open>x' \<sharp> xvec2\<close> \<open>x' \<noteq> y'\<close> Eq \<open>M=M'\<close> \<open>N=N'\<close>
            by(rule_tac Open) auto
          with \<open>x' \<noteq> y'\<close> \<open>x \<noteq> y'\<close> \<open>x' \<sharp> [(y, y')] \<bullet> P\<close>
          have "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>y'\<rparr>([(y, y')] \<bullet> P)) \<longmapsto>M\<lparr>\<nu>*(xvec1@x'#xvec2'@y'#yvec2)\<rparr>\<langle>N\<rangle> \<prec> P'"
            by(subst alphaRes[where y=x']) (simp add: calc_atm eqvts abs_fresh)+
          with Eq1 \<open>y' \<sharp> \<lparr>\<nu>x\<rparr>P\<close> \<open>x \<noteq> y'\<close> R1 show ?case
            by(fastforce simp add: alphaRes abs_fresh)
        next
          assume "\<not>x' mem yvec1"
          hence "x' \<sharp> yvec1" by(simp add: fresh_def)
          from \<open>\<not>x' mem yvec1\<close> \<open>yvec1@yvec2 = xvec1@x'#xvec2\<close>
          have "x' mem yvec2"
            by(fastforce simp add: append_eq_append_conv2 append_eq_Cons_conv
                                  fresh_list_append fresh_list_cons)
          with \<open>yvec1@yvec2 = xvec1@x'#xvec2\<close> \<open>distinct (yvec1@yvec2)\<close>
          obtain xvec2' where Eq: "xvec1=yvec1@xvec2'"
                          and Eq1: "yvec2=xvec2'@x'#xvec2"
            by(rule_tac partitionListRight)
          from \<open>\<Psi> \<rhd> ([(x, x')] \<bullet> [(y, y')] \<bullet> P) \<longmapsto>M'\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>N'\<rangle> \<prec> P'\<close> \<open>y' \<in> supp N\<close> \<open>y' \<sharp> \<Psi>\<close> \<open>y' \<sharp> M\<close> \<open>y' \<sharp> xvec1\<close> \<open>y' \<sharp> xvec2\<close> Eq \<open>M=M'\<close> \<open>N = N'\<close>
          have "\<Psi> \<rhd> \<lparr>\<nu>y'\<rparr>([(x, x')] \<bullet> [(y, y')] \<bullet> P) \<longmapsto>M'\<lparr>\<nu>*(yvec1@y'#xvec2'@xvec2)\<rparr>\<langle>N'\<rangle> \<prec> P'" 
            by(rule_tac Open) (assumption | simp)+
          then have "\<Psi> \<rhd> \<lparr>\<nu>x'\<rparr>(\<lparr>\<nu>y'\<rparr>([(x, x')] \<bullet> [(y, y')] \<bullet> P)) \<longmapsto>M\<lparr>\<nu>*((yvec1@y'#xvec2')@x'#xvec2)\<rparr>\<langle>N\<rangle> \<prec> P'" 
            using \<open>x' \<in> supp N'\<close> \<open>x' \<sharp> \<Psi>\<close> \<open>x' \<sharp> M'\<close> \<open>x' \<sharp> xvec1\<close> \<open>x' \<sharp> xvec2\<close> \<open>x' \<noteq> y'\<close> Eq \<open>M=M'\<close> \<open>N=N'\<close>
            by(rule_tac Open) auto
          with \<open>x' \<noteq> y'\<close> \<open>x \<noteq> y'\<close> \<open>x' \<sharp> [(y, y')] \<bullet> P\<close>
          have "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>y'\<rparr>([(y, y')] \<bullet> P)) \<longmapsto>M\<lparr>\<nu>*((yvec1@y'#xvec2')@x'#xvec2)\<rparr>\<langle>N\<rangle> \<prec> P'"
            by(subst alphaRes[where y=x']) (simp add: calc_atm eqvts abs_fresh)+
          with Eq1 \<open>y' \<sharp> \<lparr>\<nu>x\<rparr>P\<close> \<open>x \<noteq> y'\<close> R1 show ?case
            by(fastforce simp add: alphaRes abs_fresh)
        qed
      next
        case(cRes P')
        from \<open>\<Psi> \<rhd> ([(y, y')] \<bullet> P) \<longmapsto>M\<lparr>\<nu>*(yvec1@yvec2)\<rparr>\<langle>N\<rangle> \<prec> P'\<close> \<open>y' \<in> supp N\<close> \<open>y' \<sharp> \<Psi>\<close> \<open>y' \<sharp> M\<close> \<open>y' \<sharp> yvec1\<close> \<open>y' \<sharp> yvec2\<close>
        have "\<Psi> \<rhd> \<lparr>\<nu>y'\<rparr>([(y, y')] \<bullet> P) \<longmapsto>M\<lparr>\<nu>*(yvec1@y'#yvec2)\<rparr>\<langle>N\<rangle> \<prec> P'" by(rule Open)
        with \<open>y' \<sharp> \<lparr>\<nu>x\<rparr>P\<close> \<open>x \<noteq> y'\<close>have "\<Psi> \<rhd> \<lparr>\<nu>y\<rparr>P \<longmapsto>M\<lparr>\<nu>*(yvec1@y'#yvec2)\<rparr>\<langle>N\<rangle> \<prec> P'" by(simp add: alphaRes abs_fresh)
        hence "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>y\<rparr>P) \<longmapsto>M\<lparr>\<nu>*(yvec1@y'#yvec2)\<rparr>\<langle>N\<rangle> \<prec> \<lparr>\<nu>x\<rparr>P'" using \<open>x \<sharp> \<Psi>\<close> \<open>x \<sharp> M\<close> \<open>x \<sharp> yvec1\<close> \<open>x \<noteq> y'\<close> \<open>x \<sharp> yvec2\<close> \<open>x \<sharp> N\<close>
          by(rule_tac Scope) auto
        moreover have "(\<Psi>, \<lparr>\<nu>x\<rparr>P', \<lparr>\<nu>x\<rparr>P') \<in> Rel" by(rule R1)
        ultimately show ?case by blast
      qed
    next
      case(cRes P')
      from \<open>x \<sharp> \<lparr>\<nu>y\<rparr>P'\<close> \<open>x \<noteq> y\<close> have "x \<sharp> P'" by(simp add: abs_fresh)
      with \<open>\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>P \<longmapsto>\<alpha> \<prec> P'\<close> \<open>x \<sharp> \<Psi>\<close> \<open>x \<sharp> \<alpha>\<close>
      show ?case using \<open>bn \<alpha> \<sharp>* \<Psi>\<close> \<open>bn \<alpha> \<sharp>* P\<close> \<open>bn \<alpha> \<sharp>* subject \<alpha>\<close> \<open>y \<sharp> \<alpha>\<close>
      proof(induct rule: resCases')
        case(cOpen M xvec1 xvec2 x' N P')
        from \<open>y \<sharp> M\<lparr>\<nu>*(xvec1@x'#xvec2)\<rparr>\<langle>N\<rangle>\<close> have "y \<noteq> x'" and "y \<sharp> M\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>N\<rangle>" by simp+
        from \<open>\<Psi> \<rhd> ([(x, x')] \<bullet> P) \<longmapsto>M\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>N\<rangle> \<prec> P'\<close> \<open>y \<sharp> \<Psi>\<close> \<open>y \<sharp> M\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>N\<rangle>\<close>
        have "\<Psi> \<rhd> \<lparr>\<nu>y\<rparr>([(x, x')] \<bullet> P) \<longmapsto>M\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>N\<rangle> \<prec> \<lparr>\<nu>y\<rparr>P'" 
          by(rule Scope)
        hence "\<Psi> \<rhd> \<lparr>\<nu>x'\<rparr>(\<lparr>\<nu>y\<rparr>([(x, x')] \<bullet> P)) \<longmapsto>M\<lparr>\<nu>*(xvec1@x'#xvec2)\<rparr>\<langle>N\<rangle> \<prec> \<lparr>\<nu>y\<rparr>P'" 
          using \<open>x' \<in> supp N\<close> \<open>x' \<sharp> \<Psi>\<close> \<open>x' \<sharp> M\<close> \<open>x' \<sharp> xvec1\<close> \<open>x' \<sharp> xvec2\<close>
          by(rule Open)
        with \<open>y \<noteq> x'\<close> \<open>x \<noteq> y\<close> \<open>x' \<sharp> P\<close> have "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>y\<rparr>P) \<longmapsto>M\<lparr>\<nu>*(xvec1@x'#xvec2)\<rparr>\<langle>N\<rangle> \<prec> \<lparr>\<nu>y\<rparr>P'"
          by(subst alphaRes[where y=x']) (simp add: abs_fresh eqvts calc_atm)+
        moreover have "(\<Psi>, \<lparr>\<nu>y\<rparr>P', \<lparr>\<nu>y\<rparr>P') \<in> Rel" by(rule R1)
        ultimately show ?case by blast
      next
        case(cRes P')
        from \<open>\<Psi> \<rhd> P \<longmapsto>\<alpha> \<prec> P'\<close> \<open>y \<sharp> \<Psi>\<close> \<open>y \<sharp> \<alpha>\<close>
        have "\<Psi> \<rhd> \<lparr>\<nu>y\<rparr>P \<longmapsto>\<alpha> \<prec> \<lparr>\<nu>y\<rparr>P'" by(rule Scope)
        hence "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>y\<rparr>P) \<longmapsto>\<alpha> \<prec> \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>y\<rparr>P')" using \<open>x \<sharp> \<Psi>\<close> \<open>x \<sharp> \<alpha>\<close>
          by(rule Scope)
        moreover from \<open>x \<sharp> \<Psi>\<close> \<open>y \<sharp> \<Psi>\<close> have "(\<Psi>, \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>y\<rparr>P'), \<lparr>\<nu>y\<rparr>(\<lparr>\<nu>x\<rparr>P')) \<in> Rel"
          by(rule R2)
        ultimately show ?case by blast
      qed
    qed
  qed
qed

lemma parAssocLeft:
  fixes \<Psi>   :: 'b
  and   P   :: "('a, 'b, 'c) psi"
  and   Q   :: "('a, 'b, 'c) psi"
  and   R   :: "('a, 'b, 'c) psi"
  and   Rel :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"

  assumes "eqvt Rel"
  and     C1: "\<And>\<Psi>' S T U. (\<Psi>, (S \<parallel> T) \<parallel> U, S \<parallel> (T \<parallel> U)) \<in> Rel"
  and     C2: "\<And>xvec \<Psi>' S T U. \<lbrakk>xvec \<sharp>* \<Psi>'; xvec \<sharp>* S\<rbrakk> \<Longrightarrow> (\<Psi>', \<lparr>\<nu>*xvec\<rparr>((S \<parallel> T) \<parallel> U), S \<parallel> (\<lparr>\<nu>*xvec\<rparr>(T \<parallel> U))) \<in> Rel"
  and     C3: "\<And>xvec \<Psi>' S T U. \<lbrakk>xvec \<sharp>* \<Psi>'; xvec \<sharp>* U\<rbrakk> \<Longrightarrow> (\<Psi>', (\<lparr>\<nu>*xvec\<rparr>(S \<parallel> T)) \<parallel> U, \<lparr>\<nu>*xvec\<rparr>(S \<parallel> (T \<parallel> U))) \<in> Rel"
  and     C4: "\<And>\<Psi>' S T xvec. \<lbrakk>(\<Psi>', S, T) \<in> Rel; xvec \<sharp>* \<Psi>'\<rbrakk> \<Longrightarrow> (\<Psi>', \<lparr>\<nu>*xvec\<rparr>S, \<lparr>\<nu>*xvec\<rparr>T) \<in> Rel"

  shows "\<Psi> \<rhd> (P \<parallel> Q) \<parallel> R \<leadsto>[Rel] P \<parallel> (Q \<parallel> R)"
using \<open>eqvt Rel\<close>
proof(induct rule: simI[of _ _ _ _ "()"])
  case(cSim \<alpha> PQR) 
  from \<open>bn \<alpha> \<sharp>* (P \<parallel> Q \<parallel> R)\<close> have "bn \<alpha> \<sharp>* P" and "bn \<alpha> \<sharp>* Q" and "bn \<alpha> \<sharp>* R" by simp+
  hence "bn \<alpha> \<sharp>* (Q \<parallel> R)" by simp
  with \<open>\<Psi> \<rhd> P \<parallel> (Q \<parallel> R) \<longmapsto>\<alpha> \<prec> PQR\<close> \<open>bn \<alpha> \<sharp>* \<Psi>\<close> \<open>bn \<alpha> \<sharp>* P\<close>
  show ?case using \<open>bn \<alpha> \<sharp>* subject \<alpha>\<close>
  proof(induct rule: parCases[where C = "(\<Psi>, P, Q, R, \<alpha>)"])
    case(cPar1 P' A\<^sub>Q\<^sub>R \<Psi>\<^sub>Q\<^sub>R)
    from \<open>A\<^sub>Q\<^sub>R \<sharp>* (\<Psi>, P, Q, R, \<alpha>)\<close> have "A\<^sub>Q\<^sub>R \<sharp>* Q" and  "A\<^sub>Q\<^sub>R \<sharp>* R"
      by simp+
    with \<open>extractFrame(Q \<parallel> R) = \<langle>A\<^sub>Q\<^sub>R, \<Psi>\<^sub>Q\<^sub>R\<rangle>\<close> \<open>distinct A\<^sub>Q\<^sub>R\<close>
    obtain A\<^sub>Q \<Psi>\<^sub>Q A\<^sub>R \<Psi>\<^sub>R where "A\<^sub>Q\<^sub>R = A\<^sub>Q@A\<^sub>R" and "\<Psi>\<^sub>Q\<^sub>R = \<Psi>\<^sub>Q \<otimes> \<Psi>\<^sub>R" and FrQ: "extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" and  FrR: "extractFrame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>"
                           and "A\<^sub>Q \<sharp>* \<Psi>\<^sub>R" and "A\<^sub>R \<sharp>* \<Psi>\<^sub>Q"
      by(rule_tac mergeFrameE) (auto dest: extractFrameFreshChain)

    from \<open>A\<^sub>Q\<^sub>R = A\<^sub>Q@A\<^sub>R\<close> \<open>A\<^sub>Q\<^sub>R \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q\<^sub>R \<sharp>* P\<close> \<open>A\<^sub>Q\<^sub>R \<sharp>* Q\<close> \<open>A\<^sub>Q\<^sub>R \<sharp>* \<alpha>\<close>
    have "A\<^sub>Q \<sharp>* \<Psi>" and "A\<^sub>R \<sharp>* \<Psi>" and "A\<^sub>Q \<sharp>* P" and "A\<^sub>R \<sharp>* P" and "A\<^sub>Q \<sharp>* Q" and "A\<^sub>R \<sharp>* Q" and "A\<^sub>Q \<sharp>* \<alpha>" and "A\<^sub>R \<sharp>* \<alpha>"
      by simp+

    from \<open>\<Psi> \<otimes> \<Psi>\<^sub>Q\<^sub>R \<rhd> P \<longmapsto>\<alpha> \<prec> P'\<close> \<open>\<Psi>\<^sub>Q\<^sub>R = \<Psi>\<^sub>Q \<otimes> \<Psi>\<^sub>R\<close> have "(\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>\<alpha> \<prec> P'"
      by(metis statEqTransition Associativity Commutativity Composition)
    hence "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> P \<parallel> Q \<longmapsto>\<alpha> \<prec> (P' \<parallel> Q)" using FrQ \<open>bn \<alpha> \<sharp>* Q\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<^sub>R\<close> \<open>A\<^sub>Q \<sharp>* P\<close> \<open>A\<^sub>Q \<sharp>* \<alpha>\<close>
      by(rule_tac Par1) auto
    hence "\<Psi> \<rhd> (P \<parallel> Q) \<parallel> R \<longmapsto>\<alpha> \<prec> ((P' \<parallel> Q) \<parallel> R)" using FrR \<open>bn \<alpha> \<sharp>* R\<close> \<open>A\<^sub>R \<sharp>* \<Psi>\<close> \<open>A\<^sub>R \<sharp>* P\<close> \<open>A\<^sub>R \<sharp>* Q\<close> \<open>A\<^sub>R \<sharp>* \<alpha>\<close>
      by(rule_tac Par1) auto
    moreover have "(\<Psi>, (P' \<parallel> Q) \<parallel> R, P' \<parallel> (Q \<parallel> R)) \<in> Rel" by(rule C1)
    ultimately show ?case by blast
  next
    case(cPar2 QR A\<^sub>P \<Psi>\<^sub>P)
    from \<open>A\<^sub>P \<sharp>* (\<Psi>, P, Q, R, \<alpha>)\<close> have "A\<^sub>P \<sharp>* Q" and "A\<^sub>P \<sharp>* R" and "A\<^sub>P \<sharp>* \<alpha>"
      by simp+
    have FrP: "extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" by fact
    with \<open>bn \<alpha> \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* \<alpha>\<close> have "bn \<alpha> \<sharp>* \<Psi>\<^sub>P" by(auto dest: extractFrameFreshChain)
    with \<open>bn \<alpha> \<sharp>* \<Psi>\<close> have "bn \<alpha> \<sharp>* (\<Psi> \<otimes> \<Psi>\<^sub>P)" by force
    with \<open>\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<parallel> R \<longmapsto>\<alpha> \<prec> QR\<close>
    show ?case using \<open>bn \<alpha> \<sharp>* Q\<close> \<open>bn \<alpha> \<sharp>* R\<close> \<open>bn \<alpha> \<sharp>* subject \<alpha>\<close> \<open>A\<^sub>P \<sharp>* Q\<close> \<open>A\<^sub>P \<sharp>* R\<close>
    proof(induct rule: parCasesSubject[where C = "(A\<^sub>P, \<Psi>\<^sub>P, P, Q, R, \<Psi>)"])
      case(cPar1 Q' A\<^sub>R \<Psi>\<^sub>R)
      from \<open>A\<^sub>R \<sharp>* (A\<^sub>P, \<Psi>\<^sub>P, P, Q, R, \<Psi>)\<close> have "A\<^sub>R \<sharp>* A\<^sub>P" and "A\<^sub>R \<sharp>* P" and "A\<^sub>R \<sharp>* Q" and "A\<^sub>R \<sharp>* \<Psi>\<^sub>P" and "A\<^sub>R \<sharp>* \<Psi>"
        by simp+
      from \<open>A\<^sub>P \<sharp>* R\<close> \<open>extractFrame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>\<close> \<open>A\<^sub>R \<sharp>* A\<^sub>P\<close> have "A\<^sub>P \<sharp>* \<Psi>\<^sub>R"
        by(drule_tac extractFrameFreshChain) auto
      from \<open>(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>R \<rhd> Q \<longmapsto>\<alpha> \<prec> Q'\<close> have "(\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>\<alpha> \<prec> Q'" 
        by(metis statEqTransition Associativity Commutativity Composition)
      hence "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> P \<parallel> Q \<longmapsto>\<alpha> \<prec> (P \<parallel> Q')"
        using FrP \<open>bn \<alpha> \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<^sub>R\<close> \<open>A\<^sub>P \<sharp>* Q\<close> \<open>A\<^sub>P \<sharp>* \<alpha>\<close>
        by(rule_tac Par2) (assumption | force)+
      hence "\<Psi> \<rhd> (P \<parallel> Q) \<parallel> R \<longmapsto>\<alpha> \<prec> ((P \<parallel> Q') \<parallel> R)"
        using \<open>extractFrame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>\<close> \<open>bn \<alpha> \<sharp>* R\<close> \<open>A\<^sub>R \<sharp>* \<Psi>\<close> \<open>A\<^sub>R \<sharp>* P\<close> \<open>A\<^sub>R \<sharp>* Q\<close> \<open>A\<^sub>R \<sharp>* \<alpha>\<close>
        by(rule_tac Par1) (assumption | simp)+
      moreover have "(\<Psi>, (P \<parallel> Q') \<parallel> R, P \<parallel> (Q' \<parallel> R)) \<in> Rel" by(rule C1)
      ultimately show ?case by blast
    next
      case(cPar2 R' A\<^sub>Q \<Psi>\<^sub>Q)
      from \<open>A\<^sub>Q \<sharp>* (A\<^sub>P, \<Psi>\<^sub>P, P, Q, R, \<Psi>)\<close> have "A\<^sub>Q \<sharp>* A\<^sub>P" and "A\<^sub>Q \<sharp>* R" and "A\<^sub>Q \<sharp>* \<Psi>\<^sub>P" and "A\<^sub>Q \<sharp>* \<Psi>"
        by simp+
      have FrQ: "extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" by fact
      from \<open>A\<^sub>P \<sharp>* Q\<close> FrQ \<open>A\<^sub>Q \<sharp>* A\<^sub>P\<close> have "A\<^sub>P \<sharp>* \<Psi>\<^sub>Q"
        by(drule_tac extractFrameFreshChain) auto
      from \<open>(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>Q \<rhd> R \<longmapsto>\<alpha> \<prec> R'\<close>
      have "\<Psi> \<otimes> (\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q) \<rhd> R \<longmapsto>\<alpha> \<prec> R'"
        by(blast intro: statEqTransition Associativity)
      moreover from FrP FrQ \<open>A\<^sub>Q \<sharp>* A\<^sub>P\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<^sub>Q\<close>  \<open>A\<^sub>Q \<sharp>* \<Psi>\<^sub>P\<close> 
      have "extractFrame(P \<parallel> Q) = \<langle>(A\<^sub>P@A\<^sub>Q), \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q\<rangle> " by simp
      moreover from \<open>bn \<alpha> \<sharp>* P\<close> \<open>bn \<alpha> \<sharp>* Q\<close> have "bn \<alpha> \<sharp>* (P \<parallel> Q)" by simp
      moreover from \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<close> have "(A\<^sub>P@A\<^sub>Q) \<sharp>* \<Psi>" by simp
      moreover from \<open>A\<^sub>P \<sharp>* R\<close> \<open>A\<^sub>Q \<sharp>* R\<close> have "(A\<^sub>P@A\<^sub>Q) \<sharp>* R" by simp
      moreover from \<open>A\<^sub>P \<sharp>* \<alpha>\<close> \<open>A\<^sub>Q \<sharp>* \<alpha>\<close> have "(A\<^sub>P@A\<^sub>Q) \<sharp>* \<alpha>" by simp
      ultimately have "\<Psi> \<rhd> (P \<parallel> Q) \<parallel> R \<longmapsto>\<alpha> \<prec> ((P \<parallel> Q) \<parallel> R')"
        by(rule Par2) 
      moreover have "(\<Psi>, (P \<parallel> Q) \<parallel> R', P \<parallel> (Q \<parallel> R')) \<in> Rel" by(rule C1)
      ultimately show ?case by blast
    next
      case(cComm1 \<Psi>\<^sub>R M N Q' A\<^sub>Q \<Psi>\<^sub>Q K xvec R' A\<^sub>R) 
      from \<open>A\<^sub>Q \<sharp>* (A\<^sub>P, \<Psi>\<^sub>P, P, Q, R, \<Psi>)\<close>
      have "A\<^sub>Q \<sharp>* P" and "A\<^sub>Q \<sharp>* Q" and "A\<^sub>Q \<sharp>* R" and "A\<^sub>Q \<sharp>* A\<^sub>P" and "A\<^sub>Q \<sharp>* \<Psi>\<^sub>P"  and "A\<^sub>Q \<sharp>* \<Psi>" by simp+
      from \<open>A\<^sub>R \<sharp>* (A\<^sub>P, \<Psi>\<^sub>P, P, Q, R, \<Psi>)\<close> have "A\<^sub>R \<sharp>* P" and "A\<^sub>R \<sharp>* Q" and "A\<^sub>R \<sharp>* R" and "A\<^sub>R \<sharp>* A\<^sub>P"  and "A\<^sub>R \<sharp>* \<Psi>" by simp+
      from \<open>xvec \<sharp>* (A\<^sub>P,  \<Psi>\<^sub>P, P, Q, R, \<Psi>)\<close> have "xvec \<sharp>* A\<^sub>P" and "xvec \<sharp>* P" and "xvec \<sharp>* Q" and "xvec \<sharp>* \<Psi>" by simp+

      have FrQ: "extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" by fact
      with \<open>A\<^sub>P \<sharp>* Q\<close> \<open>A\<^sub>Q \<sharp>* A\<^sub>P\<close> have "A\<^sub>P \<sharp>* \<Psi>\<^sub>Q"
        by(drule_tac extractFrameFreshChain) auto
      have FrR: "extractFrame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>" by fact
      with \<open>A\<^sub>P \<sharp>* R\<close> \<open>A\<^sub>R \<sharp>* A\<^sub>P\<close> have "A\<^sub>P \<sharp>* \<Psi>\<^sub>R"
        by(drule_tac extractFrameFreshChain) auto
      from \<open>(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>Q \<rhd> R \<longmapsto>K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> R'\<close> \<open>A\<^sub>P \<sharp>* R\<close> \<open>xvec \<sharp>* A\<^sub>P\<close> \<open>xvec \<sharp>* K\<close> \<open>distinct xvec\<close> have "A\<^sub>P \<sharp>* N" 
        by(rule_tac outputFreshChainDerivative) auto

      from \<open>(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>R \<rhd> Q \<longmapsto>M\<lparr>N\<rparr> \<prec> Q'\<close> have "(\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>M\<lparr>N\<rparr> \<prec> Q'"
        by(metis statEqTransition Associativity Commutativity Composition)
      hence "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> P \<parallel> Q \<longmapsto>M\<lparr>N\<rparr> \<prec> (P \<parallel> Q')" using FrP \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<^sub>R\<close> \<open>A\<^sub>P \<sharp>* Q\<close> \<open>A\<^sub>P \<sharp>* M\<close> \<open>A\<^sub>P \<sharp>* N\<close>
        by(rule_tac Par2) auto
      moreover from FrP FrQ \<open>A\<^sub>P \<sharp>* \<Psi>\<^sub>Q\<close> \<open>A\<^sub>Q \<sharp>* A\<^sub>P\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<^sub>P\<close> have "extractFrame(P \<parallel> Q) = \<langle>(A\<^sub>P@A\<^sub>Q), \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q\<rangle>"
        by simp
      moreover from  \<open>(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>Q \<rhd> R \<longmapsto>K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> R'\<close> have "\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q \<rhd> R \<longmapsto>K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> R'"
        by(metis statEqTransition Associativity)
      moreover note \<open>extractFrame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>\<close>
      moreover from \<open>(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>Q \<otimes> \<Psi>\<^sub>R \<turnstile> M \<leftrightarrow> K\<close> have "\<Psi> \<otimes> (\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>R \<turnstile> M \<leftrightarrow> K"
        by(metis statEqEnt Associativity Commutativity Composition)
      ultimately have "\<Psi> \<rhd> (P \<parallel> Q) \<parallel> R \<longmapsto>\<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>((P \<parallel> Q') \<parallel> R')"
        using \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<close> \<open>A\<^sub>R \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* P\<close> \<open>A\<^sub>Q \<sharp>* P\<close> \<open>A\<^sub>R \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* Q\<close> \<open>A\<^sub>Q \<sharp>* Q\<close> \<open>A\<^sub>R \<sharp>* Q\<close> \<open>A\<^sub>P \<sharp>* R\<close> \<open>A\<^sub>Q \<sharp>* R\<close> \<open>A\<^sub>R \<sharp>* R\<close>
              \<open>A\<^sub>P \<sharp>* M\<close> \<open>A\<^sub>Q \<sharp>* M\<close> \<open>A\<^sub>R \<sharp>* K\<close> \<open>A\<^sub>R \<sharp>* A\<^sub>P\<close> \<open>A\<^sub>Q \<sharp>* A\<^sub>R\<close> \<open>xvec \<sharp>* P\<close> \<open>xvec \<sharp>* Q\<close>
        by(rule_tac Comm1) (assumption | simp)+
      moreover from \<open>xvec \<sharp>* \<Psi>\<close> \<open>xvec \<sharp>* P\<close> have "(\<Psi>, \<lparr>\<nu>*xvec\<rparr>((P \<parallel> Q') \<parallel> R'), P \<parallel> (\<lparr>\<nu>*xvec\<rparr>(Q' \<parallel> R'))) \<in> Rel"
        by(rule C2)
      ultimately show ?case by blast
    next
      case(cComm2 \<Psi>\<^sub>R M xvec N Q' A\<^sub>Q \<Psi>\<^sub>Q K R' A\<^sub>R) 
      from \<open>A\<^sub>Q \<sharp>* (A\<^sub>P,  \<Psi>\<^sub>P, P, Q, R, \<Psi>)\<close>
      have "A\<^sub>Q \<sharp>* P" and "A\<^sub>Q \<sharp>* Q" and "A\<^sub>Q \<sharp>* R" and "A\<^sub>Q \<sharp>* A\<^sub>P" and "A\<^sub>Q \<sharp>* \<Psi>" and "A\<^sub>Q \<sharp>* \<Psi>\<^sub>P" by simp+
      from \<open>A\<^sub>R \<sharp>* (A\<^sub>P,  \<Psi>\<^sub>P, P, Q, R, \<Psi>)\<close> have "A\<^sub>R \<sharp>* P" and "A\<^sub>R \<sharp>* Q" and "A\<^sub>R \<sharp>* R" and "A\<^sub>R \<sharp>* A\<^sub>P"and "A\<^sub>R \<sharp>* \<Psi>" by simp+
      from \<open>xvec \<sharp>* (A\<^sub>P,  \<Psi>\<^sub>P, P, Q, R, \<Psi>)\<close> have "xvec \<sharp>* A\<^sub>P" and "xvec \<sharp>* P" and "xvec \<sharp>* Q" and "xvec \<sharp>* \<Psi>" by simp+

      have FrQ: "extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" by fact
      with \<open>A\<^sub>P \<sharp>* Q\<close> \<open>A\<^sub>Q \<sharp>* A\<^sub>P\<close> have "A\<^sub>P \<sharp>* \<Psi>\<^sub>Q"
        by(drule_tac extractFrameFreshChain) auto
      have FrR: "extractFrame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>" by fact
      with \<open>A\<^sub>P \<sharp>* R\<close> \<open>A\<^sub>R \<sharp>* A\<^sub>P\<close> have "A\<^sub>P \<sharp>* \<Psi>\<^sub>R"
        by(drule_tac extractFrameFreshChain) auto

      from \<open>(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>R \<rhd> Q \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'\<close> \<open>A\<^sub>P \<sharp>* Q\<close> \<open>xvec \<sharp>* A\<^sub>P\<close> \<open>xvec \<sharp>* M\<close> \<open>distinct xvec\<close> have "A\<^sub>P \<sharp>* N" 
        by(rule_tac outputFreshChainDerivative) auto

      from \<open>(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>R \<rhd> Q \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'\<close> have "(\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'"
        by(metis statEqTransition Associativity Commutativity Composition)
      hence "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> P \<parallel> Q \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> (P \<parallel> Q')" using FrP \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<^sub>R\<close> \<open>A\<^sub>P \<sharp>* Q\<close> \<open>A\<^sub>P \<sharp>* M\<close> \<open>A\<^sub>P \<sharp>* N\<close> \<open>xvec \<sharp>* P\<close> \<open>xvec \<sharp>* A\<^sub>P\<close>
        by(rule_tac Par2) auto
      moreover from FrP FrQ \<open>A\<^sub>P \<sharp>* \<Psi>\<^sub>Q\<close> \<open>A\<^sub>Q \<sharp>* A\<^sub>P\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<^sub>P\<close> have "extractFrame(P \<parallel> Q) = \<langle>(A\<^sub>P@A\<^sub>Q), \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q\<rangle>"
        by simp+
      moreover from  \<open>(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>Q \<rhd> R \<longmapsto>K\<lparr>N\<rparr> \<prec> R'\<close> have "\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q \<rhd> R \<longmapsto>K\<lparr>N\<rparr> \<prec> R'"
        by(metis statEqTransition Associativity)
      moreover note \<open>extractFrame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>\<close>
      moreover from \<open>(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>Q \<otimes> \<Psi>\<^sub>R \<turnstile> M \<leftrightarrow> K\<close> have "\<Psi> \<otimes> (\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>R \<turnstile> M \<leftrightarrow> K"
        by(metis statEqEnt Associativity Commutativity Composition)
      ultimately have "\<Psi> \<rhd> (P \<parallel> Q) \<parallel> R \<longmapsto>\<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>((P \<parallel> Q') \<parallel> R')"
        using \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<close> \<open>A\<^sub>R \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* P\<close> \<open>A\<^sub>Q \<sharp>* P\<close> \<open>A\<^sub>R \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* Q\<close> \<open>A\<^sub>Q \<sharp>* Q\<close> \<open>A\<^sub>R \<sharp>* Q\<close> \<open>A\<^sub>P \<sharp>* R\<close> \<open>A\<^sub>Q \<sharp>* R\<close> \<open>A\<^sub>R \<sharp>* R\<close>
              \<open>A\<^sub>P \<sharp>* M\<close> \<open>A\<^sub>Q \<sharp>* M\<close> \<open>A\<^sub>R \<sharp>* K\<close> \<open>A\<^sub>R \<sharp>* A\<^sub>P\<close> \<open>A\<^sub>Q \<sharp>* A\<^sub>R\<close> \<open>xvec \<sharp>* R\<close>
        by(rule_tac Comm2) (assumption | simp)+
      moreover from \<open>xvec \<sharp>* \<Psi>\<close> \<open>xvec \<sharp>* P\<close> have "(\<Psi>, \<lparr>\<nu>*xvec\<rparr>((P \<parallel> Q') \<parallel> R'), P \<parallel> (\<lparr>\<nu>*xvec\<rparr>(Q' \<parallel> R'))) \<in> Rel"
        by(rule C2)
      ultimately show ?case by blast
    qed
  next
    case(cComm1 \<Psi>\<^sub>Q\<^sub>R M N P' A\<^sub>P \<Psi>\<^sub>P K xvec QR' A\<^sub>Q\<^sub>R)
    from \<open>xvec \<sharp>* (\<Psi>, P, Q, R, \<alpha>)\<close> have "xvec \<sharp>* Q" and "xvec \<sharp>* R" by simp+
    from \<open>A\<^sub>Q\<^sub>R \<sharp>* (\<Psi>, P, Q, R, \<alpha>)\<close> have "A\<^sub>Q\<^sub>R \<sharp>* Q" and "A\<^sub>Q\<^sub>R \<sharp>* R" and "A\<^sub>Q\<^sub>R \<sharp>* \<Psi>" by simp+
    from \<open>A\<^sub>P \<sharp>* (Q \<parallel> R)\<close> have "A\<^sub>P \<sharp>* Q" and "A\<^sub>P \<sharp>* R" by simp+
    have PTrans: "\<Psi> \<otimes> \<Psi>\<^sub>Q\<^sub>R \<rhd> P \<longmapsto>M\<lparr>N\<rparr> \<prec> P'" and FrP: "extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" and MeqK: "\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q\<^sub>R \<turnstile> M \<leftrightarrow> K" by fact+
    note \<open>\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<parallel> R \<longmapsto>K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> QR'\<close>  
    moreover from \<open>xvec \<sharp>* \<Psi>\<close> \<open>xvec \<sharp>* \<Psi>\<^sub>P\<close> have "xvec \<sharp>* (\<Psi> \<otimes> \<Psi>\<^sub>P)" by force
    moreover note \<open>xvec \<sharp>* Q\<close>\<open>xvec \<sharp>* R\<close> \<open>xvec \<sharp>* K\<close>
         \<open>extractFrame(Q \<parallel> R) = \<langle>A\<^sub>Q\<^sub>R, \<Psi>\<^sub>Q\<^sub>R\<rangle>\<close> \<open>distinct A\<^sub>Q\<^sub>R\<close> 
    moreover from \<open>A\<^sub>Q\<^sub>R \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q\<^sub>R \<sharp>* \<Psi>\<^sub>P\<close> have "A\<^sub>Q\<^sub>R \<sharp>* (\<Psi> \<otimes> \<Psi>\<^sub>P)" by force
    ultimately show ?case using \<open>A\<^sub>Q\<^sub>R \<sharp>* Q\<close> \<open>A\<^sub>Q\<^sub>R \<sharp>* R\<close> \<open>A\<^sub>Q\<^sub>R \<sharp>* K\<close>
    proof(induct rule: parCasesOutputFrame)
      case(cPar1 Q' A\<^sub>Q \<Psi>\<^sub>Q A\<^sub>R \<Psi>\<^sub>R)
      have Aeq: "A\<^sub>Q\<^sub>R = A\<^sub>Q@A\<^sub>R" and \<Psi>eq: "\<Psi>\<^sub>Q\<^sub>R = \<Psi>\<^sub>Q \<otimes> \<Psi>\<^sub>R" by fact+
      from PTrans \<Psi>eq have "(\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>M\<lparr>N\<rparr> \<prec> P'"
        by(metis statEqTransition Associativity Commutativity Composition)
      moreover note FrP
      moreover from \<open>(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>R \<rhd> Q \<longmapsto>K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'\<close> have "(\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'"
        by(metis statEqTransition Associativity Commutativity Composition)
      moreover note \<open>extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>\<close>
      moreover from MeqK \<Psi>eq have "(\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q \<turnstile> M \<leftrightarrow> K"
        by(metis statEqEnt Associativity Commutativity Composition)
      moreover from \<open>A\<^sub>P \<sharp>* R\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>Q\<^sub>R\<close> Aeq \<open>extractFrame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>\<close> have "A\<^sub>P \<sharp>* A\<^sub>Q" and "A\<^sub>P \<sharp>* \<Psi>\<^sub>R"
        by(auto dest:  extractFrameFreshChain)
      moreover from \<open>A\<^sub>Q\<^sub>R \<sharp>* P\<close> \<open>A\<^sub>Q\<^sub>R \<sharp>* \<Psi>\<close> Aeq have "A\<^sub>Q \<sharp>* P" and "A\<^sub>Q \<sharp>* \<Psi>" by simp+
      ultimately have "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> P \<parallel> Q \<longmapsto>\<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q')"
        using \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* Q\<close> \<open>A\<^sub>P \<sharp>* M\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>Q\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<^sub>R\<close> \<open>A\<^sub>Q \<sharp>* P\<close> \<open>A\<^sub>Q \<sharp>* Q\<close> \<open>A\<^sub>Q \<sharp>* K\<close> \<open>xvec \<sharp>* P\<close>
        by(rule_tac Comm1) (assumption | force)+
      moreover from \<open>A\<^sub>Q\<^sub>R \<sharp>* \<Psi>\<close> Aeq have "A\<^sub>R \<sharp>* \<Psi>" by simp
      moreover from \<open>A\<^sub>Q\<^sub>R \<sharp>* P\<close> Aeq have "A\<^sub>R \<sharp>* P" by simp
      ultimately have "\<Psi> \<rhd> (P \<parallel> Q) \<parallel> R \<longmapsto>\<tau> \<prec> (\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q')) \<parallel> R" using \<open>extractFrame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>\<close> \<open>A\<^sub>R \<sharp>* Q\<close>
        by(rule_tac Par1) (assumption | simp)+
      moreover from \<open>xvec \<sharp>* \<Psi>\<close> \<open>xvec \<sharp>* R\<close> have "(\<Psi>, (\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q')) \<parallel> R, \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> (Q' \<parallel> R))) \<in> Rel"
        by(rule C3)
      ultimately show ?case by blast
    next
      case(cPar2 R' A\<^sub>Q \<Psi>\<^sub>Q A\<^sub>R \<Psi>\<^sub>R)
      have Aeq: "A\<^sub>Q\<^sub>R = A\<^sub>Q@A\<^sub>R" and \<Psi>eq: "\<Psi>\<^sub>Q\<^sub>R = \<Psi>\<^sub>Q \<otimes> \<Psi>\<^sub>R" by fact+
      from \<open>A\<^sub>Q\<^sub>R \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q\<^sub>R \<sharp>* P\<close> \<open>A\<^sub>Q\<^sub>R \<sharp>* \<Psi>\<^sub>P\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>Q\<^sub>R\<close> Aeq have "A\<^sub>R \<sharp>* \<Psi>" and "A\<^sub>R \<sharp>* \<Psi>\<^sub>P" and "A\<^sub>P \<sharp>* A\<^sub>R" and "A\<^sub>P \<sharp>* A\<^sub>Q" and "A\<^sub>R \<sharp>* P" by simp+
      from \<open>A\<^sub>Q\<^sub>R \<sharp>* \<Psi>\<close> Aeq have "A\<^sub>Q \<sharp>* \<Psi>" by simp
      from \<open>A\<^sub>Q\<^sub>R \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>Q\<^sub>R\<close> Aeq FrP have "A\<^sub>Q \<sharp>* \<Psi>\<^sub>P" by(auto dest: extractFrameFreshChain)
      from \<open>A\<^sub>P \<sharp>* A\<^sub>Q\<^sub>R\<close> \<open>extractFrame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>\<close> \<open>extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>\<close> Aeq \<open>A\<^sub>P \<sharp>* Q\<close> \<open>A\<^sub>P \<sharp>* R\<close> have "A\<^sub>P \<sharp>* \<Psi>\<^sub>Q" and  "A\<^sub>P \<sharp>* \<Psi>\<^sub>R" by(auto dest: extractFrameFreshChain)
      have RTrans: "(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>Q \<rhd> R \<longmapsto>K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> R'" and FrR: "extractFrame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>" by fact+
      then obtain K' where KeqK': "((\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>R \<turnstile> K \<leftrightarrow> K'" and "A\<^sub>P \<sharp>* K'" and "A\<^sub>Q \<sharp>* K'"
      using \<open>A\<^sub>P \<sharp>* R\<close> \<open>A\<^sub>Q \<sharp>* R\<close> \<open>A\<^sub>R \<sharp>* \<Psi>\<close> \<open>A\<^sub>R \<sharp>* \<Psi>\<^sub>P\<close> \<open>A\<^sub>R \<sharp>* \<Psi>\<^sub>Q\<close> \<open>A\<^sub>Q \<sharp>* A\<^sub>R\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>R\<close> \<open>A\<^sub>R \<sharp>* R\<close> \<open>A\<^sub>R \<sharp>* R\<close> \<open>A\<^sub>R \<sharp>* K\<close> \<open>distinct A\<^sub>R\<close> \<open>xvec \<sharp>* K\<close> \<open>distinct xvec\<close>
        by(rule_tac B="A\<^sub>P@A\<^sub>Q" in obtainPrefix) (assumption | force)+
      from PTrans \<Psi>eq have "(\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>M\<lparr>N\<rparr> \<prec> P'"
        by(metis statEqTransition Associativity Commutativity Composition)
      moreover from MeqK KeqK' \<Psi>eq have MeqK': "((\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>P \<turnstile> M \<leftrightarrow> K'"
        by(metis statEqEnt Associativity Commutativity Composition chanEqTrans)
      ultimately have "(\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>K'\<lparr>N\<rparr> \<prec> P'" using FrP \<open>distinct A\<^sub>P\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* M\<close> \<open>A\<^sub>P \<sharp>* K'\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<^sub>Q\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<^sub>R\<close>
        by(rule_tac inputRenameSubject) auto
      moreover from \<open>A\<^sub>Q\<^sub>R \<sharp>* P\<close> \<open>A\<^sub>Q\<^sub>R \<sharp>* N\<close> Aeq have "A\<^sub>Q \<sharp>* P" and "A\<^sub>Q \<sharp>* N" by simp+
      ultimately have "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> P \<parallel> Q \<longmapsto>K'\<lparr>N\<rparr> \<prec> P' \<parallel> Q" using \<open>extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<^sub>R\<close> \<open>A\<^sub>Q \<sharp>* K'\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<close>
        by(rule_tac Par1) (assumption | force)+
      moreover from FrP \<open>extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>Q\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<^sub>Q\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<^sub>P\<close>
      have "extractFrame(P \<parallel> Q) = \<langle>(A\<^sub>P@A\<^sub>Q), \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q\<rangle>" by simp+
      moreover from RTrans have "\<Psi> \<otimes> (\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q) \<rhd> R \<longmapsto>K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> R'" by(metis Associativity statEqTransition)
      moreover note FrR
      moreover from MeqK' KeqK' have "\<Psi> \<otimes> (\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>R \<turnstile> K' \<leftrightarrow> K"
        by(metis statEqEnt Associativity Commutativity Composition chanEqTrans chanEqSym)
      ultimately have "\<Psi> \<rhd> (P \<parallel> Q) \<parallel> R \<longmapsto>\<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>((P' \<parallel> Q) \<parallel> R')"
        using \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* P\<close> \<open>A\<^sub>Q \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* Q\<close> \<open>A\<^sub>Q \<sharp>* Q\<close> \<open>A\<^sub>P \<sharp>* R\<close> \<open>A\<^sub>Q \<sharp>* R\<close> \<open>A\<^sub>P \<sharp>* K'\<close> \<open>A\<^sub>Q \<sharp>* K'\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>R\<close> \<open>A\<^sub>Q \<sharp>* A\<^sub>R\<close>
              \<open>A\<^sub>R \<sharp>* \<Psi>\<close> \<open>A\<^sub>R \<sharp>* P\<close> \<open>A\<^sub>R \<sharp>* Q\<close> \<open>A\<^sub>R \<sharp>* R\<close> \<open>A\<^sub>R \<sharp>* K\<close> \<open>xvec \<sharp>* P\<close> \<open>xvec \<sharp>* Q\<close>
        by(rule_tac Comm1) (assumption | simp)+
      moreover from \<open>xvec \<sharp>* \<Psi>\<close> have "(\<Psi>, \<lparr>\<nu>*xvec\<rparr>((P' \<parallel> Q) \<parallel> R'), \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> (Q \<parallel> R'))) \<in> Rel"
        by(metis C1 C4)
      ultimately show ?case by blast
    qed
  next
    case(cComm2 \<Psi>\<^sub>Q\<^sub>R M xvec N P' A\<^sub>P \<Psi>\<^sub>P K QR' A\<^sub>Q\<^sub>R)
    from \<open>A\<^sub>Q\<^sub>R \<sharp>* (\<Psi>, P, Q, R, \<alpha>)\<close> have "A\<^sub>Q\<^sub>R \<sharp>* Q" and "A\<^sub>Q\<^sub>R \<sharp>* R" and "A\<^sub>Q\<^sub>R \<sharp>* \<Psi>" by simp+
    from \<open>A\<^sub>P \<sharp>* (Q \<parallel> R)\<close> \<open>xvec \<sharp>* (Q \<parallel> R)\<close> have "A\<^sub>P \<sharp>* Q" and "A\<^sub>P \<sharp>* R" and "xvec \<sharp>* Q" and "xvec \<sharp>* R" by simp+
    have PTrans: "\<Psi> \<otimes> \<Psi>\<^sub>Q\<^sub>R \<rhd> P \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'" and FrP: "extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" and MeqK: "\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q\<^sub>R \<turnstile> M \<leftrightarrow> K" by fact+
    note \<open>\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<parallel> R \<longmapsto>K\<lparr>N\<rparr> \<prec> QR'\<close> \<open>extractFrame(Q \<parallel> R) = \<langle>A\<^sub>Q\<^sub>R, \<Psi>\<^sub>Q\<^sub>R\<rangle>\<close> \<open>distinct A\<^sub>Q\<^sub>R\<close> 
    moreover from \<open>A\<^sub>Q\<^sub>R \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q\<^sub>R \<sharp>* \<Psi>\<^sub>P\<close> have "A\<^sub>Q\<^sub>R \<sharp>* (\<Psi> \<otimes> \<Psi>\<^sub>P)" by force
    ultimately show ?case using \<open>A\<^sub>Q\<^sub>R \<sharp>* Q\<close> \<open>A\<^sub>Q\<^sub>R \<sharp>* R\<close> \<open>A\<^sub>Q\<^sub>R \<sharp>* K\<close>
    proof(induct rule: parCasesInputFrame)
      case(cPar1 Q' A\<^sub>Q \<Psi>\<^sub>Q A\<^sub>R \<Psi>\<^sub>R)
      have Aeq: "A\<^sub>Q\<^sub>R = A\<^sub>Q@A\<^sub>R" and \<Psi>eq: "\<Psi>\<^sub>Q\<^sub>R = \<Psi>\<^sub>Q \<otimes> \<Psi>\<^sub>R" by fact+
      from PTrans \<Psi>eq have "(\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
        by(metis statEqTransition Associativity Commutativity Composition)
      moreover note FrP
      moreover from \<open>(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>R \<rhd> Q \<longmapsto>K\<lparr>N\<rparr> \<prec> Q'\<close> have "(\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>K\<lparr>N\<rparr> \<prec> Q'"
        by(metis statEqTransition Associativity Commutativity Composition)
      moreover note \<open>extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>\<close>
      moreover from MeqK \<Psi>eq have "(\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q \<turnstile> M \<leftrightarrow> K"
        by(metis statEqEnt Associativity Commutativity Composition)
      moreover from \<open>A\<^sub>P \<sharp>* Q\<close> \<open>A\<^sub>P \<sharp>* R\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>Q\<^sub>R\<close> Aeq \<open>extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>\<close> \<open>extractFrame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>\<close>
      have "A\<^sub>P \<sharp>* A\<^sub>Q" and "A\<^sub>P \<sharp>* \<Psi>\<^sub>R" by(auto dest: extractFrameFreshChain)
      moreover from \<open>A\<^sub>Q\<^sub>R \<sharp>* \<Psi>\<close>  \<open>A\<^sub>Q\<^sub>R \<sharp>* P\<close> Aeq have "A\<^sub>Q \<sharp>* \<Psi>" and "A\<^sub>Q \<sharp>* P" by simp+
      ultimately have "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> P \<parallel> Q \<longmapsto>\<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q')"
        using \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* Q\<close> \<open>A\<^sub>P \<sharp>* M\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>Q\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<^sub>R\<close> \<open>A\<^sub>Q \<sharp>* P\<close> \<open>A\<^sub>Q \<sharp>* Q\<close> \<open>A\<^sub>Q \<sharp>* K\<close> \<open>xvec \<sharp>* Q\<close>
        by(rule_tac Comm2) (assumption | force)+
      moreover from \<open>A\<^sub>Q\<^sub>R \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q\<^sub>R \<sharp>* P\<close> Aeq have "A\<^sub>R \<sharp>* \<Psi>" and "A\<^sub>R \<sharp>* P" by simp+
      ultimately have "\<Psi> \<rhd> (P \<parallel> Q) \<parallel> R \<longmapsto>\<tau> \<prec> (\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q')) \<parallel> R" using \<open>extractFrame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>\<close> \<open>A\<^sub>R \<sharp>* Q\<close>
        by(rule_tac Par1) (assumption | simp)+
      moreover from \<open>xvec \<sharp>* \<Psi>\<close> \<open>xvec \<sharp>* R\<close> have "(\<Psi>, (\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q')) \<parallel> R, \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> (Q' \<parallel> R))) \<in> Rel"
        by(rule C3)
      ultimately show ?case by blast
    next
      case(cPar2 R' A\<^sub>Q \<Psi>\<^sub>Q A\<^sub>R \<Psi>\<^sub>R)
      have Aeq: "A\<^sub>Q\<^sub>R = A\<^sub>Q@A\<^sub>R" and \<Psi>eq: "\<Psi>\<^sub>Q\<^sub>R = \<Psi>\<^sub>Q \<otimes> \<Psi>\<^sub>R" by fact+
      from \<open>A\<^sub>Q\<^sub>R \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q\<^sub>R \<sharp>* P\<close> \<open>A\<^sub>Q\<^sub>R \<sharp>* \<Psi>\<^sub>P\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>Q\<^sub>R\<close> Aeq 
      have "A\<^sub>R \<sharp>* \<Psi>" and "A\<^sub>R \<sharp>* \<Psi>\<^sub>P" and "A\<^sub>P \<sharp>* A\<^sub>R" and "A\<^sub>P \<sharp>* A\<^sub>Q" and "A\<^sub>R \<sharp>* P" and "A\<^sub>Q \<sharp>* \<Psi>" and "A\<^sub>Q \<sharp>* \<Psi>\<^sub>P" by simp+
      have RTrans: "(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>Q \<rhd> R \<longmapsto>K\<lparr>N\<rparr> \<prec> R'" and FrR: "extractFrame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>" by fact+
      then obtain K' where KeqK': "((\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>R \<turnstile> K \<leftrightarrow> K'" and "A\<^sub>P \<sharp>* K'" and "A\<^sub>Q \<sharp>* K'"
      using \<open>A\<^sub>P \<sharp>* R\<close> \<open>A\<^sub>Q \<sharp>* R\<close> \<open>A\<^sub>R \<sharp>* \<Psi>\<close> \<open>A\<^sub>R \<sharp>* \<Psi>\<^sub>P\<close> \<open>A\<^sub>R \<sharp>* \<Psi>\<^sub>Q\<close> \<open>A\<^sub>Q \<sharp>* A\<^sub>R\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>R\<close> \<open>A\<^sub>R \<sharp>* R\<close> \<open>A\<^sub>R \<sharp>* R\<close> \<open>A\<^sub>R \<sharp>* K\<close> \<open>distinct A\<^sub>R\<close>
        by(rule_tac B="A\<^sub>P@A\<^sub>Q" in obtainPrefix) (assumption | force)+
      from PTrans \<Psi>eq have "(\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
        by(metis statEqTransition Associativity Commutativity Composition)
      moreover from MeqK KeqK' \<Psi>eq have MeqK': "((\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>P \<turnstile> M \<leftrightarrow> K'"
        by(metis statEqEnt Associativity Commutativity Composition chanEqTrans)
      moreover from \<open>A\<^sub>P \<sharp>* R\<close> \<open>A\<^sub>P \<sharp>* Q\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>Q\<^sub>R\<close> FrR \<open>extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>\<close> Aeq have "A\<^sub>P \<sharp>* \<Psi>\<^sub>Q" and "A\<^sub>P \<sharp>* \<Psi>\<^sub>R"
        by(auto dest: extractFrameFreshChain)
      ultimately have "(\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>K'\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'" using FrP \<open>distinct A\<^sub>P\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* M\<close> \<open>A\<^sub>P \<sharp>* K'\<close>
        by(rule_tac outputRenameSubject) auto
      moreover from \<open>A\<^sub>Q\<^sub>R \<sharp>* P\<close> \<open>A\<^sub>Q\<^sub>R \<sharp>* N\<close> \<open>A\<^sub>Q\<^sub>R \<sharp>* xvec\<close> Aeq have "A\<^sub>Q \<sharp>* P" and "A\<^sub>Q \<sharp>* N" and "A\<^sub>Q \<sharp>* xvec" by simp+
      ultimately have "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> P \<parallel> Q \<longmapsto>K'\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> (P' \<parallel> Q)" using \<open>extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<^sub>R\<close> \<open>A\<^sub>Q \<sharp>* K'\<close> \<open>xvec \<sharp>* Q\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<close>
        by(rule_tac Par1) (assumption | force)+
      moreover from FrP \<open>extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>Q\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<^sub>Q\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<^sub>P\<close>
      have "extractFrame(P \<parallel> Q) = \<langle>(A\<^sub>P@A\<^sub>Q), \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q\<rangle>" by simp+
      moreover from RTrans have "\<Psi> \<otimes> (\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q) \<rhd> R \<longmapsto>K\<lparr>N\<rparr> \<prec> R'" by(metis Associativity statEqTransition)
      moreover note FrR
      moreover from MeqK' KeqK' have "\<Psi> \<otimes> (\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>R \<turnstile> K' \<leftrightarrow> K"
        by(metis statEqEnt Associativity Commutativity Composition chanEqTrans chanEqSym)
      ultimately have "\<Psi> \<rhd> (P \<parallel> Q) \<parallel> R \<longmapsto>\<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>((P' \<parallel> Q) \<parallel> R')"
        using \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* P\<close> \<open>A\<^sub>Q \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* Q\<close> \<open>A\<^sub>Q \<sharp>* Q\<close> \<open>A\<^sub>P \<sharp>* R\<close> \<open>A\<^sub>Q \<sharp>* R\<close> \<open>A\<^sub>P \<sharp>* K'\<close> \<open>A\<^sub>Q \<sharp>* K'\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>R\<close> \<open>A\<^sub>Q \<sharp>* A\<^sub>R\<close>
              \<open>A\<^sub>R \<sharp>* \<Psi>\<close> \<open>A\<^sub>R \<sharp>* P\<close> \<open>A\<^sub>R \<sharp>* Q\<close> \<open>A\<^sub>R \<sharp>* R\<close> \<open>A\<^sub>R \<sharp>* K\<close> \<open>xvec \<sharp>* R\<close>
        by(rule_tac Comm2) (assumption | simp)+
      moreover from \<open>xvec \<sharp>* \<Psi>\<close> have "(\<Psi>, \<lparr>\<nu>*xvec\<rparr>((P' \<parallel> Q) \<parallel> R'), \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> (Q \<parallel> R'))) \<in> Rel"
        by(metis C1 C4)
      ultimately show ?case by blast
    qed
  qed
qed

lemma parNilLeft:
  fixes \<Psi> :: 'b
  and   P   :: "('a, 'b, 'c) psi"
  and   Rel :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"  

  assumes "eqvt Rel"
  and     C1: "\<And>Q. (\<Psi>, Q \<parallel> \<zero>, Q) \<in> Rel"

  shows "\<Psi> \<rhd> (P \<parallel> \<zero>) \<leadsto>[Rel] P"
using \<open>eqvt Rel\<close>
proof(induct rule: simI[of _ _ _ _ "()"])
  case(cSim \<alpha> P')
  from \<open>\<Psi> \<rhd> P \<longmapsto>\<alpha> \<prec> P'\<close> have "\<Psi> \<otimes> SBottom' \<rhd> P \<longmapsto>\<alpha> \<prec> P'"
    by(metis statEqTransition Identity AssertionStatEqSym)
  hence "\<Psi> \<rhd> (P \<parallel> \<zero>) \<longmapsto>\<alpha> \<prec> (P' \<parallel> \<zero>)"
    by(rule_tac Par1) auto
  moreover have "(\<Psi>, P' \<parallel> \<zero>, P') \<in> Rel" by(rule C1)
  ultimately show ?case by blast
qed

lemma parNilRight:
  fixes \<Psi> :: 'b
  and   P   :: "('a, 'b, 'c) psi"
  and   Rel :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"  

  assumes "eqvt Rel"
  and     C1: "\<And>Q. (\<Psi>, Q, (Q \<parallel> \<zero>)) \<in> Rel"

  shows "\<Psi> \<rhd> P \<leadsto>[Rel] (P \<parallel> \<zero>)"
using \<open>eqvt Rel\<close>
proof(induct rule: simI[of _ _ _ _ "()"])
  case(cSim \<alpha> P')
  note \<open>\<Psi> \<rhd> P \<parallel> \<zero> \<longmapsto>\<alpha> \<prec> P'\<close> \<open>bn \<alpha> \<sharp>* \<Psi>\<close> \<open>bn \<alpha> \<sharp>* P\<close>
  moreover have "bn \<alpha> \<sharp>* \<zero>" by simp
  ultimately show ?case using \<open>bn \<alpha> \<sharp>* subject \<alpha>\<close>
  proof(induct rule: parCases[where C="()"])
    case(cPar1 P' A\<^sub>Q \<Psi>\<^sub>Q)
    from \<open>extractFrame(\<zero>) = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>\<close> have "\<Psi>\<^sub>Q = SBottom'" by auto
    with \<open>\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>\<alpha> \<prec> P'\<close> have "\<Psi> \<rhd> P \<longmapsto>\<alpha> \<prec> P'"
      by(metis statEqTransition Identity)
    moreover have "(\<Psi>, P', P' \<parallel> \<zero>) \<in> Rel" by(rule C1)
    ultimately show ?case by blast
  next
    case(cPar2 Q' A\<^sub>P \<Psi>\<^sub>P)
    from \<open>\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> \<zero> \<longmapsto>\<alpha> \<prec> Q'\<close> have False
      by auto
    thus ?case by simp
  next
    case(cComm1 \<Psi>\<^sub>Q M N P' A\<^sub>P \<Psi>\<^sub>P K xvec Q' A\<^sub>Q)
    from \<open>\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> \<zero> \<longmapsto>K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'\<close> have False by auto
    thus ?case by simp
  next
    case(cComm2 \<Psi>\<^sub>Q M xvec N P' A\<^sub>P \<Psi>\<^sub>P K Q' A\<^sub>Q)
    from \<open>\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> \<zero> \<longmapsto>K\<lparr>N\<rparr> \<prec> Q'\<close> have False
      by auto
    thus ?case by simp
  qed
qed

lemma resNilLeft:
  fixes x   :: name
  and   \<Psi>   :: 'b
  and   Rel :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"

  shows "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>\<zero> \<leadsto>[Rel] \<zero>"
by(auto simp add: simulation_def)

lemma resNilRight:
  fixes x   :: name
  and   \<Psi>   :: 'b
  and   Rel :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"

  shows "\<Psi> \<rhd> \<zero> \<leadsto>[Rel] \<lparr>\<nu>x\<rparr>\<zero>"
apply(auto simp add: simulation_def)
by(cases rule: semantics.cases) (auto simp add: psi.inject alpha')

lemma inputPushResLeft:
  fixes \<Psi>   :: 'b
  and   x    :: name
  and   M    :: 'a
  and   xvec :: "name list"
  and   N    :: 'a
  and   P    :: "('a, 'b, 'c) psi"

  assumes "eqvt Rel"
  and     "x \<sharp> \<Psi>"
  and     "x \<sharp> M"
  and     "x \<sharp> xvec"
  and     "x \<sharp> N"
  and     C1: "\<And>Q. (\<Psi>, Q, Q) \<in> Rel"

  shows "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(M\<lparr>\<lambda>*xvec N\<rparr>.P) \<leadsto>[Rel] M\<lparr>\<lambda>*xvec N\<rparr>.\<lparr>\<nu>x\<rparr>P"
proof -
  note \<open>eqvt Rel\<close> \<open>x \<sharp> \<Psi>\<close>
  moreover have "x \<sharp> \<lparr>\<nu>x\<rparr>(M\<lparr>\<lambda>*xvec N\<rparr>.P)" by(simp add: abs_fresh)
  moreover from \<open>x \<sharp> M\<close> \<open>x \<sharp> N\<close> have "x \<sharp> M\<lparr>\<lambda>*xvec N\<rparr>.\<lparr>\<nu>x\<rparr>P"
    by(auto simp add: inputChainFresh abs_fresh)
  ultimately show ?thesis
  proof(induct rule: simIFresh[of _ _ _ _ _ "()"])
    case(cSim \<alpha> P')
    from \<open>\<Psi> \<rhd> M\<lparr>\<lambda>*xvec N\<rparr>.\<lparr>\<nu>x\<rparr>P \<longmapsto>\<alpha> \<prec> P'\<close> \<open>x \<sharp> \<alpha>\<close> show ?case
    proof(induct rule: inputCases)
      case(cInput K Tvec)
      from \<open>x \<sharp> K\<lparr>N[xvec::=Tvec]\<rparr>\<close> have "x \<sharp> K" and "x \<sharp> N[xvec::=Tvec]" by simp+
      from \<open>\<Psi> \<turnstile> M \<leftrightarrow> K\<close> \<open>distinct xvec\<close> \<open>set xvec \<subseteq> supp N\<close> \<open>length xvec = length Tvec\<close>
      have "\<Psi> \<rhd> M\<lparr>\<lambda>*xvec N\<rparr>.P \<longmapsto>K\<lparr>(N[xvec::=Tvec])\<rparr> \<prec> P[xvec::=Tvec]"
        by(rule Input)
      hence "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(M\<lparr>\<lambda>*xvec N\<rparr>.P) \<longmapsto>K\<lparr>(N[xvec::=Tvec])\<rparr> \<prec> \<lparr>\<nu>x\<rparr>(P[xvec::=Tvec])" using \<open>x \<sharp> \<Psi>\<close> \<open>x \<sharp> K\<close> \<open>x \<sharp> N[xvec::=Tvec]\<close>
        by(rule_tac Scope) auto
      moreover from \<open>length xvec = length Tvec\<close> \<open>distinct xvec\<close> \<open>set xvec \<subseteq> supp N\<close> \<open>x \<sharp> N[xvec::=Tvec]\<close> have "x \<sharp> Tvec"
        by(rule substTerm.subst3)
      with \<open>x \<sharp> xvec\<close> have "(\<Psi>, \<lparr>\<nu>x\<rparr>(P[xvec::=Tvec]), (\<lparr>\<nu>x\<rparr>P)[xvec::=Tvec]) \<in> Rel"
        by(force intro: C1)
      ultimately show ?case by blast
    qed
  qed
qed
 
lemma inputPushResRight:
  fixes \<Psi>   :: 'b
  and   x    :: name
  and   M    :: 'a
  and   xvec :: "name list"
  and   N    :: 'a
  and   P    :: "('a, 'b, 'c) psi"

  assumes "eqvt Rel"
  and     "x \<sharp> \<Psi>"
  and     "x \<sharp> M"
  and     "x \<sharp> xvec"
  and     "x \<sharp> N"
  and     C1: "\<And>Q. (\<Psi>, Q, Q) \<in> Rel"

  shows "\<Psi> \<rhd> M\<lparr>\<lambda>*xvec N\<rparr>.\<lparr>\<nu>x\<rparr>P \<leadsto>[Rel] \<lparr>\<nu>x\<rparr>(M\<lparr>\<lambda>*xvec N\<rparr>.P)"
proof -
  note \<open>eqvt Rel\<close> \<open>x \<sharp> \<Psi>\<close>
  moreover from \<open>x \<sharp> M\<close> \<open>x \<sharp> N\<close> have "x \<sharp> M\<lparr>\<lambda>*xvec N\<rparr>.\<lparr>\<nu>x\<rparr>P"
    by(auto simp add: inputChainFresh abs_fresh)
  moreover have "x \<sharp> \<lparr>\<nu>x\<rparr>(M\<lparr>\<lambda>*xvec N\<rparr>.P)" by(simp add: abs_fresh)
  ultimately show ?thesis
  proof(induct rule: simIFresh[of _ _ _ _ _ "()"])
    case(cSim \<alpha> P')
    note \<open>\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(M\<lparr>\<lambda>*xvec N\<rparr>.P) \<longmapsto>\<alpha> \<prec> P'\<close> \<open>x \<sharp> \<Psi>\<close> \<open>x \<sharp> \<alpha>\<close> \<open>x \<sharp> P'\<close> \<open>bn \<alpha> \<sharp>* \<Psi>\<close> 
    moreover from \<open>bn \<alpha> \<sharp>* (\<lparr>\<nu>x\<rparr>(M\<lparr>\<lambda>*xvec N\<rparr>.P))\<close> \<open>x \<sharp> \<alpha>\<close> have  "bn \<alpha> \<sharp>* (M\<lparr>\<lambda>*xvec N\<rparr>.P)"
      by simp
    ultimately show ?case using \<open>bn \<alpha> \<sharp>* subject \<alpha>\<close>
    proof(induct rule: resCases)
      case(cRes P')
      from \<open>\<Psi> \<rhd> M\<lparr>\<lambda>*xvec N\<rparr>.P \<longmapsto>\<alpha> \<prec> P'\<close> \<open>x \<sharp> \<alpha>\<close> show ?case
      proof(induct rule: inputCases)
        case(cInput K Tvec)
        from \<open>x \<sharp> K\<lparr>N[xvec::=Tvec]\<rparr>\<close> have "x \<sharp> K" and "x \<sharp> N[xvec::=Tvec]" by simp+
        from \<open>\<Psi> \<turnstile> M \<leftrightarrow> K\<close> \<open>distinct xvec\<close> \<open>set xvec \<subseteq> supp N\<close> \<open>length xvec = length Tvec\<close>
        have "\<Psi> \<rhd> M\<lparr>\<lambda>*xvec N\<rparr>.(\<lparr>\<nu>x\<rparr>P) \<longmapsto>K\<lparr>(N[xvec::=Tvec])\<rparr> \<prec> (\<lparr>\<nu>x\<rparr>P)[xvec::=Tvec]"
          by(rule Input)
        moreover from \<open>length xvec = length Tvec\<close> \<open>distinct xvec\<close> \<open>set xvec \<subseteq> supp N\<close> \<open>x \<sharp> N[xvec::=Tvec]\<close> have "x \<sharp> Tvec"
          by(rule substTerm.subst3)
        with \<open>x \<sharp> xvec\<close> have "(\<Psi>, (\<lparr>\<nu>x\<rparr>P)[xvec::=Tvec], \<lparr>\<nu>x\<rparr>(P[xvec::=Tvec])) \<in> Rel"
          by(force intro: C1)
        ultimately show ?case by blast
      qed
    next
      case cOpen
      then have False by auto
      thus ?case by simp
    qed
  qed
qed

lemma outputPushResLeft:
  fixes \<Psi>   :: 'b
  and   x    :: name
  and   M    :: 'a
  and   N    :: 'a
  and   P    :: "('a, 'b, 'c) psi"

  assumes "eqvt Rel"
  and     "x \<sharp> \<Psi>"
  and     "x \<sharp> M"
  and     "x \<sharp> N"
  and     C1: "\<And>Q. (\<Psi>, Q, Q) \<in> Rel"

  shows "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(M\<langle>N\<rangle>.P) \<leadsto>[Rel] M\<langle>N\<rangle>.\<lparr>\<nu>x\<rparr>P"
proof -
  note \<open>eqvt Rel\<close> \<open>x \<sharp> \<Psi>\<close>
  moreover have "x \<sharp> \<lparr>\<nu>x\<rparr>(M\<langle>N\<rangle>.P)" by(simp add: abs_fresh)
  moreover from \<open>x \<sharp> M\<close> \<open>x \<sharp> N\<close> have "x \<sharp> M\<langle>N\<rangle>.\<lparr>\<nu>x\<rparr>P"
    by(auto simp add: abs_fresh)
  ultimately show ?thesis
  proof(induct rule: simIFresh[of _ _ _ _ _ "()"])
    case(cSim \<alpha> P')
    from \<open>\<Psi> \<rhd> M\<langle>N\<rangle>.\<lparr>\<nu>x\<rparr>P \<longmapsto>\<alpha> \<prec> P'\<close> \<open>x \<sharp> \<alpha>\<close>
    show ?case
    proof(induct rule: outputCases)
      case(cOutput K)
      from \<open>\<Psi> \<turnstile> M \<leftrightarrow> K\<close> have "\<Psi> \<rhd> M\<langle>N\<rangle>.P \<longmapsto>K\<langle>N\<rangle> \<prec> P"
        by(rule Output)
      hence "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(M\<langle>N\<rangle>.P) \<longmapsto>K\<langle>N\<rangle> \<prec> \<lparr>\<nu>x\<rparr>P" using \<open>x \<sharp> \<Psi>\<close> \<open>x \<sharp> K\<langle>N\<rangle>\<close>
        by(rule Scope)
      moreover have "(\<Psi>, \<lparr>\<nu>x\<rparr>P, \<lparr>\<nu>x\<rparr>P) \<in> Rel" by(rule C1)
      ultimately show ?case by blast
    qed
  qed
qed
 
lemma outputPushResRight:
  fixes \<Psi>   :: 'b
  and   x    :: name
  and   M    :: 'a
  and   N    :: 'a
  and   P    :: "('a, 'b, 'c) psi"

  assumes "eqvt Rel"
  and     "x \<sharp> \<Psi>"
  and     "x \<sharp> M"
  and     "x \<sharp> N"
  and     C1: "\<And>Q. (\<Psi>, Q, Q) \<in> Rel"

  shows "\<Psi> \<rhd> M\<langle>N\<rangle>.\<lparr>\<nu>x\<rparr>P \<leadsto>[Rel] \<lparr>\<nu>x\<rparr>(M\<langle>N\<rangle>.P)"
proof -
  note \<open>eqvt Rel\<close> \<open>x \<sharp> \<Psi>\<close>
  moreover from \<open>x \<sharp> M\<close> \<open>x \<sharp> N\<close> have "x \<sharp> M\<langle>N\<rangle>.\<lparr>\<nu>x\<rparr>P"
    by(auto simp add: abs_fresh)
  moreover have "x \<sharp> \<lparr>\<nu>x\<rparr>(M\<langle>N\<rangle>.P)" by(simp add: abs_fresh)
  ultimately show ?thesis
  proof(induct rule: simIFresh[of _ _ _ _ _ "(M, N)"])
    case(cSim \<alpha> P')
    note \<open>\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(M\<langle>N\<rangle>.P) \<longmapsto>\<alpha> \<prec> P'\<close> \<open>x \<sharp> \<Psi>\<close> \<open>x \<sharp> \<alpha>\<close> \<open>x \<sharp> P'\<close> \<open>bn \<alpha> \<sharp>* \<Psi>\<close>
    moreover from \<open>bn \<alpha> \<sharp>* (\<lparr>\<nu>x\<rparr>(M\<langle>N\<rangle>.P))\<close> \<open>x \<sharp> \<alpha>\<close> have "bn \<alpha> \<sharp>* (M\<langle>N\<rangle>.P)" by simp
    ultimately show ?case using \<open>bn \<alpha> \<sharp>* subject \<alpha>\<close> \<open>bn \<alpha> \<sharp>* (M, N)\<close> \<open>x \<sharp> \<alpha>\<close>
    proof(induct rule: resCases)
      case(cOpen K xvec1 xvec2 y N' P')
      from \<open>bn(K\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N'\<rangle>) \<sharp>* (M, N)\<close> have "y \<sharp> N" by simp+
      from \<open>\<Psi> \<rhd> M\<langle>N\<rangle>.P \<longmapsto>K\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>([(x, y)] \<bullet> N')\<rangle> \<prec> ([(x, y)] \<bullet> P')\<close>
      have "N = ([(x, y)] \<bullet> N')"
        apply -
        by(ind_cases "\<Psi> \<rhd> M\<langle>N\<rangle>.P \<longmapsto>K\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>([(x, y)] \<bullet> N')\<rangle> \<prec> ([(x, y)] \<bullet> P')")
          (auto simp add: residualInject psi.inject)
      with \<open>x \<sharp> N\<close> \<open>y \<sharp> N\<close> \<open>x \<noteq> y\<close> have "N = N'"
        by(subst pt_bij[OF pt_name_inst, OF at_name_inst, symmetric, where pi="[(x, y)]"])
          (simp add: fresh_left calc_atm)
      with \<open>y \<in> supp N'\<close> \<open>y \<sharp> N\<close> have False by(simp add: fresh_def)
      thus ?case by simp
    next
      case(cRes P')
      from \<open>\<Psi> \<rhd> M\<langle>N\<rangle>.P \<longmapsto>\<alpha> \<prec> P'\<close> show ?case
      proof(induct rule: outputCases)
        case(cOutput K)
        from \<open>\<Psi> \<turnstile> M \<leftrightarrow> K\<close> have "\<Psi> \<rhd> M\<langle>N\<rangle>.(\<lparr>\<nu>x\<rparr>P) \<longmapsto>K\<langle>N\<rangle> \<prec> \<lparr>\<nu>x\<rparr>P"
          by(rule Output)
        moreover have "(\<Psi>, \<lparr>\<nu>x\<rparr>P, \<lparr>\<nu>x\<rparr>P) \<in> Rel" by(rule C1)
        ultimately show ?case by force
      qed
    qed
  qed
qed

lemma casePushResLeft:
  fixes \<Psi>  :: 'b
  and   x  :: name
  and   Cs :: "('c \<times> ('a, 'b, 'c) psi) list"

  assumes "eqvt Rel"
  and     "x \<sharp> \<Psi>"
  and     "x \<sharp> map fst Cs"
  and     C1: "\<And>Q. (\<Psi>, Q, Q) \<in> Rel"

  shows "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(Cases Cs) \<leadsto>[Rel] Cases (map (\<lambda>(\<phi>, P). (\<phi>, \<lparr>\<nu>x\<rparr>P)) Cs)"
proof -
  note \<open>eqvt Rel\<close> \<open>x \<sharp> \<Psi>\<close>
  moreover have "x \<sharp> \<lparr>\<nu>x\<rparr>(Cases Cs)" by(simp add: abs_fresh)
  moreover from \<open>x \<sharp> map fst Cs\<close> have "x \<sharp> Cases (map (\<lambda>(\<phi>, P). (\<phi>, \<lparr>\<nu>x\<rparr>P)) Cs)"
    by(induct Cs) (auto simp add: abs_fresh)
  ultimately show ?thesis
  proof(induct rule: simIFresh[of _ _ _ _ _ Cs])
    case(cSim \<alpha> P'')
    from \<open>\<Psi> \<rhd> Cases (map (\<lambda>(\<phi>, P). (\<phi>, \<lparr>\<nu>x\<rparr>P)) Cs) \<longmapsto>\<alpha> \<prec> P''\<close> 
    show ?case
    proof(induct rule: caseCases)
      case(cCase \<phi> P')
      from \<open>(\<phi>, P') mem (map (\<lambda>(\<phi>, P). (\<phi>, \<lparr>\<nu>x\<rparr>P)) Cs)\<close> 
      obtain P where "(\<phi>, P) mem Cs" and "P' = \<lparr>\<nu>x\<rparr>P" 
        by(induct Cs) auto
      from \<open>guarded P'\<close> \<open>P' = \<lparr>\<nu>x\<rparr>P\<close> have "guarded P" by simp
      from \<open>\<Psi> \<rhd> P' \<longmapsto>\<alpha> \<prec> P''\<close> \<open>P' = \<lparr>\<nu>x\<rparr>P\<close> have "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>P \<longmapsto>\<alpha> \<prec> P''"
        by simp
      moreover note \<open>x \<sharp> \<Psi>\<close> \<open>x \<sharp> \<alpha>\<close> \<open>x \<sharp> P''\<close> \<open>bn \<alpha> \<sharp>* \<Psi>\<close> 
      moreover from \<open>bn \<alpha> \<sharp>* Cs\<close> \<open>(\<phi>, P) mem Cs\<close>
      have "bn \<alpha> \<sharp>* P" by(auto dest: memFreshChain)
      ultimately show ?case using \<open>bn \<alpha> \<sharp>* subject \<alpha>\<close> \<open>x \<sharp> \<alpha>\<close> \<open>bn \<alpha> \<sharp>* Cs\<close>
      proof(induct rule: resCases)
        case(cOpen M xvec1 xvec2 y N P')
        from \<open>x \<sharp> M\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N\<rangle>\<close> have "x \<sharp> xvec1" and "x \<sharp> xvec2" and "x \<sharp> M" by simp+
        from \<open>bn(M\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N\<rangle>) \<sharp>* Cs\<close> have "y \<sharp> Cs" by simp
        from \<open>\<Psi> \<rhd> P \<longmapsto>M\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>([(x, y)] \<bullet> N)\<rangle> \<prec> ([(x, y)] \<bullet> P')\<close> \<open>(\<phi>, P) mem Cs\<close> \<open>\<Psi> \<turnstile> \<phi>\<close> \<open>guarded P\<close>
        have "\<Psi> \<rhd> Cases Cs \<longmapsto>M\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>([(x, y)] \<bullet> N)\<rangle> \<prec> ([(x, y)] \<bullet> P')" by(rule Case)
        hence "([(x, y)] \<bullet> \<Psi>) \<rhd> ([(x, y)] \<bullet> (Cases Cs))  \<longmapsto>([(x, y)] \<bullet> (M\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>([(x, y)] \<bullet> N)\<rangle> \<prec> ([(x, y)] \<bullet> P')))"
          by(rule semantics.eqvt)
        with \<open>x \<sharp> \<Psi>\<close> \<open>x \<sharp> M\<close> \<open>y \<sharp> xvec1\<close> \<open>y \<sharp> xvec2\<close> \<open>y \<sharp> \<Psi>\<close> \<open>y \<sharp> M\<close> \<open>x \<sharp> xvec1\<close> \<open>x \<sharp> xvec2\<close>
        have "\<Psi> \<rhd> ([(x, y)] \<bullet> (Cases Cs))  \<longmapsto>M\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>N\<rangle> \<prec> P'" by(simp add: eqvts)
        hence "\<Psi> \<rhd> \<lparr>\<nu>y\<rparr>([(x, y)] \<bullet> (Cases Cs))  \<longmapsto>M\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N\<rangle> \<prec> P'" using \<open>y \<in> supp N\<close> \<open>y \<sharp> \<Psi>\<close> \<open>y \<sharp> M\<close> \<open>y \<sharp> xvec1\<close> \<open>y \<sharp> xvec2\<close>
          by(rule Open)
        hence "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(Cases Cs)  \<longmapsto>M\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N\<rangle> \<prec> P'" using \<open>y \<sharp> Cs\<close>
          by(simp add: alphaRes)
        moreover have "(\<Psi>, P', P') \<in> Rel" by(rule C1)
        ultimately show ?case by blast
      next
        case(cRes P')
        from \<open>\<Psi> \<rhd> P \<longmapsto>\<alpha> \<prec> P'\<close> \<open>(\<phi>, P) mem Cs\<close> \<open>\<Psi> \<turnstile> \<phi>\<close> \<open>guarded P\<close>
        have "\<Psi> \<rhd> Cases Cs \<longmapsto>\<alpha> \<prec> P'" by(rule Case)
        hence "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(Cases Cs) \<longmapsto>\<alpha> \<prec> \<lparr>\<nu>x\<rparr>P'" using \<open>x \<sharp> \<Psi>\<close> \<open>x \<sharp> \<alpha>\<close>
          by(rule Scope)
        moreover have "(\<Psi>, \<lparr>\<nu>x\<rparr>P', \<lparr>\<nu>x\<rparr>P') \<in> Rel" by(rule C1)
        ultimately show ?case by blast
      qed
    qed
  qed
qed
 
lemma casePushResRight:
  fixes \<Psi>  :: 'b
  and   x  :: name
  and   Cs :: "('c \<times> ('a, 'b, 'c) psi) list"

  assumes "eqvt Rel"
  and     "x \<sharp> \<Psi>"
  and     "x \<sharp> map fst Cs"
  and     C1: "\<And>Q. (\<Psi>, Q, Q) \<in> Rel"

  shows "\<Psi> \<rhd> Cases (map (\<lambda>(\<phi>, P). (\<phi>, \<lparr>\<nu>x\<rparr>P)) Cs) \<leadsto>[Rel] \<lparr>\<nu>x\<rparr>(Cases Cs)"
proof -
  note \<open>eqvt Rel\<close> \<open>x \<sharp> \<Psi>\<close>
  moreover from \<open>x \<sharp> map fst Cs\<close> have "x \<sharp> Cases (map (\<lambda>(\<phi>, P). (\<phi>, \<lparr>\<nu>x\<rparr>P)) Cs)"
    by(induct Cs) (auto simp add: abs_fresh)
  moreover have "x \<sharp> \<lparr>\<nu>x\<rparr>(Cases Cs)" by(simp add: abs_fresh)
  ultimately show ?thesis
  proof(induct rule: simIFresh[of _ _ _ _ _ Cs])
    case(cSim \<alpha> P'')
    note \<open>\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(Cases Cs) \<longmapsto>\<alpha> \<prec> P''\<close> \<open>x \<sharp> \<Psi>\<close> \<open>x \<sharp> \<alpha>\<close> \<open>x \<sharp> P''\<close> \<open>bn \<alpha> \<sharp>* \<Psi>\<close>
    moreover from \<open>bn \<alpha> \<sharp>* \<lparr>\<nu>x\<rparr>(Cases Cs)\<close> \<open>x \<sharp> \<alpha>\<close> have "bn \<alpha> \<sharp>* (Cases Cs)" by simp
    ultimately show ?case using \<open>bn \<alpha> \<sharp>* subject \<alpha>\<close> \<open>x \<sharp> \<alpha>\<close> \<open>bn \<alpha> \<sharp>* Cs\<close>
    proof(induct rule: resCases)
      case(cOpen M xvec1 xvec2 y N P')
      from \<open>x \<sharp> M\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N\<rangle>\<close> have "x \<sharp> xvec1" and "x \<sharp> xvec2" and "x \<sharp> M" by simp+
      from \<open>bn(M\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N\<rangle>) \<sharp>* Cs\<close> have "y \<sharp> Cs" by simp
      from \<open>\<Psi> \<rhd> Cases Cs \<longmapsto>M\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>([(x, y)] \<bullet> N)\<rangle> \<prec> ([(x, y)] \<bullet> P')\<close>
      show ?case
      proof(induct rule: caseCases)
        case(cCase \<phi> P)
        from \<open>\<Psi> \<rhd> P \<longmapsto>M\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>([(x, y)] \<bullet> N)\<rangle> \<prec> ([(x, y)] \<bullet> P')\<close>
        have "([(x, y)] \<bullet> \<Psi>) \<rhd> ([(x, y)] \<bullet> P)  \<longmapsto>([(x, y)] \<bullet> (M\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>([(x, y)] \<bullet> N)\<rangle> \<prec> ([(x, y)] \<bullet> P')))"
          by(rule semantics.eqvt)
        with \<open>x \<sharp> \<Psi>\<close> \<open>x \<sharp> M\<close> \<open>y \<sharp> xvec1\<close> \<open>y \<sharp> xvec2\<close> \<open>y \<sharp> \<Psi>\<close> \<open>y \<sharp> M\<close> \<open>x \<sharp> xvec1\<close> \<open>x \<sharp> xvec2\<close>
        have "\<Psi> \<rhd> ([(x, y)] \<bullet> P)  \<longmapsto>M\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>N\<rangle> \<prec> P'" by(simp add: eqvts)
        hence "\<Psi> \<rhd> \<lparr>\<nu>y\<rparr>([(x, y)] \<bullet> P)  \<longmapsto>M\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N\<rangle> \<prec> P'" using \<open>y \<in> supp N\<close> \<open>y \<sharp> \<Psi>\<close> \<open>y \<sharp> M\<close> \<open>y \<sharp> xvec1\<close> \<open>y \<sharp> xvec2\<close>
          by(rule Open)
        hence "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>P  \<longmapsto>M\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N\<rangle> \<prec> P'" using \<open>y \<sharp> Cs\<close> \<open>(\<phi>, P) mem Cs\<close>
          by(subst alphaRes, auto dest: memFresh)
        moreover from \<open>(\<phi>, P) mem Cs\<close> have "(\<phi>, \<lparr>\<nu>x\<rparr>P) mem (map (\<lambda>(\<phi>, P). (\<phi>, \<lparr>\<nu>x\<rparr>P)) Cs)"
          by(induct Cs) auto
        moreover note \<open>\<Psi> \<turnstile> \<phi>\<close>
        moreover from \<open>guarded P\<close> have "guarded(\<lparr>\<nu>x\<rparr>P)" by simp
        ultimately have "\<Psi> \<rhd> (Cases (map (\<lambda>(\<phi>, P). (\<phi>, \<lparr>\<nu>x\<rparr>P)) Cs)) \<longmapsto>M\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N\<rangle> \<prec> P'"
          by(rule Case)
        moreover have "(\<Psi>, P', P') \<in> Rel" by(rule C1)
        ultimately show ?case by blast
      qed
    next
      case(cRes P')
      from \<open>\<Psi> \<rhd> Cases Cs \<longmapsto>\<alpha> \<prec> P'\<close>
      show ?case
      proof(induct rule: caseCases)
        case(cCase \<phi> P)
        from \<open>\<Psi> \<rhd> P \<longmapsto>\<alpha> \<prec> P'\<close> \<open>x \<sharp> \<Psi>\<close> \<open>x \<sharp> \<alpha>\<close>
        have "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>P \<longmapsto>\<alpha> \<prec> \<lparr>\<nu>x\<rparr>P'" by(rule Scope)
        moreover from \<open>(\<phi>, P) mem Cs\<close> have "(\<phi>, \<lparr>\<nu>x\<rparr>P) mem (map (\<lambda>(\<phi>, P). (\<phi>, \<lparr>\<nu>x\<rparr>P)) Cs)"
          by(induct Cs) auto
        moreover note \<open>\<Psi> \<turnstile> \<phi>\<close>
        moreover from \<open>guarded P\<close> have "guarded(\<lparr>\<nu>x\<rparr>P)" by simp
        ultimately have "\<Psi> \<rhd> (Cases (map (\<lambda>(\<phi>, P). (\<phi>, \<lparr>\<nu>x\<rparr>P)) Cs)) \<longmapsto>\<alpha> \<prec> \<lparr>\<nu>x\<rparr>P'"
          by(rule Case)
        moreover have "(\<Psi>, \<lparr>\<nu>x\<rparr>P', \<lparr>\<nu>x\<rparr>P') \<in> Rel" by(rule C1)
        ultimately show ?case by blast
      qed
    qed
  qed
qed

lemma resInputCases[consumes 5, case_names cRes]:
  fixes \<Psi>    :: 'b
  and   x    :: name
  and   P    :: "('a, 'b, 'c) psi"
  and   M    :: 'a
  and   N    :: 'a
  and   P'   :: "('a, 'b, 'c) psi"
  and   C    :: "'d::fs_name"

  assumes Trans: "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>P \<longmapsto>M\<lparr>N\<rparr> \<prec> P'"
  and     "x \<sharp> \<Psi>"
  and     "x \<sharp> M"
  and     "x \<sharp> N"
  and     "x \<sharp> P'"
  and     rScope:  "\<And>P'. \<lbrakk>\<Psi> \<rhd> P \<longmapsto>M\<lparr>N\<rparr> \<prec> P'\<rbrakk> \<Longrightarrow> Prop (\<lparr>\<nu>x\<rparr>P')"

  shows "Prop P'"
proof -
  note Trans \<open>x \<sharp> \<Psi>\<close>
  moreover from \<open>x \<sharp> M\<close> \<open>x \<sharp> N\<close> have "x \<sharp> (M\<lparr>N\<rparr>)" by simp
  moreover note \<open>x \<sharp> P'\<close>
  moreover have "bn(M\<lparr>N\<rparr>) \<sharp>* \<Psi>" and "bn(M\<lparr>N\<rparr>) \<sharp>* P" and "bn(M\<lparr>N\<rparr>) \<sharp>* subject(M\<lparr>N\<rparr>)" and "bn(M\<lparr>N\<rparr>) = []" by simp+
  ultimately show ?thesis
    by(induct rule: resCases) (auto intro: rScope)
qed

lemma scopeExtLeft:
  fixes x   :: name
  and   P   :: "('a, 'b, 'c) psi"
  and   \<Psi>   :: 'b
  and   Q   :: "('a, 'b, 'c) psi"
  and   Rel :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"

  assumes "x \<sharp> P"
  and     "x \<sharp> \<Psi>"
  and     "eqvt Rel"
  and     C1: "\<And>\<Psi>' R. (\<Psi>', R, R) \<in> Rel"
  and     C2: "\<And>y \<Psi>' R S zvec. \<lbrakk>y \<sharp> \<Psi>'; y \<sharp> R; zvec \<sharp>* \<Psi>'\<rbrakk> \<Longrightarrow> (\<Psi>', \<lparr>\<nu>y\<rparr>(\<lparr>\<nu>*zvec\<rparr>(R \<parallel> S)), \<lparr>\<nu>*zvec\<rparr>(R \<parallel> \<lparr>\<nu>y\<rparr>S)) \<in> Rel"
  and     C3: "\<And>\<Psi>' zvec R y. \<lbrakk>y \<sharp> \<Psi>'; zvec \<sharp>* \<Psi>'\<rbrakk> \<Longrightarrow> (\<Psi>', \<lparr>\<nu>y\<rparr>(\<lparr>\<nu>*zvec\<rparr>R), \<lparr>\<nu>*zvec\<rparr>(\<lparr>\<nu>y\<rparr>R)) \<in> Rel"

  shows "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(P \<parallel> Q) \<leadsto>[Rel] P \<parallel> \<lparr>\<nu>x\<rparr>Q"
proof -
  note \<open>eqvt Rel\<close> \<open>x \<sharp> \<Psi>\<close>
  moreover have "x \<sharp> \<lparr>\<nu>x\<rparr>(P \<parallel> Q)" by(simp add: abs_fresh)
  moreover from \<open>x \<sharp> P\<close> have "x \<sharp> P \<parallel> \<lparr>\<nu>x\<rparr>Q" by(simp add: abs_fresh)
  ultimately show ?thesis
  proof(induct rule: simIFresh[of _ _ _ _ _ x])
    case(cSim \<alpha> PQ)
    from \<open>x \<sharp> \<alpha>\<close> \<open>bn \<alpha> \<sharp>* (P \<parallel> \<lparr>\<nu>x\<rparr>Q)\<close> have "bn \<alpha> \<sharp>* Q" by simp
    note \<open>\<Psi> \<rhd> P \<parallel> \<lparr>\<nu>x\<rparr>Q \<longmapsto>\<alpha> \<prec> PQ\<close> \<open>bn \<alpha> \<sharp>* \<Psi>\<close>
    moreover from \<open>bn \<alpha> \<sharp>* (P \<parallel> \<lparr>\<nu>x\<rparr>Q)\<close> have "bn \<alpha> \<sharp>* P" and "bn \<alpha> \<sharp>* \<lparr>\<nu>x\<rparr>Q" by simp+
    ultimately show ?case using \<open>bn \<alpha> \<sharp>* subject \<alpha>\<close> \<open>x \<sharp> PQ\<close>
    proof(induct rule: parCases[where C=x])
      case(cPar1 P' A\<^sub>Q \<Psi>\<^sub>Q)
      from \<open>x \<sharp> P' \<parallel> \<lparr>\<nu>x\<rparr>Q\<close> have "x \<sharp> P'" by simp
      have PTrans: "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>\<alpha> \<prec> P'" by fact
      from \<open>extractFrame(\<lparr>\<nu>x\<rparr>Q) = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>\<close> have FrxQ: "\<lparr>\<nu>x\<rparr>(extractFrame Q) = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" by simp
      then obtain y A\<^sub>Q' where A: "A\<^sub>Q = y#A\<^sub>Q'" by(case_tac A\<^sub>Q) auto
      with \<open>A\<^sub>Q \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q \<sharp>* P\<close> \<open>A\<^sub>Q \<sharp>* \<alpha>\<close>
      have "A\<^sub>Q' \<sharp>* \<Psi>" and "A\<^sub>Q' \<sharp>* P" and "A\<^sub>Q' \<sharp>* \<alpha>"
        and "y \<sharp> \<Psi>" and "y \<sharp> P" and "y \<sharp> \<alpha>"
        by simp+
      from PTrans \<open>y \<sharp> P\<close> \<open>y \<sharp> \<alpha>\<close> \<open>bn \<alpha> \<sharp>* subject \<alpha>\<close> \<open>distinct(bn \<alpha>)\<close> have "y \<sharp> P'"
        by(auto intro: freeFreshDerivative)
      note PTrans
      moreover from A \<open>A\<^sub>Q \<sharp>* x\<close> FrxQ have "extractFrame([(y, x)] \<bullet> Q) = \<langle>A\<^sub>Q', \<Psi>\<^sub>Q\<rangle>" 
        by(simp add: frame.inject alpha' fresh_list_cons eqvts) 
      moreover from \<open>bn \<alpha> \<sharp>* Q\<close> have "([(y, x)] \<bullet> (bn \<alpha>)) \<sharp>* ([(y, x)] \<bullet> Q)"
        by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
      with \<open>x \<sharp> \<alpha>\<close> \<open>A\<^sub>Q \<sharp>* \<alpha>\<close> A have "bn \<alpha> \<sharp>* ([(y, x)] \<bullet> Q)" by simp
      ultimately have "\<Psi> \<rhd> P \<parallel> ([(y, x)] \<bullet> Q) \<longmapsto>\<alpha> \<prec> (P' \<parallel> ([(y, x)] \<bullet> Q))"
        using \<open>A\<^sub>Q' \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q' \<sharp>* P\<close> \<open>A\<^sub>Q' \<sharp>* \<alpha>\<close>
        by(rule Par1)
      hence "\<Psi> \<rhd> \<lparr>\<nu>y\<rparr>(P \<parallel> ([(y, x)] \<bullet> Q)) \<longmapsto>\<alpha> \<prec> \<lparr>\<nu>y\<rparr>(P' \<parallel> ([(y, x)] \<bullet> Q))"
        using \<open>y \<sharp> \<Psi>\<close> \<open>y \<sharp> \<alpha>\<close>
        by(rule Scope)
      hence "([(y, x)] \<bullet> \<Psi>) \<rhd> ([(y, x)] \<bullet> (\<lparr>\<nu>y\<rparr>(P \<parallel> ([(y, x)] \<bullet> Q)))) \<longmapsto>([(y, x)] \<bullet> (\<alpha> \<prec> \<lparr>\<nu>y\<rparr>(P' \<parallel> ([(y, x)] \<bullet> Q))))"
        by(rule semantics.eqvt)
      with \<open>x \<sharp> \<Psi>\<close> \<open>y \<sharp> \<Psi>\<close> \<open>x \<sharp> P\<close> \<open>y \<sharp> P\<close> \<open>x \<sharp> \<alpha>\<close> \<open>y \<sharp> \<alpha>\<close> \<open>x \<sharp> P'\<close> \<open>y \<sharp> P'\<close>
      have "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(P \<parallel> Q) \<longmapsto>\<alpha> \<prec> \<lparr>\<nu>x\<rparr>(P' \<parallel> Q)"
        by(simp add: eqvts calc_atm)
      moreover from \<open>x \<sharp> \<Psi>\<close> \<open>x \<sharp> P'\<close> have "(\<Psi>, \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*[]\<rparr>(P' \<parallel> Q)), \<lparr>\<nu>*[]\<rparr>(P' \<parallel> \<lparr>\<nu>x\<rparr>Q)) \<in> Rel"
        by(rule_tac C2) auto
      ultimately show ?case
        by force
    next
      case(cPar2 xQ' A\<^sub>P \<Psi>\<^sub>P)
      from \<open>A\<^sub>P \<sharp>* \<lparr>\<nu>x\<rparr>Q\<close> \<open>A\<^sub>P \<sharp>* x\<close> have "A\<^sub>P \<sharp>* Q" by simp
      note \<open>\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> \<lparr>\<nu>x\<rparr>Q \<longmapsto>\<alpha> \<prec> xQ'\<close>
      moreover have FrP: "extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" by fact
      with \<open>x \<sharp> P\<close> \<open>A\<^sub>P \<sharp>* x\<close> have "x \<sharp> \<Psi>\<^sub>P" and "x \<sharp> A\<^sub>P"
        by(force dest: extractFrameFresh)+
      with \<open>x \<sharp> \<Psi>\<close> have "x \<sharp> \<Psi> \<otimes> \<Psi>\<^sub>P" by force
      moreover note \<open>x \<sharp> \<alpha>\<close>
      moreover from \<open>x \<sharp> P \<parallel> xQ'\<close> have "x \<sharp> xQ'" by simp
      moreover from FrP \<open>bn \<alpha> \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* \<alpha>\<close> have "bn \<alpha> \<sharp>* \<Psi>\<^sub>P"
        by(drule_tac extractFrameFreshChain) auto
      with \<open>bn \<alpha> \<sharp>* \<Psi>\<close> have "bn \<alpha> \<sharp>* (\<Psi> \<otimes> \<Psi>\<^sub>P)" by force
      ultimately show ?case using \<open>bn \<alpha> \<sharp>* Q\<close> \<open>bn \<alpha> \<sharp>* subject \<alpha>\<close> \<open>x \<sharp> \<alpha>\<close> \<open>bn \<alpha> \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* \<alpha>\<close> \<open>bn \<alpha> \<sharp>* \<Psi>\<close>
      proof(induct rule: resCases')
        case(cOpen M xvec1 xvec2 y N Q')
        from \<open>x \<sharp> M\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N\<rangle>\<close> have "x \<sharp> xvec1" and "x \<noteq> y" and "x \<sharp> xvec2" by simp+
        from \<open>bn(M\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N\<rangle>) \<sharp>* \<Psi>\<close> have "y \<sharp> \<Psi>" by simp
        note \<open>\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> ([(x, y)] \<bullet> Q) \<longmapsto>M\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>N\<rangle> \<prec> Q'\<close> FrP
        moreover from \<open>bn(M\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N\<rangle>) \<sharp>* P\<close> have "(xvec1@xvec2) \<sharp>* P" and "y \<sharp> P" by simp+
        moreover from \<open>A\<^sub>P \<sharp>* (M\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N\<rangle>)\<close> have "A\<^sub>P \<sharp>* (M\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>N\<rangle>)" and "y \<sharp> A\<^sub>P" by simp+
        moreover from \<open>A\<^sub>P \<sharp>* Q\<close> \<open>x \<sharp> A\<^sub>P\<close> \<open>y \<sharp> A\<^sub>P\<close> have "A\<^sub>P \<sharp>* ([(x, y)] \<bullet> Q)" by simp
        ultimately have "\<Psi> \<rhd> P \<parallel> ([(x, y)] \<bullet> Q) \<longmapsto>M\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>N\<rangle> \<prec> (P \<parallel> Q')" 
          using \<open>A\<^sub>P \<sharp>* \<Psi>\<close>
          by(rule_tac Par2) (assumption | simp)+
         hence "\<Psi> \<rhd> \<lparr>\<nu>y\<rparr>(P \<parallel> ([(x, y)] \<bullet> Q)) \<longmapsto>M\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N\<rangle> \<prec> (P \<parallel> Q')"
           using \<open>y \<in> supp N\<close> \<open>y \<sharp> \<Psi>\<close> \<open>y \<sharp> M\<close> \<open>y \<sharp> xvec1\<close> \<open>y \<sharp> xvec2\<close>
           by(rule Open)
         with \<open>x \<sharp> P\<close> \<open>y \<sharp> P\<close> \<open>y \<sharp> Q\<close> have "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(P \<parallel> Q) \<longmapsto>M\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N\<rangle> \<prec> (P \<parallel> Q')"
           by(subst alphaRes[where y=y]) (simp add: fresh_left calc_atm eqvts)+
        moreover have "(\<Psi>, P \<parallel> Q', P \<parallel> Q') \<in> Rel" by(rule C1)
        ultimately show ?case by blast
      next
        case(cRes Q')
        from \<open>\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>\<alpha> \<prec> Q'\<close> FrP \<open>bn \<alpha> \<sharp>* P\<close>
        have "\<Psi> \<rhd> P \<parallel> Q \<longmapsto>\<alpha> \<prec> (P \<parallel> Q')" using \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* Q\<close> \<open>A\<^sub>P \<sharp>* \<alpha>\<close>
          by(rule Par2)
        hence "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(P \<parallel> Q) \<longmapsto>\<alpha> \<prec> \<lparr>\<nu>x\<rparr>(P \<parallel> Q')" using \<open>x \<sharp> \<Psi>\<close> \<open>x \<sharp> \<alpha>\<close>
          by(rule Scope)
        moreover from \<open>x \<sharp> \<Psi>\<close> \<open>x \<sharp> P\<close> have "(\<Psi>, \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*[]\<rparr>(P \<parallel> Q')), \<lparr>\<nu>*[]\<rparr>(P \<parallel> \<lparr>\<nu>x\<rparr>Q')) \<in> Rel"
          by(rule_tac C2) auto
        ultimately show ?case
          by force
      qed
    next
      case(cComm1 \<Psi>\<^sub>Q M N P' A\<^sub>P \<Psi>\<^sub>P K xvec xQ' A\<^sub>Q)
      have QTrans: "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> \<lparr>\<nu>x\<rparr>Q \<longmapsto>K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> xQ'" and FrQ: "extractFrame(\<lparr>\<nu>x\<rparr>Q) = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" by fact+
      have PTrans: "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>M\<lparr>N\<rparr> \<prec> P'" and FrP: "extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" by fact+
      have "x \<sharp> \<lparr>\<nu>x\<rparr>Q" by(simp add: abs_fresh)
      with QTrans have "x \<sharp> N" and "x \<sharp> xQ'" using \<open>xvec \<sharp>* x\<close> \<open>xvec \<sharp>* K\<close> \<open>distinct xvec\<close> 
        by(force intro: outputFreshDerivative)+
      from PTrans \<open>x \<sharp> P\<close> \<open>x \<sharp> N\<close>  have "x \<sharp> P'" by(rule inputFreshDerivative)
      from \<open>x \<sharp> \<lparr>\<nu>x\<rparr>Q\<close> FrQ \<open>A\<^sub>Q \<sharp>* x\<close> have "x \<sharp> \<Psi>\<^sub>Q"
        by(drule_tac extractFrameFresh) auto
      from \<open>x \<sharp> P\<close> FrP \<open>A\<^sub>P \<sharp>* x\<close> have "x \<sharp> \<Psi>\<^sub>P"
        by(drule_tac extractFrameFresh) auto
      from \<open>A\<^sub>P \<sharp>* \<lparr>\<nu>x\<rparr>Q\<close> \<open>A\<^sub>P \<sharp>* x\<close> have "A\<^sub>P \<sharp>* Q" by simp
      from \<open>A\<^sub>Q \<sharp>* \<lparr>\<nu>x\<rparr>Q\<close> \<open>A\<^sub>Q \<sharp>* x\<close> have "A\<^sub>Q \<sharp>* Q" by simp
      from PTrans FrP \<open>distinct A\<^sub>P\<close> \<open>x \<sharp> P\<close> \<open>A\<^sub>Q \<sharp>* P\<close> \<open>xvec \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<^sub>Q\<close> \<open>A\<^sub>P \<sharp>* x\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>Q\<close> \<open>A\<^sub>P \<sharp>* P\<close>  \<open>A\<^sub>P \<sharp>* M\<close> \<open>A\<^sub>P \<sharp>* xvec\<close>
      obtain M' where "(\<Psi> \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>P \<turnstile> M \<leftrightarrow> M'" and "x \<sharp> M'" and "A\<^sub>Q \<sharp>* M'" and "xvec \<sharp>* M'"
        by(rule_tac B="x#xvec@A\<^sub>Q" in obtainPrefix) (assumption | force simp add: fresh_star_list_cons)+
      hence MeqM': "\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q \<turnstile> M \<leftrightarrow> M'" by(metis statEqEnt Associativity Commutativity Composition)
      with \<open>\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q \<turnstile> M \<leftrightarrow> K\<close> have "\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q \<turnstile> K \<leftrightarrow> M'"
        by(blast intro: chanEqTrans chanEqSym)
      hence "(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>Q \<turnstile> K \<leftrightarrow> M'" by(metis statEqEnt Associativity Commutativity Composition)
      with QTrans FrQ \<open>distinct A\<^sub>Q\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<^sub>P\<close> \<open>A\<^sub>Q \<sharp>* (\<lparr>\<nu>x\<rparr>Q)\<close> \<open>A\<^sub>Q \<sharp>* K\<close> \<open>A\<^sub>Q \<sharp>* M'\<close>
      have "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> \<lparr>\<nu>x\<rparr>Q \<longmapsto>M'\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> xQ'"
        by(force intro: outputRenameSubject)
      moreover from \<open>x \<sharp> \<Psi>\<close> \<open>x \<sharp> \<Psi>\<^sub>P\<close> have "x \<sharp> \<Psi> \<otimes> \<Psi>\<^sub>P" by force
      moreover from \<open>xvec \<sharp>* x\<close> have "x \<sharp> xvec" by simp
      with \<open>x \<sharp> M'\<close> \<open>x \<sharp> N\<close> have "x \<sharp> M'\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>" by simp
      moreover note \<open>x \<sharp> xQ'\<close>
      moreover from \<open>xvec \<sharp>* \<Psi>\<close> \<open>xvec \<sharp>* \<Psi>\<^sub>P\<close> have "bn(M'\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>) \<sharp>* (\<Psi> \<otimes> \<Psi>\<^sub>P)" by force
      moreover from \<open>xvec \<sharp>* \<lparr>\<nu>x\<rparr>Q\<close> \<open>x \<sharp> xvec\<close> have "bn(M'\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>) \<sharp>* Q" by simp
      moreover from \<open>xvec \<sharp>* P\<close> have "bn(M'\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>) \<sharp>* P" by simp
      from \<open>xvec \<sharp>* \<Psi>\<close> have "bn(M'\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>) \<sharp>* \<Psi>" by simp
      from \<open>A\<^sub>Q \<sharp>* xvec\<close> \<open>A\<^sub>Q \<sharp>* M'\<close> \<open>A\<^sub>Q \<sharp>* N\<close> have "A\<^sub>Q \<sharp>* (M'\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>)" by simp
      have "object(M'\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>) = Some N" by simp
      have "bn(M'\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>) = xvec" by simp
      have "subject(M'\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>) = Some M'" by simp
      from \<open>xvec \<sharp>* M'\<close> have "bn(M'\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>) \<sharp>* subject(M'\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>)" by simp
      ultimately show ?case 
        using \<open>x \<sharp> M'\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>\<close> \<open>bn(M'\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>) \<sharp>* P\<close> \<open>bn(M'\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>) \<sharp>* \<Psi>\<close> \<open>object(M'\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>) = Some N\<close>
              \<open>bn(M'\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>) = xvec\<close> \<open>subject(M'\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>) = Some M'\<close> \<open>A\<^sub>Q \<sharp>* (M'\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>)\<close>
      proof(induct rule: resCases)
        case(cOpen M'' xvec1 xvec2 y N' Q')
        from \<open>x \<sharp> M''\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N'\<rangle>\<close> have "x \<sharp> xvec1" and "x \<noteq> y" and "x \<sharp> xvec2" and "x \<sharp> M''"
          by simp+
        from \<open>bn(M''\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N'\<rangle>) \<sharp>* P\<close> have "(xvec1@xvec2) \<sharp>* P" and "y \<sharp> P" by simp+
        from \<open>A\<^sub>Q \<sharp>* (M''\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N'\<rangle>)\<close> have "(xvec1@xvec2) \<sharp>* A\<^sub>Q" and "y \<sharp> A\<^sub>Q" and "A\<^sub>Q \<sharp>* M''" by simp+
        from \<open>bn(M''\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N'\<rangle>) \<sharp>* \<Psi>\<close> have "(xvec1@xvec2) \<sharp>* \<Psi>" and "y \<sharp> \<Psi>" by simp+
        from \<open>object(M''\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N'\<rangle>) = Some N\<close> have "N = N'" by simp
        from \<open>bn(M''\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N'\<rangle>) = xvec\<close> have "xvec = xvec1@y#xvec2" by simp
        from \<open>subject(M''\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N'\<rangle>) = Some M'\<close> have "M' = M''" by simp
        from \<open>x \<sharp> P\<close> \<open>y \<sharp> P\<close> \<open>x \<noteq> y\<close> \<open>\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>M\<lparr>N\<rparr> \<prec> P'\<close>
        have "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>M\<lparr>([(y, x)] \<bullet> N)\<rparr> \<prec> ([(y, x)] \<bullet> P')"
          by(rule_tac xvec="[y]" in inputAlpha) (auto simp add: calc_atm)
        hence PTrans: "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>M\<lparr>([(x, y)] \<bullet> N)\<rparr> \<prec> ([(x, y)] \<bullet> P')"
          by(simp add: name_swap)
        have QTrans: "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>M''\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>([(x, y)] \<bullet> N')\<rangle> \<prec> ([(x, y)] \<bullet> Q')" by fact
        with \<open>A\<^sub>Q \<sharp>* x\<close> \<open>y \<sharp> A\<^sub>Q\<close> \<open>distinct xvec1\<close> \<open>distinct xvec2\<close> \<open>xvec1 \<sharp>* xvec2\<close> \<open>xvec1 \<sharp>* M''\<close> \<open>xvec2 \<sharp>* M''\<close>
             \<open>(xvec1@xvec2) \<sharp>* A\<^sub>Q\<close>
        have "A\<^sub>Q \<sharp>* ([(x, y)] \<bullet> Q')" using \<open>A\<^sub>Q \<sharp>* Q\<close>
          by(rule_tac outputFreshChainDerivative(2)) (assumption | simp)+

        from \<open>extractFrame(\<lparr>\<nu>x\<rparr>Q) = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>\<close> have FrxQ: "\<lparr>\<nu>x\<rparr>(extractFrame Q) = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" by simp
        then obtain z A\<^sub>Q' where A: "A\<^sub>Q = z#A\<^sub>Q'" by(case_tac A\<^sub>Q) auto
        with \<open>A\<^sub>Q \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q \<sharp>* P\<close> \<open>A\<^sub>Q \<sharp>* P'\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<^sub>P\<close> \<open>A\<^sub>Q \<sharp>* Q\<close> \<open>(xvec1@xvec2) \<sharp>* A\<^sub>Q\<close> \<open>A\<^sub>Q \<sharp>* M''\<close> \<open>A\<^sub>Q \<sharp>* ([(x, y)] \<bullet> Q')\<close> \<open>y \<sharp> A\<^sub>Q\<close> \<open>A\<^sub>Q \<sharp>* N\<close>
        have "A\<^sub>Q' \<sharp>* \<Psi>" and "A\<^sub>Q' \<sharp>* P" and "A\<^sub>Q' \<sharp>* \<Psi>\<^sub>P" and "A\<^sub>Q' \<sharp>* Q"
          and "z \<sharp> \<Psi>" and "z \<sharp> P" and "z \<sharp> P'" and "z \<sharp> \<Psi>\<^sub>P" and "z \<sharp> Q" and "z \<sharp> xvec1" and "z \<sharp> xvec2"
          and "z \<sharp> M''" and "z \<sharp> ([(x, y)] \<bullet> Q')" and "A\<^sub>Q' \<sharp>* M''" and "z \<noteq> y" and "z \<sharp> (xvec1@xvec2)"
          by auto
        from A \<open>A\<^sub>P \<sharp>* A\<^sub>Q\<close> have "A\<^sub>P \<sharp>* A\<^sub>Q'" and "z \<sharp> A\<^sub>P" by simp+
        from A \<open>A\<^sub>Q \<sharp>* x\<close> have "x \<noteq> z" and "x \<sharp> A\<^sub>Q'" by simp+

        from \<open>distinct A\<^sub>Q\<close> A have "z \<sharp> A\<^sub>Q'" 
          by(induct A\<^sub>Q') (auto simp add: fresh_list_nil fresh_list_cons)
        from PTrans \<open>x \<sharp> P\<close> \<open>z \<sharp> P\<close> \<open>x \<noteq> z\<close> have "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>M\<lparr>([(x, z)] \<bullet> [(x, y)] \<bullet> N)\<rparr> \<prec> ([(x, z)] \<bullet> [(x, y)] \<bullet> P')"
          by(rule_tac xvec="[x]" in inputAlpha) (auto simp add: calc_atm)
        moreover note FrP 
        moreover from QTrans have "([(x, z)] \<bullet> (\<Psi> \<otimes> \<Psi>\<^sub>P)) \<rhd> ([(x, z)] \<bullet> Q) \<longmapsto>([(x, z)] \<bullet> (M''\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>([(x, y)] \<bullet> N')\<rangle> \<prec> ([(x, y)] \<bullet> Q')))" 
          by(rule semantics.eqvt)
        with \<open>x \<sharp> \<Psi>\<close> \<open>z \<sharp> \<Psi>\<close> \<open>x \<sharp> \<Psi>\<^sub>P\<close> \<open>z \<sharp> \<Psi>\<^sub>P\<close> \<open>x \<sharp> M''\<close> \<open>z \<sharp> M''\<close> \<open>x \<sharp> xvec1\<close> \<open>x \<sharp> xvec2\<close> \<open>z \<sharp> xvec1\<close> \<open>z \<sharp> xvec2\<close>
        have "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> ([(x, z)] \<bullet> Q) \<longmapsto>M''\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>([(x, z)] \<bullet> [(x, y)] \<bullet> N')\<rangle> \<prec> ([(x, z)] \<bullet> [(x, y)] \<bullet> Q')" 
          by(simp add: eqvts)
        moreover from A \<open>A\<^sub>Q \<sharp>* x\<close> FrxQ have "extractFrame([(x, z)] \<bullet> Q) = \<langle>A\<^sub>Q', \<Psi>\<^sub>Q\<rangle>"
          by(clarsimp simp add: alpha' eqvts frame.inject fresh_list_cons name_swap)
        moreover from \<open>A\<^sub>P \<sharp>* Q\<close> have "([(x, z)] \<bullet> A\<^sub>P) \<sharp>* ([(x, z)] \<bullet> Q)"
          by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
        with \<open>A\<^sub>P \<sharp>* x\<close> \<open>z \<sharp> A\<^sub>P\<close> have "A\<^sub>P \<sharp>* ([(x, z)] \<bullet> Q)" by simp
        moreover from \<open>A\<^sub>Q' \<sharp>* Q\<close> have "([(x, z)] \<bullet> A\<^sub>Q') \<sharp>* ([(x, z)] \<bullet> Q)"
          by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
        with \<open>x \<sharp> A\<^sub>Q'\<close> \<open>z \<sharp> A\<^sub>Q'\<close> have "A\<^sub>Q' \<sharp>* ([(x, z)] \<bullet> Q)" by simp
        ultimately have "\<Psi> \<rhd> (P \<parallel> ([(x, z)] \<bullet> Q)) \<longmapsto>\<tau> \<prec> \<lparr>\<nu>*(xvec1@xvec2)\<rparr>(([(x, z)] \<bullet> [(x, y)] \<bullet> P') \<parallel> ([(x, z)] \<bullet> [(x, y)] \<bullet> Q'))"
          using MeqM' \<open>M'=M''\<close> \<open>N=N'\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* P\<close>  \<open>A\<^sub>P \<sharp>* A\<^sub>Q'\<close> \<open>A\<^sub>Q' \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q' \<sharp>* P\<close> \<open>(xvec1@xvec2) \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* M\<close> \<open>A\<^sub>Q' \<sharp>* M''\<close>
          by(rule_tac Comm1) (assumption | simp)+
        with\<open>z \<sharp> \<Psi>\<close> have "\<Psi> \<rhd> \<lparr>\<nu>z\<rparr>(P \<parallel> ([(x, z)] \<bullet> Q)) \<longmapsto>\<tau> \<prec> \<lparr>\<nu>z\<rparr>(\<lparr>\<nu>*(xvec1@xvec2)\<rparr>(([(x, z)] \<bullet> [(x, y)] \<bullet> P') \<parallel> ([(x, z)] \<bullet> [(x, y)] \<bullet> Q')))"
          by(rule_tac Scope) auto
        moreover from \<open>x \<sharp> P\<close> \<open>z \<sharp> P\<close> \<open>z \<sharp> Q\<close> have "\<lparr>\<nu>z\<rparr>(P \<parallel> ([(x, z)] \<bullet> Q)) = \<lparr>\<nu>x\<rparr>([(x, z)] \<bullet> (P \<parallel> ([(x, z)] \<bullet> Q)))"
          by(subst alphaRes[of x]) (auto simp add: calc_atm fresh_left name_swap)
        with \<open>x \<sharp> P\<close> \<open>z \<sharp> P\<close> have "\<lparr>\<nu>z\<rparr>(P \<parallel> ([(x, z)] \<bullet> Q)) = \<lparr>\<nu>x\<rparr>(P \<parallel> Q)"
          by(simp add: eqvts)
        moreover from \<open>z \<noteq> y\<close> \<open>x \<noteq> z\<close> \<open>z \<sharp> P'\<close> \<open>z \<sharp> [(x, y)] \<bullet> Q'\<close> have "\<lparr>\<nu>z\<rparr>(\<lparr>\<nu>*(xvec1@xvec2)\<rparr>(([(x, z)] \<bullet> [(x, y)] \<bullet> P') \<parallel> ([(x, z)] \<bullet> [(x, y)] \<bullet> Q'))) = \<lparr>\<nu>x\<rparr>([(x, z)] \<bullet> (\<lparr>\<nu>*(xvec1@xvec2)\<rparr>(([(x, z)] \<bullet> [(x, y)] \<bullet> P') \<parallel> ([(x, z)] \<bullet> [(x, y)] \<bullet> Q'))))"
          by(subst alphaRes[of x]) (auto simp add: resChainFresh fresh_left calc_atm name_swap)
        with \<open>x \<sharp> xvec1\<close> \<open>x \<sharp> xvec2\<close> \<open>z \<sharp> xvec1\<close> \<open>z \<sharp> xvec2\<close> have "\<lparr>\<nu>z\<rparr>(\<lparr>\<nu>*(xvec1@xvec2)\<rparr>(([(x, z)] \<bullet> [(x, y)] \<bullet> P') \<parallel> ([(x, z)] \<bullet> [(x, y)] \<bullet> Q'))) = \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*(xvec1@xvec2)\<rparr>(([(x, y)] \<bullet> P') \<parallel> ([(x, y)] \<bullet> Q')))"
          by(simp add: eqvts)
        moreover from \<open>x \<sharp> P'\<close> \<open>x \<sharp> Q'\<close> \<open>x \<sharp> xvec1\<close> \<open>x \<sharp> xvec2\<close> \<open>y \<sharp> xvec1\<close> \<open>y \<sharp> xvec2\<close>
          have "\<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*(xvec1@xvec2)\<rparr>(([(x, y)] \<bullet> P') \<parallel> ([(x, y)] \<bullet> Q'))) =  \<lparr>\<nu>y\<rparr>(\<lparr>\<nu>*(xvec1@xvec2)\<rparr>(P' \<parallel> Q'))"
          by(subst alphaRes[of y]) (auto simp add: resChainFresh calc_atm eqvts fresh_left name_swap)
        ultimately have "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(P \<parallel> Q) \<longmapsto>\<tau> \<prec> \<lparr>\<nu>y\<rparr>(\<lparr>\<nu>*(xvec1@xvec2)\<rparr>(P' \<parallel> Q'))"
          by simp
        moreover from \<open>y \<sharp> \<Psi>\<close> \<open>(xvec1@xvec2) \<sharp>* \<Psi>\<close> \<open>xvec=xvec1@y#xvec2\<close>
        have "(\<Psi>, \<lparr>\<nu>y\<rparr>(\<lparr>\<nu>*(xvec1@xvec2)\<rparr>(P' \<parallel> Q')), \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q')) \<in> Rel"
          by(force intro: C3 simp add: resChainAppend)
        ultimately show ?case by blast
      next
        case(cRes Q')   
        have QTrans: "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>M'\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'" by fact
        with \<open>A\<^sub>Q \<sharp>* Q\<close> \<open>A\<^sub>Q \<sharp>* xvec\<close> \<open>xvec \<sharp>* M'\<close> \<open>distinct xvec\<close> have "A\<^sub>Q \<sharp>* Q'"
          by(force dest: outputFreshChainDerivative)
        
        with \<open>extractFrame(\<lparr>\<nu>x\<rparr>Q) = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>\<close> have FrxQ: "\<lparr>\<nu>x\<rparr>(extractFrame Q) = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" by simp
        then obtain y A\<^sub>Q' where A: "A\<^sub>Q = y#A\<^sub>Q'" by(case_tac A\<^sub>Q) auto
        with \<open>A\<^sub>Q \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q \<sharp>* P\<close> \<open>A\<^sub>Q \<sharp>* P'\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<^sub>P\<close> \<open>A\<^sub>Q \<sharp>* Q\<close> \<open>A\<^sub>Q \<sharp>* xvec\<close> \<open>A\<^sub>Q \<sharp>* M'\<close> \<open>A\<^sub>Q \<sharp>* Q'\<close>
        have "A\<^sub>Q' \<sharp>* \<Psi>" and "A\<^sub>Q' \<sharp>* P" and "A\<^sub>Q' \<sharp>* \<Psi>\<^sub>P" and "A\<^sub>Q' \<sharp>* Q" and "A\<^sub>Q \<sharp>* xvec" and "A\<^sub>Q \<sharp>* Q'"
          and "y \<sharp> \<Psi>" and "y \<sharp> P" and "y \<sharp> P'" and "y \<sharp> \<Psi>\<^sub>P" and "y \<sharp> Q" and "y \<sharp> xvec" and "y \<sharp> M'" and "y \<sharp> Q'"
          and "A\<^sub>Q' \<sharp>* M'"
          by(simp)+
        from A \<open>A\<^sub>P \<sharp>* A\<^sub>Q\<close> have "A\<^sub>P \<sharp>* A\<^sub>Q'" and "y \<sharp> A\<^sub>P" by(simp add: fresh_star_list_cons)+
        from A \<open>A\<^sub>Q \<sharp>* x\<close> have "x \<noteq> y" and "x \<sharp> A\<^sub>Q'" by(simp add: fresh_list_cons)+
        
        with A \<open>distinct A\<^sub>Q\<close> have "y \<sharp> A\<^sub>Q'" 
          by(induct A\<^sub>Q') (auto simp add: fresh_list_nil fresh_list_cons)

        from \<open>x \<sharp> P\<close> \<open>y \<sharp> P\<close> \<open>x \<noteq> y\<close> \<open>\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>M\<lparr>N\<rparr> \<prec> P'\<close>
        have "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>M\<lparr>([(y, x)] \<bullet> N)\<rparr> \<prec> [(y, x)] \<bullet> P'"
          by(rule_tac xvec="[y]" in inputAlpha) (auto simp add: calc_atm)
        hence "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>M\<lparr>([(x, y)] \<bullet> N)\<rparr> \<prec> [(x, y)] \<bullet> P'"
          by(simp add: name_swap)
        moreover note FrP
        moreover from  \<open>\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>M'\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'\<close> have "([(x, y)] \<bullet> (\<Psi> \<otimes> \<Psi>\<^sub>P)) \<rhd> ([(x, y)] \<bullet> Q) \<longmapsto>([(x, y)] \<bullet> (M'\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'))" 
          by(rule semantics.eqvt)
        with \<open>x \<sharp> \<Psi>\<close> \<open>y \<sharp> \<Psi>\<close> \<open>x \<sharp> \<Psi>\<^sub>P\<close> \<open>y \<sharp> \<Psi>\<^sub>P\<close> \<open>x \<sharp> M'\<close> \<open>y \<sharp> M'\<close> \<open>x \<sharp> xvec\<close> \<open>y \<sharp> xvec\<close>
        have "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> ([(x, y)] \<bullet> Q) \<longmapsto>M'\<lparr>\<nu>*xvec\<rparr>\<langle>([(x, y)] \<bullet> N)\<rangle> \<prec> ([(x, y)] \<bullet> Q')" 
          by(simp add: eqvts)
        moreover from A \<open>A\<^sub>Q \<sharp>* x\<close> FrxQ have FrQ: "extractFrame([(x, y)] \<bullet> Q) = \<langle>A\<^sub>Q', \<Psi>\<^sub>Q\<rangle>"
          by(clarsimp simp add: alpha' eqvts frame.inject fresh_list_cons name_swap)
        moreover from \<open>A\<^sub>P \<sharp>* Q\<close> have "([(x, y)] \<bullet> A\<^sub>P) \<sharp>* ([(x, y)] \<bullet> Q)" by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
        with \<open>A\<^sub>P \<sharp>* x\<close> \<open>y \<sharp> A\<^sub>P\<close> have "A\<^sub>P \<sharp>* ([(x, y)] \<bullet> Q)" by simp
        moreover from \<open>A\<^sub>Q' \<sharp>* Q\<close> have "([(x, y)] \<bullet> A\<^sub>Q') \<sharp>* ([(x, y)] \<bullet> Q)" by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
        with \<open>x \<sharp> A\<^sub>Q'\<close> \<open>y \<sharp> A\<^sub>Q'\<close> have "A\<^sub>Q' \<sharp>* ([(x, y)] \<bullet> Q)" by simp
        ultimately have "\<Psi> \<rhd> (P \<parallel> ([(x, y)] \<bullet> Q)) \<longmapsto>\<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>([(x, y)] \<bullet> P') \<parallel> ([(x, y)] \<bullet> Q')"
          using MeqM' \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* P\<close>  \<open>A\<^sub>P \<sharp>* A\<^sub>Q'\<close> \<open>A\<^sub>Q' \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q' \<sharp>* P\<close> \<open>xvec \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* M\<close> \<open>A\<^sub>Q' \<sharp>* M'\<close>
          by(rule_tac Comm1) (assumption | simp)+
        with\<open>y \<sharp> \<Psi>\<close> have "\<Psi> \<rhd> \<lparr>\<nu>y\<rparr>(P \<parallel> ([(x, y)] \<bullet> Q)) \<longmapsto>\<tau> \<prec> \<lparr>\<nu>y\<rparr>(\<lparr>\<nu>*xvec\<rparr>(([(x, y)] \<bullet> P') \<parallel> ([(x, y)] \<bullet> Q')))"
          by(rule_tac Scope) auto
        moreover from \<open>x \<sharp> P\<close> \<open>y \<sharp> P\<close> \<open>y \<sharp> Q\<close> have "\<lparr>\<nu>y\<rparr>(P \<parallel> ([(x, y)] \<bullet> Q)) = \<lparr>\<nu>x\<rparr>([(x, y)] \<bullet> (P \<parallel> ([(x, y)] \<bullet> Q)))"
          by(subst alphaRes[of x]) (auto simp add: calc_atm fresh_left name_swap)
        with \<open>x \<sharp> P\<close> \<open>y \<sharp> P\<close> have "\<lparr>\<nu>y\<rparr>(P \<parallel> ([(x, y)] \<bullet> Q)) = \<lparr>\<nu>x\<rparr>(P \<parallel> Q)"
          by(simp add: eqvts)
        moreover from \<open>y \<sharp> P'\<close> \<open>y \<sharp> Q'\<close> \<open>x \<sharp> xvec\<close> \<open>y \<sharp> xvec\<close> have "\<lparr>\<nu>y\<rparr>(\<lparr>\<nu>*xvec\<rparr>(([(x, y)] \<bullet> P') \<parallel> ([(x, y)] \<bullet> Q'))) =  \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q'))"
          by(subst alphaRes[of y]) (auto simp add: resChainFresh calc_atm eqvts fresh_left name_swap)
        ultimately have "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(P \<parallel> Q) \<longmapsto>\<tau> \<prec> \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q'))"
          by simp
        moreover from \<open>x \<sharp> \<Psi>\<close> \<open>x \<sharp> P'\<close> \<open>xvec \<sharp>* \<Psi>\<close> have "(\<Psi>, \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q')), \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> \<lparr>\<nu>x\<rparr>Q')) \<in> Rel"
          by(rule C2)
        ultimately show ?case by blast
      qed
    next
      case(cComm2 \<Psi>\<^sub>Q M xvec N P' A\<^sub>P \<Psi>\<^sub>P K xQ' A\<^sub>Q)
      have QTrans: "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> \<lparr>\<nu>x\<rparr>Q \<longmapsto>K\<lparr>N\<rparr> \<prec> xQ'" and FrQ: "extractFrame(\<lparr>\<nu>x\<rparr>Q) = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" by fact+
      have PTrans: "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'" and FrP: "extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" by fact+
      from PTrans \<open>x \<sharp> P\<close> have "x \<sharp> N" and "x \<sharp> P'" using \<open>xvec \<sharp>* x\<close> \<open>xvec \<sharp>* M\<close> \<open>distinct xvec\<close> 
        by(force intro: outputFreshDerivative)+
      have "x \<sharp> \<lparr>\<nu>x\<rparr>Q" by(simp add: abs_fresh)
      with FrQ \<open>A\<^sub>Q \<sharp>* x\<close> have "x \<sharp> \<Psi>\<^sub>Q"
        by(drule_tac extractFrameFresh) auto
      from \<open>x \<sharp> P\<close> FrP \<open>A\<^sub>P \<sharp>* x\<close> have "x \<sharp> \<Psi>\<^sub>P"
        by(drule_tac extractFrameFresh) auto
      from \<open>A\<^sub>P \<sharp>* \<lparr>\<nu>x\<rparr>Q\<close> \<open>A\<^sub>P \<sharp>* x\<close> have "A\<^sub>P \<sharp>* Q" by simp
      from \<open>A\<^sub>Q \<sharp>* \<lparr>\<nu>x\<rparr>Q\<close> \<open>A\<^sub>Q \<sharp>* x\<close> have "A\<^sub>Q \<sharp>* Q" by simp
      from \<open>xvec \<sharp>* x\<close> \<open>xvec \<sharp>* \<lparr>\<nu>x\<rparr>Q\<close> have "xvec \<sharp>* Q" by simp

      from PTrans FrP \<open>distinct A\<^sub>P\<close> \<open>x \<sharp> P\<close> \<open>A\<^sub>Q \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<^sub>Q\<close> \<open>A\<^sub>P \<sharp>* x\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>Q\<close> \<open>A\<^sub>P \<sharp>* P\<close>  \<open>A\<^sub>P \<sharp>* M\<close> \<open>xvec \<sharp>* M\<close> \<open>distinct xvec\<close>
      obtain M' where "(\<Psi> \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>P \<turnstile> M \<leftrightarrow> M'" and "x \<sharp> M'" and "A\<^sub>Q \<sharp>* M'"
        by(rule_tac B="x#A\<^sub>Q" in obtainPrefix) (assumption | force simp add: fresh_star_list_cons)+
      hence MeqM': "\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q \<turnstile> M \<leftrightarrow> M'"
        by(metis statEqEnt Associativity Commutativity Composition)
      with \<open>\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q \<turnstile> M \<leftrightarrow> K\<close> have "\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q \<turnstile> K \<leftrightarrow> M'"
        by(blast intro: chanEqTrans chanEqSym)
      hence "(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>Q \<turnstile> K \<leftrightarrow> M'"
        by(metis statEqEnt Associativity Commutativity Composition)
      with QTrans FrQ \<open>distinct A\<^sub>Q\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<^sub>P\<close> \<open>A\<^sub>Q \<sharp>* (\<lparr>\<nu>x\<rparr>Q)\<close> \<open>A\<^sub>Q \<sharp>* K\<close> \<open>A\<^sub>Q \<sharp>* M'\<close>
      have "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> \<lparr>\<nu>x\<rparr>Q \<longmapsto>M'\<lparr>N\<rparr> \<prec> xQ'" by(force intro: inputRenameSubject)

      moreover from \<open>x \<sharp> \<Psi>\<close> \<open>x \<sharp> \<Psi>\<^sub>P\<close> have "x \<sharp> \<Psi> \<otimes> \<Psi>\<^sub>P" by force
      moreover note \<open>x \<sharp> M'\<close> \<open>x \<sharp> N\<close> 
      moreover from QTrans \<open>x \<sharp> N\<close> have "x \<sharp> xQ'" by(force dest: inputFreshDerivative simp add: abs_fresh)
      ultimately show ?case
      proof(induct rule: resInputCases)
        case(cRes Q')   
        have QTrans: "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>M'\<lparr>N\<rparr> \<prec> Q'" by fact
        with \<open>A\<^sub>Q \<sharp>* Q\<close> \<open>A\<^sub>Q \<sharp>* N\<close> have "A\<^sub>Q \<sharp>* Q'"
          by(rule_tac inputFreshChainDerivative)

        with \<open>extractFrame(\<lparr>\<nu>x\<rparr>Q) = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>\<close> have FrxQ: "\<lparr>\<nu>x\<rparr>(extractFrame Q) = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" by simp
        then obtain y A\<^sub>Q' where A: "A\<^sub>Q = y#A\<^sub>Q'" by(case_tac A\<^sub>Q) auto
        with \<open>A\<^sub>Q \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q \<sharp>* P\<close> \<open>A\<^sub>Q \<sharp>* P'\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<^sub>P\<close> \<open>A\<^sub>Q \<sharp>* Q\<close> \<open>A\<^sub>Q \<sharp>* xvec\<close> \<open>A\<^sub>Q \<sharp>* M'\<close> \<open>A\<^sub>Q \<sharp>* Q'\<close> \<open>A\<^sub>Q \<sharp>* N\<close>
        have "A\<^sub>Q' \<sharp>* \<Psi>" and "A\<^sub>Q' \<sharp>* P" and "A\<^sub>Q' \<sharp>* \<Psi>\<^sub>P" and "A\<^sub>Q' \<sharp>* Q" and "A\<^sub>Q \<sharp>* xvec" and "A\<^sub>Q \<sharp>* Q'"
          and "y \<sharp> \<Psi>" and "y \<sharp> P" and "y \<sharp> P'" and "y \<sharp> \<Psi>\<^sub>P" and "y \<sharp> Q" and "y \<sharp> xvec" and "y \<sharp> M'" and "y \<sharp> Q'" and "y \<sharp> N"
          and "A\<^sub>Q' \<sharp>* M'"
          by(simp)+
        from A \<open>A\<^sub>P \<sharp>* A\<^sub>Q\<close> have "A\<^sub>P \<sharp>* A\<^sub>Q'" and "y \<sharp> A\<^sub>P" by(simp add: fresh_star_list_cons)+
        from A \<open>A\<^sub>Q \<sharp>* x\<close> have "x \<noteq> y" and "x \<sharp> A\<^sub>Q'" by(simp add: fresh_list_cons)+
        
        with A \<open>distinct A\<^sub>Q\<close> have "y \<sharp> A\<^sub>Q'" 
          by(induct A\<^sub>Q') (auto simp add: fresh_list_nil fresh_list_cons)

        note PTrans FrP
        moreover from  \<open>\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>M'\<lparr>N\<rparr> \<prec> Q'\<close> have "([(x, y)] \<bullet> (\<Psi> \<otimes> \<Psi>\<^sub>P)) \<rhd> ([(x, y)] \<bullet> Q) \<longmapsto>([(x, y)] \<bullet> (M'\<lparr>N\<rparr> \<prec> Q'))" 
          by(rule semantics.eqvt)
        with \<open>x \<sharp> \<Psi>\<close> \<open>y \<sharp> \<Psi>\<close> \<open>x \<sharp> \<Psi>\<^sub>P\<close> \<open>y \<sharp> \<Psi>\<^sub>P\<close> \<open>x \<sharp> M'\<close> \<open>y \<sharp> M'\<close> \<open>x \<sharp> N\<close> \<open>y \<sharp> N\<close>
        have "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> ([(x, y)] \<bullet> Q) \<longmapsto>M'\<lparr>N\<rparr> \<prec> ([(x, y)] \<bullet> Q')" 
          by(simp add: eqvts)
        moreover from A \<open>A\<^sub>Q \<sharp>* x\<close> FrxQ have FrQ: "extractFrame([(x, y)] \<bullet> Q) = \<langle>A\<^sub>Q', \<Psi>\<^sub>Q\<rangle>" and "y \<sharp> extractFrame Q"
          by(clarsimp simp add: alpha' eqvts frame.inject fresh_list_cons name_swap)+
        moreover from \<open>A\<^sub>P \<sharp>* Q\<close> have "([(x, y)] \<bullet> A\<^sub>P) \<sharp>* ([(x, y)] \<bullet> Q)" by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
        with \<open>A\<^sub>P \<sharp>* x\<close> \<open>y \<sharp> A\<^sub>P\<close> have "A\<^sub>P \<sharp>* ([(x, y)] \<bullet> Q)" by simp
        moreover from \<open>A\<^sub>Q' \<sharp>* Q\<close> have "([(x, y)] \<bullet> A\<^sub>Q') \<sharp>* ([(x, y)] \<bullet> Q)" by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
        with \<open>x \<sharp> A\<^sub>Q'\<close> \<open>y \<sharp> A\<^sub>Q'\<close> have "A\<^sub>Q' \<sharp>* ([(x, y)] \<bullet> Q)" by simp
        moreover from \<open>xvec \<sharp>* Q\<close> have "([(x, y)] \<bullet> xvec) \<sharp>* ([(x, y)] \<bullet> Q)" by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
        with \<open>xvec \<sharp>* x\<close> \<open>y \<sharp> xvec\<close> have "xvec \<sharp>* ([(x, y)] \<bullet> Q)" by simp
        ultimately have "\<Psi> \<rhd> (P \<parallel> ([(x, y)] \<bullet> Q)) \<longmapsto>\<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> ([(x, y)] \<bullet> Q'))"
          using MeqM' \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* P\<close>  \<open>A\<^sub>P \<sharp>* A\<^sub>Q'\<close> \<open>A\<^sub>Q' \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q' \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* M\<close> \<open>A\<^sub>Q' \<sharp>* M'\<close>
          by(rule_tac Comm2) (assumption | simp)+
        with\<open>y \<sharp> \<Psi>\<close> have "\<Psi> \<rhd> \<lparr>\<nu>y\<rparr>(P \<parallel> ([(x, y)] \<bullet> Q)) \<longmapsto>\<tau> \<prec> \<lparr>\<nu>y\<rparr>(\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> ([(x, y)] \<bullet> Q')))"
          by(rule_tac Scope) auto
        moreover from \<open>x \<sharp> P\<close> \<open>y \<sharp> P\<close> \<open>y \<sharp> Q\<close> have "\<lparr>\<nu>y\<rparr>(P \<parallel> ([(x, y)] \<bullet> Q)) = \<lparr>\<nu>x\<rparr>([(x, y)] \<bullet> (P \<parallel> ([(x, y)] \<bullet> Q)))"
          by(subst alphaRes[of x]) (auto simp add: calc_atm fresh_left name_swap)
        with \<open>x \<sharp> P\<close> \<open>y \<sharp> P\<close> have "\<lparr>\<nu>y\<rparr>(P \<parallel> ([(x, y)] \<bullet> Q)) = \<lparr>\<nu>x\<rparr>(P \<parallel> Q)"
          by(simp add: eqvts)
        moreover from \<open>x \<sharp> P'\<close> \<open>y \<sharp> P'\<close> \<open>y \<sharp> Q'\<close> \<open>xvec \<sharp>* x\<close> \<open>y \<sharp> xvec\<close> have "\<lparr>\<nu>y\<rparr>(\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> ([(x, y)] \<bullet> Q'))) =  \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q'))"
          by(subst alphaRes[of y]) (auto simp add: resChainFresh calc_atm eqvts fresh_left name_swap)
        ultimately have "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(P \<parallel> Q) \<longmapsto>\<tau> \<prec> \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q'))"
          by simp
        moreover from \<open>x \<sharp> \<Psi>\<close> \<open>x \<sharp> P'\<close> \<open>xvec \<sharp>* \<Psi>\<close> have "(\<Psi>, \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q')), \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> \<lparr>\<nu>x\<rparr>Q')) \<in> Rel"
          by(rule C2)
        ultimately show ?case by blast
      qed
    qed
  qed
qed

lemma scopeExtRight:
  fixes x   :: name
  and   P   :: "('a, 'b, 'c) psi"
  and   \<Psi>   :: 'b
  and   Q   :: "('a, 'b, 'c) psi"
  and   Rel :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"

  assumes "x \<sharp> P"
  and     "x \<sharp> \<Psi>"
  and     "eqvt Rel"
  and     C1: "\<And>\<Psi>' R. (\<Psi>, R, R) \<in> Rel"
  and     C2: "\<And>y \<Psi>' R S zvec. \<lbrakk>y \<sharp> \<Psi>'; y \<sharp> R; zvec \<sharp>* \<Psi>'\<rbrakk> \<Longrightarrow> (\<Psi>', \<lparr>\<nu>*zvec\<rparr>(R \<parallel> \<lparr>\<nu>y\<rparr>S), \<lparr>\<nu>y\<rparr>(\<lparr>\<nu>*zvec\<rparr>(R \<parallel> S))) \<in> Rel"

  shows "\<Psi> \<rhd> P \<parallel> \<lparr>\<nu>x\<rparr>Q \<leadsto>[Rel] \<lparr>\<nu>x\<rparr>(P \<parallel> Q)"
proof -
  note \<open>eqvt Rel\<close> \<open>x \<sharp> \<Psi>\<close>
  moreover from \<open>x \<sharp> P\<close> have "x \<sharp> P \<parallel> \<lparr>\<nu>x\<rparr>Q" by(simp add: abs_fresh)
  moreover from \<open>x \<sharp> P\<close> have "x \<sharp> \<lparr>\<nu>x\<rparr>(P \<parallel> Q)" by(simp add: abs_fresh)
  ultimately show ?thesis
  proof(induct rule: simIFresh[of _ _ _ _ _ "()"])
    case(cSim \<alpha> xPQ)
    from \<open>bn \<alpha> \<sharp>* (P \<parallel> \<lparr>\<nu>x\<rparr>Q)\<close> \<open>x \<sharp> \<alpha>\<close> have "bn \<alpha>  \<sharp>* P" and "bn \<alpha>  \<sharp>* Q" by simp+
    note \<open>\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(P \<parallel> Q) \<longmapsto>\<alpha> \<prec> xPQ\<close> \<open>x \<sharp> \<Psi>\<close> \<open>x \<sharp> \<alpha>\<close> \<open>x \<sharp> xPQ\<close> \<open>bn \<alpha> \<sharp>* \<Psi>\<close>
    moreover from \<open>bn \<alpha> \<sharp>* P\<close> \<open>bn \<alpha> \<sharp>* Q\<close> have "bn \<alpha> \<sharp>* (P \<parallel> Q)" by simp
    ultimately show ?case using \<open>bn \<alpha> \<sharp>* subject \<alpha>\<close> \<open>x \<sharp> \<alpha>\<close>
    proof(induct rule: resCases)
      case(cOpen M xvec1 xvec2 y N PQ)
      from \<open>x \<sharp> M\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N\<rangle>\<close> have "x \<sharp> xvec1" and "x \<noteq> y" and "x \<sharp> xvec2" and "x \<sharp> M" by simp+
      from \<open>xvec1 \<sharp>* (P \<parallel> Q)\<close> \<open>xvec2 \<sharp>* (P \<parallel> Q)\<close> \<open>y \<sharp> (P \<parallel> Q)\<close>
      have "(xvec1@xvec2) \<sharp>* P" and "(xvec1@xvec2) \<sharp>* Q" and "y \<sharp> P" and "y \<sharp> Q"
        by simp+
      from \<open>\<Psi> \<rhd> P \<parallel> Q \<longmapsto> M\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>([(x, y)] \<bullet> N)\<rangle> \<prec> ([(x, y)] \<bullet> PQ)\<close>
      have "([(x, y)] \<bullet> \<Psi>) \<rhd> ([(x, y)] \<bullet> (P \<parallel> Q)) \<longmapsto> ([(x, y)] \<bullet> (M\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>([(x, y)] \<bullet> N)\<rangle> \<prec> ([(x, y)] \<bullet> PQ)))"
        by(rule semantics.eqvt)
      with \<open>x \<sharp> \<Psi>\<close> \<open>y \<sharp> \<Psi>\<close> \<open>x \<sharp> P\<close> \<open>y \<sharp> P\<close> \<open>x \<sharp> M\<close> \<open>y \<sharp> M\<close> \<open>x \<sharp> xvec1\<close> \<open>x \<sharp> xvec2\<close> \<open>y \<sharp> xvec1\<close> \<open>y \<sharp> xvec2\<close>
      have "\<Psi> \<rhd> P \<parallel> ([(x, y)] \<bullet> Q) \<longmapsto> M\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>N\<rangle> \<prec> PQ"
        by(simp add: eqvts)
      moreover from \<open>xvec1 \<sharp>* \<Psi>\<close> \<open>xvec2 \<sharp>* \<Psi>\<close> have "(xvec1@xvec2) \<sharp>* \<Psi>" by simp
      moreover note \<open>(xvec1@xvec2) \<sharp>* P\<close>
      moreover from \<open>(xvec1@xvec2) \<sharp>* Q\<close> have "([(x, y)] \<bullet> (xvec1@xvec2)) \<sharp>* ([(x, y)] \<bullet> Q)"
        by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
      with \<open>x \<sharp> xvec1\<close> \<open>x \<sharp> xvec2\<close> \<open>y \<sharp> xvec1\<close> \<open>y \<sharp> xvec2\<close> have "(xvec1@xvec2) \<sharp>* ([(x, y)] \<bullet> Q)"
        by(auto simp add: eqvts)
      moreover from \<open>xvec1 \<sharp>* M\<close> \<open>xvec2 \<sharp>* M\<close> have "(xvec1@xvec2) \<sharp>* M" by simp
      ultimately show ?case
      proof(induct rule: parOutputCases[where C=y])
        case(cPar1 P' A\<^sub>Q \<Psi>\<^sub>Q)
        from \<open>y \<sharp> xvec1\<close> \<open>y \<sharp> xvec2\<close> have "y \<sharp> (xvec1@xvec2)" by(auto simp add: fresh_list_append)
        with \<open>\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>M\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>N\<rangle> \<prec> P'\<close> \<open>(xvec1@xvec2) \<sharp>* M\<close> \<open>y \<sharp> P\<close> 
             \<open>distinct xvec1\<close> \<open>distinct xvec2\<close> \<open>xvec1 \<sharp>* xvec2\<close> 
        have "y \<sharp> N" by(force intro: outputFreshDerivative)
        with \<open>y \<in> supp N\<close> have False by(simp add: fresh_def)
        thus ?case by simp
      next
        case(cPar2 Q' A\<^sub>P \<Psi>\<^sub>P)
        have FrP: "extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" by fact
        with \<open>y \<sharp> P\<close> \<open>A\<^sub>P \<sharp>* y\<close> have "y \<sharp> \<Psi>\<^sub>P" 
          apply(drule_tac extractFrameFresh)
          by(simp add: frameResChainFresh) (simp add: fresh_def name_list_supp)
        from \<open>\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> ([(x, y)] \<bullet> Q) \<longmapsto>M\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>N\<rangle> \<prec> Q'\<close> \<open>y \<in> supp N\<close> \<open>y \<sharp> \<Psi>\<close> \<open>y \<sharp> \<Psi>\<^sub>P\<close> \<open>y \<sharp> M\<close> \<open>y \<sharp> xvec1\<close> \<open>y \<sharp> xvec2\<close>
        have "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> \<lparr>\<nu>y\<rparr>(([(x, y)] \<bullet> Q)) \<longmapsto>M\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N\<rangle> \<prec> Q'" by(force intro: Open) 
        with \<open>y \<sharp> Q\<close> have "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> \<lparr>\<nu>x\<rparr>Q \<longmapsto>M\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N\<rangle> \<prec> Q'"
          by(simp add: alphaRes)
        moreover from \<open>A\<^sub>P \<sharp>* ([(x, y)] \<bullet> Q)\<close> have "A\<^sub>P \<sharp>* \<lparr>\<nu>y\<rparr>([(x, y)] \<bullet> Q)" by(auto simp add: fresh_star_def abs_fresh)
        with \<open>y \<sharp> Q\<close> have "A\<^sub>P \<sharp>* \<lparr>\<nu>x\<rparr>Q" by(simp add: alphaRes)
        ultimately have "\<Psi> \<rhd> P \<parallel> (\<lparr>\<nu>x\<rparr>Q) \<longmapsto>M\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N\<rangle> \<prec> (P \<parallel> Q')" 
          using FrP \<open>(xvec1@xvec2) \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* M\<close> \<open>y \<sharp> P\<close> \<open>A\<^sub>P \<sharp>* (xvec1@xvec2)\<close> \<open>A\<^sub>P \<sharp>* y\<close> \<open>A\<^sub>P \<sharp>* N\<close>
          by(rule_tac Par2) auto
        moreover have "(\<Psi>, P \<parallel> Q', P \<parallel> Q') \<in> Rel" by(rule C1)
        ultimately show ?case by blast
      qed
    next
      case(cRes PQ)
      from \<open>\<Psi> \<rhd> P \<parallel> Q \<longmapsto>\<alpha> \<prec> PQ\<close> \<open>bn \<alpha> \<sharp>* \<Psi>\<close>  \<open>bn \<alpha> \<sharp>* P\<close> \<open>bn \<alpha> \<sharp>* Q\<close> \<open>bn \<alpha> \<sharp>* subject \<alpha>\<close>
      show ?case
      proof(induct rule: parCases[where C=x])
        case(cPar1 P' A\<^sub>Q \<Psi>\<^sub>Q)
        note \<open>\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>\<alpha> \<prec> P'\<close>
        moreover with \<open>x \<sharp> P\<close> \<open>x \<sharp> \<alpha>\<close> \<open>bn \<alpha> \<sharp>* subject \<alpha>\<close> \<open>distinct(bn \<alpha>)\<close>
        have "x \<sharp> P'" by(force dest: freeFreshDerivative)
        with \<open>extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>\<close> have "extractFrame(\<lparr>\<nu>x\<rparr>Q) = \<langle>(x#A\<^sub>Q), \<Psi>\<^sub>Q\<rangle>"
          by simp
        moreover from \<open>bn \<alpha> \<sharp>* Q\<close> have "bn \<alpha> \<sharp>* (\<lparr>\<nu>x\<rparr>Q)" by(simp add: fresh_star_def abs_fresh)
        moreover from \<open>x \<sharp> \<Psi>\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<close> have "(x#A\<^sub>Q) \<sharp>* \<Psi>" by simp
        moreover from \<open>x \<sharp> P\<close> \<open>A\<^sub>Q \<sharp>* P\<close> have "(x#A\<^sub>Q) \<sharp>* P" by simp
        moreover from \<open>x \<sharp> \<alpha>\<close> \<open>A\<^sub>Q \<sharp>* \<alpha>\<close> have "(x#A\<^sub>Q) \<sharp>* \<alpha>" by simp
        ultimately have "\<Psi> \<rhd> P \<parallel> \<lparr>\<nu>x\<rparr>Q \<longmapsto>\<alpha> \<prec> (P' \<parallel> \<lparr>\<nu>x\<rparr>Q)"
          by(rule Par1)
        moreover from \<open>x \<sharp> P'\<close> \<open>x \<sharp> \<Psi>\<close> have "(\<Psi>, \<lparr>\<nu>*[]\<rparr>(P' \<parallel> (\<lparr>\<nu>x\<rparr>Q)), \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*[]\<rparr>(P' \<parallel> Q))) \<in> Rel"
          by(rule_tac C2) auto
        ultimately show ?case
          by force
      next
        case(cPar2 Q' A\<^sub>P \<Psi>\<^sub>P)
        have FrP: "extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" by fact
        with \<open>x \<sharp> P\<close> \<open>A\<^sub>P \<sharp>* x\<close> have "x \<sharp> \<Psi>\<^sub>P"
          apply(drule_tac extractFrameFresh)
          by(simp add: frameResChainFresh) (simp add: fresh_def name_list_supp)
        from \<open>\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>\<alpha> \<prec> Q'\<close> \<open>x \<sharp> \<Psi>\<close> \<open>x \<sharp> \<Psi>\<^sub>P\<close> \<open>x \<sharp> \<alpha>\<close>
        have "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> \<lparr>\<nu>x\<rparr>Q \<longmapsto>\<alpha> \<prec> \<lparr>\<nu>x\<rparr>Q'"
          by(rule_tac Scope) auto
        moreover note FrP \<open>bn \<alpha> \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<close>
        moreover from \<open>A\<^sub>P \<sharp>* Q\<close> have "A\<^sub>P \<sharp>* \<lparr>\<nu>x\<rparr>Q" by(simp add: fresh_star_def abs_fresh)
        ultimately have "\<Psi> \<rhd> P \<parallel> \<lparr>\<nu>x\<rparr>Q \<longmapsto>\<alpha> \<prec> (P \<parallel> \<lparr>\<nu>x\<rparr>Q')" using \<open>A\<^sub>P \<sharp>* \<alpha>\<close>
          by(rule Par2)
        moreover from \<open>x \<sharp> P\<close> \<open>x \<sharp> \<Psi>\<close> have "(\<Psi>, \<lparr>\<nu>*[]\<rparr>(P \<parallel> (\<lparr>\<nu>x\<rparr>Q')), \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*[]\<rparr>(P \<parallel> Q'))) \<in> Rel"
          by(rule_tac C2) auto
        ultimately show ?case
          by force
      next
        case(cComm1 \<Psi>\<^sub>Q M N P' A\<^sub>P \<Psi>\<^sub>P K xvec Q' A\<^sub>Q)
        have PTrans: "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>M\<lparr>N\<rparr> \<prec> P'" and FrP: "extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" by fact+
        have QTrans: "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'" and FrQ: "extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" by fact+
        from FrP \<open>x \<sharp> P\<close> have "x \<sharp> \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" by(drule_tac extractFrameFresh) simp
        with \<open>A\<^sub>P \<sharp>* x\<close> have "x \<sharp> \<Psi>\<^sub>P" by(simp add: frameResChainFresh) (simp add: fresh_def name_list_supp)
        from PTrans FrP \<open>distinct A\<^sub>P\<close> \<open>x \<sharp> P\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<^sub>Q\<close> \<open>A\<^sub>P \<sharp>* x\<close> \<open>A\<^sub>P \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* M\<close> \<open>A\<^sub>Q \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>Q\<close>
        obtain M' where MeqM': "(\<Psi> \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>P \<turnstile> M \<leftrightarrow> M'" and "x \<sharp> M'" and "A\<^sub>Q \<sharp>* M'"
          by(rule_tac B="x#A\<^sub>Q" in obtainPrefix) (assumption | force simp add: fresh_star_list_cons)+
        
        from MeqM' have MeqM': "\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q \<turnstile> M \<leftrightarrow> M'"
          by(metis statEqEnt Associativity Composition Commutativity)
        with \<open>\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q \<turnstile> M \<leftrightarrow> K\<close> have "\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q \<turnstile> K \<leftrightarrow> M'"
          by(blast intro: chanEqTrans chanEqSym)
        hence "(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>Q \<turnstile> K \<leftrightarrow> M'"
          by(metis statEqEnt Associativity Composition Commutativity)
        with QTrans FrQ \<open>distinct A\<^sub>Q\<close> have QTrans: "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>M'\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'" using \<open>A\<^sub>Q \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<^sub>P\<close> \<open>A\<^sub>Q \<sharp>* Q\<close> \<open>A\<^sub>Q \<sharp>* K\<close> \<open>A\<^sub>Q \<sharp>* M'\<close>
          by(rule_tac outputRenameSubject) (assumption | force)+
        show ?case
        proof(case_tac "x \<in> supp N")
          note PTrans FrP
          moreover assume "x \<in> supp N"
          hence "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> \<lparr>\<nu>x\<rparr>Q \<longmapsto>M'\<lparr>\<nu>*([]@(x#xvec))\<rparr>\<langle>N\<rangle> \<prec> Q'" using QTrans \<open>x \<sharp> \<Psi>\<close> \<open>x \<sharp> \<Psi>\<^sub>P\<close> \<open>x \<sharp> M'\<close> \<open>xvec \<sharp>* x\<close>
            by(rule_tac Open) (assumption | force simp add: fresh_list_nil)+
          hence QTrans: "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> \<lparr>\<nu>x\<rparr>Q \<longmapsto>M'\<lparr>\<nu>*(x#xvec)\<rparr>\<langle>N\<rangle> \<prec> Q'" by simp
          moreover from \<open>extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>\<close> have "extractFrame(\<lparr>\<nu>x\<rparr>Q) = \<langle>(x#A\<^sub>Q), \<Psi>\<^sub>Q\<rangle>" 
            by simp
          moreover note MeqM' \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* P\<close>
          moreover from  \<open>A\<^sub>P \<sharp>* Q\<close> have "A\<^sub>P \<sharp>* (\<lparr>\<nu>x\<rparr>Q)" by(simp add: fresh_star_def abs_fresh)
          moreover from \<open>A\<^sub>P \<sharp>* A\<^sub>Q\<close> \<open>A\<^sub>P \<sharp>* x\<close> have "A\<^sub>P \<sharp>* (x#A\<^sub>Q)" 
            by(simp add: fresh_star_def fresh_list_cons) (auto simp add: fresh_def name_list_supp)
          moreover from \<open>x \<sharp> \<Psi>\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<close> have "(x#A\<^sub>Q) \<sharp>* \<Psi>" by simp
          moreover from \<open>x \<sharp> P\<close> \<open>A\<^sub>Q \<sharp>* P\<close> have "(x#A\<^sub>Q) \<sharp>* P" by simp
          moreover from \<open>x \<sharp> M'\<close> \<open>A\<^sub>Q \<sharp>* M'\<close> have "(x#A\<^sub>Q) \<sharp>* M'" by simp
          moreover from \<open>A\<^sub>Q \<sharp>* Q\<close> have "(x#A\<^sub>Q) \<sharp>* (\<lparr>\<nu>x\<rparr>Q)" by(simp add: fresh_star_def abs_fresh)
          moreover from \<open>x \<sharp> P\<close> \<open>xvec \<sharp>* P\<close> have "(x#xvec) \<sharp>* P" by(simp)
          ultimately have "\<Psi> \<rhd> P \<parallel> \<lparr>\<nu>x\<rparr>Q \<longmapsto>\<tau> \<prec> \<lparr>\<nu>*(x#xvec)\<rparr>(P' \<parallel> Q')" using \<open>A\<^sub>P \<sharp>* M\<close>
            by(rule_tac Comm1) (assumption | simp)+
          moreover have "(\<Psi>, \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q')), \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q'))) \<in> Rel" by(rule C1)
          ultimately show ?case by force
        next
          note PTrans FrP
          moreover assume "x \<notin> supp N"
          hence "x \<sharp> N" by(simp add: fresh_def)
          with QTrans \<open>x \<sharp> \<Psi>\<close> \<open>x \<sharp> \<Psi>\<^sub>P\<close> \<open>x \<sharp> M'\<close> \<open>xvec \<sharp>* x\<close>
          have QTrans: "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> \<lparr>\<nu>x\<rparr>Q \<longmapsto>M'\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> \<lparr>\<nu>x\<rparr>Q'"
            by(rule_tac Scope) (assumption | force)+
          moreover from PTrans \<open>x \<sharp> P\<close> \<open>x \<sharp> N\<close> have "x \<sharp> P'" by(rule inputFreshDerivative)
          with \<open>extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>\<close> have "extractFrame(\<lparr>\<nu>x\<rparr>Q) = \<langle>(x#A\<^sub>Q), \<Psi>\<^sub>Q\<rangle>"
            by simp
          moreover note MeqM' \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* P\<close>
          moreover from  \<open>A\<^sub>P \<sharp>* Q\<close> have "A\<^sub>P \<sharp>* (\<lparr>\<nu>x\<rparr>Q)" by(simp add: fresh_star_def abs_fresh)
          moreover from \<open>A\<^sub>P \<sharp>* A\<^sub>Q\<close> \<open>A\<^sub>P \<sharp>* x\<close> have "A\<^sub>P \<sharp>* (x#A\<^sub>Q)" 
            by(simp add: fresh_star_def fresh_list_cons) (auto simp add: fresh_def name_list_supp)
          moreover from \<open>x \<sharp> \<Psi>\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<close> have "(x#A\<^sub>Q) \<sharp>* \<Psi>" by simp
          moreover from \<open>x \<sharp> P\<close> \<open>A\<^sub>Q \<sharp>* P\<close> have "(x#A\<^sub>Q) \<sharp>* P" by simp
          moreover from \<open>x \<sharp> M'\<close> \<open>A\<^sub>Q \<sharp>* M'\<close> have "(x#A\<^sub>Q) \<sharp>* M'" by simp
          moreover from \<open>A\<^sub>Q \<sharp>* Q\<close> have "(x#A\<^sub>Q) \<sharp>* (\<lparr>\<nu>x\<rparr>Q)" by(simp add: fresh_star_def abs_fresh)
          moreover from \<open>x \<sharp> P\<close> \<open>xvec \<sharp>* P\<close> have "(x#xvec) \<sharp>* P" by(simp)
          ultimately have "\<Psi> \<rhd> P \<parallel> \<lparr>\<nu>x\<rparr>Q \<longmapsto>\<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> \<lparr>\<nu>x\<rparr>Q')" using \<open>A\<^sub>P \<sharp>* M\<close>
            by(rule_tac Comm1) (assumption | simp)+
          moreover from \<open>x \<sharp> \<Psi>\<close> \<open>x \<sharp> P'\<close> \<open>xvec \<sharp>* \<Psi>\<close> have "(\<Psi>, \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> \<lparr>\<nu>x\<rparr>Q'), \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q'))) \<in> Rel" by(rule C2)
          ultimately show ?case by blast
        qed
      next
        case(cComm2 \<Psi>\<^sub>Q M xvec N P' A\<^sub>P \<Psi>\<^sub>P K Q' A\<^sub>Q)
        have PTrans: "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'" and FrP: "extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" by fact+
        have QTrans: "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>K\<lparr>N\<rparr> \<prec> Q'" and FrQ: "extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" by fact+
        from FrP \<open>x \<sharp> P\<close> have "x \<sharp> \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" by(drule_tac extractFrameFresh) simp
        with \<open>A\<^sub>P \<sharp>* x\<close> have "x \<sharp> \<Psi>\<^sub>P" by(simp add: frameResChainFresh) (simp add: fresh_def name_list_supp)
        from PTrans FrP \<open>distinct A\<^sub>P\<close> \<open>x \<sharp> P\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<^sub>Q\<close> \<open>A\<^sub>P \<sharp>* x\<close> \<open>A\<^sub>P \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* M\<close> \<open>A\<^sub>Q \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>Q\<close> \<open>xvec \<sharp>* M\<close> \<open>distinct xvec\<close>
        obtain M' where MeqM': "(\<Psi> \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>P \<turnstile> M \<leftrightarrow> M'" and "x \<sharp> M'" and "A\<^sub>Q \<sharp>* M'"
          by(rule_tac B="x#A\<^sub>Q" in obtainPrefix) (assumption | force simp add: fresh_star_list_cons)+
        
        from MeqM' have MeqM': "\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q \<turnstile> M \<leftrightarrow> M'"
          by(metis statEqEnt Associativity Commutativity Composition)
        with \<open>\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q \<turnstile> M \<leftrightarrow> K\<close> have "\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q \<turnstile> K \<leftrightarrow> M'"
          by(blast intro: chanEqTrans chanEqSym)
        hence "(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>Q \<turnstile> K \<leftrightarrow> M'"
          by(metis statEqEnt Associativity Commutativity Composition)
        with QTrans FrQ \<open>distinct A\<^sub>Q\<close> have QTrans: "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>M'\<lparr>N\<rparr> \<prec> Q'" using \<open>A\<^sub>Q \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<^sub>P\<close> \<open>A\<^sub>Q \<sharp>* Q\<close> \<open>A\<^sub>Q \<sharp>* K\<close> \<open>A\<^sub>Q \<sharp>* M'\<close>
          by(rule_tac inputRenameSubject) (assumption | force)+

        from PTrans \<open>x \<sharp> P\<close> \<open>xvec \<sharp>* x\<close> \<open>distinct xvec\<close> \<open>xvec \<sharp>* M\<close>
        have "x \<sharp> N" and "x \<sharp> P'" by(force intro: outputFreshDerivative)+
        from QTrans \<open>x \<sharp> \<Psi>\<close>  \<open>x \<sharp> \<Psi>\<^sub>P\<close> \<open>x \<sharp> M'\<close> \<open>x \<sharp> N\<close> have QTrans: "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> \<lparr>\<nu>x\<rparr>Q \<longmapsto>M'\<lparr>N\<rparr> \<prec> \<lparr>\<nu>x\<rparr>Q'"
          by(rule_tac Scope) (assumption | force)+

        note PTrans FrP QTrans
        moreover with \<open>extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>\<close> have "extractFrame(\<lparr>\<nu>x\<rparr>Q) = \<langle>(x#A\<^sub>Q), \<Psi>\<^sub>Q\<rangle>"
          by simp
        moreover note MeqM' \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* P\<close>
        moreover from  \<open>A\<^sub>P \<sharp>* Q\<close> have "A\<^sub>P \<sharp>* (\<lparr>\<nu>x\<rparr>Q)" by(simp add: fresh_star_def abs_fresh)
        moreover from \<open>A\<^sub>P \<sharp>* A\<^sub>Q\<close> \<open>A\<^sub>P \<sharp>* x\<close> have "A\<^sub>P \<sharp>* (x#A\<^sub>Q)" 
          by(simp add: fresh_star_def fresh_list_cons) (auto simp add: fresh_def name_list_supp)
        moreover from \<open>x \<sharp> \<Psi>\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<close> have "(x#A\<^sub>Q) \<sharp>* \<Psi>" by simp
        moreover from \<open>x \<sharp> P\<close> \<open>A\<^sub>Q \<sharp>* P\<close> have "(x#A\<^sub>Q) \<sharp>* P" by simp
        moreover from \<open>x \<sharp> M'\<close> \<open>A\<^sub>Q \<sharp>* M'\<close> have "(x#A\<^sub>Q) \<sharp>* M'" by simp
        moreover from \<open>A\<^sub>Q \<sharp>* Q\<close> have "(x#A\<^sub>Q) \<sharp>* (\<lparr>\<nu>x\<rparr>Q)" by(simp add: fresh_star_def abs_fresh)
        moreover from \<open>xvec \<sharp>* Q\<close> have "(x#xvec) \<sharp>* (\<lparr>\<nu>x\<rparr>Q)" by(simp add: abs_fresh fresh_star_def)
        ultimately have "\<Psi> \<rhd> P \<parallel> \<lparr>\<nu>x\<rparr>Q \<longmapsto>\<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> \<lparr>\<nu>x\<rparr>Q')" using \<open>A\<^sub>P \<sharp>* M\<close>
          by(rule_tac Comm2) (assumption | simp)+
        moreover from \<open>x \<sharp> \<Psi>\<close> \<open>x \<sharp> P'\<close> \<open>xvec \<sharp>* \<Psi>\<close> have "(\<Psi>, \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> \<lparr>\<nu>x\<rparr>Q'), \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q'))) \<in> Rel" by(rule C2)
        ultimately show ?case by blast
      qed
    qed
  qed
qed

lemma simParComm:
  fixes \<Psi>   :: 'b
  and   P   :: "('a, 'b, 'c) psi"
  and   Q   :: "('a, 'b, 'c) psi"
  and   Rel :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
  
  assumes "eqvt Rel"
  and     C1: "\<And>\<Psi>' R S. (\<Psi>', R \<parallel> S, S \<parallel> R) \<in> Rel"
  and     C2: "\<And>\<Psi>' R S xvec. \<lbrakk>(\<Psi>', R, S) \<in> Rel; xvec \<sharp>* \<Psi>'\<rbrakk> \<Longrightarrow> (\<Psi>', \<lparr>\<nu>*xvec\<rparr>R, \<lparr>\<nu>*xvec\<rparr>S) \<in> Rel"

  shows "\<Psi> \<rhd> P \<parallel> Q \<leadsto>[Rel] Q \<parallel> P"
using \<open>eqvt Rel\<close>
proof(induct rule: simI[of _ _ _ _ "()"])
  case(cSim \<alpha> PQ)
  from \<open>bn \<alpha> \<sharp>* (P \<parallel> Q)\<close> have "bn \<alpha> \<sharp>* Q" and "bn \<alpha> \<sharp>* P" by simp+
  with \<open>\<Psi> \<rhd> Q \<parallel> P \<longmapsto>\<alpha> \<prec> PQ\<close> \<open>bn \<alpha> \<sharp>* \<Psi>\<close> show ?case using \<open>bn \<alpha> \<sharp>* subject \<alpha>\<close>
  proof(induct rule: parCases[where C="()"])
    case(cPar1 Q' A\<^sub>P \<Psi>\<^sub>P)
    from \<open>\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>\<alpha>\<prec> Q'\<close> \<open>extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>\<close> \<open>bn \<alpha> \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* Q\<close> \<open>A\<^sub>P \<sharp>* \<alpha>\<close> 
    have "\<Psi> \<rhd> P \<parallel> Q \<longmapsto>\<alpha> \<prec> (P \<parallel> Q')" by(rule Par2)
    moreover have "(\<Psi>, P \<parallel> Q', Q' \<parallel> P) \<in> Rel" by(rule C1)
    ultimately show ?case by blast
  next
    case(cPar2 P' A\<^sub>Q \<Psi>\<^sub>Q)
    from \<open>\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>\<alpha> \<prec> P'\<close> \<open>extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>\<close> \<open>bn \<alpha> \<sharp>* Q\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q \<sharp>* P\<close> \<open>A\<^sub>Q \<sharp>* \<alpha>\<close> 
    have "\<Psi> \<rhd> P \<parallel> Q \<longmapsto>\<alpha> \<prec> (P' \<parallel> Q)" by(rule Par1)
    moreover have "(\<Psi>, P' \<parallel> Q, Q \<parallel> P') \<in> Rel" by(rule C1)
    ultimately show ?case by blast
  next
    case(cComm1 \<Psi>\<^sub>P M N Q' A\<^sub>Q \<Psi>\<^sub>Q K xvec P' A\<^sub>P)
    note \<open>\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'\<close> \<open>extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>\<close>
         \<open>\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>M\<lparr>N\<rparr> \<prec> Q'\<close> \<open>extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>\<close>
    moreover from \<open>\<Psi> \<otimes> \<Psi>\<^sub>Q \<otimes> \<Psi>\<^sub>P \<turnstile> M \<leftrightarrow> K\<close>
    have "\<Psi> \<otimes> \<Psi>\<^sub>Q \<otimes> \<Psi>\<^sub>P \<turnstile> K \<leftrightarrow> M"
      by(rule chanEqSym)
    hence "\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q \<turnstile> K \<leftrightarrow> M"
      by(blast intro: statEqEnt compositionSym Commutativity)
    ultimately have "\<Psi> \<rhd> P \<parallel> Q \<longmapsto>\<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q')"
      using \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* Q\<close> \<open>A\<^sub>Q \<sharp>* A\<^sub>P\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q \<sharp>* P\<close> \<open>A\<^sub>Q \<sharp>* Q\<close> \<open>xvec \<sharp>* Q\<close> \<open>A\<^sub>P \<sharp>* K\<close> \<open>A\<^sub>Q \<sharp>* M\<close>
      by(rule_tac Comm2) (assumption | simp)+
    moreover have "(\<Psi>, P' \<parallel> Q', Q' \<parallel> P') \<in> Rel" by(rule C1)
    hence "(\<Psi>, \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q'), \<lparr>\<nu>*xvec\<rparr>(Q' \<parallel> P')) \<in> Rel" using \<open>xvec \<sharp>* \<Psi>\<close> by(rule C2)
    ultimately show ?case by blast
  next
    case(cComm2 \<Psi>\<^sub>P M xvec N Q' A\<^sub>Q \<Psi>\<^sub>Q K P' A\<^sub>P)
    note \<open>\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>K\<lparr>N\<rparr> \<prec> P'\<close> \<open>extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>\<close>
         \<open>\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'\<close> \<open>extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>\<close>
    moreover from \<open>\<Psi> \<otimes> \<Psi>\<^sub>Q \<otimes> \<Psi>\<^sub>P \<turnstile> M \<leftrightarrow> K\<close>
    have "\<Psi> \<otimes> \<Psi>\<^sub>Q \<otimes> \<Psi>\<^sub>P \<turnstile> K \<leftrightarrow> M"
      by(rule chanEqSym)
    hence "\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q \<turnstile> K \<leftrightarrow> M"
      by(blast intro: statEqEnt compositionSym Commutativity)
    ultimately have "\<Psi> \<rhd> P \<parallel> Q \<longmapsto>\<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q')"
      using \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* Q\<close> \<open>A\<^sub>Q \<sharp>* A\<^sub>P\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q \<sharp>* P\<close> \<open>A\<^sub>Q \<sharp>* Q\<close> \<open>xvec \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* K\<close> \<open>A\<^sub>Q \<sharp>* M\<close>
      by(rule_tac Comm1) (assumption | simp add: freshChainSym)+
    moreover have "(\<Psi>, P' \<parallel> Q', Q' \<parallel> P') \<in> Rel" by(rule C1)
    hence "(\<Psi>, \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q'), \<lparr>\<nu>*xvec\<rparr>(Q' \<parallel> P')) \<in> Rel" using \<open>xvec \<sharp>* \<Psi>\<close> by(rule C2)
    ultimately show ?case by blast
  qed
qed

lemma bangExtLeft:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"

  assumes "guarded P"
  and     "\<And>\<Psi>' Q. (\<Psi>', Q, Q) \<in> Rel"

  shows "\<Psi> \<rhd> !P \<leadsto>[Rel] P \<parallel> !P"
using assms
by(auto simp add: simulation_def dest: Bang)

lemma bangExtRight:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"

  assumes C1: "\<And>\<Psi>' Q. (\<Psi>', Q, Q) \<in> Rel"

  shows "\<Psi> \<rhd> P \<parallel> !P \<leadsto>[Rel] !P"
proof(auto simp add: simulation_def)
  fix \<alpha> P'
  assume "\<Psi> \<rhd> !P \<longmapsto>\<alpha> \<prec> P'"
  hence "\<Psi> \<rhd> P \<parallel> !P \<longmapsto>\<alpha> \<prec> P'"
    apply -
    by(ind_cases "\<Psi> \<rhd> !P \<longmapsto>\<alpha> \<prec> P'") (auto simp add: psi.inject)
  moreover have "(\<Psi>, P', P') \<in> Rel" by(rule C1)
  ultimately show "\<exists>P''. \<Psi> \<rhd> P \<parallel> !P \<longmapsto>\<alpha> \<prec> P'' \<and> (\<Psi>, P'', P') \<in> Rel"
    by blast
qed

end

end
