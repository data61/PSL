(* 
   Title: Psi-calculi   
   Author/Maintainer: Jesper Bengtson (jebe@itu.dk), 2012
*)
theory Tau
  imports Weak_Congruence Bisim_Struct_Cong
begin 

locale tau = env +
  fixes nameTerm :: "name \<Rightarrow> 'a"

  assumes ntEqvt[eqvt]: "(p::name prm) \<bullet> (nameTerm x) = nameTerm(p \<bullet> x)"
  and     ntSupp: "supp(nameTerm x) = {x}"
  and     ntEq: "\<Psi> \<turnstile> (nameTerm x) \<leftrightarrow> M = (M = nameTerm x)"
  and     subst4: "\<lbrakk>length xvec = length Tvec; distinct xvec; xvec \<sharp>* (M::'a)\<rbrakk> \<Longrightarrow> M[xvec::=Tvec] = M"
begin

lemma ntChanEq[simp]:
  fixes \<Psi> :: 'b
  and   x :: name

  shows "\<Psi> \<turnstile> (nameTerm x) \<leftrightarrow> (nameTerm x)"
using ntEq
by auto

lemma nameTermFresh[simp]:
  fixes x :: name
  and   y :: name
  
  shows "x \<sharp> (nameTerm y) = (x \<noteq> y)"
using ntSupp
by(auto simp add: fresh_def)

lemma nameTermFreshChain[simp]:
  fixes xvec :: "name list"
  and   x    :: name

  shows "xvec \<sharp>* (nameTerm x) = x \<sharp> xvec"
by(induct xvec) auto

definition tauPrefix :: "('a, 'b, 'c) psi \<Rightarrow> ('a, 'b, 'c) psi" ("\<tau>._" [85] 85)
  where "tauPrefix P \<equiv> THE P'. \<exists>x::name. x \<sharp> P \<and> P' = \<lparr>\<nu>x\<rparr>(((nameTerm x)\<lparr>\<lambda>*([]) (nameTerm x)\<rparr>.\<zero>) \<parallel> ((nameTerm x)\<langle>(nameTerm x)\<rangle>.P))"

lemma tauActionUnfold:
  fixes P :: "('a, 'b, 'c) psi"
  and   C :: "'d::fs_name"

  obtains x::name where "x \<sharp> P" and "x \<sharp> C" and "\<tau>.(P) = \<lparr>\<nu>x\<rparr>(((nameTerm x)\<lparr>\<lambda>*([]) (nameTerm x)\<rparr>.\<zero>) \<parallel> ((nameTerm x)\<langle>(nameTerm x)\<rangle>.P))"
proof -
  obtain x::name where "x \<sharp> P" and "x \<sharp> C" by(generate_fresh "name") auto
  hence "\<exists>x::name. x \<sharp> P \<and> x \<sharp> C \<and> \<tau>.(P) = \<lparr>\<nu>x\<rparr>(((nameTerm x)\<lparr>\<lambda>*([]) (nameTerm x)\<rparr>.\<zero>) \<parallel> ((nameTerm x)\<langle>(nameTerm x)\<rangle>.P))"
    apply(simp add: tauPrefix_def)
    apply(subst the_equality)
    apply(rule_tac x=x in exI)
    apply simp
    apply(clarify)
    apply(simp add: psi.inject alpha)
    by(auto simp add: calc_atm eqvts abs_fresh)
  moreover assume "\<And>x. \<lbrakk>x \<sharp> P; x \<sharp> C;
          \<tau>.(P) =
          \<lparr>\<nu>x\<rparr>((nameTerm x\<lparr>\<lambda>*[] nameTerm x\<rparr>.\<zero>) \<parallel> nameTerm x\<langle>nameTerm x\<rangle>.P)\<rbrakk>
         \<Longrightarrow> thesis"
  ultimately show ?thesis by blast
qed

lemma tauActionI:
  fixes P :: "('a, 'b, 'c) psi"

  shows "\<exists>P'. \<Psi> \<rhd> \<tau>.(P) \<longmapsto>\<tau> \<prec> P' \<and> \<Psi> \<rhd> P \<sim> P'"
proof -
  obtain x:: name where "x \<sharp> \<Psi>" and "x \<sharp> P" and "\<tau>.(P) = \<lparr>\<nu>x\<rparr>(((nameTerm x)\<lparr>\<lambda>*([]) (nameTerm x)\<rparr>.\<zero>) \<parallel> ((nameTerm x)\<langle>(nameTerm x)\<rangle>.P))"
    by(rule tauActionUnfold)
  
  then have "\<Psi> \<rhd> \<tau>.(P) \<longmapsto>\<tau> \<prec> \<lparr>\<nu>x\<rparr>(\<zero> \<parallel> P)"
    apply simp
    apply(rule Scope)
    apply auto
    apply(subgoal_tac "\<Psi> \<rhd> ((nameTerm x)\<lparr>\<lambda>*([]) (nameTerm x)\<rparr>.\<zero>) \<parallel> ((nameTerm x)\<langle>(nameTerm x)\<rangle>.P) \<longmapsto>\<tau> \<prec> \<lparr>\<nu>*[]\<rparr>(\<zero> \<parallel> P)")
    apply simp
    apply(rule_tac M="(nameTerm x)" and N="(nameTerm x)" and K="(nameTerm x)" in Comm1)
    apply(auto intro: ntChanEq Output Input)
    apply(subgoal_tac "\<Psi> \<otimes> \<one> \<rhd> (nameTerm x)\<lparr>\<lambda>*([]) (nameTerm x)\<rparr>.\<zero> \<longmapsto>(nameTerm x)\<lparr>((nameTerm x)[([])::=[]])\<rparr> \<prec> (\<zero>[[]::=[]])")
    apply(simp add: subst4)
    by(rule_tac Input) auto
  moreover from \<open>x \<sharp> \<Psi>\<close> \<open>x \<sharp> P\<close> have "\<Psi> \<rhd> P \<sim> \<lparr>\<nu>x\<rparr>(\<zero> \<parallel> P)"
    by(metis bisimTransitive bisimParNil bisimScopeExtSym bisimResNil bisimParPresSym bisimParComm bisimE(4))
  ultimately show ?thesis by blast
qed

lemma outputEmpy[dest]:
  assumes "\<Psi> \<rhd> M\<langle>N\<rangle>.P \<longmapsto>K\<lparr>\<nu>*xvec\<rparr>\<langle>N'\<rangle> \<prec> P'"

  shows "xvec = []"
using assms
apply -
by(ind_cases "\<Psi> \<rhd> M\<langle>N\<rangle>.P \<longmapsto>K\<lparr>\<nu>*xvec\<rparr>\<langle>N'\<rangle> \<prec> P'") (auto simp add: psi.inject residualInject)

lemma tauActionE:
  fixes P :: "('a, 'b, 'c) psi"

  assumes "\<Psi> \<rhd> \<tau>.(P) \<longmapsto>\<tau> \<prec> P'"

  shows "\<Psi> \<rhd> P \<sim> P'" and "supp P' = ((supp P)::name set)"
proof -
  obtain x:: name where "x \<sharp> (\<Psi>, P')" and "x \<sharp> P" and "\<tau>.(P) = \<lparr>\<nu>x\<rparr>(((nameTerm x)\<lparr>\<lambda>*([]) (nameTerm x)\<rparr>.\<zero>) \<parallel> ((nameTerm x)\<langle>(nameTerm x)\<rangle>.P))"
    by(rule tauActionUnfold)
  with assms have "\<Psi> \<rhd> P \<sim> P' \<and> supp P' = ((supp P)::name set)"
    apply simp
    apply(erule_tac resTauCases)
    apply simp+
    apply(erule_tac C="x" in parCases)
    apply simp+
    apply(drule_tac nilTrans(3)[where xvec="[]", simplified])
    apply simp
    apply force
    apply simp
    apply(subgoal_tac "\<Psi> \<otimes> \<one> \<rhd> (nameTerm x)\<lparr>\<lambda>*[] (nameTerm x)\<rparr>.\<zero> \<longmapsto>M\<lparr>N\<rparr> \<prec> P'a")
    apply(erule_tac inputCases)
    apply simp
    apply(subgoal_tac "xvec = []")
    apply(erule_tac outputCases)
    apply simp
    apply(clarsimp)
    apply(rule conjI)
    apply(metis bisimTransitive bisimParNil bisimScopeExtSym bisimResNil bisimParPresSym bisimParComm bisimE(4))
    apply(auto simp add: psi.supp abs_supp suppBottom)
    by(simp add: fresh_def)
  thus "\<Psi> \<rhd> P \<sim> P'" and "supp P' = ((supp P)::name set)"
    by auto
qed

lemma tauActionEqvt[eqvt]:
  fixes P :: "('a, 'b, 'c) psi"
  and   p :: "name prm"

  shows "(p \<bullet> \<tau>.(P)) = \<tau>.(p \<bullet> P)"
proof -
  obtain x::name where "x \<sharp> P" and "x \<sharp> p" and "\<tau>.(P) = \<lparr>\<nu>x\<rparr>(((nameTerm x)\<lparr>\<lambda>*([]) (nameTerm x)\<rparr>.\<zero>) \<parallel> ((nameTerm x)\<langle>(nameTerm x)\<rangle>.P))"
    by(rule tauActionUnfold)
  moreover obtain y::name where "y \<sharp> p \<bullet> P" and "y \<sharp> (p, x)" and "\<tau>.(p \<bullet> P) = \<lparr>\<nu>y\<rparr>(((nameTerm y)\<lparr>\<lambda>*([]) (nameTerm y)\<rparr>.\<zero>) \<parallel> ((nameTerm y)\<langle>(nameTerm y)\<rangle>.(p \<bullet> P)))"
    by(rule tauActionUnfold)
  ultimately show ?thesis
    by(simp add: eqvts calc_atm at_prm_fresh[OF at_name_inst] psi.inject alpha pt_fresh_perm_app[OF pt_name_inst, OF at_name_inst])
qed

lemma resCases'[consumes 7, case_names cOpen cRes]:
  fixes \<Psi>    :: 'b
  and   x    :: name
  and   P    :: "('a, 'b, 'c) psi"
  and   \<alpha>    :: "'a action"
  and   P'   :: "('a, 'b, 'c) psi"
  and   C    :: "'d::fs_name"

  assumes Trans: "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>P \<longmapsto>x\<alpha> \<prec> xP'"
  and     "x \<sharp> \<Psi>"
  and     "x \<sharp> x\<alpha>"
  and     "x \<sharp> xP'"
  and     "bn x\<alpha> \<sharp>* \<Psi>"
  and     "bn x\<alpha> \<sharp>* P"
  and     "bn x\<alpha> \<sharp>* subject x\<alpha>"
  and     rOpen: "\<And>M xvec yvec y N P'. \<lbrakk>\<Psi> \<rhd> P \<longmapsto>M\<lparr>\<nu>*(xvec@yvec)\<rparr>\<langle>([(x, y)] \<bullet> N)\<rangle> \<prec> ([(x, y)] \<bullet> P'); y \<in> supp N;
                                         x \<sharp> N; x \<sharp> P'; x \<noteq> y; y \<sharp> xvec; y \<sharp> yvec; y \<sharp> M; distinct xvec; distinct yvec;
                                         xvec \<sharp>* \<Psi>; y \<sharp> \<Psi>; yvec \<sharp>* \<Psi>; xvec \<sharp>* P; y \<sharp> P; yvec \<sharp>* P; xvec \<sharp>* M; y \<sharp> M;
                                         yvec \<sharp>* M; xvec \<sharp>* yvec; x\<alpha> = M\<lparr>\<nu>*(xvec@y#yvec)\<rparr>\<langle>N\<rangle>; xP' = P'\<rbrakk> \<Longrightarrow>
                                         Prop"
  and     rScope:  "\<And>P'. \<lbrakk>\<Psi> \<rhd> P \<longmapsto>x\<alpha> \<prec> P'; xP' = \<lparr>\<nu>x\<rparr>P'\<rbrakk> \<Longrightarrow> Prop"

  shows "Prop"
proof -
  from Trans have "distinct(bn x\<alpha>)" by(auto dest: boundOutputDistinct)
  have "length(bn x\<alpha>) = residualLength(x\<alpha> \<prec> xP')" by simp
  note Trans
  moreover have "length [] = inputLength(\<lparr>\<nu>x\<rparr>P)" and "distinct []"
    by(auto simp add: inputLength_inputLength'_inputLength''.simps)
  moreover note \<open>length(bn x\<alpha>) = residualLength(x\<alpha> \<prec> xP')\<close> \<open>distinct(bn x\<alpha>)\<close>
  moreover note \<open>length(bn x\<alpha>) = residualLength(x\<alpha> \<prec> xP')\<close> \<open>distinct(bn x\<alpha>)\<close>
  moreover note \<open>length(bn x\<alpha>) = residualLength(x\<alpha> \<prec> xP')\<close> \<open>distinct(bn x\<alpha>)\<close>
  moreover note \<open>length(bn x\<alpha>) = residualLength(x\<alpha> \<prec> xP')\<close> \<open>distinct(bn x\<alpha>)\<close>
  ultimately show ?thesis using \<open>bn x\<alpha> \<sharp>* \<Psi>\<close> \<open>bn x\<alpha> \<sharp>* P\<close> \<open>bn x\<alpha> \<sharp>* subject x\<alpha>\<close> \<open>x \<sharp> \<Psi>\<close> \<open>x \<sharp> x\<alpha>\<close> \<open>x \<sharp> xP'\<close> \<open>distinct(bn x\<alpha>)\<close> rScope rOpen
    apply(cases rule: semanticsCases[of _ _ _ _ _ _ _ _ _ _ x x]) 
    apply(auto simp add: psi.inject alpha abs_fresh residualInject boundOutputApp boundOutput.inject eqvts)
    apply(subgoal_tac "y \<in> supp Na")
    apply(auto simp add: residualInject boundOutputApp)
    apply(drule_tac pi="[(x, y)]" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
    by(simp add: calc_atm eqvts)
qed

lemma parCases'[consumes 5, case_names cPar1 cPar2 cComm1 cComm2]:
  fixes \<Psi>    :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   Q    :: "('a, 'b, 'c) psi"
  and   \<alpha>    :: "'a action"
  and   T    :: "('a, 'b, 'c) psi"
  and   C    :: "'d::fs_name"

  assumes Trans: "\<Psi> \<rhd> P \<parallel> Q \<longmapsto>x\<alpha> \<prec> xT"
  and     "bn x\<alpha> \<sharp>* \<Psi>"
  and     "bn x\<alpha> \<sharp>* P"
  and     "bn x\<alpha> \<sharp>* Q"
  and     "bn x\<alpha> \<sharp>* subject x\<alpha>"
  and     rPar1: "\<And>P' A\<^sub>Q \<Psi>\<^sub>Q. \<lbrakk>\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>x\<alpha> \<prec> P';  extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>; distinct A\<^sub>Q;
                                  A\<^sub>Q \<sharp>* \<Psi>; A\<^sub>Q \<sharp>* P; A\<^sub>Q \<sharp>* Q; A\<^sub>Q \<sharp>* x\<alpha>; A\<^sub>Q \<sharp>* P'; A\<^sub>Q \<sharp>* C; xT = P' \<parallel> Q\<rbrakk> \<Longrightarrow> Prop"
  and     rPar2: "\<And>Q' A\<^sub>P \<Psi>\<^sub>P. \<lbrakk>\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>x\<alpha> \<prec> Q';  extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P;
                                 A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* Q; A\<^sub>P \<sharp>* x\<alpha>; A\<^sub>P \<sharp>* Q'; A\<^sub>P \<sharp>* C; xT = P \<parallel> Q'\<rbrakk> \<Longrightarrow> Prop"
  and     rComm1: "\<And>\<Psi>\<^sub>Q M N P' A\<^sub>P \<Psi>\<^sub>P K xvec Q' A\<^sub>Q.
           \<lbrakk>\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>M\<lparr>N\<rparr> \<prec> P'; extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P;
            \<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'; extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>; distinct A\<^sub>Q;
            \<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q \<turnstile> M \<leftrightarrow> K; distinct xvec;
            A\<^sub>P \<sharp>* \<Psi>;  A\<^sub>P \<sharp>* \<Psi>\<^sub>Q;  A\<^sub>P \<sharp>* P;  A\<^sub>P \<sharp>* M;  A\<^sub>P \<sharp>* N;  A\<^sub>P \<sharp>* P';  A\<^sub>P \<sharp>* Q;  A\<^sub>P \<sharp>* xvec;  A\<^sub>P \<sharp>* Q'; A\<^sub>P \<sharp>* A\<^sub>Q;  A\<^sub>P \<sharp>* C; 
            A\<^sub>Q \<sharp>* \<Psi>;  A\<^sub>Q \<sharp>* \<Psi>\<^sub>P; A\<^sub>Q \<sharp>* P;  A\<^sub>Q \<sharp>* K;  A\<^sub>Q \<sharp>* N;  A\<^sub>Q \<sharp>* P';  A\<^sub>Q \<sharp>* Q;  A\<^sub>Q \<sharp>* xvec;  A\<^sub>Q \<sharp>* Q'; A\<^sub>Q \<sharp>* C; 
            xvec \<sharp>* \<Psi>;  xvec \<sharp>* \<Psi>\<^sub>P; xvec \<sharp>* P;  xvec \<sharp>* M;  xvec \<sharp>* K; xvec \<sharp>* Q;  xvec \<sharp>* \<Psi>\<^sub>Q;  xvec \<sharp>* C; x\<alpha>=\<tau>; xT = \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q')\<rbrakk> \<Longrightarrow> Prop"
  and     rComm2: "\<And>\<Psi>\<^sub>Q M xvec N P' A\<^sub>P \<Psi>\<^sub>P K Q' A\<^sub>Q.
           \<lbrakk>\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'; extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P;
            \<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>K\<lparr>N\<rparr> \<prec> Q'; extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>; distinct A\<^sub>Q;
            \<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q \<turnstile> M \<leftrightarrow> K; distinct xvec;
            A\<^sub>P \<sharp>* \<Psi>;  A\<^sub>P \<sharp>* \<Psi>\<^sub>Q;  A\<^sub>P \<sharp>* P;  A\<^sub>P \<sharp>* M;  A\<^sub>P \<sharp>* N;  A\<^sub>P \<sharp>* P';  A\<^sub>P \<sharp>* Q;  A\<^sub>P \<sharp>* xvec;  A\<^sub>P \<sharp>* Q'; A\<^sub>P \<sharp>* A\<^sub>Q;  A\<^sub>P \<sharp>* C; 
            A\<^sub>Q \<sharp>* \<Psi>;  A\<^sub>Q \<sharp>* \<Psi>\<^sub>P; A\<^sub>Q \<sharp>* P;  A\<^sub>Q \<sharp>* K;  A\<^sub>Q \<sharp>* N;  A\<^sub>Q \<sharp>* P';  A\<^sub>Q \<sharp>* Q;  A\<^sub>Q \<sharp>* xvec;  A\<^sub>Q \<sharp>* Q'; A\<^sub>Q \<sharp>* C; 
            xvec \<sharp>* \<Psi>;  xvec \<sharp>* \<Psi>\<^sub>P; xvec \<sharp>* P;  xvec \<sharp>* M;  xvec \<sharp>* K;  xvec \<sharp>* Q;  xvec \<sharp>* \<Psi>\<^sub>Q;  xvec \<sharp>* C; x\<alpha>=\<tau>; xT = \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q')\<rbrakk> \<Longrightarrow> Prop"

  shows "Prop"
proof -
  from Trans have "distinct(bn x\<alpha>)" by(auto dest: boundOutputDistinct)
  have "length(bn x\<alpha>) = residualLength(x\<alpha> \<prec> xT)" by simp
  note Trans
  moreover have "length [] = inputLength(P \<parallel> Q)" and "distinct []"
    by(auto simp add: inputLength_inputLength'_inputLength''.simps)
  moreover note \<open>length(bn x\<alpha>) = residualLength(x\<alpha> \<prec> xT)\<close> \<open>distinct(bn x\<alpha>)\<close>
  moreover note \<open>length(bn x\<alpha>) = residualLength(x\<alpha> \<prec> xT)\<close> \<open>distinct(bn x\<alpha>)\<close>
  moreover note \<open>length(bn x\<alpha>) = residualLength(x\<alpha> \<prec> xT)\<close> \<open>distinct(bn x\<alpha>)\<close>
  moreover note \<open>length(bn x\<alpha>) = residualLength(x\<alpha> \<prec> xT)\<close> \<open>distinct(bn x\<alpha>)\<close>
  moreover obtain x::name where "x \<sharp> \<Psi>" and "x \<sharp> P" and "x \<sharp> Q" and "x \<sharp> x\<alpha>" and "x \<sharp> xT"
    by(generate_fresh "name") auto
  ultimately show ?thesis using \<open>bn x\<alpha> \<sharp>* \<Psi>\<close> \<open>bn x\<alpha> \<sharp>* P\<close> \<open>bn x\<alpha> \<sharp>* Q\<close> \<open>bn x\<alpha> \<sharp>* subject x\<alpha>\<close> using rPar1 rPar2 rComm1 rComm2
    by(cases rule: semanticsCases[of _ _ _ _ _ _ _ _ _ C x x]) (auto simp add: psi.inject residualInject residualInject')
qed

lemma inputCases'[consumes 1, case_names cInput]:
  fixes \<Psi>   :: 'b
  and   M    :: 'a
  and   xvec :: "name list"
  and   N    :: 'a
  and   P    :: "('a, 'b, 'c) psi"  
  and   \<alpha>    :: "'a action"
  and   P'   :: "('a, 'b, 'c) psi"
  
  assumes Trans: "\<Psi> \<rhd> M\<lparr>\<lambda>*xvec N\<rparr>.P \<longmapsto>\<alpha> \<prec> P'"  
  and     rInput: "\<And>K Tvec. \<lbrakk>\<Psi> \<turnstile> M \<leftrightarrow> K; set xvec \<subseteq> supp N; length xvec = length Tvec; distinct xvec; \<alpha>=K\<lparr>N[xvec::=Tvec]\<rparr>; P' = P[xvec::=Tvec]\<rbrakk> \<Longrightarrow> Prop (K\<lparr>N[xvec::=Tvec]\<rparr>) (P[xvec::=Tvec])"

  shows "Prop \<alpha> P'"
proof -
  {
    fix xvec N P
    assume Trans: "\<Psi> \<rhd> M\<lparr>\<lambda>*xvec N\<rparr>.P \<longmapsto>\<alpha> \<prec> P'"
       and "xvec \<sharp>* \<Psi>" and "xvec \<sharp>* M" and "xvec \<sharp>* \<alpha>" and "xvec \<sharp>* P'" and "distinct xvec"
       and rInput: "\<And>K Tvec. \<lbrakk>\<Psi> \<turnstile> M \<leftrightarrow> K; set xvec \<subseteq> supp N; length xvec = length Tvec; distinct xvec; \<alpha>=K\<lparr>N[xvec::=Tvec]\<rparr>; P'=P[xvec::=Tvec]\<rbrakk> \<Longrightarrow> Prop (K\<lparr>N[xvec::=Tvec]\<rparr>) (P[xvec::=Tvec])"

    from Trans have "bn \<alpha> = []"
      apply -
      by(ind_cases "\<Psi> \<rhd> M\<lparr>\<lambda>*xvec N\<rparr>.P \<longmapsto>\<alpha> \<prec> P'") (auto simp add: residualInject)
    from Trans have "distinct(bn \<alpha>)" by(auto dest: boundOutputDistinct)
    have "length(bn \<alpha>) = residualLength(\<alpha> \<prec> P')" by simp
    note Trans
    moreover have "length xvec = inputLength(M\<lparr>\<lambda>*xvec N\<rparr>.P)" by auto
    moreover note \<open>distinct xvec\<close>
    moreover note \<open>length(bn \<alpha>) = residualLength(\<alpha> \<prec> P')\<close> \<open>distinct(bn \<alpha>)\<close>
    moreover note \<open>length(bn \<alpha>) = residualLength(\<alpha> \<prec> P')\<close> \<open>distinct(bn \<alpha>)\<close>
    moreover note \<open>length(bn \<alpha>) = residualLength(\<alpha> \<prec> P')\<close> \<open>distinct(bn \<alpha>)\<close>
    moreover note \<open>length(bn \<alpha>) = residualLength(\<alpha> \<prec> P')\<close> \<open>distinct(bn \<alpha>)\<close>
    moreover note \<open>length(bn \<alpha>) = residualLength(\<alpha> \<prec> P')\<close> \<open>distinct(bn \<alpha>)\<close>
    moreover obtain x::name where "x \<sharp> \<Psi>" and "x \<sharp> P" and "x \<sharp> M" and "x \<sharp> xvec" and "x \<sharp> \<alpha>" and "x \<sharp> P'" and "x \<sharp> N"
      by(generate_fresh "name") auto
    ultimately have "Prop \<alpha> P'" using \<open>bn \<alpha> = []\<close> \<open>xvec \<sharp>* \<Psi>\<close>\<open>xvec \<sharp>* M\<close> \<open>xvec \<sharp>* \<alpha>\<close> \<open>xvec \<sharp>* P'\<close> rInput
      apply(cases rule: semanticsCases[of _ _ _ _ _ _ _ _ _ C x])  
      by(fastforce simp add: residualInject psi.inject inputChainFresh)+
  }
  note Goal = this
  moreover obtain p :: "name prm" where "(p \<bullet> xvec) \<sharp>* \<Psi>" and "(p \<bullet> xvec) \<sharp>* M" and "(p \<bullet> xvec) \<sharp>* N" and "(p \<bullet> xvec) \<sharp>* P"
                                    and "(p \<bullet> xvec) \<sharp>* \<alpha>" and "(p \<bullet> xvec) \<sharp>* P'" and S: "set p \<subseteq> set xvec \<times> set(p \<bullet> xvec)"
                                    and "distinctPerm p"
    by(rule_tac xvec=xvec and c="(\<Psi>, M, N, P, \<alpha>, P')" in name_list_avoiding) auto
  from Trans \<open>(p \<bullet> xvec) \<sharp>* N\<close> \<open>(p \<bullet> xvec) \<sharp>* P\<close> S have "\<Psi> \<rhd> M\<lparr>\<lambda>*(p \<bullet> xvec) (p \<bullet> N)\<rparr>.(p \<bullet> P) \<longmapsto>\<alpha> \<prec> P'"
    by(simp add: inputChainAlpha')
  moreover {
    fix K Tvec
    assume "\<Psi> \<turnstile> M \<leftrightarrow> K"
    moreover assume "set(p \<bullet> xvec) \<subseteq> supp(p \<bullet> N)"
    hence "(p \<bullet> set(p \<bullet> xvec)) \<subseteq> (p \<bullet> supp(p \<bullet> N))" by simp
    with \<open>distinctPerm p\<close> have "set xvec \<subseteq> supp N" by(simp add: eqvts)
    moreover assume "length(p \<bullet> xvec) = length(Tvec::'a list)"
    hence "length xvec = length Tvec" by simp
    moreover assume "distinct xvec"
    moreover assume "\<alpha>=K\<lparr>(p \<bullet> N)[(p \<bullet> xvec)::=Tvec]\<rparr>" and "P' = (p \<bullet> P)[(p \<bullet> xvec)::=Tvec]"
    with \<open>(p \<bullet> xvec) \<sharp>* P\<close> \<open>(p \<bullet> xvec) \<sharp>* N\<close> \<open>distinctPerm p\<close> \<open>length xvec = length Tvec\<close> S
    have "\<alpha>=K\<lparr>(N[xvec::=Tvec])\<rparr>" and "P' = P[xvec::=Tvec]"
      by(simp add: renaming substTerm.renaming)+
    ultimately have "Prop (K\<lparr>N[xvec::=Tvec]\<rparr>) (P[xvec::=Tvec])" 
      by(rule rInput)
    with \<open>length xvec = length Tvec\<close> S \<open>distinctPerm p\<close> \<open>(p \<bullet> xvec) \<sharp>* N\<close> \<open>(p \<bullet> xvec) \<sharp>* P\<close>
    have "Prop (K\<lparr>(p \<bullet> N)[(p \<bullet> xvec)::=Tvec]\<rparr>) ((p \<bullet> P)[(p \<bullet> xvec)::=Tvec])"
      by(simp add: renaming substTerm.renaming)
  }
  moreover from Trans have "distinct xvec" by(rule inputDistinct)
  hence "distinct(p \<bullet> xvec)" by simp
  ultimately show ?thesis using \<open>(p \<bullet> xvec) \<sharp>* \<Psi>\<close> \<open>(p \<bullet> xvec) \<sharp>* M\<close> \<open>(p \<bullet> xvec) \<sharp>* \<alpha>\<close> \<open>(p \<bullet> xvec) \<sharp>* P'\<close> \<open>distinct xvec\<close>
    by(rule_tac Goal) assumption+
qed

lemma outputCases'[consumes 1, case_names cOutput]:
  fixes \<Psi> :: 'b
  and   M  :: 'a
  and   N  :: 'a
  and   P  :: "('a, 'b, 'c) psi"  
  and   \<alpha>  :: "'a action"
  and   P' :: "('a, 'b, 'c) psi"
  
  assumes "\<Psi> \<rhd> M\<langle>N\<rangle>.P \<longmapsto>\<alpha> \<prec> P'"
  and     "\<And>K. \<lbrakk>\<Psi> \<turnstile> M \<leftrightarrow> K; subject \<alpha>=Some K\<rbrakk> \<Longrightarrow> Prop (K\<langle>N\<rangle>) P"

  shows "Prop \<alpha> P'"
using assms
by(cases rule: semantics.cases) (auto simp add: residualInject psi.inject)

lemma tauOutput[dest]:
  fixes \<Psi>   :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   M    :: 'a
  and   xvec :: "name list"
  and   N    :: 'a
  and   P'   :: "('a, 'b, 'c) psi"

  assumes "\<Psi> \<rhd> \<tau>.(P) \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
  
  shows False
proof -
  {
    fix xvec N P'

    assume "\<Psi> \<rhd> \<tau>.(P) \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
    and    "xvec \<sharp>* \<Psi>"
    and    "xvec \<sharp>* P"
    and    "xvec \<sharp>* M"

    moreover obtain x:: name where "x \<sharp> \<Psi>" and "x \<sharp> P" and "x \<sharp> xvec" and "x \<sharp> M" and "x \<sharp> N" and "x \<sharp> P'"
                               and "\<tau>.(P) = \<lparr>\<nu>x\<rparr>(((nameTerm x)\<lparr>\<lambda>*([]) (nameTerm x)\<rparr>.\<zero>) \<parallel> ((nameTerm x)\<langle>(nameTerm x)\<rangle>.P))"
      by(rule_tac C="(\<Psi>, M, xvec, N, P')" in tauActionUnfold) auto
    ultimately have False
      apply simp
      apply(erule_tac resCases')
      apply simp+
      apply(erule_tac parOutputCases)
      apply(simp add: action.inject psi.inject)+
      apply(drule_tac nilTrans(2)[where xvec="[]", simplified])
      apply simp+
      apply(simp add: action.inject)
      apply(clarify)
      apply(erule outputCases')
      apply(auto simp add: ntEq)
      apply(erule_tac parCases')
      apply(auto simp add: abs_fresh)
      apply(drule_tac nilTrans(2)[where xvec="[]", simplified])
      apply simp
      apply(erule_tac outputCases')
      apply auto
      by(simp add: ntEq)
  }
  moreover obtain p where "set p \<subseteq> set xvec \<times> set(p \<bullet> xvec)" and "(p \<bullet> xvec) \<sharp>* N" and  "(p \<bullet> xvec) \<sharp>* P'" 
                      and "(p \<bullet> xvec) \<sharp>* \<Psi>" and "(p \<bullet> xvec) \<sharp>* P" and "(p \<bullet> xvec) \<sharp>* M"
    by(rule_tac c="(N, P', \<Psi>, P, M)" and xvec=xvec in name_list_avoiding) auto
    ultimately show False using assms by(simp add: boundOutputChainAlpha'' residualInject) auto
qed

lemma tauInput[dest]:
  fixes \<Psi> :: 'b
  and   P  :: "('a, 'b, 'c) psi"
  and   M  :: 'a
  and   N  :: 'a
  and   P' :: "('a, 'b, 'c) psi"

  assumes "\<Psi> \<rhd> \<tau>.(P) \<longmapsto>M\<lparr>N\<rparr> \<prec> P'"

  shows False
proof -
  obtain x:: name where "x \<sharp> \<Psi>" and "x \<sharp> P" and "x \<sharp> M" and "x \<sharp> N" and "x \<sharp> P'"
                    and "\<tau>.(P) = \<lparr>\<nu>x\<rparr>(((nameTerm x)\<lparr>\<lambda>*([]) (nameTerm x)\<rparr>.\<zero>) \<parallel> ((nameTerm x)\<langle>(nameTerm x)\<rangle>.P))"
    by(rule_tac C="(\<Psi>, M, N, P')" in tauActionUnfold) auto
  with assms show False
    apply simp
    apply(erule_tac resCases')
    apply auto
    apply(drule_tac  parCases')
    apply(auto simp add: abs_fresh)
    apply(subgoal_tac "\<Psi> \<otimes> \<one> \<rhd> (nameTerm x)\<lparr>\<lambda>*[] (nameTerm x)\<rparr>.\<zero> \<longmapsto>M\<lparr>N\<rparr> \<prec> P'a")
    apply(erule_tac inputCases')
    by(auto simp add: action.inject subst4)
qed

lemma tauPrefixFrame:
  fixes P :: "('a, 'b, 'c) psi"

  shows "extractFrame(\<tau>.(P)) \<simeq>\<^sub>F \<langle>\<epsilon>, \<one>\<rangle>"
proof -
  obtain x:: name where "x \<sharp> P"
                    and "\<tau>.(P) = \<lparr>\<nu>x\<rparr>(((nameTerm x)\<lparr>\<lambda>*([]) (nameTerm x)\<rparr>.\<zero>) \<parallel> ((nameTerm x)\<langle>(nameTerm x)\<rangle>.P))"
    by(rule_tac C="()" in tauActionUnfold) auto
  thus ?thesis
    by(force intro: frameResFresh Identity FrameStatEqTrans)
qed

lemma insertTauAssertion:
  fixes P :: "('a, 'b, 'c) psi"
  and   \<Psi> :: 'b

  shows "insertAssertion (extractFrame(\<tau>.(P))) \<Psi> \<simeq>\<^sub>F \<langle>\<epsilon>, \<Psi>\<rangle>"
proof -
  obtain x:: name where "x \<sharp> P" and "x \<sharp> \<Psi>"
                    and "\<tau>.(P) = \<lparr>\<nu>x\<rparr>(((nameTerm x)\<lparr>\<lambda>*([]) (nameTerm x)\<rparr>.\<zero>) \<parallel> ((nameTerm x)\<langle>(nameTerm x)\<rangle>.P))"
    by(rule_tac C=\<Psi> in tauActionUnfold) auto
  thus ?thesis
    apply auto
    apply(rule_tac G="\<langle>\<epsilon>, \<Psi> \<otimes> \<one> \<otimes> \<one>\<rangle>" in FrameStatEqTrans)
    apply(rule_tac frameResFresh) apply auto
    apply(subgoal_tac "x \<sharp> \<one> \<otimes> \<one>")
    apply auto
    by(metis Identity AssertionStatEqTrans AssertionStatEqSym Associativity)
qed

lemma seqSubst4:
  assumes "y \<sharp> \<sigma>"
  and     "wellFormedSubst \<sigma>"

  shows "substTerm.seqSubst (nameTerm y) \<sigma> = nameTerm y"
using assms
by(induct \<sigma>) (auto simp add: subst4)

lemma tauSeqSubst[simp]:
  fixes P :: "('a, 'b, 'c) psi"
  and   \<sigma> :: "(name list \<times> 'a list) list"
  
  assumes "wellFormedSubst \<sigma>"

  shows "(\<tau>.(P))[<\<sigma>>] = \<tau>.(P[<\<sigma>>])"
proof -
  obtain x:: name where "x \<sharp> P[<\<sigma>>]" and "x \<sharp> \<sigma>" and "x \<sharp> P"
                    and "\<tau>.(P[<\<sigma>>]) = \<lparr>\<nu>x\<rparr>(((nameTerm x)\<lparr>\<lambda>*([]) (nameTerm x)\<rparr>.\<zero>) \<parallel> ((nameTerm x)\<langle>(nameTerm x)\<rangle>.(P[<\<sigma>>])))"
    by(rule_tac C="(\<sigma>, P)" in tauActionUnfold) auto
  moreover obtain y:: name where "y \<sharp> P[<\<sigma>>]" and "y \<sharp> \<sigma>" and "y \<sharp> P" and "x \<noteq> y"
                    and "\<tau>.(P) = \<lparr>\<nu>y\<rparr>(((nameTerm y)\<lparr>\<lambda>*([]) (nameTerm y)\<rparr>.\<zero>) \<parallel> ((nameTerm y)\<langle>(nameTerm y)\<rangle>.(P)))"
    by(rule_tac C="(\<sigma>, P[<\<sigma>>], x)" in tauActionUnfold) auto
  ultimately show ?thesis using assms
    by(auto simp add: psi.inject alpha eqvts calc_atm psi.inject input.inject seqSubst4)
qed

lemma tauSubst[simp]:
  fixes P    :: "('a, 'b, 'c) psi"
  and   xvec :: "name list"
  and   Tvec :: "'a list"
  
  assumes "distinct xvec"
  and     "length xvec = length Tvec"

  shows "(\<tau>.(P))[xvec::=Tvec] = \<tau>.(P[xvec::=Tvec])"
proof -
  obtain x:: name where "x \<sharp> P[xvec::=Tvec]" and "x \<sharp> xvec" and "x \<sharp> Tvec" and "x \<sharp> P"
                    and "\<tau>.(P[xvec::=Tvec]) = \<lparr>\<nu>x\<rparr>(((nameTerm x)\<lparr>\<lambda>*([]) (nameTerm x)\<rparr>.\<zero>) \<parallel> ((nameTerm x)\<langle>(nameTerm x)\<rangle>.(P[xvec::=Tvec])))"
    by(rule_tac C="(xvec, Tvec, P)" in tauActionUnfold) auto
  moreover obtain y:: name where "y \<sharp> P[xvec::=Tvec]" and "y \<sharp> xvec" and "y \<sharp> Tvec" and "y \<sharp> P" and "x \<noteq> y"
                    and "\<tau>.(P) = \<lparr>\<nu>y\<rparr>(((nameTerm y)\<lparr>\<lambda>*([]) (nameTerm y)\<rparr>.\<zero>) \<parallel> ((nameTerm y)\<langle>(nameTerm y)\<rangle>.(P)))"
    by(rule_tac C="(xvec, Tvec, P[xvec::=Tvec], x)" in tauActionUnfold) auto
  ultimately show ?thesis using assms
    by(auto simp add: psi.inject alpha eqvts calc_atm psi.inject input.inject subst4)
qed

lemma tauFresh[simp]:
  fixes P :: "('a, 'b, 'c) psi"
  and   x :: name

  shows "x \<sharp> \<tau>.(P) = x \<sharp> P"
proof -
  obtain y::name where "y \<noteq> x" and "y \<sharp> P" and "\<tau>.(P) = \<lparr>\<nu>y\<rparr>(((nameTerm y)\<lparr>\<lambda>*([]) (nameTerm y)\<rparr>.\<zero>) \<parallel> ((nameTerm y)\<langle>(nameTerm y)\<rangle>.P))"
    by(rule_tac C=x in tauActionUnfold) auto

  thus ?thesis by(auto simp add: abs_fresh)
qed

lemma tauFreshChain[simp]:
  fixes P    :: "('a, 'b, 'c) psi"
  and   xvec :: "name list"

  shows "xvec \<sharp>* (\<tau>.(P)) = (xvec \<sharp>* P)"
by(induct xvec) auto

lemma guardedTau:
  fixes P :: "('a, 'b, 'c) psi"

  shows "guarded(\<tau>.(P))"
proof -
  obtain x::name where "x \<sharp> P" and "\<tau>.(P) = \<lparr>\<nu>x\<rparr>(((nameTerm x)\<lparr>\<lambda>*([]) (nameTerm x)\<rparr>.\<zero>) \<parallel> ((nameTerm x)\<langle>(nameTerm x)\<rangle>.P))"
    by(rule_tac C="()" in tauActionUnfold) auto

  thus ?thesis by auto
qed

lemma tauChainBisim:
  fixes \<Psi>  :: 'b
  and   P   :: "('a, 'b, 'c) psi"
  and   P'  :: "('a, 'b, 'c) psi"
  and   P'' :: "('a, 'b, 'c) psi"
  
  assumes "\<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'"
  and     "\<Psi> \<rhd> P \<sim> P''"

  obtains P''' where "\<Psi> \<rhd> P'' \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'''" and "\<Psi> \<rhd> P' \<sim> P'''"
using assms
proof(induct arbitrary: thesis rule: tauChainInduct)
  case(TauBase P)
  thus ?case by auto
next
  case(TauStep P P' P''')
  from \<open>\<Psi> \<rhd> P \<sim> P''\<close> obtain P'''' where P''Chain: "\<Psi> \<rhd> P'' \<Longrightarrow>\<^sup>^\<^sub>\<tau> P''''" and "\<Psi> \<rhd> P' \<sim> P''''"
    by(rule_tac TauStep) auto
  from \<open>\<Psi> \<rhd> P' \<sim> P''''\<close> \<open>\<Psi> \<rhd> P' \<longmapsto>\<tau> \<prec> P'''\<close> 
  obtain P''''' where P''''Trans: "\<Psi> \<rhd> P'''' \<longmapsto>\<tau> \<prec> P'''''" and "\<Psi> \<rhd> P''' \<sim> P'''''"
    apply(drule_tac bisimE(4))
    apply(drule_tac bisimE(2))
    apply(drule_tac simE)
    apply auto
    apply(drule_tac bisimE(4))
    by blast
  from P''Chain P''''Trans have "\<Psi> \<rhd> P'' \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'''''" by(drule_tac tauActTauChain) auto
  with \<open>\<Psi> \<rhd> P''' \<sim> P'''''\<close> show ?case
    by(metis TauStep)
qed

lemma tauChainStepCons:
  fixes \<Psi> :: 'b
  and   P  :: "('a, 'b, 'c) psi"
  and   P' :: "('a, 'b, 'c) psi"
  
  assumes PChain: "\<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'"

  obtains P'' where "\<Psi> \<rhd> \<tau>.(P) \<Longrightarrow>\<^sub>\<tau> P''" and "\<Psi> \<rhd> P' \<sim> P''"
proof -
  assume Goal: "\<And>P''. \<lbrakk>\<Psi> \<rhd> \<tau>.(P) \<Longrightarrow>\<^sub>\<tau> P''; \<Psi> \<rhd> P' \<sim> P''\<rbrakk> \<Longrightarrow> thesis"
  obtain P'' where PTrans: "\<Psi> \<rhd> \<tau>.(P) \<longmapsto>\<tau> \<prec> P''" and "\<Psi> \<rhd> P \<sim> P''" using tauActionI
    by auto
  from PChain \<open>\<Psi> \<rhd> P \<sim> P''\<close> obtain P''' where P''Chain: "\<Psi> \<rhd> P'' \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'''" and "\<Psi> \<rhd> P' \<sim> P'''"
    by(rule tauChainBisim)
  from PTrans P''Chain have "\<Psi> \<rhd> \<tau>.(P) \<Longrightarrow>\<^sub>\<tau> P'''" by(drule_tac tauActTauStepChain) auto
  thus ?thesis using \<open>\<Psi> \<rhd> P' \<sim> P'''\<close>
    by(rule Goal)
qed

lemma tauChainCons:
  fixes \<Psi> :: 'b
  and   P  :: "('a, 'b, 'c) psi"
  and   P' :: "('a, 'b, 'c) psi"
  
  assumes "\<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'"

  obtains P'' where "\<Psi> \<rhd> \<tau>.(P) \<Longrightarrow>\<^sup>^\<^sub>\<tau> P''" and "\<Psi> \<rhd> P' \<sim> P''"
proof -
  assume Goal: "\<And>P''. \<lbrakk>\<Psi> \<rhd> \<tau>.(P) \<Longrightarrow>\<^sup>^\<^sub>\<tau> P''; \<Psi> \<rhd> P' \<sim> P''\<rbrakk> \<Longrightarrow> thesis"  
  from assms obtain P'' where "\<Psi> \<rhd> \<tau>.(P) \<Longrightarrow>\<^sub>\<tau> P''" and "\<Psi> \<rhd> P' \<sim> P''"
    by(rule tauChainStepCons)
  thus ?thesis by(rule_tac Goal) auto
qed
  
lemma weakTransitionTau:
  fixes \<Psi>   :: 'b
  and   Q    :: "('a, 'b, 'c) psi"
  and   P    :: "('a, 'b, 'c) psi"
  and   \<alpha>    :: "'a action"
  and   P'   :: "('a, 'b, 'c) psi"

  assumes PTrans: "\<Psi> : Q \<rhd> P \<Longrightarrow>\<alpha> \<prec> P'"
  and     "bn \<alpha> \<sharp>* \<Psi>"
  and     "bn \<alpha> \<sharp>* P"

  obtains P'' where "\<Psi> : Q \<rhd> \<tau>.(P) \<Longrightarrow>\<alpha> \<prec> P''" and "\<Psi> \<rhd> P' \<sim> P''"
proof -
  assume Goal: "\<And>P''. \<lbrakk>\<Psi> : Q \<rhd> \<tau>.(P) \<Longrightarrow>\<alpha> \<prec> P''; \<Psi> \<rhd> P' \<sim> P''\<rbrakk> \<Longrightarrow> thesis"
  from PTrans obtain P'' where PChain: "\<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P''"
                           and QimpP'': "insertAssertion (extractFrame Q) \<Psi> \<hookrightarrow>\<^sub>F insertAssertion(extractFrame P'') \<Psi>"
                           and P''Trans: "\<Psi> \<rhd> P'' \<longmapsto>\<alpha> \<prec> P'"
    by(blast dest: weakTransitionE)

  from PChain obtain P''' where tPChain: "\<Psi> \<rhd> \<tau>.(P) \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'''" and "\<Psi> \<rhd> P'' \<sim> P'''" by(rule tauChainCons)
  moreover from QimpP'' \<open>\<Psi> \<rhd> P'' \<sim> P'''\<close> have "insertAssertion (extractFrame Q) \<Psi> \<hookrightarrow>\<^sub>F insertAssertion(extractFrame P''') \<Psi>"
    by(metis bisimE FrameStatEq_def FrameStatImpTrans)
  moreover from tPChain \<open>bn \<alpha> \<sharp>* P\<close> have "bn \<alpha> \<sharp>* P'''" by(force intro: tauChainFreshChain)
  with \<open>\<Psi> \<rhd> P'' \<sim> P'''\<close> P''Trans \<open>bn \<alpha> \<sharp>* \<Psi>\<close> obtain P'''' where "\<Psi> \<rhd> P''' \<longmapsto>\<alpha> \<prec> P''''" and "\<Psi> \<rhd> P' \<sim> P''''"
    by(metis bisimE simE)
  ultimately show ?thesis
    by(rule_tac Goal) (blast intro: weakTransitionI)
qed                          

end

end
