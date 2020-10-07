(* 
   Title: The pi-calculus   
   Author/Maintainer: Jesper Bengtson (jebe.dk), 2012
*)
theory Strong_Late_Sim_SC
  imports Strong_Late_Sim
begin

(************** Zero **********************)

lemma nilSim[dest]:
  fixes a :: name
  and   b :: name
  and   x :: name
  and   P :: pi
  and   Q :: pi

  shows "\<zero> \<leadsto>[Rel] \<tau>.(P) \<Longrightarrow> False"
  and   "\<zero> \<leadsto>[Rel] a<x>.P \<Longrightarrow> False"
  and   "\<zero> \<leadsto>[Rel] a{b}.P \<Longrightarrow> False"
by(fastforce simp add: simulation_def intro: Tau Input Output)+

lemma nilSimRight:
  fixes P   :: pi
  and   Rel :: "(pi \<times> pi) set"

  shows "P \<leadsto>[Rel] \<zero>"
by(auto simp add: simulation_def)

(************** Match *********************)

lemma matchIdLeft:
  fixes a   :: name
  and   P   :: pi
  and   Rel :: "(pi \<times> pi) set"

  assumes "Id \<subseteq> Rel"

  shows "[a\<frown>a]P \<leadsto>[Rel] P"
using assms
by(force simp add: simulation_def dest: Match derivativeReflexive)

lemma matchIdRight:
  fixes P   :: pi
  and   a   :: name
  and   Rel :: "(pi \<times> pi) set"

  assumes IdRel: "Id \<subseteq> Rel"

  shows "P \<leadsto>[Rel] [a\<frown>a]P"
using assms
by(fastforce simp add: simulation_def elim: matchCases intro: derivativeReflexive)

lemma matchNilLeft:
  fixes a :: name
  and   b :: name
  and   P :: pi

  assumes "a \<noteq> b"
  
  shows "\<zero> \<leadsto>[Rel] [a\<frown>b]P"
using assms
by(auto simp add: simulation_def)

(************** Mismatch *********************)

lemma mismatchIdLeft:
  fixes a   :: name
  and   b   :: name
  and   P   :: pi
  and   Rel :: "(pi \<times> pi) set"

  assumes "Id \<subseteq> Rel"
  and     "a \<noteq> b"

  shows "[a\<noteq>b]P \<leadsto>[Rel] P"
using assms
by(fastforce simp add: simulation_def intro: Mismatch dest: derivativeReflexive)

lemma mismatchIdRight:
  fixes P   :: pi
  and   a   :: name
  and   b   :: name
  and   Rel :: "(pi \<times> pi) set"

  assumes IdRel: "Id \<subseteq> Rel"
  and     aineqb: "a \<noteq> b"

  shows "P \<leadsto>[Rel] [a\<noteq>b]P"
using assms
by(fastforce simp add: simulation_def elim: mismatchCases intro: derivativeReflexive)

lemma mismatchNilLeft:
  fixes a :: name
  and   P :: pi
  
  shows "\<zero> \<leadsto>[Rel] [a\<noteq>a]P"
by(auto simp add: simulation_def)

(************** +-operator *****************)

lemma sumSym:
  fixes P   :: pi
  and   Q   :: pi
  and   Rel :: "(pi \<times> pi) set"

  assumes Id: "Id \<subseteq> Rel"
  
  shows "P \<oplus> Q \<leadsto>[Rel] Q \<oplus> P"
using assms
by(fastforce simp add: simulation_def elim: sumCases intro: Sum1 Sum2 derivativeReflexive)

lemma sumIdempLeft:
  fixes P :: pi
  and Rel :: "(pi \<times> pi) set"

  assumes "Id \<subseteq> Rel"

  shows "P \<leadsto>[Rel] P \<oplus> P"
using assms
by(fastforce simp add: simulation_def elim: sumCases intro: derivativeReflexive)

lemma sumIdempRight:
  fixes P :: pi
  and Rel :: "(pi \<times> pi) set"

  assumes I: "Id \<subseteq> Rel"

  shows "P \<oplus> P \<leadsto>[Rel] P"
using assms
by(fastforce simp add: simulation_def intro: Sum1 derivativeReflexive)

lemma sumAssocLeft:
  fixes P   :: pi
  and   Q   :: pi
  and   R   :: pi
  and   Rel :: "(pi \<times> pi) set"

  assumes Id: "Id \<subseteq> Rel"

  shows "(P \<oplus> Q) \<oplus> R \<leadsto>[Rel] P \<oplus> (Q \<oplus> R)"
using assms
by(fastforce simp add: simulation_def elim: sumCases intro: Sum1 Sum2 derivativeReflexive)

lemma sumAssocRight:
  fixes P   :: pi
  and   Q   :: pi
  and   R   :: pi
  and   Rel :: "(pi \<times> pi) set"

  assumes Id: "Id \<subseteq> Rel"

  shows "P \<oplus> (Q \<oplus> R) \<leadsto>[Rel] (P \<oplus> Q) \<oplus> R"
using assms
by(fastforce simp add: simulation_def elim: sumCases intro: Sum1 Sum2 derivativeReflexive)

lemma sumZeroLeft:
  fixes P   :: pi
  and   Rel :: "(pi \<times> pi) set"

  assumes Id: "Id \<subseteq> Rel"

  shows "P \<oplus> \<zero> \<leadsto>[Rel] P"
using assms
by(fastforce simp add: simulation_def intro: Sum1 derivativeReflexive)

lemma sumZeroRight:
  fixes P   :: pi
  and   Rel :: "(pi \<times> pi) set"

  assumes Id: "Id \<subseteq> Rel"

  shows "P \<leadsto>[Rel] P \<oplus> \<zero>"
using assms
by(fastforce simp add: simulation_def elim: sumCases intro: derivativeReflexive)

lemma sumResLeft:
  fixes x   :: name
  and   P   :: pi
  and   Q   :: pi

  assumes Id: "Id \<subseteq> Rel"
  and     Eqvt: "eqvt Rel"

  shows "(<\<nu>x>P) \<oplus> (<\<nu>x>Q) \<leadsto>[Rel] <\<nu>x>(P \<oplus> Q)"
using Eqvt
proof(induct rule: simCasesCont[where C="(x, P, Q)"])
  case(Bound a y PQ)
  from \<open>y \<sharp> (x, P, Q)\<close> have "y \<noteq> x" and "y \<sharp> P" and "y \<sharp> Q" by(simp add: fresh_prod)+
  hence "y \<sharp> P \<oplus> Q" by simp
  with \<open><\<nu>x>(P \<oplus> Q) \<longmapsto>a\<guillemotleft>y\<guillemotright> \<prec> PQ\<close> \<open>y \<noteq> x\<close> show ?case
  proof(induct rule: resCasesB)
    case(cOpen a PQ)
    from \<open>P \<oplus> Q \<longmapsto>a[x] \<prec> PQ\<close> \<open>y \<sharp> P\<close> \<open>y \<sharp> Q\<close> have "y \<sharp> PQ" by(force dest: freshFreeDerivative)
    from \<open>P \<oplus> Q \<longmapsto>a[x] \<prec> PQ\<close> show ?case
    proof(induct rule: sumCases)
      case cSum1
      from \<open>P \<longmapsto>a[x] \<prec> PQ\<close> \<open>a \<noteq> x\<close> have "<\<nu>x>P \<longmapsto>a<\<nu>x> \<prec> PQ" by(rule Open)
      hence "(<\<nu>x>P) \<oplus> (<\<nu>x>Q) \<longmapsto>a<\<nu>x> \<prec> PQ" by(rule Sum1)
      with \<open>y \<sharp> PQ\<close> have "(<\<nu>x>P) \<oplus> (<\<nu>x>Q) \<longmapsto>a<\<nu>y> \<prec> ([(y, x)] \<bullet> PQ)" 
        by(simp add: alphaBoundResidual)
      moreover from Id have "derivative ([(y, x)] \<bullet> PQ) ([(y, x)] \<bullet> PQ) (BoundOutputS a) y Rel"
        by(force simp add: derivative_def)
      ultimately show ?case by blast
    next
      case cSum2
      from \<open>Q \<longmapsto>a[x] \<prec> PQ\<close> \<open>a \<noteq> x\<close> have "<\<nu>x>Q \<longmapsto>a<\<nu>x> \<prec> PQ" by(rule Open)
      hence "(<\<nu>x>P) \<oplus> (<\<nu>x>Q) \<longmapsto>a<\<nu>x> \<prec> PQ" by(rule Sum2)
      with \<open>y \<sharp> PQ\<close> have "(<\<nu>x>P) \<oplus> (<\<nu>x>Q) \<longmapsto>a<\<nu>y> \<prec> ([(y, x)] \<bullet> PQ)" 
        by(simp add: alphaBoundResidual)
      moreover from Id have "derivative ([(y, x)] \<bullet> PQ) ([(y, x)] \<bullet> PQ) (BoundOutputS a) y Rel"
        by(force simp add: derivative_def)
      ultimately show ?case by blast
    qed
  next
    case(cRes PQ)
    from \<open>P \<oplus> Q \<longmapsto>a\<guillemotleft>y\<guillemotright> \<prec> PQ\<close> show ?case
    proof(induct rule: sumCases)
      case cSum1
      from \<open>P \<longmapsto>a\<guillemotleft>y\<guillemotright> \<prec> PQ\<close> \<open>x \<sharp> a\<close> \<open>y \<noteq> x\<close> have "<\<nu>x>P \<longmapsto>a\<guillemotleft>y\<guillemotright> \<prec> <\<nu>x>PQ" by(rule_tac ResB) auto
      hence "(<\<nu>x>P) \<oplus> (<\<nu>x>Q) \<longmapsto>a\<guillemotleft>y\<guillemotright> \<prec> <\<nu>x>PQ" by(rule Sum1)
      moreover from Id have "derivative (<\<nu>x>PQ) (<\<nu>x>PQ) a y Rel"
        by(cases a) (auto simp add: derivative_def)
      ultimately show ?case by blast
    next
      case cSum2
      from \<open>Q \<longmapsto>a\<guillemotleft>y\<guillemotright> \<prec> PQ\<close> \<open>x \<sharp> a\<close> \<open>y \<noteq> x\<close> have "<\<nu>x>Q \<longmapsto>a\<guillemotleft>y\<guillemotright> \<prec> <\<nu>x>PQ" by(rule_tac ResB) auto
      hence "(<\<nu>x>P) \<oplus> (<\<nu>x>Q) \<longmapsto>a\<guillemotleft>y\<guillemotright> \<prec> <\<nu>x>PQ" by(rule Sum2)
      moreover from Id have "derivative (<\<nu>x>PQ) (<\<nu>x>PQ) a y Rel"
        by(cases a) (auto simp add: derivative_def)
      ultimately show ?case by blast
    qed
  qed
next
  case(Free \<alpha> PQ)
  from \<open><\<nu>x>(P \<oplus> Q) \<longmapsto>\<alpha> \<prec> PQ\<close> show ?case
  proof(induct rule: resCasesF)
    case(cRes PQ)
    from \<open>P \<oplus> Q \<longmapsto>\<alpha> \<prec> PQ\<close> show ?case
    proof(induct rule: sumCases)
      case cSum1 
      from \<open>P \<longmapsto>\<alpha> \<prec> PQ\<close> \<open>x \<sharp> \<alpha>\<close> have "<\<nu>x>P \<longmapsto>\<alpha> \<prec> <\<nu>x>PQ" by(rule ResF)
      hence "(<\<nu>x>P) \<oplus> (<\<nu>x>Q) \<longmapsto>\<alpha> \<prec> <\<nu>x>PQ" by(rule Sum1)
      with Id show ?case by blast
    next
      case cSum2
      from \<open>Q \<longmapsto>\<alpha> \<prec> PQ\<close> \<open>x \<sharp> \<alpha>\<close> have "<\<nu>x>Q \<longmapsto>\<alpha> \<prec> <\<nu>x>PQ" by(rule ResF)
      hence "(<\<nu>x>P) \<oplus> (<\<nu>x>Q) \<longmapsto>\<alpha> \<prec> <\<nu>x>PQ" by(rule Sum2)
      with Id show ?case by blast
    qed
  qed
qed

lemma sumResRight:
  fixes x   :: name
  and   P   :: pi
  and   Q   :: pi

  assumes Id: "Id \<subseteq> Rel"
  and     Eqvt: "eqvt Rel"

  shows "<\<nu>x>(P \<oplus> Q) \<leadsto>[Rel] (<\<nu>x>P) \<oplus> (<\<nu>x>Q)"
using \<open>eqvt Rel\<close>
proof(induct rule: simCasesCont[where C="(x, P, Q)"])
  case(Bound a y PQ)
  from \<open>y \<sharp> (x, P, Q)\<close> have "y \<noteq> x" and "y \<sharp> P" and "y \<sharp> Q" by(simp add: fresh_prod)+
  from \<open>(<\<nu>x>P) \<oplus> (<\<nu>x>Q) \<longmapsto>a\<guillemotleft>y\<guillemotright> \<prec> PQ\<close> show ?case
  proof(induct rule: sumCases)
    case cSum1
    from \<open><\<nu>x>P \<longmapsto>a\<guillemotleft>y\<guillemotright> \<prec> PQ\<close> show ?case using \<open>y \<noteq> x\<close> \<open>y \<sharp> P\<close>
    proof(induct rule: resCasesB)
      case(cOpen a P')
      from \<open>P \<longmapsto>a[x] \<prec> P'\<close> \<open>y \<sharp> P\<close> have "y \<sharp> P'" by(rule freshFreeDerivative)
      
      from \<open>P \<longmapsto>a[x] \<prec> P'\<close> have "P \<oplus> Q \<longmapsto>a[x] \<prec> P'" by(rule Sum1)
      hence "<\<nu>x>(P \<oplus> Q) \<longmapsto>a<\<nu>x> \<prec> P'" using \<open>a \<noteq> x\<close> by(rule Open)
      with \<open>y \<sharp> P'\<close> have "<\<nu>x>(P \<oplus> Q) \<longmapsto>a<\<nu>y> \<prec> [(y, x)] \<bullet> P'" by(simp add: alphaBoundResidual)
      moreover from Id have "derivative ([(y, x)] \<bullet> P') ([(y, x)] \<bullet> P') (BoundOutputS a) y Rel"
        by(force simp add: derivative_def)
      ultimately show ?case by blast
    next
      case(cRes P')
      from \<open>P \<longmapsto>a\<guillemotleft>y\<guillemotright> \<prec> P'\<close> have "P \<oplus> Q \<longmapsto>a\<guillemotleft>y\<guillemotright> \<prec> P'" by(rule Sum1)
      hence "<\<nu>x>(P \<oplus> Q) \<longmapsto>a\<guillemotleft>y\<guillemotright> \<prec> <\<nu>x>P'" using \<open>x \<sharp> a\<close> \<open>y \<noteq> x\<close> by(rule_tac ResB) auto
      moreover from Id have "derivative (<\<nu>x>P') (<\<nu>x>P') a y Rel"
        by(cases a) (auto simp add: derivative_def)
      ultimately show ?case by blast
    qed
  next
    case cSum2
    from \<open><\<nu>x>Q \<longmapsto>a\<guillemotleft>y\<guillemotright> \<prec> PQ\<close> show ?case using \<open>y \<noteq> x\<close> \<open>y \<sharp> Q\<close>
    proof(induct rule: resCasesB)
      case(cOpen a Q')
      from \<open>Q \<longmapsto>a[x] \<prec> Q'\<close> \<open>y \<sharp> Q\<close> have "y \<sharp> Q'" by(rule freshFreeDerivative)
      
      from \<open>Q \<longmapsto>a[x] \<prec> Q'\<close> have "P \<oplus> Q \<longmapsto>a[x] \<prec> Q'" by(rule Sum2)
      hence "<\<nu>x>(P \<oplus> Q) \<longmapsto>a<\<nu>x> \<prec> Q'" using \<open>a \<noteq> x\<close> by(rule Open)
      with \<open>y \<sharp> Q'\<close> have "<\<nu>x>(P \<oplus> Q) \<longmapsto>a<\<nu>y> \<prec> [(y, x)] \<bullet> Q'" by(simp add: alphaBoundResidual)
      moreover from Id have "derivative ([(y, x)] \<bullet> Q') ([(y, x)] \<bullet> Q') (BoundOutputS a) y Rel"
        by(force simp add: derivative_def)
      ultimately show ?case by blast
    next
      case(cRes Q')
      from \<open>Q \<longmapsto>a\<guillemotleft>y\<guillemotright> \<prec> Q'\<close> have "P \<oplus> Q \<longmapsto>a\<guillemotleft>y\<guillemotright> \<prec> Q'" by(rule Sum2)
      hence "<\<nu>x>(P \<oplus> Q) \<longmapsto>a\<guillemotleft>y\<guillemotright> \<prec> <\<nu>x>Q'" using \<open>x \<sharp> a\<close> \<open>y \<noteq> x\<close> by(rule_tac ResB) auto
      moreover from Id have "derivative (<\<nu>x>Q') (<\<nu>x>Q') a y Rel"
        by(cases a) (auto simp add: derivative_def)
      ultimately show ?case by blast
    qed
  qed
next
  case(Free \<alpha> PQ)
  from \<open>(<\<nu>x>P) \<oplus> (<\<nu>x>Q) \<longmapsto>\<alpha> \<prec> PQ\<close> show ?case
  proof(induct rule: sumCases)
    case cSum1
    from \<open><\<nu>x>P \<longmapsto>\<alpha> \<prec> PQ\<close> show ?case
    proof(induct rule: resCasesF)
      case(cRes P')
      from \<open>P \<longmapsto>\<alpha> \<prec> P'\<close> have "P \<oplus> Q \<longmapsto>\<alpha> \<prec> P'" by(rule Sum1)
      hence "<\<nu>x>(P \<oplus> Q) \<longmapsto>\<alpha> \<prec> <\<nu>x>P'" using \<open>x \<sharp> \<alpha>\<close> by(rule ResF)
      with Id show ?case by blast
    qed
  next
    case cSum2
    from \<open><\<nu>x>Q \<longmapsto>\<alpha> \<prec> PQ\<close> show ?case
    proof(induct rule: resCasesF)
      case(cRes Q')
      from \<open>Q \<longmapsto>\<alpha> \<prec> Q'\<close> have "P \<oplus> Q \<longmapsto>\<alpha> \<prec> Q'" by(rule Sum2)
      hence "<\<nu>x>(P \<oplus> Q) \<longmapsto>\<alpha> \<prec> <\<nu>x>Q'" using \<open>x \<sharp> \<alpha>\<close> by(rule ResF)
      with Id show ?case by blast
    qed
  qed
qed

(************** |-operator *************)

lemma parZeroLeft:
  fixes P   :: pi
  and   Rel :: "(pi \<times> pi) set"

  assumes ParZero: "\<And>Q. (Q \<parallel> \<zero>, Q) \<in> Rel"

  shows "P \<parallel> \<zero> \<leadsto>[Rel] P"
proof -
  {
    fix P Q a x
    from ParZero have "derivative (P \<parallel> \<zero>) P a x Rel"
      by(case_tac a) (auto simp add: derivative_def)
  }
  thus ?thesis using assms
    by(fastforce simp add: simulation_def intro: Par1B Par1F)
qed

lemma parZeroRight:
  fixes P   :: pi
  and   Rel :: "(pi \<times> pi) set"

  assumes ParZero: "\<And>Q. (Q, Q \<parallel> \<zero>) \<in> Rel"

  shows "P \<leadsto>[Rel] P \<parallel> \<zero>"
proof -
  {
    fix P Q a x
    from ParZero have "derivative P (P \<parallel> \<zero>) a x Rel"
      by(case_tac a) (auto simp add: derivative_def)
  }
  thus ?thesis using assms
    by(fastforce simp add: simulation_def elim: parCasesF parCasesB)+
qed
  
lemma parSym:
  fixes P    :: pi
  and   Q    :: pi
  and   Rel  :: "(pi \<times> pi) set"
  
  assumes Sym: "\<And>R S. (R \<parallel> S, S \<parallel> R) \<in> Rel"
  and     Res: "\<And>R S x. (R, S) \<in> Rel \<Longrightarrow> (<\<nu>x>R, <\<nu>x>S) \<in> Rel"
  
  shows "P \<parallel> Q \<leadsto>[Rel] Q \<parallel> P"
proof(induct rule: simCases)
  case(Bound a x QP)
  from \<open>x \<sharp> (P \<parallel> Q)\<close> have "x \<sharp> Q" and "x \<sharp> P" by simp+
  with \<open>Q \<parallel> P \<longmapsto> a\<guillemotleft>x\<guillemotright> \<prec> QP\<close> show ?case
  proof(induct rule: parCasesB)
    case(cPar1 Q')
    from \<open>Q \<longmapsto>a\<guillemotleft>x\<guillemotright> \<prec> Q'\<close> have "P \<parallel> Q \<longmapsto>a\<guillemotleft>x\<guillemotright> \<prec> P \<parallel> Q'" using \<open>x \<sharp> P\<close> by(rule Par2B)
    moreover have "derivative (P \<parallel> Q')  (Q' \<parallel> P) a x Rel"
      by(cases a, auto simp add: derivative_def intro: Sym)
    ultimately show ?case by blast
  next
    case(cPar2 P')
    from \<open>P \<longmapsto>a\<guillemotleft>x\<guillemotright> \<prec> P'\<close> have "P \<parallel> Q \<longmapsto>a\<guillemotleft>x\<guillemotright> \<prec> P' \<parallel> Q" using \<open>x \<sharp> Q\<close> by(rule Par1B)
    moreover have "derivative (P' \<parallel> Q)  (Q \<parallel> P') a x Rel"
      by(cases a, auto simp add: derivative_def intro: Sym)
    ultimately show ?case by blast
  qed
next
  case(Free \<alpha> QP)
  from \<open>Q \<parallel> P \<longmapsto> \<alpha> \<prec> QP\<close> show ?case
  proof(induct rule: parCasesF[where C="()"])
    case(cPar1 Q')
    from \<open>Q \<longmapsto> \<alpha> \<prec> Q'\<close> have "P \<parallel> Q \<longmapsto> \<alpha> \<prec> P \<parallel> Q'" by(rule Par2F)
    moreover have "(P \<parallel> Q', Q' \<parallel> P) \<in> Rel" by(rule Sym)
    ultimately show ?case by blast
  next
    case(cPar2 P')
    from \<open>P \<longmapsto> \<alpha> \<prec> P'\<close> have "P \<parallel> Q \<longmapsto> \<alpha> \<prec> P' \<parallel> Q" by(rule Par1F)
    moreover have "(P' \<parallel> Q, Q \<parallel> P') \<in> Rel" by(rule Sym)
    ultimately show ?case by blast
  next
    case(cComm1 Q' P' a b x)
    from \<open>P \<longmapsto>a[b] \<prec> P'\<close> \<open>Q \<longmapsto>a<x> \<prec> Q'\<close>
    have "P \<parallel> Q \<longmapsto> \<tau> \<prec> P' \<parallel> (Q'[x::=b])" by(rule Comm2)
    moreover have "(P' \<parallel> Q'[x::=b], Q'[x::=b] \<parallel> P') \<in> Rel" by(rule Sym)
    ultimately show ?case by blast
  next
    case(cComm2 Q' P' a b x)
    from \<open>P \<longmapsto>a<x> \<prec> P'\<close> \<open>Q \<longmapsto>a[b] \<prec> Q'\<close>
    have "P \<parallel> Q \<longmapsto> \<tau> \<prec> (P'[x::=b]) \<parallel> Q'" by(rule Comm1)
    moreover have "(P'[x::=b] \<parallel> Q', Q' \<parallel> P'[x::=b]) \<in> Rel" by(rule Sym)
    ultimately show ?case by blast
  next
    case(cClose1 Q' P' a x y)
    from \<open>P \<longmapsto> a<\<nu>y> \<prec> P'\<close> \<open>Q \<longmapsto> a<x> \<prec> Q'\<close> \<open>y \<sharp> Q\<close>
    have "P \<parallel> Q \<longmapsto> \<tau> \<prec> <\<nu>y>(P' \<parallel> (Q'[x::=y]))" by(rule Close2)
    moreover have "(<\<nu>y>(P' \<parallel> Q'[x::=y]), <\<nu>y>(Q'[x::=y] \<parallel> P')) \<in> Rel" by(metis Res Sym)
    ultimately show ?case by blast
  next
    case(cClose2 Q' P' a x y)
    from \<open>P \<longmapsto> a<x> \<prec> P'\<close> \<open>Q \<longmapsto> a<\<nu>y> \<prec> Q'\<close> \<open>y \<sharp> P\<close>
    have "P \<parallel> Q \<longmapsto> \<tau> \<prec> <\<nu>y>((P'[x::=y]) \<parallel> Q')" by(rule Close1)
    moreover have "(<\<nu>y>(P'[x::=y] \<parallel> Q'), <\<nu>y>(Q' \<parallel> P'[x::=y])) \<in> Rel" by(metis Res Sym)
    ultimately show ?case by blast
  qed
qed

lemma parAssocLeft:
  fixes P    :: pi
  and   Q    :: pi
  and   R    :: pi
  and   Rel  :: "(pi \<times> pi) set"

  assumes Ass:       "\<And>S T U. ((S \<parallel> T) \<parallel> U, S \<parallel> (T \<parallel> U)) \<in> Rel"
  and     Res:       "\<And>S T x. (S, T) \<in> Rel \<Longrightarrow> (<\<nu>x>S, <\<nu>x>T) \<in> Rel"
  and     FreshExt:  "\<And>S T U x. x \<sharp> S \<Longrightarrow> (<\<nu>x>((S \<parallel> T) \<parallel> U), S \<parallel> <\<nu>x>(T \<parallel> U)) \<in> Rel"
  and     FreshExt': "\<And>S T U x. x \<sharp> U \<Longrightarrow> ((<\<nu>x>(S \<parallel> T)) \<parallel> U, <\<nu>x>(S \<parallel> (T \<parallel> U))) \<in> Rel"

  shows "(P \<parallel> Q) \<parallel> R \<leadsto>[Rel] P \<parallel> (Q \<parallel> R)"
proof(induct rule: simCases)
  case(Bound a x PQR)
  from \<open>x \<sharp> (P \<parallel> Q) \<parallel> R\<close> have "x \<sharp> P" and "x \<sharp> Q" and "x \<sharp> R" by simp+
  hence "x \<sharp> (Q \<parallel> R)" by simp
  with \<open>P \<parallel> (Q \<parallel> R) \<longmapsto> a\<guillemotleft>x\<guillemotright> \<prec> PQR\<close> \<open>x \<sharp> P\<close> show ?case
  proof(induct rule: parCasesB)
    case(cPar1 P')
    from \<open>P \<longmapsto> a\<guillemotleft>x\<guillemotright> \<prec> P'\<close> have "P \<parallel> Q \<longmapsto> a\<guillemotleft>x\<guillemotright> \<prec> P' \<parallel> Q" using \<open>x \<sharp> Q\<close> by(rule Par1B)
    hence "(P \<parallel> Q) \<parallel> R \<longmapsto> a\<guillemotleft>x\<guillemotright> \<prec> (P' \<parallel> Q) \<parallel> R" using \<open>x \<sharp> R\<close> by(rule Par1B)
    moreover have "derivative ((P' \<parallel> Q) \<parallel> R) (P' \<parallel> (Q \<parallel> R)) a x Rel"
      by(cases a, auto intro: Ass simp add: derivative_def)
    ultimately show ?case by blast
  next
    case(cPar2 QR)
    from \<open>Q \<parallel> R \<longmapsto> a\<guillemotleft>x\<guillemotright> \<prec> QR\<close> \<open>x \<sharp> Q\<close> \<open>x \<sharp> R\<close> show ?case
    proof(induct rule: parCasesB)
      case(cPar1 Q')
      from \<open>Q \<longmapsto> a\<guillemotleft>x\<guillemotright> \<prec> Q'\<close> have "P \<parallel> Q \<longmapsto> a\<guillemotleft>x\<guillemotright> \<prec> P \<parallel> Q'" using \<open>x \<sharp> P\<close> by(rule Par2B)
      hence "(P \<parallel> Q) \<parallel> R \<longmapsto> a\<guillemotleft>x\<guillemotright> \<prec> (P \<parallel> Q') \<parallel> R" using \<open>x \<sharp> R\<close>by(rule Par1B)
      moreover have "derivative ((P \<parallel> Q') \<parallel> R) (P \<parallel> (Q' \<parallel> R)) a x Rel"
        by(cases a, auto intro: Ass simp add: derivative_def)
      ultimately show ?case by blast
    next
      case(cPar2 R')
      from \<open>R \<longmapsto> a\<guillemotleft>x\<guillemotright> \<prec> R'\<close> have "(P \<parallel> Q) \<parallel> R \<longmapsto> a\<guillemotleft>x\<guillemotright> \<prec> (P \<parallel> Q) \<parallel> R'" using \<open>x \<sharp> P\<close> \<open>x \<sharp> Q\<close> 
        by(rule_tac Par2B) auto
      moreover have "derivative ((P \<parallel> Q) \<parallel> R') (P \<parallel> (Q \<parallel> R')) a x Rel"
        by(cases a, auto intro: Ass simp add: derivative_def)
      ultimately show ?case by blast
    qed
  qed
next
  case(Free \<alpha> PQR)
  from \<open>P \<parallel> (Q \<parallel> R) \<longmapsto> \<alpha> \<prec> PQR\<close> show ?case
  proof(induct rule: parCasesF[where C="Q"])
    case(cPar1 P')
    from \<open>P \<longmapsto> \<alpha> \<prec> P'\<close> have "P \<parallel> Q \<longmapsto> \<alpha> \<prec> P' \<parallel> Q" by(rule Par1F)
    hence "(P \<parallel> Q) \<parallel> R \<longmapsto> \<alpha> \<prec> (P' \<parallel> Q) \<parallel> R" by(rule Par1F)
    moreover from Ass have "((P' \<parallel> Q) \<parallel> R, P' \<parallel> (Q \<parallel> R)) \<in> Rel" by blast
    ultimately show ?case by blast
  next
    case(cPar2 QR)
    from \<open>Q \<parallel> R \<longmapsto> \<alpha> \<prec> QR\<close> show ?case
    proof(induct rule: parCasesF[where C="P"])
      case(cPar1 Q')
      from \<open>Q \<longmapsto> \<alpha> \<prec> Q'\<close> have "(P \<parallel> Q) \<longmapsto> \<alpha> \<prec> P \<parallel> Q'" by(rule Par2F)
      hence "(P \<parallel> Q) \<parallel> R \<longmapsto> \<alpha> \<prec> (P \<parallel> Q') \<parallel> R" by(rule Par1F)
      moreover from Ass have "((P \<parallel> Q') \<parallel> R, P \<parallel> (Q' \<parallel> R)) \<in> Rel" by blast
      ultimately show ?case by blast
    next
      case(cPar2 R')
      from \<open>R \<longmapsto> \<alpha> \<prec> R'\<close> have "(P \<parallel> Q) \<parallel> R \<longmapsto> \<alpha> \<prec> (P \<parallel> Q) \<parallel> R'" by(rule Par2F)
      moreover from Ass have "((P \<parallel> Q) \<parallel> R', P \<parallel> (Q \<parallel> R')) \<in> Rel" by blast
      ultimately show ?case by blast
    next
      case(cComm1 Q' R' a b x)
      from \<open>Q \<longmapsto>a<x> \<prec> Q'\<close> \<open>x \<sharp> P\<close> have "P \<parallel> Q \<longmapsto>a<x> \<prec> P \<parallel> Q'" by(rule Par2B)
      hence "(P \<parallel> Q) \<parallel> R \<longmapsto> \<tau> \<prec> (P \<parallel> Q')[x::=b] \<parallel> R'" using \<open>R \<longmapsto>a[b] \<prec> R'\<close> by(rule Comm1)
      with \<open>x \<sharp> P\<close> have "(P \<parallel> Q) \<parallel> R \<longmapsto> \<tau> \<prec> (P \<parallel> (Q'[x::=b])) \<parallel> R'" by(simp add: forget)
      moreover from Ass have "((P \<parallel> (Q'[x::=b])) \<parallel> R', P \<parallel> (Q'[x::=b] \<parallel> R')) \<in> Rel" by blast
      ultimately show ?case by blast
    next
      case(cComm2 Q' R' a b x)
      from \<open>Q \<longmapsto>a[b] \<prec> Q'\<close> have "P \<parallel> Q \<longmapsto>a[b] \<prec> P \<parallel> Q'" by(rule Par2F)
      with \<open>x \<sharp> P\<close> \<open>x \<sharp> Q\<close> \<open>R \<longmapsto>a<x> \<prec> R'\<close> have "(P \<parallel> Q) \<parallel> R \<longmapsto> \<tau> \<prec> (P \<parallel> Q') \<parallel> R'[x::=b]"
        by(force intro: Comm2)
      moreover from Ass have "((P \<parallel> Q') \<parallel> R'[x::=b], P \<parallel> (Q' \<parallel> R'[x::=b])) \<in> Rel" by blast
      ultimately show ?case by blast
    next
      case(cClose1 Q' R' a x y)
      from \<open>Q \<longmapsto>a<x> \<prec> Q'\<close> \<open>x \<sharp> P\<close> have "P \<parallel> Q \<longmapsto>a<x> \<prec> P \<parallel> Q'" by(rule Par2B)
      with \<open>y \<sharp> P\<close> \<open>y \<sharp> Q\<close> \<open>x \<sharp> P\<close> \<open>R \<longmapsto>a<\<nu>y> \<prec> R'\<close> have "(P \<parallel> Q) \<parallel> R \<longmapsto> \<tau> \<prec> <\<nu>y>((P \<parallel> Q')[x::=y] \<parallel> R')"
        by(rule_tac Close1) auto
      with \<open>x \<sharp> P\<close> have "(P \<parallel> Q) \<parallel> R \<longmapsto> \<tau> \<prec> <\<nu>y>((P \<parallel> (Q'[x::=y])) \<parallel> R')" by(simp add: forget)
      moreover from \<open>y \<sharp> P\<close> have "(<\<nu>y>((P \<parallel> Q'[x::=y]) \<parallel> R'), P \<parallel> <\<nu>y>(Q'[x::=y] \<parallel> R')) \<in> Rel"
        by(rule FreshExt)
      ultimately show ?case by blast
    next
      case(cClose2 Q' R' a x y)
      from \<open>Q \<longmapsto>a<\<nu>y> \<prec> Q'\<close> \<open>y \<sharp> P\<close> have "P \<parallel> Q \<longmapsto>a<\<nu>y> \<prec> P \<parallel> Q'" by(rule Par2B)
      hence Act: "(P \<parallel> Q) \<parallel> R \<longmapsto> \<tau> \<prec> <\<nu>y>((P \<parallel> Q') \<parallel> R'[x::=y])" using \<open>R \<longmapsto>a<x> \<prec> R'\<close> \<open>y \<sharp> R\<close> by(rule Close2)
      moreover from \<open>y \<sharp> P\<close> have "(<\<nu>y>((P \<parallel> Q') \<parallel> R'[x::=y]), P \<parallel> <\<nu>y>(Q' \<parallel> R'[x::=y])) \<in> Rel"
        by(rule FreshExt)
      ultimately show ?case by blast
    qed
  next
    case(cComm1 P' QR a b x)
    from \<open>Q \<parallel> R \<longmapsto> a[b] \<prec> QR\<close> show ?case
    proof(induct rule: parCasesF[where C="()"])
      case(cPar1 Q')
      from \<open>P \<longmapsto>a<x> \<prec> P'\<close> \<open>Q \<longmapsto>a[b] \<prec> Q'\<close> have "P \<parallel> Q \<longmapsto> \<tau> \<prec> P'[x::=b] \<parallel> Q'" by(rule Comm1)
      hence "(P \<parallel> Q) \<parallel> R \<longmapsto> \<tau> \<prec> (P'[x::=b] \<parallel> Q') \<parallel> R" by(rule Par1F)
      moreover from Ass have "((P'[x::=b] \<parallel> Q') \<parallel> R, P'[x::=b] \<parallel> (Q' \<parallel> R)) \<in> Rel" by blast
      ultimately show ?case by blast
    next
      case(cPar2 R')
      from \<open>P \<longmapsto>a<x> \<prec> P'\<close> \<open>x \<sharp> Q\<close> have "P \<parallel> Q \<longmapsto> a<x> \<prec> P' \<parallel> Q" by(rule Par1B)
      hence "(P \<parallel> Q) \<parallel> R \<longmapsto> \<tau> \<prec> (P' \<parallel> Q)[x::=b] \<parallel> R'" using \<open>R \<longmapsto> a[b] \<prec> R'\<close> by(rule Comm1)
      with \<open>x \<sharp> Q\<close> have "(P \<parallel> Q) \<parallel> R \<longmapsto> \<tau> \<prec> (P'[x::=b] \<parallel> Q) \<parallel> R'" by(simp add: forget)
      moreover from Ass have "((P'[x::=b] \<parallel> Q) \<parallel> R', P'[x::=b] \<parallel> (Q \<parallel> R')) \<in> Rel" by blast
      ultimately show ?case by blast
    next
      case(cComm1 Q' R')
      from \<open>a[b] = \<tau>\<close> have False by simp thus ?case by simp
    next
      case(cComm2 Q' R')
      from \<open>a[b] = \<tau>\<close> have False by simp thus ?case by simp
    next
      case(cClose1 Q' R')
      from \<open>a[b] = \<tau>\<close> have False by simp thus ?case by simp
    next
      case(cClose2 Q' R')
      from \<open>a[b] = \<tau>\<close> have False by simp thus ?case by simp
    qed
  next
    case(cComm2 P' QR a b x)
    from \<open>x \<sharp> Q \<parallel> R\<close> have "x \<sharp> Q" and "x \<sharp> R" by simp+
    with \<open>Q \<parallel> R \<longmapsto> a<x> \<prec> QR\<close> show ?case
    proof(induct rule: parCasesB)
      case(cPar1 Q')
      from \<open>P \<longmapsto>a[b] \<prec> P'\<close> \<open>Q \<longmapsto> a<x> \<prec> Q'\<close> have "P \<parallel> Q \<longmapsto> \<tau> \<prec> P' \<parallel> (Q'[x::=b])" by(rule Comm2)
      hence "(P \<parallel> Q) \<parallel> R \<longmapsto> \<tau> \<prec> (P' \<parallel> Q'[x::=b]) \<parallel> R" by(rule Par1F)
      moreover from Ass have "((P' \<parallel> Q'[x::=b]) \<parallel> R, P' \<parallel> Q'[x::=b] \<parallel> R) \<in> Rel" by blast
      with \<open>x \<sharp> R\<close> have "((P' \<parallel> Q'[x::=b]) \<parallel> R, P' \<parallel> (Q' \<parallel> R)[x::=b]) \<in> Rel" by(force simp add: forget)
      ultimately show ?case by blast
    next
      case(cPar2 R')
      from \<open>P \<longmapsto>a[b] \<prec> P'\<close> have "P \<parallel> Q \<longmapsto> a[b] \<prec> P' \<parallel> Q" by(rule Par1F)
      hence "(P \<parallel> Q) \<parallel> R \<longmapsto> \<tau> \<prec> (P' \<parallel> Q) \<parallel> (R'[x::=b])" using \<open>R \<longmapsto>a<x> \<prec> R'\<close> by (rule Comm2)
      moreover from Ass have "((P' \<parallel> Q) \<parallel> R'[x::=b], P' \<parallel> Q \<parallel> (R'[x::=b])) \<in> Rel" by blast
      hence "((P' \<parallel> Q) \<parallel> R'[x::=b], P' \<parallel> (Q \<parallel> R')[x::=b]) \<in> Rel" using \<open>x \<sharp> Q\<close> by(force simp add: forget)
      ultimately show ?case by blast
    qed
  next
    case(cClose1 P' QR a x y)
    from \<open>x \<sharp> Q \<parallel> R\<close> have "x \<sharp> Q" by simp
    from \<open>y \<sharp> Q \<parallel> R\<close> have "y \<sharp> Q" and "y \<sharp> R" by simp+
    from \<open>Q \<parallel> R \<longmapsto> a<\<nu>y> \<prec> QR\<close> \<open>y \<sharp> Q\<close> \<open>y \<sharp> R\<close> show ?case
    proof(induct rule: parCasesB)
      case(cPar1 Q')
      from \<open>P \<longmapsto>a<x> \<prec> P'\<close> \<open>Q \<longmapsto> a<\<nu>y> \<prec> Q'\<close> \<open>y \<sharp> P\<close> have "P \<parallel> Q \<longmapsto> \<tau> \<prec> <\<nu>y>(P'[x::=y] \<parallel> Q')" by(rule Close1)
      hence "(P \<parallel> Q) \<parallel> R \<longmapsto> \<tau> \<prec> (<\<nu>y>(P'[x::=y] \<parallel> Q')) \<parallel> R" by(rule Par1F)
      moreover from \<open>y \<sharp> R\<close> have "((<\<nu>y>(P'[x::=y] \<parallel> Q')) \<parallel> R, <\<nu>y>(P'[x::=y] \<parallel> Q' \<parallel> R)) \<in> Rel"
        by(rule FreshExt')
      ultimately show ?case by blast
    next
      case(cPar2 R')
      from \<open>P \<longmapsto>a<x> \<prec> P'\<close> \<open>x \<sharp> Q\<close> have "P \<parallel> Q \<longmapsto> a<x> \<prec> P' \<parallel> Q" by(rule Par1B)
      with \<open>R \<longmapsto> a<\<nu>y> \<prec> R'\<close> \<open>y \<sharp> P\<close> \<open>y \<sharp> Q\<close> have "(P \<parallel> Q) \<parallel> R \<longmapsto> \<tau> \<prec> <\<nu>y>((P' \<parallel> Q)[x::=y] \<parallel> R')"
        by(rule_tac Close1) auto
      with \<open>x \<sharp> Q\<close> have "(P \<parallel> Q) \<parallel> R \<longmapsto> \<tau> \<prec> <\<nu>y>((P'[x::=y] \<parallel> Q) \<parallel> R')" by(simp add: forget)
      moreover have "(<\<nu>y>((P'[x::=y] \<parallel> Q) \<parallel> R'), <\<nu>y>(P'[x::=y] \<parallel> (Q \<parallel> R'))) \<in> Rel" by(metis Ass Res)
      ultimately show ?case by blast
    qed
  next
    case(cClose2 P' QR a x y)
    from \<open>y \<sharp> Q \<parallel> R\<close> have "y \<sharp> Q" and "y \<sharp> R" by simp+
    from \<open>x \<sharp> Q \<parallel> R\<close> have "x \<sharp> Q" and "x \<sharp> R" by simp+
    with \<open>Q \<parallel> R \<longmapsto> a<x> \<prec> QR\<close> show ?case
    proof(induct rule: parCasesB)
      case(cPar1 Q')
      from \<open>P \<longmapsto>a<\<nu>y> \<prec> P'\<close> \<open>Q \<longmapsto>a<x> \<prec> Q'\<close> have "P \<parallel> Q \<longmapsto> \<tau> \<prec> <\<nu>y>(P' \<parallel> Q'[x::=y])" using \<open>y \<sharp> Q\<close>
        by(rule Close2)
      hence "(P \<parallel> Q) \<parallel> R \<longmapsto> \<tau> \<prec> (<\<nu>y>(P' \<parallel> Q'[x::=y])) \<parallel> R" by(rule Par1F)
      moreover from \<open>y \<sharp> R\<close> have "((<\<nu>y>(P' \<parallel> Q'[x::=y])) \<parallel> R, <\<nu>y>(P' \<parallel>  (Q'[x::=y] \<parallel> R))) \<in> Rel"
        by(rule FreshExt')
      with \<open>x \<sharp> R\<close> have "((<\<nu>y>(P' \<parallel> Q'[x::=y])) \<parallel> R, <\<nu>y>(P' \<parallel>  (Q' \<parallel> R)[x::=y])) \<in> Rel"
        by(simp add: forget)
      ultimately show ?case by blast
    next
      case(cPar2 R')
      from \<open>P \<longmapsto>a<\<nu>y> \<prec> P'\<close> \<open>y \<sharp> Q\<close> have "P \<parallel> Q \<longmapsto> a<\<nu>y> \<prec> P' \<parallel> Q" by(rule Par1B)
      hence "(P \<parallel> Q) \<parallel> R \<longmapsto> \<tau> \<prec> <\<nu>y>((P' \<parallel> Q) \<parallel> R'[x::=y])" using \<open>R \<longmapsto> a<x> \<prec> R'\<close> \<open>y \<sharp> R\<close> by(rule Close2)
      moreover have "((P' \<parallel> Q) \<parallel> R'[x::=y], P' \<parallel> (Q \<parallel> R'[x::=y])) \<in> Rel" by(rule Ass)
      hence "(<\<nu>y>((P' \<parallel> Q) \<parallel> R'[x::=y]), <\<nu>y>(P' \<parallel> (Q \<parallel> R'[x::=y]))) \<in> Rel" by(rule Res) 
      hence "(<\<nu>y>((P' \<parallel> Q) \<parallel> R'[x::=y]), <\<nu>y>(P' \<parallel> (Q \<parallel> R')[x::=y])) \<in> Rel" using \<open>x \<sharp> Q\<close>
        by(simp add: forget)
      ultimately show ?case by blast
    qed
  qed
qed

lemma substRes3:
  fixes a :: name
  and   P :: pi
  and   x :: name

  shows "(<\<nu>a>P)[x::=a] = <\<nu>x>([(x, a)] \<bullet> P)"
proof -
  have "a \<sharp> <\<nu>a>P" by(simp add: name_fresh_abs)
  hence "(<\<nu>a>P)[x::=a] = [(x, a)] \<bullet> <\<nu>a>P" by(rule injPermSubst[THEN sym])
  thus "(<\<nu>a>P)[x::=a] = <\<nu>x>([(x, a)] \<bullet> P)" by(simp add: name_calc)
qed

lemma scopeExtParLeft:
  fixes P   :: pi
  and   Q   :: pi
  and   a   :: name
  and   lst :: "name list"
  and   Rel :: "(pi \<times> pi) set"

  assumes "x \<sharp> P"
  and     Id:         "Id \<subseteq> Rel"
  and     EqvtRel:    "eqvt Rel"
  and     Res:        "\<And>R S y. y \<sharp> R \<Longrightarrow> (<\<nu>y>(R \<parallel> S), R \<parallel> <\<nu>y>S) \<in> Rel"
  and     ScopeExt:   "\<And>R S y z. y \<sharp> R \<Longrightarrow> (<\<nu>y><\<nu>z>(R \<parallel> S), <\<nu>z>(R \<parallel> <\<nu>y>S)) \<in> Rel"

  shows "<\<nu>x>(P \<parallel> Q) \<leadsto>[Rel] P \<parallel> <\<nu>x>Q"
using \<open>eqvt Rel\<close>
proof(induct rule: simCasesCont[where C="(x, P, Q)"])
  case(Bound a y PxQ)
  from \<open>y \<sharp> (x, P, Q)\<close> have "y \<noteq> x" and "y \<sharp> P" and "y \<sharp> Q" by simp+
  hence "y \<sharp> P" and "y \<sharp> <\<nu>x>Q" by(simp add: abs_fresh)+
  with \<open>P \<parallel> <\<nu>x>Q \<longmapsto> a\<guillemotleft>y\<guillemotright> \<prec> PxQ\<close> show ?case
  proof(induct rule: parCasesB)
    case(cPar1 P')
    from \<open>P \<longmapsto>a\<guillemotleft>y\<guillemotright> \<prec> P'\<close> \<open>x \<sharp> P\<close> \<open>y \<noteq> x\<close> have "x \<sharp> a" and "x \<sharp> P'"
      by(force intro: freshBoundDerivative)+

    from \<open>P \<longmapsto>a\<guillemotleft>y\<guillemotright> \<prec> P'\<close> \<open>y \<sharp> Q\<close> have "P \<parallel> Q \<longmapsto>a\<guillemotleft>y\<guillemotright> \<prec> P' \<parallel> Q" by(rule Par1B)
    with \<open>x \<sharp> a\<close> \<open>y \<noteq> x\<close> have "<\<nu>x>(P \<parallel> Q) \<longmapsto> a\<guillemotleft>y\<guillemotright> \<prec> <\<nu>x>(P' \<parallel> Q)" by(rule_tac ResB) auto
    moreover have "derivative (<\<nu>x>(P' \<parallel> Q)) (P' \<parallel> <\<nu>x>Q) a y Rel"
    proof(cases a, auto simp add: derivative_def)
      fix u

      show "((<\<nu>x>(P' \<parallel> Q))[y::=u],  P'[y::=u] \<parallel>  ((<\<nu>x>Q)[y::=u])) \<in> Rel"
      proof(cases "x=u")
        case True
        have "(<\<nu>x>(P' \<parallel> Q))[y::=x] = <\<nu>y>(([(y, x)] \<bullet> P') \<parallel> ([(y, x)] \<bullet> Q))"
          by(simp add: substRes3)
        moreover from \<open>x \<sharp> P'\<close> have "P'[y::=x] = [(y, x)] \<bullet> P'" by(rule injPermSubst[THEN sym])
        moreover have "(<\<nu>x>Q)[y::=x] = <\<nu>y>([(y, x)] \<bullet> Q)" by(rule substRes3)
        moreover from \<open>x \<sharp> P'\<close> \<open>y \<noteq> x\<close> have "y \<sharp> [(y, x)] \<bullet> P'" by(simp add: name_fresh_left name_calc)
        ultimately show ?thesis using \<open>x = u\<close>by(force intro: Res)
      next
        case False
        with \<open>y \<noteq> x\<close> have "(<\<nu>x>(P' \<parallel> Q))[y::=u] = <\<nu>x>(P'[y::=u] \<parallel> Q[y::=u])"
          by(simp add: fresh_prod name_fresh)
        moreover from \<open>x \<noteq> u\<close> \<open>y \<noteq> x\<close> have "(<\<nu>x>Q)[y::=u] = <\<nu>x>(Q[y::=u])"
          by(simp add: fresh_prod name_fresh)
        moreover from \<open>x \<sharp> P'\<close> \<open>x \<noteq> u\<close> have "x \<sharp> P'[y::=u]" by(simp add: fresh_fact1)
        ultimately show ?thesis by(force intro: Res)
      qed
    next
      from \<open>x \<sharp> P'\<close> show "(<\<nu>x>(P' \<parallel> Q), P' \<parallel> <\<nu>x>Q) \<in> Rel" by(rule Res)
    qed
    
    ultimately show ?case by blast
  next
    case(cPar2 xQ)
    from \<open><\<nu>x>Q \<longmapsto>a\<guillemotleft>y\<guillemotright> \<prec> xQ\<close> \<open>y \<noteq> x\<close> \<open>y \<sharp> Q\<close> show ?case
    proof(induct rule: resCasesB)
      case(cOpen a Q')
      from \<open>Q \<longmapsto>a[x] \<prec> Q'\<close> \<open>y \<sharp> Q\<close> have yFreshQ': "y \<sharp> Q'" by(force intro: freshFreeDerivative)

      from \<open>Q \<longmapsto> a[x] \<prec> Q'\<close> have "P \<parallel> Q \<longmapsto> a[x] \<prec> P \<parallel> Q'" by(rule Par2F)
      hence "<\<nu>x>(P \<parallel> Q) \<longmapsto> a<\<nu>x> \<prec> P \<parallel> Q'" using \<open>a \<noteq> x\<close> by(rule Open)
      with \<open>y \<sharp> P\<close> \<open>y \<sharp> Q'\<close> have "<\<nu>x>(P \<parallel> Q) \<longmapsto> a<\<nu>y> \<prec> [(x, y)] \<bullet> (P \<parallel> Q')"
        by(subst alphaBoundResidual[where x'=x]) (auto simp add: fresh_left calc_atm)
      with \<open>y \<sharp> P\<close> \<open>x \<sharp> P\<close> have "<\<nu>x>(P \<parallel> Q) \<longmapsto> a<\<nu>y> \<prec> P \<parallel> ([(x, y)] \<bullet> Q')"
        by(simp add: name_fresh_fresh)

      moreover have "derivative (P \<parallel> ([(x, y)] \<bullet> Q')) (P \<parallel> ([(y, x)] \<bullet> Q')) (BoundOutputS a) y Rel" using Id
        by(auto simp add: derivative_def name_swap)
         
      ultimately show ?case by blast
    next
      case(cRes Q')

      from \<open>Q \<longmapsto> a\<guillemotleft>y\<guillemotright> \<prec> Q'\<close> \<open>y \<sharp> P\<close> have "P \<parallel> Q \<longmapsto> a\<guillemotleft>y\<guillemotright> \<prec> P \<parallel> Q'" by(rule Par2B)
      hence "<\<nu>x>(P \<parallel> Q) \<longmapsto> a\<guillemotleft>y\<guillemotright> \<prec> <\<nu>x>(P \<parallel> Q')" using \<open>x \<sharp> a\<close> \<open>y \<noteq> x\<close>
        by(rule_tac ResB) auto
      moreover have "derivative (<\<nu>x>(P \<parallel> Q')) (P \<parallel> <\<nu>x>Q') a y Rel"
      proof(cases a, auto simp add: derivative_def)
        fix u
        show "((<\<nu>x>(P \<parallel> Q'))[y::=u],  P[y::=u] \<parallel>  (<\<nu>x>Q')[y::=u]) \<in> Rel"
        proof(cases "x=u")
          case True
          from \<open>x \<sharp> P\<close> \<open>y \<sharp> P\<close> have "(<\<nu>x>(P \<parallel> Q'))[y::=x] = <\<nu>y>(P \<parallel> ([(y, x)] \<bullet> Q'))"
            by(simp add: substRes3 perm_fresh_fresh)
          moreover from \<open>y \<sharp> P\<close> have "P[y::=x] = P" by(simp add: forget)
          moreover have "(<\<nu>x>Q')[y::=x] = <\<nu>y>([(y, x)] \<bullet> Q')" by(rule substRes3)
          ultimately show ?thesis using \<open>x=u\<close> \<open>y \<sharp> P\<close> by(force intro: Res)
        next
          case False
          with \<open>y \<noteq> x\<close> have "(<\<nu>x>(P \<parallel> Q'))[y::=u] = <\<nu>x>((P \<parallel> Q')[y::=u])"
            by(simp add: fresh_prod name_fresh)
          moreover from \<open>y \<noteq> x\<close> \<open>x \<noteq> u\<close> have "(<\<nu>x>Q')[y::=u] = <\<nu>x>(Q'[y::=u])"
            by(simp add: fresh_prod name_fresh)
          moreover from \<open>x \<sharp> P\<close> \<open>x \<noteq> u\<close> have "x \<sharp> P[y::=u]" by(force simp add: fresh_fact1)
          ultimately show ?thesis by(force intro: Res)
        qed
      next
        from \<open>x \<sharp> P\<close> show "(<\<nu>x>(P \<parallel> Q'), P \<parallel> <\<nu>x>Q') \<in> Rel" by(rule Res)
      qed
      ultimately show ?case by blast
    qed
  qed
next
  case(Free \<alpha> PxQ)
  from \<open>P \<parallel> <\<nu>x>Q \<longmapsto>\<alpha> \<prec> PxQ\<close> show ?case
  proof(induct rule: parCasesF[where C="x"])
    case(cPar1 P')
    from \<open>P \<longmapsto> \<alpha> \<prec> P'\<close> \<open>x \<sharp> P\<close>have "x \<sharp> \<alpha>" and "x \<sharp> P'" by(force intro: freshFreeDerivative)+
    from \<open>P \<longmapsto> \<alpha> \<prec> P'\<close> have "P \<parallel> Q \<longmapsto> \<alpha> \<prec> P' \<parallel> Q" by(rule Par1F)
    hence "<\<nu>x>(P \<parallel> Q) \<longmapsto> \<alpha> \<prec> <\<nu>x>(P' \<parallel> Q)" using \<open>x \<sharp> \<alpha>\<close> by(rule ResF)
    moreover from \<open>x \<sharp> P'\<close> have "(<\<nu>x>(P' \<parallel> Q), P' \<parallel> <\<nu>x>Q) \<in> Rel" by(rule Res)
    ultimately show ?case by blast
  next
    case(cPar2 Q')
    from \<open><\<nu>x>Q \<longmapsto> \<alpha> \<prec> Q'\<close> show ?case
    proof(induct rule: resCasesF)
      case(cRes Q')
      from \<open>Q \<longmapsto> \<alpha> \<prec> Q'\<close> have "P \<parallel> Q \<longmapsto> \<alpha> \<prec> P \<parallel> Q'" by(rule Par2F)
      hence "<\<nu>x>(P \<parallel> Q) \<longmapsto>\<alpha> \<prec> <\<nu>x>(P \<parallel> Q')" using \<open>x \<sharp> \<alpha>\<close>  by(rule ResF)
      moreover from \<open>x \<sharp> P\<close> have "(<\<nu>x>(P \<parallel> Q'), P \<parallel> <\<nu>x>Q') \<in> Rel" by(rule Res)
      ultimately show ?case by blast
    qed
  next
    case(cComm1 P' xQ a b y)
    from \<open>y \<sharp> x\<close> have "y \<noteq> x" by simp
    from \<open>P \<longmapsto> a<y> \<prec> P'\<close> \<open>x \<sharp> P\<close> \<open>y \<noteq> x\<close> have "x \<sharp> P'" by(force intro: freshBoundDerivative)
    from \<open><\<nu>x>Q \<longmapsto>a[b] \<prec> xQ\<close> show ?case
    proof(induct rule: resCasesF)
      case(cRes Q')
      from \<open>x \<sharp> a[b]\<close> have "x \<noteq> b" by simp
      from \<open>P \<longmapsto> a<y> \<prec> P'\<close> \<open>Q \<longmapsto> a[b] \<prec> Q'\<close> have "P \<parallel> Q \<longmapsto> \<tau> \<prec> P'[y::=b] \<parallel> Q'" by(rule Comm1)
      hence "<\<nu>x>(P \<parallel> Q) \<longmapsto> \<tau> \<prec> <\<nu>x>(P'[y::=b] \<parallel> Q')" by(rule_tac ResF) auto
      moreover from \<open>x \<sharp> P'\<close> \<open>x \<noteq> b\<close> have "x \<sharp> P'[y::=b]" by(force intro: fresh_fact1)
      hence "(<\<nu>x>(P'[y::=b] \<parallel> Q'), P'[y::=b] \<parallel> <\<nu>x>Q') \<in> Rel" by(rule Res)
      ultimately show ?case by blast
    qed
  next
    case(cComm2 P' xQ a b y)
    from \<open>y \<sharp> x\<close> \<open>y \<sharp> <\<nu>x>Q\<close> have "y \<noteq> x" and "y \<sharp> Q" by(simp add: abs_fresh)+ 
    with \<open><\<nu>x>Q \<longmapsto>a<y> \<prec> xQ\<close> show ?case
    proof(induct rule: resCasesB)
      case(cOpen b Q')
      from \<open>InputS a = BoundOutputS b\<close> have False by simp
      thus ?case by simp
    next
      case(cRes Q')
      from \<open>P \<longmapsto>a[b] \<prec> P'\<close> \<open>Q \<longmapsto>a<y> \<prec> Q'\<close> have "P \<parallel> Q \<longmapsto> \<tau> \<prec> P' \<parallel> Q'[y::=b]" by(rule Comm2)
      hence "<\<nu>x>(P \<parallel> Q) \<longmapsto> \<tau> \<prec> <\<nu>x>(P' \<parallel> Q'[y::=b])" by(rule_tac ResF) auto
      moreover from \<open>P \<longmapsto>a[b] \<prec> P'\<close> \<open>x \<sharp> P\<close> have "x \<sharp> P'" and "x \<noteq> b" by(force dest: freshFreeDerivative)+
      from \<open>x \<sharp> P'\<close> have "(<\<nu>x>(P' \<parallel> Q'[y::=b]), P' \<parallel> <\<nu>x>(Q'[y::=b])) \<in> Rel" by(rule Res)
      with \<open>y \<noteq> x\<close> \<open>x \<noteq> b\<close> have "(<\<nu>x>(P' \<parallel> Q'[y::=b]), P' \<parallel> (<\<nu>x>Q')[y::=b]) \<in> Rel" by simp
      ultimately show ?case by blast
    qed
  next
    case(cClose1 P' Q' a y z)
    from \<open>y \<sharp> x\<close> have "y \<noteq> x" by simp
    from \<open>z \<sharp> x\<close> \<open>z \<sharp> <\<nu>x>Q\<close> have "z \<sharp> Q" and "z \<noteq> x" by(simp add: abs_fresh)+
    from \<open>P \<longmapsto>a<y> \<prec> P'\<close> \<open>z \<sharp> P\<close> have "z \<noteq> a" by(force dest: freshBoundDerivative)
    from \<open><\<nu>x>Q \<longmapsto> a<\<nu>z> \<prec> Q'\<close> \<open>z \<noteq> x\<close> \<open>z \<sharp> Q\<close> show ?case
    proof(induct rule: resCasesB)
      case(cOpen b Q')
      from \<open>BoundOutputS a = BoundOutputS b\<close> have "a = b" by simp
      with \<open>Q \<longmapsto> b[x] \<prec> Q'\<close> have "([(z, x)] \<bullet> Q) \<longmapsto> [(z, x)] \<bullet> (a[x] \<prec> Q')"
        by(rule_tac transitions.eqvt) simp
      with \<open>b \<noteq> x\<close> \<open>z \<noteq> a\<close> \<open>a = b\<close> \<open>z \<noteq> x\<close> have "([(z, x)] \<bullet> Q) \<longmapsto> a[z] \<prec> ([(z, x)] \<bullet> Q')"
        by(simp add: name_calc eqvts)
      with \<open>P \<longmapsto>a<y> \<prec> P'\<close> have "P \<parallel> ([(z, x)] \<bullet> Q) \<longmapsto>\<tau> \<prec> P'[y::=z] \<parallel> ([(z, x)] \<bullet> Q')"
        by(rule Comm1)
      hence "<\<nu>z>(P \<parallel> ([(x, z)] \<bullet> Q)) \<longmapsto> \<tau> \<prec> <\<nu>z>(P'[y::=z] \<parallel> ([(z, x)] \<bullet> Q'))"
        by(rule_tac ResF) auto
      hence "<\<nu>x>(P \<parallel> Q) \<longmapsto> \<tau> \<prec> <\<nu>z>(P'[y::=z] \<parallel> ([(z, x)] \<bullet> Q'))" using \<open>z \<sharp> P\<close> \<open>z \<sharp> Q\<close> \<open>x \<sharp> P\<close>
        by(subst alphaRes[where c=z]) auto
      with Id show ?case by force
    next
      case(cRes Q')
      from \<open>P \<longmapsto>a<y> \<prec> P'\<close> \<open>Q \<longmapsto>a<\<nu>z> \<prec> Q'\<close> \<open>z \<sharp> P\<close> have "P \<parallel> Q \<longmapsto> \<tau> \<prec> <\<nu>z>(P'[y::=z] \<parallel> Q')"
        by(rule Close1)
      hence "<\<nu>x>(P \<parallel> Q) \<longmapsto> \<tau> \<prec> <\<nu>x><\<nu>z>(P'[y::=z] \<parallel> Q')" by(rule_tac ResF) auto
      moreover from \<open>P \<longmapsto>a<y> \<prec> P'\<close> \<open>y \<noteq> x\<close> \<open>x \<sharp> P\<close> have "x \<sharp> P'"
        by(force dest: freshBoundDerivative)
      with \<open>z \<noteq> x\<close> have "x \<sharp> P'[y::=z]" by(simp add: fresh_fact1)
      hence "(<\<nu>x><\<nu>z>(P'[y::=z] \<parallel> Q'), <\<nu>z>(P'[y::=z] \<parallel> <\<nu>x>Q')) \<in> Rel"
        by(rule ScopeExt)
      ultimately show ?case by blast
    qed
  next
    case(cClose2 P' xQ a y z)
    from \<open>z \<sharp> x\<close> \<open>z \<sharp> <\<nu>x>Q\<close> have "z \<noteq> x" and "z \<sharp> Q" by(auto simp add: abs_fresh)
    from \<open>y \<sharp> x\<close> \<open>y \<sharp> <\<nu>x>Q\<close> have "y \<noteq> x" and "y \<sharp> Q" by(auto simp add: abs_fresh)
    with \<open><\<nu>x>Q \<longmapsto>a<y> \<prec> xQ\<close> show ?case
    proof(induct rule: resCasesB)
      case(cOpen b Q')
      from \<open>InputS a = BoundOutputS b\<close> have False by simp
      thus ?case by simp
    next
      case(cRes Q')
      from \<open>P \<longmapsto>a<\<nu>z> \<prec> P'\<close> \<open>Q \<longmapsto>a<y> \<prec> Q'\<close> \<open>z \<sharp> Q\<close> have "P \<parallel> Q \<longmapsto> \<tau> \<prec> <\<nu>z>(P' \<parallel> Q'[y::=z])"
        by(rule Close2)
      hence "<\<nu>x>(P \<parallel> Q) \<longmapsto> \<tau> \<prec> <\<nu>x><\<nu>z>(P' \<parallel> (Q'[y::=z]))"
        by(rule_tac ResF) auto
      moreover from \<open>P \<longmapsto>a<\<nu>z> \<prec> P'\<close> \<open>x \<sharp> P\<close> \<open>z \<noteq> x\<close> have "x \<sharp> P'" by(force dest: freshBoundDerivative)
      hence "(<\<nu>x><\<nu>z>(P' \<parallel> (Q'[y::=z])), <\<nu>z>(P' \<parallel> (<\<nu>x>(Q'[y::=z])))) \<in> Rel"
        by(rule ScopeExt)
      with \<open>z \<noteq> x\<close> \<open>y \<noteq> x\<close> have "(<\<nu>x><\<nu>z>(P' \<parallel> (Q'[y::=z])), <\<nu>z>(P' \<parallel> (<\<nu>x>Q')[y::=z])) \<in> Rel"
        by simp
      ultimately show ?case by blast
    qed
  qed
qed

lemma scopeExtParRight:
  fixes P   :: pi
  and   Q   :: pi
  and   a   :: name
  and   Rel :: "(pi \<times> pi) set"

  assumes "x \<sharp> P"
  and     Id:         "Id \<subseteq> Rel"
  and     "eqvt Rel"
  and     Res:        "\<And>R S y. y \<sharp> R \<Longrightarrow> (R \<parallel> <\<nu>y>S, <\<nu>y>(R \<parallel> S)) \<in> Rel"
  and     ScopeExt:   "\<And>R S y z. y \<sharp> R \<Longrightarrow> (<\<nu>z>(R \<parallel> <\<nu>y>S), <\<nu>y><\<nu>z>(R \<parallel> S)) \<in> Rel"

  shows "P \<parallel> <\<nu>x>Q \<leadsto>[Rel] <\<nu>x>(P \<parallel> Q)"
using \<open>eqvt Rel\<close>
proof(induct rule: simCasesCont[where C="(x, P, Q)"])
  case(Bound a y xPQ)
  from \<open>y \<sharp> (x, P, Q)\<close> have "y \<noteq> x" and "y \<sharp> P" and "y \<sharp> Q" by simp+
  hence "y \<noteq> x" and "y \<sharp> P \<parallel> Q" by(auto simp add: abs_fresh)
  with \<open><\<nu>x>(P \<parallel> Q) \<longmapsto>a\<guillemotleft>y\<guillemotright> \<prec> xPQ\<close> show ?case
  proof(induct rule: resCasesB)
    case(cOpen a PQ)
    from \<open>P \<parallel> Q \<longmapsto>a[x] \<prec> PQ\<close> show ?case
    proof(induct rule: parCasesF[where C="()"])
      case(cPar1 P')
      from \<open>P \<longmapsto>a[x] \<prec> P'\<close> \<open>x \<sharp> P\<close> have "x \<noteq> x" by(force dest: freshFreeDerivative)
      thus ?case by simp
    next
      case(cPar2 Q')
      from \<open>Q \<longmapsto>a[x] \<prec> Q'\<close> \<open>y \<sharp> Q\<close> have "y \<sharp> Q'" by(force dest: freshFreeDerivative)
      from \<open>Q \<longmapsto>a[x] \<prec> Q'\<close> \<open>a \<noteq> x\<close> have "<\<nu>x>Q \<longmapsto>a<\<nu>x> \<prec> Q'" by(rule Open)
      hence "P \<parallel> <\<nu>x>Q \<longmapsto>a<\<nu>x> \<prec> P \<parallel> Q'" using \<open>x \<sharp> P\<close> by(rule Par2B)
      with \<open>y \<sharp> P\<close> \<open>y \<sharp> Q'\<close> \<open>x \<sharp> P\<close> have "P \<parallel> <\<nu>x>Q \<longmapsto>a<\<nu>y> \<prec> ([(y, x)] \<bullet> (P \<parallel> Q'))"
        by(subst alphaBoundResidual[where x'=x]) (auto simp add: fresh_left calc_atm)
      moreover with Id have "derivative ([(y, x)] \<bullet> (P \<parallel>  Q'))
                                        ([(y, x)] \<bullet> (P \<parallel> Q')) (BoundOutputS a) y Rel"
        by(auto simp add: derivative_def)
      ultimately show ?case by blast
    next
      case(cComm1 P' Q' b c y)
      from \<open>a[x] = \<tau>\<close> show ?case by simp
    next
      case(cComm2 P' Q' b c y)
      from \<open>a[x] = \<tau>\<close> show ?case by simp
    next
      case(cClose1 P' Q' b y z)
      from \<open>a[x] = \<tau>\<close> show ?case by simp
    next
      case(cClose2 P' Q' b y z)
      from \<open>a[x] = \<tau>\<close> show ?case by simp
    qed
  next
    case(cRes PQ)
    from \<open>P \<parallel> Q \<longmapsto>a\<guillemotleft>y\<guillemotright> \<prec> PQ\<close> \<open>y \<sharp> P\<close> \<open>y \<sharp> Q\<close>
    show ?case
    proof(induct rule: parCasesB)
      case(cPar1 P')
      from \<open>y \<noteq> x\<close> \<open>x \<sharp> P\<close> \<open>P \<longmapsto>a\<guillemotleft>y\<guillemotright> \<prec> P'\<close> have "x \<sharp> P'" by(force dest: freshBoundDerivative)
      
      from \<open>P \<longmapsto>a\<guillemotleft>y\<guillemotright> \<prec> P'\<close> \<open>y \<sharp> Q\<close> have "P \<parallel> <\<nu>x>Q \<longmapsto>a\<guillemotleft>y\<guillemotright> \<prec> P' \<parallel> <\<nu>x>Q"
        by(rule_tac Par1B) (auto simp add: abs_fresh)
      moreover have "derivative (P' \<parallel> <\<nu>x>Q) (<\<nu>x>(P' \<parallel> Q)) a y Rel"
      proof(cases a, auto simp add: derivative_def)
        fix u::name
        obtain z::name where "z \<sharp> Q" and "y \<noteq> z" and "z \<noteq> u" and "z \<sharp> P" and "z \<sharp> P'"
          by(generate_fresh "name") auto
        thus "(P'[y::=u] \<parallel> (<\<nu>x>Q)[y::=u], (<\<nu>x>(P' \<parallel> Q))[y::=u]) \<in> Rel" using \<open>x \<sharp> P'\<close>
          by(subst alphaRes[where c=z and a=x], auto)
            (subst alphaRes[where c=z and a=x], auto intro: Res simp add: fresh_fact1)
      next
        from \<open>x \<sharp> P'\<close> show "(P' \<parallel> <\<nu>x>Q, <\<nu>x>(P' \<parallel> Q)) \<in> Rel"
          by(rule Res)
      qed

      ultimately show ?case by blast
    next
      case(cPar2 Q')
      from \<open>Q \<longmapsto>a\<guillemotleft>y\<guillemotright> \<prec> Q'\<close> have "<\<nu>x>Q \<longmapsto>a\<guillemotleft>y\<guillemotright> \<prec> <\<nu>x>Q'" using \<open>x \<sharp> a\<close> \<open>y \<noteq> x\<close> 
        by(rule_tac ResB) auto
      hence "P \<parallel> <\<nu>x>Q \<longmapsto>a\<guillemotleft>y\<guillemotright> \<prec> P \<parallel> <\<nu>x>Q'" using \<open>y \<sharp> P\<close> by(rule Par2B)
      
      moreover have "derivative (P \<parallel> <\<nu>x>Q') (<\<nu>x>(P \<parallel> Q')) a y Rel"
      proof(cases a, auto simp add: derivative_def)
        fix u::name
        obtain z::name where "z \<sharp> Q" and "z \<noteq> y" and "z \<noteq> u" and "z \<sharp> P" and "z \<sharp> Q'"
          by(generate_fresh "name") auto
        
        thus  "(P[y::=u] \<parallel> (<\<nu>x>Q')[y::=u], (<\<nu>x>(P \<parallel> Q'))[y::=u]) \<in> Rel" using \<open>x \<sharp> P\<close>
          by(subst alphaRes[where a=x and c=z], auto)
            (subst alphaRes[where a=x and c=z], auto intro: Res simp add: fresh_fact1)
      next
        from \<open>x \<sharp> P\<close> show "(P \<parallel> <\<nu>x>Q', <\<nu>x>(P \<parallel> Q')) \<in> Rel"
          by(rule Res)
      qed
      
      ultimately show ?case by blast
    qed
  qed
next
  case(Free \<alpha> xPQ)
  from \<open><\<nu>x>(P \<parallel> Q) \<longmapsto>\<alpha> \<prec> xPQ\<close> show ?case
  proof(induct rule: resCasesF)
    case(cRes PQ)
    from \<open>P \<parallel> Q \<longmapsto>\<alpha> \<prec> PQ\<close> show ?case
    proof(induct rule: parCasesF[where C="x"])
      case(cPar1 P')
      from \<open>P \<longmapsto>\<alpha> \<prec> P'\<close> have "P \<parallel> <\<nu>x>Q \<longmapsto>\<alpha> \<prec> P' \<parallel> <\<nu>x>Q" by(rule Par1F)
      moreover from \<open>P \<longmapsto>\<alpha> \<prec> P'\<close> \<open>x \<sharp> P\<close> have "x \<sharp> P'" by(rule freshFreeDerivative)
      hence "(P' \<parallel> <\<nu>x>Q, <\<nu>x>(P' \<parallel> Q)) \<in> Rel" by(rule Res)
      ultimately show ?case by blast
    next
      case(cPar2 Q')
      from \<open>Q \<longmapsto>\<alpha> \<prec> Q'\<close> \<open>x \<sharp> \<alpha>\<close> have "<\<nu>x>Q \<longmapsto>\<alpha> \<prec> <\<nu>x>Q'" by(rule ResF)
      hence "P \<parallel> <\<nu>x>Q \<longmapsto>\<alpha> \<prec> P \<parallel> <\<nu>x>Q'" by(rule Par2F)
      moreover from \<open>x \<sharp> P\<close> have "(P \<parallel> <\<nu>x>Q', <\<nu>x>(P \<parallel> Q')) \<in> Rel" by(rule Res)
      ultimately show ?case by blast
    next
      case(cComm1 P' Q' a b y)
      from \<open>x \<sharp> P\<close> \<open>y \<sharp> x\<close> \<open>P \<longmapsto>a<y> \<prec> P'\<close> have "x \<noteq> a" and "x \<sharp> P'" by(force dest: freshBoundDerivative)+
      show ?case
      proof(cases "b=x")
        case True
        from \<open>Q \<longmapsto>a[b] \<prec> Q'\<close> \<open>x \<noteq> a\<close> \<open>b = x\<close> have "<\<nu>x>Q \<longmapsto>a<\<nu>x> \<prec> Q'" by(rule_tac Open) auto
        with \<open>P \<longmapsto>a<y> \<prec> P'\<close> have "P \<parallel> <\<nu>x>Q \<longmapsto>\<tau> \<prec> <\<nu>x>(P'[y::=x] \<parallel> Q')" using \<open>x \<sharp> P\<close> by(rule Close1)
        moreover from Id have "(<\<nu>x>(P'[y::=b] \<parallel> Q'), <\<nu>x>(P'[y::=b] \<parallel> Q')) \<in> Rel" by blast
        ultimately show ?thesis using \<open>b=x\<close> by blast
      next
        case False
        from \<open>Q \<longmapsto>a[b] \<prec> Q'\<close> \<open>x \<noteq> a\<close> \<open>b \<noteq> x\<close> have "<\<nu>x>Q \<longmapsto>a[b] \<prec> <\<nu>x>Q'" by(rule_tac ResF) auto
        with \<open>P \<longmapsto>a<y> \<prec> P'\<close> have "P \<parallel> <\<nu>x>Q \<longmapsto>\<tau> \<prec> (P'[y::=b] \<parallel> <\<nu>x>Q')" by(rule Comm1)
        moreover from \<open>x \<sharp> P'\<close> \<open>b \<noteq> x\<close> have "(P'[y::=b] \<parallel> <\<nu>x>Q', <\<nu>x>(P'[y::=b] \<parallel> Q')) \<in> Rel"
          by(force intro: Res simp add: fresh_fact1)
        ultimately show ?thesis by blast
      qed
    next
      case(cComm2 P' Q' a b y)
      from \<open>P \<longmapsto>a[b] \<prec> P'\<close> \<open>x \<sharp> P\<close> have "x \<noteq> a" and "x \<noteq> b" and "x \<sharp> P'" by(force dest: freshFreeDerivative)+
      from \<open>Q \<longmapsto>a<y> \<prec> Q'\<close> \<open>y \<sharp> x\<close> \<open>x \<noteq> a\<close> have "<\<nu>x>Q \<longmapsto>a<y> \<prec> <\<nu>x>Q'" by(rule_tac ResB) auto
      with \<open>P \<longmapsto>a[b] \<prec> P'\<close> have "P \<parallel> <\<nu>x>Q \<longmapsto>\<tau> \<prec> P' \<parallel> (<\<nu>x>Q')[y::=b]" by(rule Comm2)
      moreover from \<open>x \<sharp> P'\<close> have "(P' \<parallel> <\<nu>x>(Q'[y::=b]), <\<nu>x>(P' \<parallel> Q'[y::=b])) \<in> Rel" by(rule Res)
      ultimately show ?case using \<open>y \<sharp> x\<close> \<open>x \<noteq> b\<close> by force
    next
      case(cClose1 P' Q' a y z)
      from \<open>P \<longmapsto>a<y> \<prec> P'\<close> \<open>x \<sharp> P\<close> \<open>y \<sharp> x\<close> have "x \<noteq> a" and "x \<sharp> P'" by(force dest: freshBoundDerivative)+
      from \<open>Q \<longmapsto>a<\<nu>z> \<prec> Q'\<close> \<open>z \<sharp> x\<close> \<open>x \<noteq> a\<close> have "<\<nu>x>Q \<longmapsto>a<\<nu>z> \<prec> <\<nu>x>Q'" by(rule_tac ResB) auto
      with \<open>P \<longmapsto>a<y> \<prec> P'\<close> have "P \<parallel> <\<nu>x>Q \<longmapsto>\<tau> \<prec> <\<nu>z>(P'[y::=z] \<parallel> <\<nu>x>Q')" using \<open>z \<sharp> P\<close> by(rule Close1)
      moreover from \<open>x \<sharp> P'\<close> \<open>z \<sharp> x\<close> have "(<\<nu>z>(P'[y::=z] \<parallel> <\<nu>x>Q'), <\<nu>x>(<\<nu>z>(P'[y::=z] \<parallel> Q'))) \<in> Rel" 
        by(rule_tac ScopeExt) (auto simp add: fresh_fact1)
      ultimately show ?case by blast
    next
      case(cClose2 P' Q' a y z)
      from \<open>P \<longmapsto>a<\<nu>z> \<prec> P'\<close> \<open>x \<sharp> P\<close> \<open>z \<sharp> x\<close> have "x \<noteq> a" and "x \<sharp> P'" by(force dest: freshBoundDerivative)+
      from \<open>Q \<longmapsto>a<y> \<prec> Q'\<close> \<open>y \<sharp> x\<close> \<open>x \<noteq> a\<close> have "<\<nu>x>Q \<longmapsto>a<y> \<prec> <\<nu>x>Q'" by(rule_tac ResB) auto
      with \<open>P \<longmapsto>a<\<nu>z> \<prec> P'\<close> have "P \<parallel> <\<nu>x>Q \<longmapsto>\<tau> \<prec> <\<nu>z>(P' \<parallel> (<\<nu>x>Q')[y::=z])" using \<open>z \<sharp> Q\<close>
        by(rule_tac Close2) (auto simp add: abs_fresh)
      moreover from \<open>x \<sharp> P'\<close> have "(<\<nu>z>(P' \<parallel> <\<nu>x>(Q'[y::=z])), <\<nu>x><\<nu>z>(P' \<parallel> Q'[y::=z])) \<in> Rel" by(rule ScopeExt)
      ultimately show ?case using \<open>z \<sharp> x\<close> \<open>y \<sharp> x\<close> by force
    qed
  qed
qed

lemma resNilRight:
  fixes x   :: name
  and   Rel :: "(pi \<times> pi) set"

  shows "\<zero> \<leadsto>[Rel] <\<nu>x>\<zero>"
by(fastforce simp add: simulation_def pi.inject alpha' elim: resCasesB' resCasesF)

lemma resComm:
  fixes a   :: name
  and   b   :: name
  and   P   :: pi
  and   Rel :: "(pi \<times> pi) set"

  assumes ResComm: "\<And>c d Q. (<\<nu>c><\<nu>d>Q, <\<nu>d><\<nu>c>Q) \<in> Rel"
  and     Id:      "Id \<subseteq> Rel"
  and     EqvtRel: "eqvt Rel"

  shows "<\<nu>a><\<nu>b>P \<leadsto>[Rel] <\<nu>b><\<nu>a>P"
proof(cases "a=b")
  assume "a=b"
  with Id show ?thesis by(force intro: Strong_Late_Sim.reflexive)
next
  assume aineqb: "a \<noteq> b"
  from EqvtRel show ?thesis
  proof(induct rule: simCasesCont[where C="(a, b, P)"])
    case(Bound c x baP)
    from \<open>x \<sharp> (a, b, P)\<close> have "x \<noteq> a" and "x \<noteq> b" and "x \<sharp> P" by simp+
    from \<open>x \<sharp> P\<close> have "x \<sharp> <\<nu>a>P" by(simp add: abs_fresh)
    with \<open><\<nu>b><\<nu>a>P \<longmapsto> c\<guillemotleft>x\<guillemotright> \<prec> baP\<close> \<open>x \<noteq> b\<close> show ?case
    proof(induct rule: resCasesB)
      case(cOpen c aP)
      from \<open><\<nu>a>P \<longmapsto>c[b] \<prec> aP\<close>
      show ?case
      proof(induct rule: resCasesF)
        case(cRes P')
        from \<open>a \<sharp> c[b]\<close> have "a \<noteq> c" and "a \<noteq> b" by simp+
        from \<open>x \<sharp> P\<close> \<open>P \<longmapsto>c[b] \<prec> P'\<close> have "x \<noteq> c" and "x \<sharp> P'" by(force dest: freshFreeDerivative)+
        from \<open>P \<longmapsto> c[b] \<prec> P'\<close> have "([(x, b)] \<bullet> P) \<longmapsto> [(x, b)] \<bullet> (c[b] \<prec> P')" by(rule transitions.eqvt)
        with \<open>x \<noteq> c\<close> \<open>c \<noteq> b\<close> \<open>x \<noteq> b\<close> have "([(x, b)] \<bullet> P) \<longmapsto> c[x] \<prec> [(x, b)] \<bullet> P'" by(simp add: eqvts calc_atm)
        hence "<\<nu>x>([(x, b)] \<bullet> P) \<longmapsto> c<\<nu>x> \<prec> [(x, b)] \<bullet> P'" using \<open>x \<noteq> c\<close> by(rule_tac Open) auto
        with \<open>x \<sharp> P\<close> have "<\<nu>b>P \<longmapsto> c<\<nu>x> \<prec> [(x, b)] \<bullet> P'" by(simp add: alphaRes)
        hence "<\<nu>a><\<nu>b>P \<longmapsto> c<\<nu>x> \<prec> <\<nu>a>([(x, b)] \<bullet> P')" using \<open>a \<noteq> c\<close> \<open>x \<noteq> a\<close>
          by(rule_tac ResB) auto
        moreover from Id have "derivative (<\<nu>a>([(x, b)] \<bullet> P')) (<\<nu>a>([(x, b)] \<bullet> P')) (BoundOutputS c) x Rel"
          by(force simp add: derivative_def)
        ultimately show ?case using \<open>a \<noteq> b\<close> \<open>x \<noteq> a\<close> \<open>a \<noteq> c\<close> by(force simp add: eqvts calc_atm)
      qed
    next
      case(cRes aP)
      from \<open><\<nu>a>P \<longmapsto> c\<guillemotleft>x\<guillemotright> \<prec> aP\<close> \<open>x \<noteq> a\<close> \<open>x \<sharp> P\<close> \<open>b \<sharp> c\<close> show ?case
      proof(induct rule: resCasesB)
        case(cOpen c P')
        from \<open>P \<longmapsto>c[a] \<prec> P'\<close> \<open>x \<sharp> P\<close> have "x \<sharp> P'" by(force intro: freshFreeDerivative)
        from \<open>b \<sharp> BoundOutputS c\<close> have "b \<noteq> c" by simp
        with \<open>P \<longmapsto>c[a] \<prec> P'\<close> \<open>a \<noteq> b\<close> have "<\<nu>b>P \<longmapsto> c[a] \<prec> <\<nu>b>P'" by(rule_tac ResF) auto
        with \<open>c \<noteq> a\<close> have "<\<nu>a><\<nu>b>P \<longmapsto> c<\<nu>a> \<prec> <\<nu>b>P'" by(rule_tac Open) auto
        hence "<\<nu>a><\<nu>b>P \<longmapsto>c<\<nu>x> \<prec> <\<nu>b>([(x, a)] \<bullet> P')" using \<open>x \<noteq> b\<close> \<open>a \<noteq> b\<close> \<open>x \<sharp> P'\<close>
          apply(subst alphaBoundResidual[where x'=a]) by(auto simp add: abs_fresh fresh_left calc_atm)
        moreover have "derivative (<\<nu>b>([(x, a)] \<bullet> P')) (<\<nu>b>([(x, a)] \<bullet> P')) (BoundOutputS c) x Rel" using Id
          by(force simp add: derivative_def)
        ultimately show ?case by blast
      next
        case(cRes P')
        from \<open>P \<longmapsto>c\<guillemotleft>x\<guillemotright> \<prec> P'\<close> \<open>b \<sharp> c\<close> \<open>x \<noteq> b\<close> have "<\<nu>b>P \<longmapsto> c\<guillemotleft>x\<guillemotright> \<prec> <\<nu>b>P'" by(rule_tac ResB) auto
        hence "<\<nu>a><\<nu>b>P \<longmapsto> c\<guillemotleft>x\<guillemotright> \<prec> <\<nu>a><\<nu>b>P'" using \<open>a \<sharp> c\<close> \<open>x \<noteq> a\<close> by(rule_tac ResB) auto
        moreover have "derivative (<\<nu>a><\<nu>b>P') (<\<nu>b><\<nu>a>P') c x Rel"
        proof(cases c, auto simp add: derivative_def)
          fix u::name
          show  "((<\<nu>a><\<nu>b>P')[x::=u],  (<\<nu>b><\<nu>a>P')[x::=u]) \<in> Rel"
          proof(cases "u=a")
            case True
            from \<open>u = a\<close> \<open>a \<noteq> b\<close> show ?thesis
              by(subst injPermSubst[symmetric], auto simp add: abs_fresh)
                (subst injPermSubst[symmetric], auto simp add: abs_fresh calc_atm intro: ResComm)
          next
            case False
            show ?thesis
            proof(cases "u=b")
              case True
              from \<open>u = b\<close> \<open>u \<noteq> a\<close> show ?thesis
              by(subst injPermSubst[symmetric], auto simp add: abs_fresh)
                (subst injPermSubst[symmetric], auto simp add: abs_fresh calc_atm intro: ResComm)
            next
              case False
              from \<open>u \<noteq> a\<close> \<open>u \<noteq> b\<close> \<open>x \<noteq> a\<close> \<open>x \<noteq> b\<close> show ?thesis by(auto intro: ResComm)
            qed
          qed
        next
          show "(<\<nu>a><\<nu>b>P', <\<nu>b><\<nu>a>P') \<in> Rel" by(rule ResComm)
        qed
        ultimately show ?case by blast
      qed
    qed
  next
    case(Free \<alpha> baP)
    from \<open><\<nu>b><\<nu>a>P \<longmapsto> \<alpha> \<prec> baP\<close> show ?case
    proof(induct rule: resCasesF)
      case(cRes aP)
      from \<open><\<nu>a>P \<longmapsto> \<alpha> \<prec> aP\<close> show ?case
      proof(induct rule: resCasesF)
        case(cRes P')
        from \<open>P \<longmapsto> \<alpha> \<prec> P'\<close> \<open>b \<sharp> \<alpha>\<close> have "<\<nu>b>P \<longmapsto> \<alpha> \<prec> <\<nu>b>P'" by(rule ResF)
        hence "<\<nu>a><\<nu>b>P \<longmapsto> \<alpha> \<prec> <\<nu>a><\<nu>b>P'" using \<open>a \<sharp> \<alpha>\<close> by(rule ResF)
        moreover have "(<\<nu>a><\<nu>b>P', <\<nu>b><\<nu>a>P') \<in> Rel" by(rule ResComm)
        ultimately show ?case by blast
      qed
    qed
  qed
qed

(***************** !-operator ********************)

lemma bangLeftSC:
  fixes P   :: pi
  and   Rel :: "(pi \<times> pi) set"

  assumes "Id \<subseteq> Rel"

  shows "!P \<leadsto>[Rel] P \<parallel> !P"
using assms
by(force simp add: simulation_def dest: Bang derivativeReflexive)

lemma bangRightSC:
  fixes P   :: pi
  and   Rel :: "(pi \<times> pi) set"

  assumes IdRel: "Id \<subseteq> Rel"

  shows "P \<parallel> !P \<leadsto>[Rel] !P"
using assms
by(fastforce simp add: pi.inject simulation_def intro: derivativeReflexive elim: bangCases)

lemma resNilLeft:
  fixes x   :: name
  and   y   :: name
  and   P   :: pi
  and   Rel :: "(pi \<times> pi) set"
  and   b   :: name

  shows "\<zero> \<leadsto>[Rel] <\<nu>x>(x<y>.P)"
  and   "\<zero> \<leadsto>[Rel] <\<nu>x>(x{b}.P)"
by(auto simp add: simulation_def)

lemma resInputLeft:
  fixes x :: name
  and   a :: name
  and   y :: name
  and   P :: pi
  and   Rel :: "(pi \<times> pi) set"

  assumes xineqa: "x \<noteq> a"
  and     xineqy: "x \<noteq> y"
  and     Eqvt: "eqvt Rel"
  and     Id: "Id \<subseteq> Rel"

  shows "<\<nu>x>a<y>.P \<leadsto>[Rel] a<y>.(<\<nu>x>P)"
using Eqvt
proof(induct rule: simCasesCont[where C="(x, y, a, P)"])
  case(Bound b z P')
  from \<open>z \<sharp> (x, y, a, P)\<close> have "z \<noteq> x" and "z \<noteq> y" and "z \<sharp> P" and "z \<noteq> a"  by simp+
  from \<open>z \<sharp> P\<close> have "z \<sharp> <\<nu>x>P" by(simp add: abs_fresh)
  with \<open>a<y>.(<\<nu>x>P) \<longmapsto>b\<guillemotleft>z\<guillemotright> \<prec> P'\<close> \<open>z \<noteq> a\<close> \<open>z \<noteq> y\<close> show ?case
  proof(induct rule: inputCases)
    case cInput
    have "a<y>.P \<longmapsto>a<y> \<prec> P" by(rule Input)
    with \<open>x \<noteq> y\<close> \<open>x \<noteq> a\<close> have "<\<nu>x>a<y>.P \<longmapsto>a<y> \<prec> <\<nu>x>P" by(rule_tac ResB) auto
    hence "<\<nu>x>a<y>.P \<longmapsto>a<z> \<prec> [(y,  z)] \<bullet> <\<nu>x>P" using \<open>z \<sharp> P\<close> 
      by(subst alphaBoundResidual[where x'=y]) (auto simp add: abs_fresh fresh_left calc_atm)
    moreover from Id have "derivative ([(y, z)] \<bullet> <\<nu>x>P) ([(y, z)] \<bullet> <\<nu>x>P) (InputS a) z Rel" 
      by(rule derivativeReflexive)
    ultimately show ?case by blast
  qed
next
  case(Free \<alpha> P')
  from \<open>a<y>.(<\<nu>x>P) \<longmapsto>\<alpha> \<prec> P'\<close> have False by auto
  thus ?case by simp
qed

lemma resInputRight:
  fixes a :: name
  and   y :: name
  and   x :: name
  and   P :: pi
  and   Rel :: "(pi \<times> pi) set"

  assumes xineqa: "x \<noteq> a"
  and     xineqy: "x \<noteq> y"
  and     Eqvt: "eqvt Rel"
  and     Id: "Id \<subseteq> Rel"

  shows "a<y>.(<\<nu>x>P) \<leadsto>[Rel] <\<nu>x>a<y>.P"
  using Eqvt
proof(induct rule: simCasesCont[where C="(x, y, a, P)"])
  case(Bound b z xP)
  from \<open>z \<sharp> (x, y, a, P)\<close> have "z \<noteq> x" and "z \<noteq> y" and "z \<sharp> P" and "z \<noteq> a" by simp+
  from \<open>z \<noteq> a\<close> \<open>z \<sharp> P\<close> have "z \<sharp> a<y>.P" by(simp add: abs_fresh)
  with \<open><\<nu>x>a<y>.P \<longmapsto>b\<guillemotleft>z\<guillemotright> \<prec> xP\<close> \<open>z \<noteq> x\<close> show ?case
  proof(induct rule: resCasesB)
    case(cOpen b P')
    from \<open>a<y>.P \<longmapsto>b[x] \<prec> P'\<close> have False by auto
    thus ?case by simp
  next
    case(cRes P')
    from \<open>a<y>.P \<longmapsto>b\<guillemotleft>z\<guillemotright> \<prec> P'\<close>\<open>z \<noteq> a\<close> \<open>z \<noteq> y\<close> \<open>z \<sharp> P\<close> show ?case
    proof(induct rule: inputCases)
      case cInput
      have "a<y>.(<\<nu>x>P) \<longmapsto>a<y> \<prec> (<\<nu>x>P)" by(rule Input)
      with \<open>z \<sharp> P\<close> \<open>x \<noteq> y\<close> \<open>z \<noteq> x\<close> have "a<y>.(<\<nu>x>P) \<longmapsto>a<z> \<prec> (<\<nu>x>([(y, z)] \<bullet> P))"
        by(subst alphaBoundResidual[where x'=y]) (auto simp add: abs_fresh calc_atm fresh_left)
      moreover from Id have "derivative (<\<nu>x>([(y, z)] \<bullet> P)) (<\<nu>x>([(y, z)] \<bullet> P)) (InputS a) z Rel"
        by(rule derivativeReflexive)
      ultimately show ?case by blast
    qed
  qed
next
  case(Free \<alpha> P')
  from \<open><\<nu>x>a<y>.P \<longmapsto>\<alpha> \<prec> P'\<close> have False by auto
  thus ?case by simp
qed

lemma resOutputLeft:
  fixes x   :: name
  and   a   :: name
  and   b   :: name
  and   P   :: pi
  and   Rel :: "(pi \<times> pi) set"

  assumes xineqa: "x \<noteq> a"
  and     xineqb: "x \<noteq> b"
  and     Id: "Id \<subseteq> Rel"

  shows "<\<nu>x>a{b}.P \<leadsto>[Rel] a{b}.(<\<nu>x>P)"
using assms
by(fastforce simp add: simulation_def elim: outputCases intro: Output ResF)

lemma resOutputRight:
  fixes x   :: name
  and   a   :: name
  and   b   :: name
  and   P   :: pi
  and   Rel :: "(pi \<times> pi) set"

  assumes xineqa: "x \<noteq> a"
  and     xineqb: "x \<noteq> b"
  and     Id: "Id \<subseteq> Rel"
  and     Eqvt: "eqvt Rel"

  shows "a{b}.(<\<nu>x>P) \<leadsto>[Rel] <\<nu>x>a{b}.P"
using assms
by(erule_tac simCasesCont[where C=x])
  (force simp add: abs_fresh elim: resCasesB resCasesF outputCases intro: ResF Output)+

lemma resTauLeft:
  fixes x   :: name
  and   P   :: pi
  and   Rel :: "(pi \<times> pi) set"

  assumes Id: "Id \<subseteq> Rel"

  shows "<\<nu>x>(\<tau>.(P)) \<leadsto>[Rel] \<tau>.(<\<nu>x>P)"
using assms
by(force simp add: simulation_def elim: tauCases resCasesF intro: Tau ResF)

lemma resTauRight: 
  fixes x   :: name
  and   P   :: pi
  and   Rel :: "(pi \<times> pi) set"

  assumes Id:   "Id \<subseteq> Rel"

  shows "\<tau>.(<\<nu>x>P) \<leadsto>[Rel] <\<nu>x>(\<tau>.(P))"
using assms
by(force simp add: simulation_def elim: tauCases resCasesF intro: Tau ResF)

end
