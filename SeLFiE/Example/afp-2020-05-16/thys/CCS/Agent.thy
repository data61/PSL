(* 
   Title: The Calculus of Communicating Systems   
   Author/Maintainer: Jesper Bengtson (jebe@itu.dk), 2012
*)
theory Agent
  imports "HOL-Nominal.Nominal"
begin

atom_decl name

nominal_datatype act = actAction name      ("\<lparr>_\<rparr>" 100)
                     | actCoAction name    ("\<langle>_\<rangle>" 100)
                     | actTau              ("\<tau>" 100)

nominal_datatype ccs = CCSNil           ("\<zero>" 115)
                     | Action act ccs   ("_._" [120, 110] 110)
                     | Sum ccs ccs      (infixl "\<oplus>" 90)
                     | Par ccs ccs      (infixl "\<parallel>" 85)
                     | Res "\<guillemotleft>name\<guillemotright> ccs" ("\<lparr>\<nu>_\<rparr>_" [105, 100] 100)
                     | Bang ccs         ("!_" [95])

nominal_primrec coAction :: "act \<Rightarrow> act"
where
  "coAction (\<lparr>a\<rparr>) = (\<langle>a\<rangle>)"
| "coAction (\<langle>a\<rangle>)= (\<lparr>a\<rparr>)"
| "coAction (\<tau>) = \<tau>"
by(rule TrueI)+

lemma coActionEqvt[eqvt]:
  fixes p :: "name prm"
  and   a :: act

  shows "(p \<bullet> coAction a) = coAction(p \<bullet> a)"
by(nominal_induct a rule: act.strong_induct) (auto simp add: eqvts)

lemma coActionSimps[simp]:
  fixes a :: act

  shows "coAction(coAction a) = a"
  and   "(coAction a = \<tau>) = (a = \<tau>)"
by auto (nominal_induct rule: act.strong_induct, auto)+

lemma coActSimp[simp]: shows "coAction \<alpha> \<noteq> \<tau> = (\<alpha> \<noteq> \<tau>)" and "(coAction \<alpha> = \<tau>) = (\<alpha> = \<tau>)"
by(nominal_induct \<alpha> rule: act.strong_induct) auto
    
lemma coActFresh[simp]:
  fixes x :: name
  and   a :: act

  shows "x \<sharp> coAction a = x \<sharp> a"
by(nominal_induct a rule: act.strong_induct) (auto)
  
lemma alphaRes:
  fixes y :: name
  and   P :: ccs
  and   x :: name

  assumes "y \<sharp> P"
  
  shows "\<lparr>\<nu>x\<rparr>P = \<lparr>\<nu>y\<rparr>([(x, y)] \<bullet> P)"
using assms
by(auto simp add: ccs.inject alpha fresh_left calc_atm pt_swap_bij[OF pt_name_inst, OF at_name_inst]pt3[OF pt_name_inst, OF at_ds1[OF at_name_inst]])

inductive semantics :: "ccs \<Rightarrow> act \<Rightarrow> ccs \<Rightarrow> bool"    ("_ \<longmapsto>_ \<prec> _" [80, 80, 80] 80)
where
  Action:   "\<alpha>.(P) \<longmapsto>\<alpha> \<prec> P"
| Sum1:     "P \<longmapsto>\<alpha> \<prec> P' \<Longrightarrow> P \<oplus> Q \<longmapsto>\<alpha> \<prec> P'"
| Sum2:     "Q \<longmapsto>\<alpha> \<prec> Q' \<Longrightarrow> P \<oplus> Q \<longmapsto>\<alpha> \<prec> Q'"
| Par1:     "P \<longmapsto>\<alpha> \<prec> P' \<Longrightarrow> P \<parallel> Q \<longmapsto>\<alpha> \<prec> P' \<parallel> Q"
| Par2:     "Q \<longmapsto>\<alpha> \<prec> Q' \<Longrightarrow> P \<parallel> Q \<longmapsto>\<alpha> \<prec> P \<parallel> Q'"
| Comm:     "\<lbrakk>P \<longmapsto>a \<prec> P'; Q \<longmapsto>(coAction a) \<prec> Q'; a \<noteq> \<tau>\<rbrakk> \<Longrightarrow> P \<parallel> Q \<longmapsto>\<tau> \<prec> P' \<parallel> Q'"
| Res:      "\<lbrakk>P \<longmapsto>\<alpha> \<prec> P'; x \<sharp> \<alpha>\<rbrakk> \<Longrightarrow> \<lparr>\<nu>x\<rparr>P \<longmapsto>\<alpha> \<prec> \<lparr>\<nu>x\<rparr>P'"
| Bang:     "P \<parallel> !P \<longmapsto>\<alpha> \<prec> P' \<Longrightarrow> !P \<longmapsto>\<alpha> \<prec> P'"

equivariance semantics

nominal_inductive semantics
by(auto simp add: abs_fresh)

lemma semanticsInduct:
"\<lbrakk>R \<longmapsto>\<beta> \<prec> R'; \<And>\<alpha> P \<C>. Prop \<C> (\<alpha>.(P)) \<alpha> P;
 \<And>P \<alpha> P' Q \<C>. \<lbrakk>P \<longmapsto>\<alpha> \<prec> P'; \<And>\<C>. Prop \<C> P \<alpha> P'\<rbrakk> \<Longrightarrow> Prop \<C> (ccs.Sum P Q) \<alpha> P';
 \<And>Q \<alpha> Q' P \<C>. \<lbrakk>Q \<longmapsto>\<alpha> \<prec> Q'; \<And>\<C>. Prop \<C> Q \<alpha> Q'\<rbrakk> \<Longrightarrow> Prop \<C> (ccs.Sum P Q) \<alpha> Q';
 \<And>P \<alpha> P' Q \<C>. \<lbrakk>P \<longmapsto>\<alpha> \<prec> P'; \<And>\<C>. Prop \<C> P \<alpha> P'\<rbrakk> \<Longrightarrow> Prop \<C> (P \<parallel> Q) \<alpha> (P' \<parallel> Q);
 \<And>Q \<alpha> Q' P \<C>. \<lbrakk>Q \<longmapsto>\<alpha> \<prec> Q'; \<And>\<C>. Prop \<C> Q \<alpha> Q'\<rbrakk> \<Longrightarrow> Prop \<C> (P \<parallel> Q) \<alpha> (P \<parallel> Q');
 \<And>P a P' Q Q' \<C>.
    \<lbrakk>P \<longmapsto>a \<prec> P'; \<And>\<C>. Prop \<C> P a P'; Q \<longmapsto>(coAction a) \<prec> Q';
     \<And>\<C>. Prop \<C> Q (coAction a) Q'; a \<noteq> \<tau>\<rbrakk>
    \<Longrightarrow> Prop \<C> (P \<parallel> Q) (\<tau>) (P' \<parallel> Q');
 \<And>P \<alpha> P' x \<C>.
    \<lbrakk>x \<sharp> \<C>; P \<longmapsto>\<alpha> \<prec> P'; \<And>\<C>. Prop \<C> P \<alpha> P'; x \<sharp> \<alpha>\<rbrakk> \<Longrightarrow> Prop \<C> (\<lparr>\<nu>x\<rparr>P) \<alpha> (\<lparr>\<nu>x\<rparr>P');
 \<And>P \<alpha> P' \<C>. \<lbrakk>P \<parallel> !P \<longmapsto>\<alpha> \<prec> P'; \<And>\<C>. Prop \<C> (P \<parallel> !P) \<alpha> P'\<rbrakk> \<Longrightarrow> Prop \<C> !P \<alpha> P'\<rbrakk>

\<Longrightarrow> Prop (\<C>::'a::fs_name) R \<beta> R'"
by(erule_tac z=\<C> in semantics.strong_induct) auto

lemma NilTrans[dest]:
  shows "\<zero> \<longmapsto>\<alpha> \<prec> P' \<Longrightarrow> False"
  and   "(\<lparr>b\<rparr>).P \<longmapsto>\<langle>c\<rangle> \<prec> P' \<Longrightarrow> False"
  and   "(\<lparr>b\<rparr>).P \<longmapsto>\<tau> \<prec> P' \<Longrightarrow> False"
  and   "(\<langle>b\<rangle>).P \<longmapsto>\<lparr>c\<rparr> \<prec> P' \<Longrightarrow> False"
  and   "(\<langle>b\<rangle>).P \<longmapsto>\<tau> \<prec> P' \<Longrightarrow> False"
apply(ind_cases "\<zero> \<longmapsto>\<alpha> \<prec> P'")
apply(ind_cases "(\<lparr>b\<rparr>).P \<longmapsto>\<langle>c\<rangle> \<prec> P'", auto simp add: ccs.inject)
apply(ind_cases "(\<lparr>b\<rparr>).P \<longmapsto>\<tau> \<prec> P'", auto simp add: ccs.inject)
apply(ind_cases "(\<langle>b\<rangle>).P \<longmapsto>\<lparr>c\<rparr> \<prec> P'", auto simp add: ccs.inject)
apply(ind_cases "(\<langle>b\<rangle>).P \<longmapsto>\<tau> \<prec> P'", auto simp add: ccs.inject)
done

lemma freshDerivative:
  fixes P  :: ccs
  and   a  :: act
  and   P' :: ccs
  and   x  :: name

  assumes "P \<longmapsto>\<alpha> \<prec> P'"
  and     "x \<sharp> P"

  shows "x \<sharp> \<alpha>" and "x \<sharp> P'"
using assms
by(nominal_induct rule: semantics.strong_induct)
  (auto simp add: ccs.fresh abs_fresh)
  
lemma actCases[consumes 1, case_names cAct]:
  fixes \<alpha>  :: act
  and   P  :: ccs
  and   \<beta>  :: act
  and   P' :: ccs

  assumes "\<alpha>.(P) \<longmapsto>\<beta> \<prec> P'"
  and     "Prop \<alpha> P"

  shows "Prop \<beta> P'"
using assms
by - (ind_cases "\<alpha>.(P) \<longmapsto>\<beta> \<prec> P'", auto simp add: ccs.inject)

lemma sumCases[consumes 1, case_names cSum1 cSum2]:
  fixes P :: ccs
  and   Q :: ccs
  and   \<alpha> :: act
  and   R :: ccs

  assumes "P \<oplus> Q \<longmapsto>\<alpha> \<prec> R"
  and     "\<And>P'. P \<longmapsto>\<alpha> \<prec> P' \<Longrightarrow> Prop P'"
  and     "\<And>Q'. Q \<longmapsto>\<alpha> \<prec> Q' \<Longrightarrow> Prop Q'"

  shows "Prop R"
using assms
by - (ind_cases "P \<oplus> Q \<longmapsto>\<alpha> \<prec> R", auto simp add: ccs.inject)

lemma parCases[consumes 1, case_names cPar1 cPar2 cComm]:
  fixes P :: ccs
  and   Q :: ccs
  and   a :: act
  and   R :: ccs

  assumes "P \<parallel> Q \<longmapsto>\<alpha> \<prec> R"
  and     "\<And>P'. P \<longmapsto>\<alpha> \<prec> P' \<Longrightarrow> Prop \<alpha> (P' \<parallel> Q)"
  and     "\<And>Q'. Q \<longmapsto>\<alpha> \<prec> Q' \<Longrightarrow> Prop \<alpha> (P \<parallel> Q')"
  and     "\<And>P' Q' a. \<lbrakk>P \<longmapsto>a \<prec> P'; Q \<longmapsto>(coAction a) \<prec> Q'; a \<noteq> \<tau>; \<alpha> = \<tau>\<rbrakk> \<Longrightarrow> Prop (\<tau>) (P' \<parallel> Q')"

  shows "Prop \<alpha> R"
using assms
by - (ind_cases "P \<parallel> Q \<longmapsto>\<alpha> \<prec> R", auto simp add: ccs.inject)

lemma resCases[consumes 1, case_names cRes]:
  fixes x  :: name
  and   P  :: ccs
  and   \<alpha>  :: act
  and   P' :: ccs

  assumes "\<lparr>\<nu>x\<rparr>P \<longmapsto>\<alpha> \<prec> P'"
  and     "\<And>P'. \<lbrakk>P \<longmapsto>\<alpha> \<prec> P'; x \<sharp> \<alpha>\<rbrakk> \<Longrightarrow> Prop (\<lparr>\<nu>x\<rparr>P')"

  shows "Prop P'"
proof -
  from \<open>\<lparr>\<nu>x\<rparr>P \<longmapsto>\<alpha> \<prec> P'\<close> have "x \<sharp> \<alpha>" and "x \<sharp> P'"
    by(auto intro: freshDerivative simp add: abs_fresh)+
  with assms show ?thesis
    by(cases rule: semantics.strong_cases[of _ _ _ _ x])
      (auto simp add: abs_fresh ccs.inject alpha)
qed

inductive bangPred :: "ccs \<Rightarrow> ccs \<Rightarrow> bool"
where
  aux1: "bangPred P (!P)"
| aux2: "bangPred P (P \<parallel> !P)"

lemma bangInduct[consumes 1, case_names cPar1 cPar2 cComm cBang]:
  fixes P  :: ccs
  and   \<alpha>  :: act
  and   P' :: ccs
  and   \<C>  :: "'a::fs_name"

  assumes "!P \<longmapsto>\<alpha> \<prec> P'"
  and     rPar1: "\<And>\<alpha> P' \<C>. \<lbrakk>P \<longmapsto>\<alpha> \<prec> P'\<rbrakk> \<Longrightarrow> Prop \<C> (P \<parallel> !P) \<alpha> (P' \<parallel> !P)"
  and     rPar2: "\<And>\<alpha> P' \<C>. \<lbrakk>!P \<longmapsto>\<alpha> \<prec> P'; \<And>\<C>. Prop \<C> (!P) \<alpha> P'\<rbrakk> \<Longrightarrow> Prop \<C> (P \<parallel> !P) \<alpha> (P \<parallel> P')"
  and     rComm: "\<And>a P' P'' \<C>. \<lbrakk>P \<longmapsto>a \<prec> P'; !P \<longmapsto>(coAction a) \<prec> P''; \<And>\<C>. Prop \<C> (!P) (coAction a) P''; a \<noteq> \<tau>\<rbrakk> \<Longrightarrow> Prop \<C> (P \<parallel> !P) (\<tau>) (P' \<parallel> P'')"
  and     rBang: "\<And>\<alpha> P' \<C>. \<lbrakk>P \<parallel> !P \<longmapsto>\<alpha> \<prec> P'; \<And>\<C>. Prop \<C> (P \<parallel> !P) \<alpha> P'\<rbrakk> \<Longrightarrow> Prop \<C> (!P) \<alpha> P'"


  shows "Prop \<C> (!P) \<alpha> P'"
proof -
  {
    fix X \<alpha> P'
    assume "X \<longmapsto>\<alpha> \<prec> P'" and "bangPred P X"
    hence "Prop \<C> X \<alpha> P'"
    proof(nominal_induct avoiding: \<C> rule: semantics.strong_induct)
      case(Action \<alpha> Pa)
      thus ?case 
        by - (ind_cases "bangPred P (\<alpha>.(Pa))") 
    next
      case(Sum1 Pa \<alpha> P' Q)
      thus ?case
        by - (ind_cases "bangPred P (Pa \<oplus> Q)") 
    next
      case(Sum2 Q \<alpha> Q' Pa)
      thus ?case
        by - (ind_cases "bangPred P (Pa \<oplus> Q)") 
    next
      case(Par1 Pa \<alpha> P' Q)
      thus ?case
        apply -
        by(ind_cases "bangPred P (Pa \<parallel> Q)", auto intro: rPar1 simp add: ccs.inject)
    next
      case(Par2 Q \<alpha> P' Pa)
      thus ?case
        apply -
        by(ind_cases "bangPred P (Pa \<parallel> Q)", auto intro: rPar2 aux1 simp add: ccs.inject)
    next
      case(Comm Pa a P' Q Q' C)
      thus ?case
        apply -
        by(ind_cases "bangPred P (Pa \<parallel> Q)", auto intro: rComm aux1 simp add: ccs.inject)
    next
      case(Res Pa \<alpha> P' x)
      thus ?case
        by - (ind_cases "bangPred P (\<lparr>\<nu>x\<rparr>Pa)") 
    next
      case(Bang Pa \<alpha> P')
      thus ?case
        apply -
        by(ind_cases "bangPred P (!Pa)", auto intro: rBang aux2 simp add: ccs.inject)
    qed
  }
  with \<open>!P \<longmapsto>\<alpha> \<prec> P'\<close> show ?thesis by(force intro: bangPred.aux1)
qed

inductive_set bangRel :: "(ccs \<times> ccs) set \<Rightarrow> (ccs \<times> ccs) set"
for Rel :: "(ccs \<times> ccs) set"
where
  BRBang: "(P, Q) \<in> Rel \<Longrightarrow> (!P, !Q) \<in> bangRel Rel"
| BRPar: "(R, T) \<in> Rel \<Longrightarrow> (P, Q) \<in> (bangRel Rel) \<Longrightarrow> (R \<parallel> P, T \<parallel> Q) \<in> (bangRel Rel)"

lemma BRBangCases[consumes 1, case_names BRBang]:
  fixes P   :: ccs
  and   Q   :: ccs
  and   Rel :: "(ccs \<times> ccs) set"
  and   F   :: "ccs \<Rightarrow> bool"

  assumes "(P, !Q) \<in> bangRel Rel"
  and     "\<And>P. (P, Q) \<in> Rel \<Longrightarrow> F (!P)"
  
  shows "F P"
using assms
by - (ind_cases "(P, !Q) \<in> bangRel Rel", auto simp add: ccs.inject) 

lemma BRParCases[consumes 1, case_names BRPar]:
  fixes P   :: ccs
  and   Q   :: ccs
  and   Rel :: "(ccs \<times> ccs) set"
  and   F   :: "ccs \<Rightarrow> bool"

  assumes "(P, Q \<parallel> !Q) \<in> bangRel Rel"
  and     "\<And>P R. \<lbrakk>(P, Q) \<in> Rel; (R, !Q) \<in> bangRel Rel\<rbrakk> \<Longrightarrow> F (P \<parallel> R)"

  shows "F P"
using assms
by - (ind_cases "(P, Q \<parallel> !Q) \<in> bangRel Rel", auto simp add: ccs.inject) 

lemma bangRelSubset:
  fixes Rel  :: "(ccs \<times> ccs) set"
  and   Rel' :: "(ccs \<times> ccs) set"

  assumes "(P, Q) \<in> bangRel Rel"
  and     "\<And>P Q. (P, Q) \<in> Rel \<Longrightarrow> (P, Q) \<in> Rel'"

  shows "(P, Q) \<in> bangRel Rel'"
using assms
by(induct rule:  bangRel.induct) (auto intro: BRBang BRPar)

end
