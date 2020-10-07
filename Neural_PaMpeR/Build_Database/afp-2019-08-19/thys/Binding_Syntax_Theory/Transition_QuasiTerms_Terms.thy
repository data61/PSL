section {* Transition from Quasi-Terms to Terms*}

theory Transition_QuasiTerms_Terms
imports QuasiTerms_Environments_Substitution Equiv_Relation2
begin

text{* This section transits from quasi-terms to terms: defines terms as alpha-equivalence
classes of quasi-terms
(and also abstractions as alpha-equivalence classes of  quasi-abstractions),
then defines operators on terms corresponding to those on quasi-terms:
variable injection, binding operation, freshness, swapping, parallel substitution, etc.
Properties previously shown invariant
under alpha-equivalence, including induction principles, are lifted from quasi-terms.
Moreover, a new powerful induction principle, allowing freshness assumptions,
is proved for terms.

As a matter of notation:
Starting from this section, we change the notations for quasi-item meta-variables, prefixing
their names with a "q" -- e.g., qX, qA, qinp, qenv, etc. The old names are now assigned
to the ``real" items: terms, abstractions, inputs, environments. *}

subsection {* Preparation: Integrating quasi-inputs as first-class citizens *}

context FixVars
begin

text{* From now on it will be convenient to
   also define fresh, swap, good and alpha-equivalence for quasi-inpus. *}

definition qSwapInp where
"qSwapInp xs x y qinp == lift (qSwap xs x y) qinp"

definition qSwapBinp where
"qSwapBinp xs x y qbinp == lift (qSwapAbs xs x y) qbinp"

abbreviation qSwapInp_abbrev ("_ %[[_ \<and> _]]'__" 200) where
"(qinp %[[z1 \<and> z2]]_zs) == qSwapInp zs z1 z2 qinp"

abbreviation qSwapBinp_abbrev ("_ %%[[_ \<and> _]]'__" 200) where
"(qbinp %%[[z1 \<and> z2]]_zs) == qSwapBinp zs z1 z2 qbinp"

lemma qSwap_qSwapInp:
"((qOp delta qinp qbinp) #[[x \<and> y]]_xs) =
 qOp delta (qinp %[[x \<and> y]]_xs) (qbinp %%[[x \<and> y]]_xs)"
unfolding qSwapInp_def qSwapBinp_def by simp

(* For the qOp case, qSwap shall henceforth simplify to qSwapInp:  *)

declare qSwap.simps(2) [simp del]
declare qSwap_qSwapInp[simp]

(* and qSwap_simps and qSwapAll_simps, rather than qSwap.simps and qSwapAll.simps,
   shall refer to the simplification rules for qSwap *)

lemmas qSwapAll_simps = qSwap.simps(1) qSwap_qSwapInp

definition qPsubstInp where
"qPsubstInp qrho qinp == lift (qPsubst qrho) qinp"

definition qPsubstBinp where
"qPsubstBinp qrho qbinp == lift (qPsubstAbs qrho) qbinp"

abbreviation qPsubstInp_abbrev ("_ %[[_]]" 200)
where "(qinp %[[qrho]]) == qPsubstInp qrho qinp"

abbreviation qPsubstBinp_abbrev ("_ %%[[_]]" 200)
where "(qbinp %%[[qrho]]) == qPsubstBinp qrho qbinp"

lemma qPsubst_qPsubstInp:
"((qOp delta qinp qbinp) #[[rho]]) = qOp delta (qinp %[[rho]]) (qbinp %%[[rho]])"
unfolding qPsubstInp_def qPsubstBinp_def by simp

(* For the qOp case, qPsubst shall henceforth simplify to qPsubstInp:  *)

declare qPsubst.simps(2) [simp del]
declare qPsubst_qPsubstInp[simp]

(* and qPsubst_simps and qPsubstAll_simps, rather than qPsubst.simps and qPsubstAll.simps,
   shall refer to the simplification rules for qPsubst *)

lemmas qPsubstAll_simps = qPsubst.simps(1) qPsubst_qPsubstInp

definition qSkelInp
where "qSkelInp qinp = lift qSkel qinp"

definition qSkelBinp
where "qSkelBinp qbinp = lift qSkelAbs qbinp"

lemma qSkel_qSkelInp:
"qSkel (qOp delta qinp qbinp) =
 Branch (qSkelInp qinp) (qSkelBinp qbinp)"
unfolding qSkelInp_def qSkelBinp_def by simp

(* For the qOp case, qSkel shall henceforth simplify to qSkelInp:  *)

declare qSkel.simps(2) [simp del]
declare qSkel_qSkelInp[simp]

(* and qSkel_simps and qSkelAll_simps, rather than qSkel.simps and qSkelAll.simps,
   shall refer to the simplification rules for qSkel *)

lemmas qSkelAll_simps = qSkel.simps(1) qSkel_qSkelInp

definition qFreshInp ::
"'varSort \<Rightarrow> 'var \<Rightarrow> ('index,('index,'bindex,'varSort,'var,'opSym)qTerm)input \<Rightarrow> bool"
where
"qFreshInp xs x qinp == liftAll (qFresh xs x) qinp"

definition qFreshBinp ::
"'varSort \<Rightarrow> 'var \<Rightarrow> ('bindex,('index,'bindex,'varSort,'var,'opSym)qAbs)input \<Rightarrow> bool"
where
"qFreshBinp xs x qbinp == liftAll (qFreshAbs xs x) qbinp"

lemma qFresh_qFreshInp:
"qFresh xs x (qOp delta qinp qbinp) =
 (qFreshInp xs x qinp \<and> qFreshBinp xs x qbinp)"
unfolding qFreshInp_def qFreshBinp_def by simp

(* For the qOp case, qFresh shall henceforth simplify to qFreshInp:  *)

declare qFresh.simps(2) [simp del]
declare qFresh_qFreshInp[simp]

(* and qFresh_simps and qFreshAll_simps, rather than qFresh.simps and qFreshAll.simps,
   shall refer to the simplification rules for qFresh *)

lemmas qFreshAll_simps = qFresh.simps(1) qFresh_qFreshInp

definition qGoodInp where
"qGoodInp qinp ==
 liftAll qGood qinp \<and>
 |{i. qinp i \<noteq> None}| <o |UNIV :: 'var set|"

definition qGoodBinp where
"qGoodBinp qbinp ==
 liftAll qGoodAbs qbinp \<and>
 |{i. qbinp i \<noteq> None}| <o |UNIV :: 'var set|"

lemma qGood_qGoodInp:
"qGood (qOp delta qinp qbinp) = (qGoodInp qinp \<and> qGoodBinp qbinp)"
unfolding qGoodInp_def qGoodBinp_def by auto

(* For the qOp case, qGood shall henceforth simplify to qGoodInp:  *)

declare qGood.simps(2) [simp del]
declare qGood_qGoodInp [simp]

(* and qGood_simps (and qGoodAll_simps), rather than qGood.simps,
   shall refer to the simplification rules for qGood *)

lemmas qGoodAll_simps = qGood.simps(1) qGood_qGoodInp

definition alphaInp where
"alphaInp ==
 {(qinp,qinp'). sameDom qinp qinp' \<and> liftAll2 (\<lambda>qX qX'. qX #= qX') qinp qinp'}"

definition alphaBinp where
"alphaBinp ==
 {(qbinp,qbinp'). sameDom qbinp qbinp' \<and> liftAll2 (\<lambda>qA qA'. qA $= qA') qbinp qbinp'}"

abbreviation alphaInp_abbrev (infix "%=" 50) where
"qinp %= qinp' == (qinp,qinp') \<in> alphaInp"

abbreviation alphaBinp_abbrev (infix "%%=" 50) where
"qbinp %%= qbinp' == (qbinp,qbinp') \<in> alphaBinp"

lemma alpha_alphaInp:
"(qOp delta qinp qbinp #= qOp delta' qinp' qbinp') =
 (delta = delta' \<and> qinp %= qinp' \<and> qbinp %%= qbinp')"
unfolding alphaInp_def alphaBinp_def by auto

(* For the qOp case, alpha shall henceforth simplify to alphaInp:  *)
declare alpha.simps(2) [simp del]
declare alpha_alphaInp[simp]

(* and alpha_Simps and alphaAll_Simps, rather than alpha_simps and alphaAll_simps,
   shall refer to the simplification rules for alpha *)

lemmas alphaAll_Simps =
alpha.simps(1) alpha_alphaInp
alphaAbs.simps

lemma alphaInp_refl:
"qGoodInp qinp \<Longrightarrow> qinp %= qinp"
using alpha_refl
unfolding alphaInp_def qGoodInp_def liftAll_def liftAll2_def sameDom_def
by fastforce

lemma alphaBinp_refl:
"qGoodBinp qbinp \<Longrightarrow> qbinp %%= qbinp"
using alphaAbs_refl
unfolding alphaBinp_def qGoodBinp_def liftAll_def liftAll2_def sameDom_def
by fastforce

lemma alphaInp_sym:
fixes qinp qinp' :: "('index,('index,'bindex,'varSort,'var,'opSym)qTerm)input"
shows "qinp %= qinp' \<Longrightarrow> qinp' %= qinp"
using alpha_sym unfolding alphaInp_def sameDom_def liftAll2_def by blast

lemma alphaBinp_sym:
fixes qbinp qbinp' :: "('bindex,('index,'bindex,'varSort,'var,'opSym)qAbs)input"
shows "qbinp %%= qbinp' \<Longrightarrow> qbinp' %%= qbinp"
using alphaAbs_sym unfolding alphaBinp_def sameDom_def liftAll2_def by blast

lemma alphaInp_trans:
assumes good: "qGoodInp qinp" and
        alpha1: "qinp %= qinp'" and alpha2: "qinp' %= qinp''"
shows "qinp %= qinp''"
proof-
  {fix i qX qX''  assume qinp: "qinp i = Some qX" and qinp'': "qinp'' i = Some qX''"
  then obtain qX' where qinp': "qinp' i = Some qX'"
  using alpha1 unfolding alphaInp_def sameDom_def liftAll2_def by(cases "qinp' i", force)
  hence "qX #= qX'"
  using alpha1 qinp unfolding alphaInp_def sameDom_def liftAll2_def by auto
  moreover have "qX' #= qX''" using alpha2 qinp' qinp''
  unfolding alphaInp_def sameDom_def liftAll2_def by auto
  moreover have "qGood qX" using good qinp unfolding qGoodInp_def liftAll_def by auto
  ultimately have "qX #= qX''" using alpha_trans by blast
  }
  thus ?thesis using assms unfolding alphaInp_def sameDom_def liftAll2_def by auto
qed

lemma alphaBinp_trans:
assumes good: "qGoodBinp qbinp" and
        alpha1: "qbinp %%= qbinp'" and alpha2: "qbinp' %%= qbinp''"
shows "qbinp %%= qbinp''"
proof-
  {fix i qA qA''  assume qbinp: "qbinp i = Some qA" and qbinp'': "qbinp'' i = Some qA''"
  then obtain qA' where qbinp': "qbinp' i = Some qA'"
  using alpha1 unfolding alphaBinp_def sameDom_def liftAll2_def by(cases "qbinp' i", force)
  hence "qA $= qA'"
  using alpha1 qbinp unfolding alphaBinp_def sameDom_def liftAll2_def by auto
  moreover have "qA' $= qA''" using alpha2 qbinp' qbinp''
  unfolding alphaBinp_def sameDom_def liftAll2_def by auto
  moreover have "qGoodAbs qA" using good qbinp unfolding qGoodBinp_def liftAll_def by auto
  ultimately have "qA $= qA''" using alphaAbs_trans by blast
  }
  thus ?thesis using assms unfolding alphaBinp_def sameDom_def liftAll2_def by auto
qed

lemma qSwapInp_preserves_qGoodInp:
assumes "qGoodInp qinp"
shows "qGoodInp (qinp %[[x1 \<and> x2]]_xs)"
proof-
  {let ?qinp' = "lift (qSwap xs x1 x2) qinp"
  fix xsa  let ?Left = "{i. ?qinp' i \<noteq> None}"
  have "?Left = {i. qinp i \<noteq> None}" by(auto simp add: lift_None)
  hence "|?Left| <o |UNIV :: 'var set|" using assms unfolding qGoodInp_def by auto
  }
  thus ?thesis using assms 
  unfolding qGoodInp_def qSwapInp_def liftAll_lift_comp qGoodInp_def
  unfolding comp_def liftAll_def
  by (auto simp add: qSwap_preserves_qGood simp del: not_None_eq)
qed

lemma qSwapBinp_preserves_qGoodBinp:
assumes "qGoodBinp qbinp"
shows "qGoodBinp (qbinp %%[[x1 \<and> x2]]_xs)"
proof-
  {let ?qbinp' = "lift (qSwapAbs xs x1 x2) qbinp"
  fix xsa  let ?Left = "{i. ?qbinp' i \<noteq> None}"
  have "?Left = {i. qbinp i \<noteq> None}" by(auto simp add: lift_None)
  hence "|?Left| <o |UNIV :: 'var set|" using assms unfolding qGoodBinp_def by auto
  }
  thus ?thesis using assms 
  unfolding qGoodBinp_def qSwapBinp_def liftAll_lift_comp 
  unfolding qGoodBinp_def unfolding comp_def liftAll_def
  by (auto simp add: qSwapAbs_preserves_qGoodAbs simp del: not_None_eq)
qed

lemma qSwapInp_preserves_alphaInp:
assumes "qGoodInp qinp \<or> qGoodInp qinp'" and "qinp %= qinp'"
shows "(qinp %[[x1 \<and> x2]]_xs) %= (qinp' %[[x1 \<and> x2]]_xs)"
using assms unfolding alphaInp_def qSwapInp_def sameDom_def liftAll2_def
by (simp add: lift_None)  
   (smt liftAll_def lift_def option.case_eq_if option.exhaust_sel 
      option.sel qGoodInp_def qSwap_preserves_alpha)

lemma qSwapBinp_preserves_alphaBinp:
assumes "qGoodBinp qbinp \<or> qGoodBinp qbinp'" and "qbinp %%= qbinp'"
shows "(qbinp %%[[x1 \<and> x2]]_xs) %%= (qbinp' %%[[x1 \<and> x2]]_xs)"
using assms unfolding alphaBinp_def qSwapBinp_def sameDom_def liftAll2_def
by (simp add: lift_None)
   (smt liftAll_def lift_def option.case_eq_if option.exhaust_sel option.sel 
     qGoodBinp_def qSwapAbs_preserves_alphaAbs) 

lemma qPsubstInp_preserves_qGoodInp:
assumes "qGoodInp qinp" and "qGoodEnv qrho"
shows "qGoodInp (qinp %[[qrho]])"
using assms unfolding qGoodInp_def qPsubstInp_def liftAll_def
by simp (smt Collect_cong lift_def option.case_eq_if 
   option.exhaust_sel option.sel qPsubst_preserves_qGood) 

lemma qPsubstBinp_preserves_qGoodBinp:
assumes "qGoodBinp qbinp" and "qGoodEnv qrho"
shows "qGoodBinp (qbinp %%[[qrho]])"
using assms unfolding qGoodBinp_def qPsubstBinp_def liftAll_def
by simp (smt Collect_cong lift_def option.case_eq_if 
   option.exhaust_sel option.sel qPsubstAbs_preserves_qGoodAbs)  

lemma qPsubstInp_preserves_alphaInp:
assumes "qGoodInp qinp \<or> qGoodInp qinp'" and "qGoodEnv qrho" and "qinp %= qinp'"
shows "(qinp %[[qrho]]) %= (qinp' %[[qrho]])"
using assms unfolding alphaInp_def qPsubstInp_def sameDom_def liftAll2_def
by (simp add: lift_None)
   (smt liftAll_def lift_def option.case_eq_if option.exhaust_sel 
       option.sel qGoodInp_def qPsubst_preserves_alpha1)

lemma qPsubstBinp_preserves_alphaBinp:
assumes "qGoodBinp qbinp \<or> qGoodBinp qbinp'" and "qGoodEnv qrho" and "qbinp %%= qbinp'"
shows "(qbinp %%[[qrho]]) %%= (qbinp' %%[[qrho]])"
using assms unfolding alphaBinp_def qPsubstBinp_def sameDom_def liftAll2_def
by (simp add: lift_None)
   (smt liftAll_def lift_def option.case_eq_if option.exhaust_sel 
       option.sel qGoodBinp_def qPsubstAbs_preserves_alphaAbs1) 

lemma qFreshInp_preserves_alphaInp_aux:
assumes good: "qGoodInp qinp \<or> qGoodInp qinp'" and alpha: "qinp %= qinp'"
and fresh: "qFreshInp xs x qinp"
shows "qFreshInp xs x qinp'"
using assms unfolding qFreshInp_def liftAll_def proof clarify
  fix i qX' assume qinp': "qinp' i = Some qX'"
  then obtain qX where qinp: "qinp i = Some qX"
  using alpha unfolding alphaInp_def sameDom_def liftAll2_def by (cases "qinp i", auto)
  hence "qGood qX \<or> qGood qX'"
  using qinp' good unfolding qGoodInp_def liftAll_def by auto
  moreover have "qX #= qX'"
  using qinp qinp' alpha unfolding alphaInp_def sameDom_def liftAll2_def by auto
  moreover have "qFresh xs x qX"
  using fresh qinp unfolding qFreshInp_def liftAll_def by simp
  ultimately show "qFresh xs x qX'"
  using qFresh_preserves_alpha by auto
qed

lemma qFreshBinp_preserves_alphaBinp_aux:
assumes good: "qGoodBinp qbinp \<or> qGoodBinp qbinp'" and alpha: "qbinp %%= qbinp'"
and fresh: "qFreshBinp xs x qbinp"
shows "qFreshBinp xs x qbinp'"
using assms unfolding qFreshBinp_def liftAll_def proof clarify
  fix i qA' assume qbinp': "qbinp' i = Some qA'"
  then obtain qA where qbinp: "qbinp i = Some qA"
  using alpha unfolding alphaBinp_def sameDom_def liftAll2_def by (cases "qbinp i", auto)
  hence "qGoodAbs qA \<or> qGoodAbs qA'"
  using qbinp' good unfolding qGoodBinp_def liftAll_def by auto
  moreover have "qA $= qA'"
  using qbinp qbinp' alpha unfolding alphaBinp_def sameDom_def liftAll2_def by auto
  moreover have "qFreshAbs xs x qA"
  using fresh qbinp unfolding qFreshBinp_def liftAll_def by simp
  ultimately show "qFreshAbs xs x qA'"
  using qFreshAbs_preserves_alphaAbs by auto
qed

lemma qFreshInp_preserves_alphaInp:
assumes "qGoodInp qinp \<or> qGoodInp qinp'" and "qinp %= qinp'"
shows "qFreshInp xs x qinp \<longleftrightarrow> qFreshInp xs x qinp'"
using alphaInp_sym assms qFreshInp_preserves_alphaInp_aux by blast
 
lemma qFreshBinp_preserves_alphaBinp:
assumes "qGoodBinp qbinp \<or> qGoodBinp qbinp'" and "qbinp %%= qbinp'"
shows "qFreshBinp xs x qbinp \<longleftrightarrow> qFreshBinp xs x qbinp'"
using alphaBinp_sym assms qFreshBinp_preserves_alphaBinp_aux by blast
 

(****************************************************)
lemmas qItem_simps =
qSkelAll_simps qFreshAll_simps qSwapAll_simps qPsubstAll_simps qGoodAll_simps alphaAll_Simps
qSwap_qAFresh_otherSimps qAFresh.simps qGoodItem.simps
(****************************************************)

end (* context FixVars *)

subsection {* Definitions of terms and their operators *}

type_synonym ('index,'bindex,'varSort,'var,'opSym)"term" =
      "('index,'bindex,'varSort,'var,'opSym)qTerm set"

type_synonym ('index,'bindex,'varSort,'var,'opSym)abs =
      "('index,'bindex,'varSort,'var,'opSym)qAbs set"

type_synonym ('index,'bindex,'varSort,'var,'opSym)env =
      "'varSort \<Rightarrow> 'var \<Rightarrow> ('index,'bindex,'varSort,'var,'opSym)term option"

text{* A ``parameter" will be something for which
freshness makes sense.  Here is the most typical case of a parameter in proofs, putting
together (as lists) finite collections of variables, terms, abstractions and environments:  *}

datatype ('index,'bindex,'varSort,'var,'opSym)param =
  Par "'var list"
      "('index,'bindex,'varSort,'var,'opSym)term list"
      "('index,'bindex,'varSort,'var,'opSym)abs list"
      "('index,'bindex,'varSort,'var,'opSym)env list"

fun varsOf where
"varsOf (Par xL _ _ _) = set xL"

fun termsOf where
"termsOf (Par _ XL _ _) = set XL"

fun absOf where
"absOf (Par _ _ AL _) = set AL"

fun envsOf where
"envsOf (Par _ _ _ rhoL) = set rhoL"

context FixVars  (* scope all throughout the file *)
begin

(* Recall the abbreviation "Restr r qA" for "r Int (qA <*> qA)"  *)
definition "alphaGood \<equiv> \<lambda> qX qY. qGood qX \<and> qGood qY \<and> qX #= qY"
definition "alphaAbsGood \<equiv> \<lambda> qA qB. qGoodAbs qA \<and> qGoodAbs qB \<and> qA $= qB"

definition "good \<equiv> qGood /// alphaGood"
definition "goodAbs \<equiv> qGoodAbs /// alphaAbsGood"

definition goodInp where
"goodInp inp ==
 liftAll good inp \<and>
 |{i. inp i \<noteq> None}| <o |UNIV :: 'var set|"

definition goodBinp where
"goodBinp binp ==
 liftAll goodAbs binp \<and>
 |{i. binp i \<noteq> None}| <o |UNIV :: 'var set|"

definition goodEnv where
"goodEnv rho ==
 (\<forall> ys. liftAll good (rho ys)) \<and>
 (\<forall> ys. |{y. rho ys y \<noteq> None}| <o |UNIV :: 'var set| )"

definition asTerm where
"asTerm qX \<equiv> proj alphaGood qX"

definition asAbs where
"asAbs qA \<equiv> proj alphaAbsGood qA"

definition pickInp where
"pickInp inp \<equiv> lift pick inp"

definition pickBinp where
"pickBinp binp \<equiv> lift pick binp"

(* Note: pickInp and pickBinp are the same (polymorphically), but
  I keep distinct notations for uniformity with the rest of the notations. *)

definition asInp where
"asInp qinp \<equiv> lift asTerm qinp"

definition asBinp where
"asBinp qbinp \<equiv> lift asAbs qbinp"

definition pickE where
"pickE rho \<equiv> \<lambda> xs. lift pick (rho xs)" 

definition asEnv where
"asEnv qrho \<equiv> \<lambda> xs. lift asTerm (qrho xs)"

definition Var where
"Var xs x \<equiv> asTerm(qVar xs x)"

definition Op where
"Op delta inp binp \<equiv> asTerm (qOp delta (pickInp inp) (pickBinp binp))"

definition Abs where
"Abs xs x X \<equiv> asAbs (qAbs xs x (pick X))"

definition skel where
"skel X \<equiv> qSkel (pick X)"

definition skelAbs where
"skelAbs A \<equiv> qSkelAbs (pick A)"

definition skelInp where
"skelInp inp = qSkelInp (pickInp inp)"

definition skelBinp where
"skelBinp binp = qSkelBinp (pickBinp binp)"

lemma skelInp_def2:
assumes "goodInp inp"
shows "skelInp inp = lift skel inp"
unfolding skelInp_def
unfolding qSkelInp_def pickInp_def skel_def[abs_def]
unfolding lift_comp comp_def by simp

lemma skelBinp_def2:
assumes "goodBinp binp"
shows "skelBinp binp = lift skelAbs binp"
unfolding skelBinp_def
unfolding qSkelBinp_def pickBinp_def skelAbs_def[abs_def]
unfolding lift_comp comp_def by simp

definition swap where
"swap xs x y X = asTerm (qSwap xs x y (pick X))"

abbreviation swap_abbrev ("_ #[_ \<and> _]'__" 200) where
"(X #[z1 \<and> z2]_zs) \<equiv> swap zs z1 z2 X"

definition swapAbs where
"swapAbs xs x y A = asAbs (qSwapAbs xs x y (pick A))"

abbreviation swapAbs_abbrev ("_ $[_ \<and> _]'__" 200) where
"(A $[z1 \<and> z2]_zs) \<equiv> swapAbs zs z1 z2 A"

definition swapInp where
"swapInp xs x y inp \<equiv> lift (swap xs x y) inp"

definition swapBinp where
"swapBinp xs x y binp \<equiv> lift (swapAbs xs x y) binp"

abbreviation swapInp_abbrev ("_ %[_ \<and> _]'__" 200) where
"(inp %[z1 \<and> z2]_zs) \<equiv> swapInp zs z1 z2 inp"

abbreviation swapBinp_abbrev ("_ %%[_ \<and> _]'__" 200) where
"(binp %%[z1 \<and> z2]_zs) \<equiv> swapBinp zs z1 z2 binp"

definition swapEnvDom where
"swapEnvDom xs x y rho \<equiv> \<lambda>zs z. rho zs (z @zs[x \<and> y]_xs)"

definition swapEnvIm where
"swapEnvIm xs x y rho \<equiv> \<lambda>zs. lift (swap xs x y) (rho zs)"

definition swapEnv where
"swapEnv xs x y \<equiv> swapEnvIm xs x y o swapEnvDom xs x y"

abbreviation swapEnv_abbrev ("_ &[_ \<and> _]'__" 200) where
"(rho &[z1 \<and> z2]_zs) \<equiv> swapEnv zs z1 z2 rho"

lemmas swapEnv_defs = swapEnv_def comp_def swapEnvDom_def swapEnvIm_def

inductive_set swapped where
Refl: "(X,X) \<in> swapped"
|
Trans: "\<lbrakk>(X,Y) \<in> swapped; (Y,Z) \<in> swapped\<rbrakk> \<Longrightarrow> (X,Z) \<in> swapped"
|
Swap: "(X,Y) \<in> swapped \<Longrightarrow> (X, Y #[x \<and> y]_zs) \<in> swapped"

lemmas swapped_Clauses = swapped.Refl swapped.Trans swapped.Swap

definition fresh where
"fresh xs x X \<equiv> qFresh xs x (pick X)"

definition freshAbs where
"freshAbs xs x A \<equiv> qFreshAbs xs x (pick A)"

definition freshInp where
"freshInp xs x inp \<equiv> liftAll (fresh xs x) inp"

definition freshBinp where
"freshBinp xs x binp \<equiv> liftAll (freshAbs xs x) binp"

definition freshEnv where
"freshEnv xs x rho ==
rho xs x = None \<and> (\<forall> ys. liftAll (fresh xs x) (rho ys))"

definition psubst where
"psubst rho X \<equiv> asTerm(qPsubst (pickE rho) (pick X))"

abbreviation psubst_abbrev ("_ #[_]") where
"(X #[rho]) \<equiv> psubst rho X"

definition psubstAbs where
"psubstAbs rho A \<equiv> asAbs(qPsubstAbs (pickE rho) (pick A))"

abbreviation psubstAbs_abbrev  ("_ $[_]") where
"A $[rho] \<equiv> psubstAbs rho A"

definition psubstInp where
"psubstInp rho inp \<equiv> lift (psubst rho) inp"

definition psubstBinp where
"psubstBinp rho binp \<equiv> lift (psubstAbs rho) binp"

abbreviation psubstInp_abbrev  ("_ %[_]") where
"inp %[rho] \<equiv> psubstInp rho inp"

abbreviation psubstBinp_abbrev  ("_ %%[_]") where
"binp %%[rho] \<equiv> psubstBinp rho binp"

definition psubstEnv where
"psubstEnv rho rho' \<equiv>
 \<lambda> xs x. case rho' xs x of None \<Rightarrow> rho xs x
                          |Some X \<Rightarrow> Some (X #[rho])"

abbreviation psubstEnv_abbrev ("_ &[_]") where
"rho &[rho'] \<equiv> psubstEnv rho' rho"

definition idEnv where
"idEnv \<equiv> \<lambda>xs. Map.empty"

definition updEnv ::
"('index,'bindex,'varSort,'var,'opSym)env \<Rightarrow>
 'var \<Rightarrow> ('index,'bindex,'varSort,'var,'opSym)term \<Rightarrow> 'varSort \<Rightarrow>
 ('index,'bindex,'varSort,'var,'opSym)env"
("_ [_ \<leftarrow> _]'__" 200) where
"(rho [x \<leftarrow> X]_xs) \<equiv> \<lambda> ys y. (if ys = xs \<and> y = x then Some X else rho ys y)"

text{* (Unary) substitution: *}

definition subst where
"subst xs X x \<equiv> psubst (idEnv [x \<leftarrow> X]_xs)"

abbreviation subst_abbrev ("_ #[_ '/ _]'__" 200) where
"(Y #[X / x]_xs) \<equiv> subst xs X x Y"

definition substAbs where
"substAbs xs X x \<equiv> psubstAbs (idEnv [x \<leftarrow> X]_xs)"

abbreviation substAbs_abbrev ("_ $[_ '/ _]'__" 200) where
"(A $[X / x]_xs) \<equiv> substAbs xs X x A"

definition substInp where
"substInp xs X x \<equiv> psubstInp (idEnv [x \<leftarrow> X]_xs)"

definition substBinp where
"substBinp xs X x \<equiv> psubstBinp (idEnv [x \<leftarrow> X]_xs)"

abbreviation substInp_abbrev ("_ %[_ '/ _]'__" 200) where
"(inp %[X / x]_xs) \<equiv> substInp xs X x inp"

abbreviation substBinp_abbrev ("_ %%[_ '/ _]'__" 200) where
"(binp %%[X / x]_xs) \<equiv> substBinp xs X x binp"

theorem substInp_def2:
"substInp ys Y y = lift (subst ys Y y)"
unfolding substInp_def[abs_def] subst_def psubstInp_def[abs_def] by simp

theorem substBinp_def2:
"substBinp ys Y y = lift (substAbs ys Y y)"
unfolding substBinp_def[abs_def] substAbs_def psubstBinp_def[abs_def] by simp

definition substEnv where
"substEnv xs X x \<equiv> psubstEnv (idEnv [x \<leftarrow> X]_xs)"

abbreviation substEnv_abbrev ("_ &[_ '/ _]'__" 200) where
"(Y &[X / x]_xs) \<equiv> substEnv xs X x Y"

theorem substEnv_def2:
"(rho &[Y / y]_ys) =
 (\<lambda>xs x. case rho xs x of
           None \<Rightarrow> if (xs = ys \<and> x = y) then Some Y else None
          |Some X \<Rightarrow> Some (X #[Y / y]_ys))"
unfolding substEnv_def psubstEnv_def subst_def idEnv_def updEnv_def
apply(rule ext)+ by(case_tac "rho xs x", simp_all)

text{* Variable-for-variable substitution: *}

definition vsubst where
"vsubst ys y1 y2 \<equiv> subst ys (Var ys y1) y2"

abbreviation vsubst_abbrev ("_ #[_ '/'/ _]'__" 200) where
"(X #[y1 // y2]_ys) \<equiv> vsubst ys y1 y2 X"

definition vsubstAbs where
"vsubstAbs ys y1 y2 \<equiv> substAbs ys (Var ys y1) y2"

abbreviation vsubstAbs_abbrev ("_ $[_ '/'/ _]'__" 200) where
"(A $[y1 // y2]_ys) \<equiv> vsubstAbs ys y1 y2 A"

definition vsubstInp where
"vsubstInp ys y1 y2 \<equiv> substInp ys (Var ys y1) y2"

definition vsubstBinp where
"vsubstBinp ys y1 y2 \<equiv> substBinp ys (Var ys y1) y2"

abbreviation vsubstInp_abbrev ("_ %[_ '/'/ _]'__" 200) where
"(inp %[y1 // y2]_ys) \<equiv> vsubstInp ys y1 y2 inp"

abbreviation vsubstBinp_abbrev ("_ %%[_ '/'/ _]'__" 200) where
"(binp %%[y1 // y2]_ys) \<equiv> vsubstBinp ys y1 y2 binp"

lemma vsubstInp_def2:
"(inp %[y1 // y2]_ys) = lift (vsubst ys y1 y2) inp"
unfolding vsubstInp_def vsubst_def
by(auto simp add: substInp_def2)

lemma vsubstBinp_def2:
"(binp %%[y1 // y2]_ys) = lift (vsubstAbs ys y1 y2) binp"
unfolding vsubstBinp_def vsubstAbs_def
by(auto simp add: substBinp_def2)

definition vsubstEnv where
"vsubstEnv ys y1 y2 \<equiv> substEnv ys (Var ys y1) y2"

abbreviation vsubstEnv_abbrev ("_ &[_ '/'/ _]'__" 200) where
"(rho &[y1 // y2]_ys) \<equiv> vsubstEnv ys y1 y2 rho"

theorem vsubstEnv_def2:
"(rho &[y1 // y]_ys) =
 (\<lambda>xs x. case rho xs x of
           None \<Rightarrow> if (xs = ys \<and> x = y) then Some (Var ys y1) else None
          |Some X \<Rightarrow> Some (X #[y1 // y]_ys))"
unfolding vsubstEnv_def vsubst_def by(auto simp add: substEnv_def2)

definition goodPar where
"goodPar P \<equiv> (\<forall> X \<in> termsOf P. good X) \<and>
              (\<forall> A \<in> absOf P. goodAbs A) \<and>
              (\<forall> rho \<in> envsOf P. goodEnv rho)"

lemma Par_preserves_good[simp]:
assumes "!! X. X \<in> set XL \<Longrightarrow> good X"
and "!! A. A \<in> set AL  \<Longrightarrow> goodAbs A"
and "!! rho. rho \<in> set rhoL \<Longrightarrow> goodEnv rho"
shows "goodPar (Par xL XL AL rhoL)"
using assms unfolding goodPar_def by auto

lemma termsOf_preserves_good[simp]:
assumes "goodPar P" and "X : termsOf P"
shows "good X"
using assms unfolding goodPar_def by auto

lemma absOf_preserves_good[simp]:
assumes "goodPar P" and "A : absOf P"
shows "goodAbs A"
using assms unfolding goodPar_def by auto

lemma envsOf_preserves_good[simp]:
assumes "goodPar P" and "rho : envsOf P"
shows "goodEnv rho"
using assms unfolding goodPar_def by blast

lemmas param_simps =
termsOf.simps absOf.simps envsOf.simps
Par_preserves_good
termsOf_preserves_good absOf_preserves_good envsOf_preserves_good

subsection {* Items versus quasi-items modulo alpha  *}

text{* Here we ``close the accounts" (for a while) with quasi-items  --
 beyond this subsection, there will not be any theorem that mentions
 quasi-items, except much later when we deal with iteration principles
 (and need to briefly switch back to quasi-terms in order to define the needed
 iterative map by the universality of the alpha-quotient).  *}

subsubsection {* For terms *}

lemma alphaGood_equivP: "equivP qGood alphaGood"
unfolding equivP_def reflP_def symP_def transP_def alphaGood_def
using alpha_refl alpha_sym alpha_trans by blast

lemma univ_asTerm_alphaGood[simp]:
assumes *: "congruentP alphaGood f" and **: "qGood X"
shows "univ f (asTerm X) = f X"
by (metis assms alphaGood_equivP asTerm_def univ_commute)

corollary univ_asTerm_alpha[simp]:
assumes *: "congruentP alpha f" and **: "qGood X"
shows "univ f (asTerm X) = f X"
apply(rule univ_asTerm_alphaGood)
using assms unfolding alphaGood_def congruentP_def by auto

lemma pick_inj_on_good: "inj_on pick (Collect good)"
unfolding good_def using alphaGood_equivP equivP_pick_inj_on by auto

lemma pick_injective_good[simp]:
"\<lbrakk>good X; good Y\<rbrakk> \<Longrightarrow> (pick X = pick Y) = (X = Y)"
using pick_inj_on_good unfolding inj_on_def by auto

lemma good_imp_qGood_pick:
"good X \<Longrightarrow> qGood (pick X)"
unfolding good_def
by (metis alphaGood_equivP equivP_pick_preserves)

lemma qGood_iff_good_asTerm:
"good (asTerm qX) = qGood qX"
unfolding good_def asTerm_def
using alphaGood_equivP proj_in_iff by fastforce

lemma pick_asTerm:
assumes "qGood qX"
shows "pick (asTerm qX) #= qX"
by (metis (full_types) alphaGood_def alphaGood_equivP asTerm_def assms pick_proj)

lemma asTerm_pick:
assumes "good X"
shows "asTerm (pick X) = X"
by (metis alphaGood_equivP asTerm_def assms good_def proj_pick)

lemma pick_alpha: "good X \<Longrightarrow> pick X #= pick X"
using good_imp_qGood_pick alpha_refl by auto

lemma alpha_imp_asTerm_equal:
assumes "qGood qX" and "qX #= qY"
shows "asTerm qX = asTerm qY"
proof-
  have "alphaGood qX qY" unfolding alphaGood_def using assms
  by (metis alpha_preserves_qGood)
  thus ?thesis unfolding asTerm_def using alphaGood_equivP proj_iff
  by (metis alpha_preserves_qGood1 assms)
qed

lemma asTerm_equal_imp_alpha:
assumes "qGood qX" and "asTerm qX = asTerm qY"
shows "qX #= qY"
by (metis alphaAll_sym alphaAll_trans assms pick_asTerm qGood_iff_good_asTerm)

lemma asTerm_equal_iff_alpha:
assumes "qGood qX \<or> qGood qY"
shows "(asTerm qX = asTerm qY) = (qX #= qY)"
by (metis alpha_imp_asTerm_equal alpha_sym asTerm_equal_imp_alpha assms)

lemma pick_alpha_iff_equal:
assumes "good X" and "good Y"
shows "pick X #= pick Y \<longleftrightarrow> X = Y"
by (metis asTerm_equal_iff_alpha asTerm_pick assms good_imp_qGood_pick)

lemma pick_swap_qSwap:
assumes "good X"
shows "pick (X #[x1 \<and> x2]_xs) #= ((pick X) #[[x1 \<and> x2]]_xs)"
by (metis assms good_imp_qGood_pick pick_asTerm qSwap_preserves_qGood1 swap_def)

lemma asTerm_qSwap_swap:
assumes "qGood qX"
shows "asTerm (qX #[[x1 \<and> x2]]_xs) = ((asTerm qX) #[x1 \<and> x2]_xs)"
 by (simp add: alpha_imp_asTerm_equal alpha_sym assms local.swap_def 
pick_asTerm qSwap_preserves_alpha qSwap_preserves_qGood1) 

lemma fresh_asTerm_qFresh:
assumes "qGood qX"
shows "fresh xs x (asTerm qX) = qFresh xs x qX"
by (simp add: assms fresh_def pick_asTerm qFresh_preserves_alpha)
 
(* Note that fresh and skel commute with pick by definition, so we only need
  to prove they commute with asTerm.  *)

lemma skel_asTerm_qSkel:
assumes "qGood qX"
shows "skel (asTerm qX) = qSkel qX"
by (simp add: alpha_qSkel assms pick_asTerm skel_def)
 
lemma double_swap_qSwap:
assumes "good X"
shows "qGood (((pick X) #[[x \<and> y]]_zs) #[[x' \<and> y']]_zs') \<and>
       ((X #[x \<and> y]_zs) #[x' \<and> y']_zs') = asTerm (((pick X) #[[x \<and> y]]_zs) #[[x' \<and> y']]_zs')"
by (simp add: asTerm_qSwap_swap assms 
    good_imp_qGood_pick local.swap_def qSwap_preserves_qGood1)

lemma fresh_swap_qFresh_qSwap:
assumes "good X"
shows "fresh xs x (X #[y1 \<and> y2]_ys) = qFresh xs x ((pick X) #[[y1 \<and> y2]]_ys)"
by (simp add: assms 
    fresh_asTerm_qFresh good_imp_qGood_pick local.swap_def qSwap_preserves_qGood)

subsubsection {* For abstractions *}

lemma alphaAbsGood_equivP: "equivP qGoodAbs alphaAbsGood"
unfolding equivP_def reflP_def symP_def transP_def alphaAbsGood_def
using alphaAbs_refl alphaAbs_sym alphaAbs_trans by blast

lemma univ_asAbs_alphaAbsGood[simp]:
assumes "fAbs respectsP alphaAbsGood" and "qGoodAbs A"
shows "univ fAbs (asAbs A) = fAbs A"
by (metis assms alphaAbsGood_equivP asAbs_def univ_commute)

corollary univ_asAbs_alphaAbs[simp]:
assumes *: "fAbs respectsP alphaAbs" and **: "qGoodAbs A"
shows "univ fAbs (asAbs A) = fAbs A"
apply(rule univ_asAbs_alphaAbsGood)
using assms unfolding alphaAbsGood_def congruentP_def by auto

lemma pick_inj_on_goodAbs: "inj_on pick (Collect goodAbs)"
unfolding goodAbs_def using alphaAbsGood_equivP equivP_pick_inj_on by auto

lemma pick_injective_goodAbs[simp]:
"\<lbrakk>goodAbs A; goodAbs B\<rbrakk> \<Longrightarrow> pick A = pick B \<longleftrightarrow> A = B"
using pick_inj_on_goodAbs unfolding inj_on_def by auto

lemma goodAbs_imp_qGoodAbs_pick:
"goodAbs A \<Longrightarrow> qGoodAbs (pick A)"
unfolding goodAbs_def
using alphaAbsGood_equivP equivP_pick_preserves by fastforce

lemma qGoodAbs_iff_goodAbs_asAbs:
"goodAbs(asAbs qA) = qGoodAbs qA"
unfolding goodAbs_def asAbs_def
using alphaAbsGood_equivP proj_in_iff by fastforce

lemma pick_asAbs:
assumes "qGoodAbs qA"
shows "pick (asAbs qA) $= qA"
by (metis (full_types) alphaAbsGood_def alphaAbsGood_equivP asAbs_def assms pick_proj)

lemma asAbs_pick:
assumes "goodAbs A"
shows "asAbs (pick A) = A"
by (metis alphaAbsGood_equivP asAbs_def assms goodAbs_def proj_pick)

lemma pick_alphaAbs: "goodAbs A \<Longrightarrow> pick A $= pick A"
using goodAbs_imp_qGoodAbs_pick alphaAbs_refl by auto

lemma alphaAbs_imp_asAbs_equal:
assumes "qGoodAbs qA" and "qA $= qB"
shows "asAbs qA = asAbs qB"
by (metis (no_types, hide_lams) proj_iff alphaAbsGood_def alphaAbsGood_equivP 
 alphaAbs_preserves_qGoodAbs asAbs_def assms)

lemma asAbs_equal_imp_alphaAbs:
assumes "qGoodAbs qA" and "asAbs qA = asAbs qB"
shows "qA $= qB"
by (metis alphaAbs_refl 
  alphaAbs_sym alphaAbs_trans_twice assms pick_asAbs qGoodAbs_iff_goodAbs_asAbs)
 
lemma asAbs_equal_iff_alphaAbs:
assumes "qGoodAbs qA \<or> qGoodAbs qB"
shows "(asAbs qA = asAbs qB) = (qA $= qB)"
by (metis alphaAbs_imp_asAbs_equal alphaAbs_preserves_qGoodAbs 
 asAbs_equal_imp_alphaAbs assms) 

lemma pick_alphaAbs_iff_equal:
assumes "goodAbs A" and "goodAbs B"
shows "(pick A $= pick B) = (A = B)"
using asAbs_equal_iff_alphaAbs asAbs_pick assms goodAbs_imp_qGoodAbs_pick by blast

lemma pick_swapAbs_qSwapAbs:
assumes "goodAbs A"
shows "pick (A $[x1 \<and> x2]_xs) $= ((pick A) $[[x1 \<and> x2]]_xs)"
by (simp add: assms goodAbs_imp_qGoodAbs_pick 
 pick_asAbs qSwapAbs_preserves_qGoodAbs swapAbs_def)
 
lemma asAbs_qSwapAbs_swapAbs:
assumes "qGoodAbs qA"
shows "asAbs (qA $[[x1 \<and> x2]]_xs) = ((asAbs qA) $[x1 \<and> x2]_xs)"
 by (simp add: alphaAbs_imp_asAbs_equal alphaAbs_sym assms pick_asAbs 
   qSwapAbs_preserves_alphaAbs 
  qSwapAbs_preserves_qGoodAbs1 swapAbs_def)

lemma freshAbs_asAbs_qFreshAbs:
assumes "qGoodAbs qA"
shows "freshAbs xs x (asAbs qA) = qFreshAbs xs x qA"
by (simp add: assms freshAbs_def pick_asAbs qFreshAbs_preserves_alphaAbs)

lemma skelAbs_asAbs_qSkelAbs:
assumes "qGoodAbs qA"
shows "skelAbs (asAbs qA) = qSkelAbs qA"
by (simp add: alphaAll_qSkelAll assms pick_asAbs skelAbs_def)

subsubsection {* For inputs  *}

text {* For unbound inputs: *}

lemma pickInp_inj_on_goodInp: "inj_on pickInp (Collect goodInp)"
unfolding pickInp_def[abs_def] inj_on_def  
proof(safe, rule ext)
  fix inp inp' i
  assume good: "goodInp inp" "goodInp inp'" and *: "lift pick inp = lift pick inp'"
  show "inp i = inp' i"
  proof(cases "inp i")
    assume inp: "inp i = None"
    hence "lift pick inp i = None" by (auto simp add: lift_None)
    hence "lift pick inp' i = None" using * by simp
    hence "inp' i = None" by (auto simp add: lift_None)
    thus ?thesis using inp by simp
  next
    fix X assume inp: "inp i = Some X"
    hence "lift pick inp i = Some (pick X)" unfolding lift_def by simp
    hence "lift pick inp' i = Some (pick X)" using * by simp
    then obtain X' where inp': "inp' i = Some X'" and XX': "pick X = pick X'"
    unfolding lift_def by(cases "inp' i", auto)
    hence "good X \<and> good X'"
    using inp good goodInp_def liftAll_def by (metis (hide_lams, full_types))
    hence "X = X'" using XX' by auto
    thus ?thesis unfolding inp inp' by simp
  qed
qed

lemma goodInp_imp_qGoodInp_pickInp:
assumes "goodInp inp"
shows "qGoodInp (pickInp inp)"
unfolding pickInp_def qGoodInp_def liftAll_def  
proof safe
  fix i qX assume "lift pick inp i = Some qX"
  then obtain X where inp: "inp i = Some X" and qX: "qX = pick X"
  unfolding lift_def by(cases "inp i", auto)
  hence "good X" using assms
  unfolding goodInp_def liftAll_def by simp
  thus "qGood qX" unfolding qX using good_imp_qGood_pick by auto
next
  fix xs   let ?Left = "{i. lift pick inp i \<noteq> None}"
  have "?Left = {i. inp i \<noteq> None}" by(force simp add: lift_None)
  thus "|?Left| <o |UNIV :: 'var set|" using assms unfolding goodInp_def by auto
qed

lemma qGoodInp_iff_goodInp_asInp:
"goodInp (asInp qinp) = qGoodInp qinp"
proof(unfold asInp_def)
  let ?inp = "lift asTerm qinp"
  {assume qgood_qinp: "qGoodInp qinp"
   have "goodInp ?inp"
   unfolding goodInp_def liftAll_def proof safe
     fix i X assume inp: "?inp i = Some X"
     then obtain qX where qinp: "qinp i = Some qX" and X: "X = asTerm qX"
     unfolding lift_def by(cases "qinp i", auto)
     hence "qGood qX"
     using qgood_qinp unfolding qGoodInp_def liftAll_def by auto
     thus "good X" using X qGood_iff_good_asTerm by auto
   next
     fix xs let ?Left = "{i. lift asTerm qinp i \<noteq> None}"
     have "?Left = {i. qinp i \<noteq> None}" by(auto simp add: lift_None)
     thus "|?Left| <o |UNIV :: 'var set|" using qgood_qinp unfolding qGoodInp_def by auto
   qed
  }
  moreover
  {assume good_inp: "goodInp ?inp"
   have "qGoodInp qinp"
   unfolding qGoodInp_def liftAll_def proof safe
     fix i qX assume qinp: "qinp i = Some qX"  let ?X = "asTerm qX"
     have inp: "?inp i = Some ?X" unfolding lift_def using qinp by simp
     hence "good ?X"
     using good_inp unfolding goodInp_def liftAll_def by auto
     thus "qGood qX" using qGood_iff_good_asTerm by auto
   next
     fix xs let ?Left = "{i. qinp i \<noteq> None}"
     have "?Left = {i. lift asTerm qinp i \<noteq> None}" by(auto simp add: lift_None)
     thus "|?Left| <o |UNIV :: 'var set|" using good_inp unfolding goodInp_def by auto
   qed
  }
  ultimately show "goodInp ?inp = qGoodInp qinp" by blast
qed

lemma pickInp_asInp:
assumes "qGoodInp qinp"
shows "pickInp (asInp qinp) %= qinp"
using assms unfolding pickInp_def asInp_def lift_comp  
by (smt CollectI alphaInp_def asTerm_equal_iff_alpha asTerm_pick case_prodI comp_apply liftAll2_def liftAll_def lift_def option.case(2) option.sel qGoodInp_def qGood_iff_good_asTerm 
sameDom_lift2)

lemma asInp_pickInp:
assumes "goodInp inp"
shows "asInp (pickInp inp) = inp"
unfolding asInp_def pickInp_def lift_comp
proof(rule ext)
  fix i  show "lift (asTerm \<circ> pick) inp i = inp i"
  unfolding lift_def proof(cases "inp i", simp+)
    fix X assume "inp i = Some X"
    hence "good X" using assms unfolding goodInp_def liftAll_def by simp
    thus "asTerm (pick X) = X" using asTerm_pick by auto
  qed   
qed

lemma pickInp_alphaInp:
assumes goodInp: "goodInp inp"
shows "pickInp inp %= pickInp inp"
using assms goodInp_imp_qGoodInp_pickInp alphaInp_refl by auto

lemma alphaInp_imp_asInp_equal:
assumes "qGoodInp qinp" and "qinp %= qinp'"
shows "asInp qinp = asInp qinp'"
unfolding asInp_def proof(rule ext)
  fix i show "lift asTerm qinp i = lift asTerm qinp' i"
  proof(cases "qinp i")
    assume Case1: "qinp i = None"
    hence "qinp' i = None"
    using assms unfolding alphaInp_def sameDom_def liftAll2_def by auto
    thus ?thesis using Case1 unfolding lift_def by simp
  next
    fix qX assume Case2: "qinp i = Some qX"
    then obtain qX' where qinp': "qinp' i = Some qX'"
    using assms unfolding alphaInp_def sameDom_def liftAll2_def by (cases "qinp' i", force)
    hence "qX #= qX'"
    using assms Case2 unfolding alphaInp_def sameDom_def liftAll2_def by auto
    moreover have "qGood qX" using assms Case2 unfolding qGoodInp_def liftAll_def by auto
    ultimately show ?thesis
    using Case2 qinp' alpha_imp_asTerm_equal unfolding lift_def by auto
  qed
qed

lemma asInp_equal_imp_alphaInp:
assumes "qGoodInp qinp" and "asInp qinp = asInp qinp'"
shows "qinp %= qinp'"
using assms unfolding alphaInp_def liftAll2_def sameDom_def
by simp (smt asInp_def asTerm_equal_iff_alpha liftAll_def lift_def option.case(2) 
  option.sel qGoodInp_def sameDom_def sameDom_lift2)  

lemma asInp_equal_iff_alphaInp:
"qGoodInp qinp \<Longrightarrow> (asInp qinp = asInp qinp') = (qinp %= qinp')"
using asInp_equal_imp_alphaInp alphaInp_imp_asInp_equal by blast

lemma pickInp_alphaInp_iff_equal:
assumes "goodInp inp" and "goodInp inp'"
shows "(pickInp inp %= pickInp inp') = (inp = inp')"
by (metis alphaInp_imp_asInp_equal asInp_equal_imp_alphaInp 
 asInp_pickInp assms goodInp_imp_qGoodInp_pickInp)

lemma pickInp_swapInp_qSwapInp:
assumes "goodInp inp"
shows "pickInp (inp %[x1 \<and> x2]_xs) %= ((pickInp inp) %[[x1 \<and> x2]]_xs)"
using assms unfolding alphaInp_def sameDom_def liftAll2_def 
pickInp_def swapInp_def qSwapInp_def lift_comp
by (simp add: lift_None)  
(smt assms comp_apply goodInp_imp_qGoodInp_pickInp liftAll_def lift_def local.swap_def option.case_eq_if option.sel option.simps(3) pickInp_def 
pick_asTerm qGoodInp_def qSwap_preserves_qGood1) 

lemma asInp_qSwapInp_swapInp:
assumes "qGoodInp qinp"
shows "asInp (qinp %[[x1 \<and> x2]]_xs) = ((asInp qinp) %[x1 \<and> x2]_xs)"
proof- 
  {fix i qX assume "qinp i = Some qX"
  hence "qGood qX" using assms unfolding qGoodInp_def liftAll_def by auto
  hence "asTerm (qX #[[x1 \<and> x2]]_xs) = swap xs x1 x2 (asTerm qX)"
  by(auto simp add: asTerm_qSwap_swap)
  }
  thus ?thesis
  using assms 
  by (smt asInp_def comp_apply lift_comp lift_cong qSwapInp_def swapInp_def)
qed

lemma swapInp_def2:
"(inp %[x1 \<and> x2]_xs) = asInp ((pickInp inp) %[[x1 \<and> x2]]_xs)"
unfolding swapInp_def asInp_def pickInp_def qSwapInp_def lift_def swap_def
apply(rule ext) subgoal for i by (cases "inp i") auto .

lemma freshInp_def2:
"freshInp xs x inp = qFreshInp xs x (pickInp inp)"
unfolding freshInp_def qFreshInp_def pickInp_def lift_def fresh_def liftAll_def
apply(rule iff_allI) subgoal for i by (cases "inp i") auto . 

text {* For bound inputs: *}

lemma pickBinp_inj_on_goodBinp: "inj_on pickBinp (Collect goodBinp)"
unfolding pickBinp_def[abs_def] inj_on_def 
proof(safe, rule ext)
  fix binp binp' i
  assume good: "goodBinp binp" "goodBinp binp'" and *: "lift pick binp = lift pick binp'"
  show "binp i = binp' i"
  proof(cases "binp i")
    assume binp: "binp i = None"
    hence "lift pick binp i = None" by (auto simp add: lift_None)
    hence "lift pick binp' i = None" using * by simp
    hence "binp' i = None" by (auto simp add: lift_None)
    thus ?thesis using binp by simp
  next
    fix A assume binp: "binp i = Some A"
    hence "lift pick binp i = Some (pick A)" unfolding lift_def by simp
    hence "lift pick binp' i = Some (pick A)" using * by simp
    then obtain A' where binp': "binp' i = Some A'" and AA': "pick A = pick A'"
    unfolding lift_def by(cases "binp' i", auto)
    hence "goodAbs A \<and> goodAbs A'"
    using binp good goodBinp_def liftAll_def by (metis (hide_lams, full_types))
    hence "A = A'" using AA' by auto
    thus ?thesis unfolding binp binp' by simp
  qed
qed

lemma goodBinp_imp_qGoodBinp_pickBinp:
assumes "goodBinp binp"
shows "qGoodBinp (pickBinp binp)"
unfolding pickBinp_def qGoodBinp_def liftAll_def proof safe
  fix i qA assume "lift pick binp i = Some qA"
  then obtain A where binp: "binp i = Some A" and qA: "qA = pick A"
  unfolding lift_def by(cases "binp i", auto)
  hence "goodAbs A" using assms
  unfolding goodBinp_def liftAll_def by simp
  thus "qGoodAbs qA" unfolding qA using goodAbs_imp_qGoodAbs_pick by auto
next
  fix xs   let ?Left = "{i. lift pick binp i \<noteq> None}"
  have "?Left = {i. binp i \<noteq> None}" by(force simp add: lift_None)
  thus "|?Left| <o |UNIV :: 'var set|" using assms unfolding goodBinp_def by auto
qed

lemma qGoodBinp_iff_goodBinp_asBinp:
"goodBinp (asBinp qbinp) = qGoodBinp qbinp"
proof(unfold asBinp_def)
  let ?binp = "lift asAbs qbinp"
  {assume qgood_qbinp: "qGoodBinp qbinp"
   have "goodBinp ?binp"
   unfolding goodBinp_def liftAll_def proof safe
     fix i A assume binp: "?binp i = Some A"
     then obtain qA where qbinp: "qbinp i = Some qA" and A: "A = asAbs qA"
     unfolding lift_def by(cases "qbinp i", auto)
     hence "qGoodAbs qA"
     using qgood_qbinp unfolding qGoodBinp_def liftAll_def by auto
     thus "goodAbs A" using A qGoodAbs_iff_goodAbs_asAbs by auto
   next
     fix xs let ?Left = "{i. lift asAbs qbinp i \<noteq> None}"
     have "?Left = {i. qbinp i \<noteq> None}" by(auto simp add: lift_None)
     thus "|?Left| <o |UNIV :: 'var set|" using qgood_qbinp unfolding qGoodBinp_def by auto
   qed
  }
  moreover
  {assume good_binp: "goodBinp ?binp"
   have "qGoodBinp qbinp"
   unfolding qGoodBinp_def liftAll_def proof safe
     fix i qA assume qbinp: "qbinp i = Some qA"  let ?A = "asAbs qA"
     have binp: "?binp i = Some ?A" unfolding lift_def using qbinp by simp
     hence "goodAbs ?A"
     using good_binp unfolding goodBinp_def liftAll_def by auto
     thus "qGoodAbs qA" using qGoodAbs_iff_goodAbs_asAbs by auto
   next
     fix xs let ?Left = "{i. qbinp i \<noteq> None}"
     have "?Left = {i. lift asAbs qbinp i \<noteq> None}" by(auto simp add: lift_None)
     thus "|?Left| <o |UNIV :: 'var set|" using good_binp unfolding goodBinp_def by auto
   qed
  }
  ultimately show "goodBinp ?binp = qGoodBinp qbinp" by blast
qed

lemma pickBinp_asBinp:
assumes "qGoodBinp qbinp"
shows "pickBinp (asBinp qbinp) %%= qbinp"
unfolding pickBinp_def asBinp_def lift_comp alphaBinp_def using sameDom_lift2  
by auto (smt assms comp_apply liftAll2_def liftAll_def 
lift_def option.sel option.simps(5) pick_asAbs qGoodBinp_def)

lemma asBinp_pickBinp:
assumes "goodBinp binp"
shows "asBinp (pickBinp binp) = binp"
unfolding asBinp_def pickBinp_def lift_comp 
apply(rule ext)
subgoal for i apply(cases "binp i") 
using assms asAbs_pick unfolding goodBinp_def liftAll_def lift_def by auto .

lemma pickBinp_alphaBinp:
assumes goodBinp: "goodBinp binp"
shows "pickBinp binp %%= pickBinp binp"
using assms goodBinp_imp_qGoodBinp_pickBinp alphaBinp_refl by auto

lemma alphaBinp_imp_asBinp_equal:
assumes "qGoodBinp qbinp" and "qbinp %%= qbinp'"
shows "asBinp qbinp = asBinp qbinp'"
unfolding asBinp_def proof(rule ext)
  fix i show "lift asAbs qbinp i = lift asAbs qbinp' i"
  proof(cases "qbinp i") 
    case None
    hence "qbinp' i = None"
    using assms unfolding alphaBinp_def sameDom_def liftAll2_def by auto
    thus ?thesis using None unfolding lift_def by simp
  next
    case (Some qA)
    then obtain qA' where qbinp': "qbinp' i = Some qA'"
    using assms unfolding alphaBinp_def sameDom_def liftAll2_def by (cases "qbinp' i", force)
    hence "qA $= qA'"
    using assms Some unfolding alphaBinp_def sameDom_def liftAll2_def by auto
    moreover have "qGoodAbs qA" using assms Some unfolding qGoodBinp_def liftAll_def by auto
    ultimately show ?thesis
    using Some qbinp' alphaAbs_imp_asAbs_equal unfolding lift_def by auto
  qed
qed

lemma asBinp_equal_imp_alphaBinp:
assumes "qGoodBinp qbinp" and "asBinp qbinp = asBinp qbinp'"
shows "qbinp %%= qbinp'"
using assms unfolding alphaBinp_def liftAll2_def sameDom_def
by simp (smt asAbs_equal_imp_alphaAbs asBinp_def liftAll_def 
lift_None lift_def option.inject option.simps(5) qGoodBinp_def)  

lemma asBinp_equal_iff_alphaBinp:
"qGoodBinp qbinp \<Longrightarrow> (asBinp qbinp = asBinp qbinp') = (qbinp %%= qbinp')"
using asBinp_equal_imp_alphaBinp alphaBinp_imp_asBinp_equal by blast

lemma pickBinp_alphaBinp_iff_equal:
assumes "goodBinp binp" and "goodBinp binp'"
shows "(pickBinp binp %%= pickBinp binp') = (binp = binp')"
using assms goodBinp_imp_qGoodBinp_pickBinp asBinp_pickBinp pickBinp_alphaBinp 
by (metis asBinp_equal_iff_alphaBinp)

lemma pickBinp_swapBinp_qSwapBinp:
assumes "goodBinp binp"
shows "pickBinp (binp %%[x1 \<and> x2]_xs) %%= ((pickBinp binp) %%[[x1 \<and> x2]]_xs)"
using assms unfolding pickBinp_def swapBinp_def qSwapBinp_def lift_comp
alphaBinp_def sameDom_def liftAll2_def  
by (simp add: goodBinp_def liftAll_def lift_def option.case_eq_if pick_swapAbs_qSwapAbs)

lemma asBinp_qSwapBinp_swapBinp:
assumes "qGoodBinp qbinp"
shows "asBinp (qbinp %%[[x1 \<and> x2]]_xs) = ((asBinp qbinp) %%[x1 \<and> x2]_xs)"
unfolding asBinp_def swapBinp_def qSwapBinp_def lift_comp alphaBinp_def lift_def
apply(rule ext) subgoal for i  apply(cases "qbinp i")
using assms asAbs_qSwapAbs_swapAbs by (fastforce simp add: liftAll_def qGoodBinp_def)+ .

lemma swapBinp_def2:
"(binp %%[x1 \<and> x2]_xs) = asBinp ((pickBinp binp) %%[[x1 \<and> x2]]_xs)"
unfolding swapBinp_def asBinp_def pickBinp_def qSwapBinp_def lift_def swapAbs_def
apply (rule ext) subgoal for i by (cases "binp i") simp_all . 

lemma freshBinp_def2:
"freshBinp xs x binp = qFreshBinp xs x (pickBinp binp)"
unfolding freshBinp_def qFreshBinp_def pickBinp_def lift_def freshAbs_def liftAll_def
apply (rule iff_allI) subgoal for i by (cases "binp i") simp_all .  

(* Note that psubstInp and psubstBinp are discussed in the next subsubsection,
about environments.  *)

subsubsection {* For environments *}

(* Remember we do not have any "quasi-swap" for environments --
   we plan to prove most of the things concerning parallel substitution
   and environments for equivPalence classes directly. *)

lemma goodEnv_imp_qGoodEnv_pickE:
assumes "goodEnv rho"
shows "qGoodEnv (pickE rho)"
unfolding qGoodEnv_def pickE_def
apply(auto simp del: "not_None_eq")
using assms good_imp_qGood_pick unfolding liftAll_lift_comp comp_def   
by (auto simp: goodEnv_def liftAll_def lift_None)   

lemma qGoodEnv_iff_goodEnv_asEnv:
"goodEnv (asEnv qrho) = qGoodEnv qrho"
unfolding asEnv_def unfolding goodEnv_def liftAll_lift_comp comp_def
by (auto simp: qGoodEnv_def lift_None liftAll_def qGood_iff_good_asTerm)

lemma pickE_asEnv:
assumes "qGoodEnv qrho"
shows "pickE (asEnv qrho) &= qrho"
using assms 
by (auto simp: lift_None liftAll_def lift_def alphaEnv_def sameDom_def liftAll2_def
pick_asTerm qGoodEnv_def pickE_def asEnv_def split: option.splits) 

lemma asEnv_pickE:
assumes "goodEnv rho"  shows "asEnv (pickE rho) xs x = rho xs x"
using assms asTerm_pick 
by (cases "rho xs x") (auto simp: goodEnv_def liftAll_def asEnv_def pickE_def lift_comp lift_def)
 
lemma pickE_alphaEnv:
assumes goodEnv: "goodEnv rho"  shows "pickE rho &= pickE rho"
using assms goodEnv_imp_qGoodEnv_pickE alphaEnv_refl by auto

lemma alphaEnv_imp_asEnv_equal:
assumes "qGoodEnv qrho" and "qrho &= qrho'"
shows "asEnv qrho = asEnv qrho'"
apply (rule ext)+ subgoal for xs x  apply(cases "qrho xs x") 
using assms asTerm_equal_iff_alpha alpha_imp_asTerm_equal 
by (auto simp add: alphaEnv_def sameDom_def asEnv_def lift_def 
    qGoodEnv_def liftAll_def liftAll2_def option.case_eq_if split: option.splits)
   blast+ .

lemma asEnv_equal_imp_alphaEnv:
assumes "qGoodEnv qrho" and "asEnv qrho = asEnv qrho'"
shows "qrho &= qrho'"
using assms unfolding alphaEnv_def sameDom_def liftAll2_def
apply (simp add: asEnv_def lift_None lift_def qGoodEnv_def liftAll_def) 
by (smt asTerm_equal_imp_alpha option.sel option.simps(5) option.case_eq_if option.distinct(1)) 

lemma asEnv_equal_iff_alphaEnv:
"qGoodEnv qrho \<Longrightarrow> (asEnv qrho = asEnv qrho') = (qrho &= qrho')"
using asEnv_equal_imp_alphaEnv alphaEnv_imp_asEnv_equal by blast

lemma pickE_alphaEnv_iff_equal:
assumes "goodEnv rho" and "goodEnv rho'"
shows "(pickE rho &= pickE rho') = (rho = rho')"
proof(rule iffI, safe, (rule ext)+)
  fix xs x
  assume alpha: "pickE rho &= pickE rho'"
  have qgood_rho: "qGoodEnv (pickE rho)" using assms goodEnv_imp_qGoodEnv_pickE by auto
  have "rho xs x = asEnv (pickE rho) xs x" using assms asEnv_pickE by fastforce
  also have "\<dots> = asEnv (pickE rho') xs x"
  using qgood_rho alpha alphaEnv_imp_asEnv_equal by fastforce
  also have "\<dots> = rho' xs x" using assms asEnv_pickE by fastforce
  finally show "rho xs x = rho' xs x" .
next
  have "qGoodEnv(pickE rho')" using assms goodEnv_imp_qGoodEnv_pickE by auto
  thus "pickE rho' &= pickE rho'" using alphaEnv_refl by auto
qed

lemma freshEnv_def2:
"freshEnv xs x rho = qFreshEnv xs x (pickE rho)"
unfolding freshEnv_def qFreshEnv_def pickE_def lift_def fresh_def liftAll_def
apply(cases "rho xs x") 
by (auto intro!: iff_allI) (metis map_option_case map_option_eq_Some)

lemma pick_psubst_qPsubst:
assumes "good X" and "goodEnv rho"
shows "pick (X #[rho]) #= ((pick X) #[[pickE rho]])"
by (simp add: assms goodEnv_imp_qGoodEnv_pickE good_imp_qGood_pick 
              pick_asTerm psubst_def qPsubst_preserves_qGood)
 
lemma pick_psubstAbs_qPsubstAbs:
assumes "goodAbs A" and "goodEnv rho"
shows "pick (A $[rho]) $= ((pick A) $[[pickE rho]])"
by (simp add: assms goodAbs_imp_qGoodAbs_pick goodEnv_imp_qGoodEnv_pickE pick_asAbs 
   psubstAbs_def qPsubstAbs_preserves_qGoodAbs)
 
lemma pickInp_psubstInp_qPsubstInp:
assumes good: "goodInp inp" and good_rho: "goodEnv rho"
shows "pickInp (inp %[rho]) %= ((pickInp inp) %[[pickE rho]])"
using assms unfolding pickInp_def psubstInp_def qPsubstInp_def lift_comp
unfolding alphaInp_def sameDom_def liftAll2_def
by (simp add: lift_None)  
   (smt comp_apply goodEnv_imp_qGoodEnv_pickE goodInp_imp_qGoodInp_pickInp liftAll_def lift_def map_option_case map_option_eq_Some option.sel pickInp_def 
   pick_asTerm psubst_def qGoodInp_def qPsubst_preserves_qGood)

lemma pickBinp_psubstBinp_qPsubstBinp:
assumes good: "goodBinp binp" and good_rho: "goodEnv rho"
shows "pickBinp (binp %%[rho]) %%= ((pickBinp binp) %%[[pickE rho]])"
using assms unfolding pickBinp_def psubstBinp_def qPsubstBinp_def lift_comp
unfolding alphaBinp_def sameDom_def liftAll2_def
by (simp add: lift_None)  
   (smt comp_apply goodBinp_def liftAll_def lift_def map_option_case map_option_eq_Some 
        option.sel pick_psubstAbs_qPsubstAbs)

subsubsection{* The structural alpha-equivPalence maps commute with the syntactic constructs *}

lemma pick_Var_qVar:
"pick (Var xs x) #= qVar xs x"
unfolding Var_def using pick_asTerm by force  

lemma Op_asInp_asTerm_qOp:
assumes "qGoodInp qinp" and "qGoodBinp qbinp"
shows "Op delta (asInp qinp) (asBinp qbinp) = asTerm (qOp delta qinp qbinp)"
using assms pickInp_asInp pickBinp_asBinp unfolding Op_def 
by(auto simp add: asTerm_equal_iff_alpha) 

lemma qOp_pickInp_pick_Op:
assumes "goodInp inp" and "goodBinp binp"
shows "qOp delta (pickInp inp) (pickBinp binp) #= pick (Op delta inp binp)"
using assms goodInp_imp_qGoodInp_pickInp goodBinp_imp_qGoodBinp_pickBinp  
unfolding Op_def using pick_asTerm alpha_sym by force

lemma Abs_asTerm_asAbs_qAbs:
assumes "qGood qX"
shows "Abs xs x (asTerm qX) = asAbs (qAbs xs x qX)"
using assms pick_asTerm qAbs_preserves_alpha unfolding Abs_def  
by(force simp add: asAbs_equal_iff_alphaAbs) 

lemma qAbs_pick_Abs:
assumes "good X"
shows "qAbs xs x (pick X) $= pick (Abs xs x X)"
using assms good_imp_qGood_pick  pick_asAbs alphaAbs_sym unfolding Abs_def by force

lemmas qItem_versus_item_simps =
univ_asTerm_alphaGood univ_asAbs_alphaAbsGood
univ_asTerm_alpha univ_asAbs_alphaAbs
pick_injective_good pick_injective_goodAbs

subsection {* All operators preserve the ``good'' predicate *}

(* Note: some facts here simply do not hold as ``iff"s.  *)

lemma Var_preserves_good[simp]:
"good(Var xs x::('index,'bindex,'varSort,'var,'opSym)term)"
by (metis Var_def qGood.simps(1) qGood_iff_good_asTerm)

lemma Op_preserves_good[simp]:
assumes "goodInp inp" and "goodBinp binp"
shows "good(Op delta inp binp)"
using assms goodInp_imp_qGoodInp_pickInp goodBinp_imp_qGoodBinp_pickBinp
qGood_iff_good_asTerm unfolding Op_def by fastforce
 
lemma Abs_preserves_good[simp]:
assumes good: "good X"
shows "goodAbs(Abs xs x X)"
using assms good_imp_qGood_pick qGoodAbs_iff_goodAbs_asAbs
unfolding Abs_def by fastforce

lemmas Cons_preserve_good =
Var_preserves_good Op_preserves_good Abs_preserves_good

lemma swap_preserves_good[simp]:
assumes "good X"
shows "good (X #[x \<and> y]_xs)"
using assms good_imp_qGood_pick qSwap_preserves_qGood qGood_iff_good_asTerm 
unfolding swap_def by fastforce

lemma swapAbs_preserves_good[simp]:
assumes "goodAbs A"
shows "goodAbs (A $[x \<and> y]_xs)"
using assms goodAbs_imp_qGoodAbs_pick qSwapAbs_preserves_qGoodAbs qGoodAbs_iff_goodAbs_asAbs 
unfolding swapAbs_def by fastforce

lemma swapInp_preserves_good[simp]:
assumes "goodInp inp"
shows "goodInp (inp %[x \<and> y]_xs)"
using assms    
by (auto simp: goodInp_def lift_def swapInp_def liftAll_def split: option.splits)  

lemma swapBinp_preserves_good[simp]:
assumes "goodBinp binp"
shows "goodBinp (binp %%[x \<and> y]_xs)"
using assms    
by (auto simp: goodBinp_def lift_def swapBinp_def liftAll_def split: option.splits) 

lemma swapEnvDom_preserves_good:
assumes "goodEnv rho"
shows "goodEnv (swapEnvDom xs x y rho)" (is "goodEnv ?rho'")
unfolding goodEnv_def liftAll_def  proof safe
  fix zs z X'  assume rho': "?rho' zs z = Some X'"
  hence "rho zs (z @zs[x \<and> y]_xs) = Some X'" unfolding swapEnvDom_def by simp
  thus "good X'" using assms unfolding goodEnv_def liftAll_def by simp
next
  fix xsa ys  let ?Left = "{ya. ?rho' ys ya \<noteq> None}"
  have "|{y} \<union> {ya. rho ys ya \<noteq> None}| <o |UNIV :: 'var set|"
  using assms var_infinite_INNER card_of_Un_singl_ordLess_infinite
  unfolding goodEnv_def by fastforce
  hence "|{x,y} \<union> {ya. rho ys ya \<noteq> None}| <o |UNIV :: 'var set|"
  using var_infinite_INNER card_of_Un_singl_ordLess_infinite by fastforce
  moreover
  {have "?Left \<subseteq> {x,y} \<union> {ya. rho ys ya \<noteq> None}"
   unfolding swapEnvDom_def sw_def[abs_def] by auto
   hence "|?Left| \<le>o |{x,y} \<union> {ya. rho ys ya \<noteq> None}|"
   using card_of_mono1 by auto
  }
  ultimately show "|?Left| <o |UNIV :: 'var set|" using ordLeq_ordLess_trans by blast
qed 

lemma swapEnvIm_preserves_good:
assumes "goodEnv rho"
shows "goodEnv (swapEnvIm xs x y rho)"
using assms unfolding goodEnv_def swapEnvIm_def liftAll_def
by (auto simp: lift_def split: option.splits)

lemma swapEnv_preserves_good[simp]:
assumes "goodEnv rho"
shows "goodEnv (rho &[x \<and> y]_xs)"
unfolding swapEnv_def comp_def
using assms by(auto simp add: swapEnvDom_preserves_good swapEnvIm_preserves_good)

lemmas swapAll_preserve_good =
swap_preserves_good swapAbs_preserves_good
swapInp_preserves_good swapBinp_preserves_good
swapEnv_preserves_good

lemma psubst_preserves_good[simp]:
assumes  "goodEnv rho" and "good X"
shows "good (X #[rho])"
using assms good_imp_qGood_pick goodEnv_imp_qGoodEnv_pickE  
qPsubst_preserves_qGood qGood_iff_good_asTerm unfolding psubst_def by fastforce

lemma psubstAbs_preserves_good[simp]:
assumes good_rho: "goodEnv rho" and goodAbs_A: "goodAbs A"
shows "goodAbs (A $[rho])"
using assms goodAbs_A goodAbs_imp_qGoodAbs_pick  goodEnv_imp_qGoodEnv_pickE 
qPsubstAbs_preserves_qGoodAbs qGoodAbs_iff_goodAbs_asAbs unfolding psubstAbs_def by fastforce

lemma psubstInp_preserves_good[simp]:
assumes good_rho: "goodEnv rho" and good: "goodInp inp"
shows "goodInp (inp %[rho])"
using assms unfolding goodInp_def psubstInp_def liftAll_def 
by (auto simp add: lift_def split: option.splits)

lemma psubstBinp_preserves_good[simp]:
assumes good_rho: "goodEnv rho" and good: "goodBinp binp"
shows "goodBinp (binp %%[rho])"
using assms unfolding goodBinp_def psubstBinp_def liftAll_def 
by (auto simp add: lift_def split: option.splits) 

lemma psubstEnv_preserves_good[simp]:
assumes good: "goodEnv rho" and good': "goodEnv rho'"
shows "goodEnv (rho &[rho'])"
unfolding goodEnv_def liftAll_def
proof safe
  fix zs z X'
  assume *: "(rho &[rho']) zs z = Some X'"
  show "good X'"
  proof(cases "rho zs z")
    case None
    hence "rho' zs z = Some X'" using * unfolding psubstEnv_def by auto
    thus ?thesis using good' unfolding goodEnv_def liftAll_def by auto
  next
    case (Some X)
    hence "X' = (X #[rho'])" using * unfolding psubstEnv_def by auto
    moreover have "good X" using Some good unfolding goodEnv_def liftAll_def by auto
    ultimately show ?thesis using good' psubst_preserves_good by auto
  qed
next
  fix xs ys  let ?Left = "{y. (rho &[rho']) ys y \<noteq> None}"
  let ?Left1 = "{y. rho ys y \<noteq> None}"  let ?Left2 = "{y. rho' ys y \<noteq> None}"
  have "|?Left1| <o |UNIV :: 'var set| \<and> |?Left2| <o |UNIV :: 'var set|"
  using good good' unfolding goodEnv_def by simp
  hence "|?Left1 \<union> ?Left2| <o |UNIV :: 'var set|"
  using var_infinite_INNER card_of_Un_ordLess_infinite by auto
  moreover
  {have "?Left \<subseteq> ?Left1 \<union> ?Left2" unfolding psubstEnv_def by auto
   hence "|?Left| \<le>o |?Left1 \<union> ?Left2|" using card_of_mono1 by auto
  }
  ultimately show "|?Left| <o |UNIV :: 'var set|" using ordLeq_ordLess_trans by blast
qed

lemmas psubstAll_preserve_good =
psubst_preserves_good psubstAbs_preserves_good
psubstInp_preserves_good psubstBinp_preserves_good
psubstEnv_preserves_good

lemma idEnv_preserves_good[simp]: "goodEnv idEnv"
unfolding goodEnv_def idEnv_def liftAll_def
using var_infinite_INNER finite_ordLess_infinite2 by auto

lemma updEnv_preserves_good[simp]:
assumes good_X: "good X" and good_rho: "goodEnv rho"
shows "goodEnv (rho [x \<leftarrow> X]_xs)"
using assms unfolding updEnv_def goodEnv_def liftAll_def
proof safe
  fix ys y Y
  assume "good X" and "\<forall>ys y Y. rho ys y = Some Y \<longrightarrow> good Y"
  and "(if ys = xs \<and> y = x then Some X else rho ys y) = Some Y"
  thus "good Y"
  by(cases "ys = xs \<and> y = x") auto
next
  fix ys
  let ?V' = "{y.  (if ys = xs \<and> y = x then Some X else rho ys y) \<noteq> None}"
  let ?V = "\<lambda> ys. {y. rho ys y \<noteq> None}"
  assume "\<forall> ys. |?V ys| <o |UNIV :: 'var set|"
  hence "|{x} \<union> ?V ys| <o |UNIV :: 'var set|"
  using var_infinite_INNER card_of_Un_singl_ordLess_infinite by fastforce
  moreover
  {have "?V' \<subseteq> {x} \<union> ?V ys" by auto
   hence "|?V'| \<le>o |{x} \<union> ?V ys|" using card_of_mono1 by auto
  }
  ultimately show "|?V'| <o |UNIV :: 'var set|" using ordLeq_ordLess_trans by blast
qed

lemma getEnv_preserves_good[simp]:
assumes "goodEnv rho" and "rho xs x = Some X"
shows "good X"
using assms unfolding goodEnv_def liftAll_def by simp

lemmas envOps_preserve_good =
idEnv_preserves_good updEnv_preserves_good
getEnv_preserves_good

lemma subst_preserves_good[simp]:
assumes "good X" and "good Y"
shows "good (Y #[X / x]_xs)"
unfolding subst_def
using assms by simp

lemma substAbs_preserves_good[simp]:
assumes "good X" and "goodAbs A"
shows "goodAbs (A $[X / x]_xs)"
unfolding substAbs_def
using assms by simp

lemma substInp_preserves_good[simp]:
assumes "good X" and "goodInp inp"
shows "goodInp (inp %[X / x]_xs)"
unfolding substInp_def using assms by simp

lemma substBinp_preserves_good[simp]:
assumes "good X" and "goodBinp binp"
shows "goodBinp (binp %%[X / x]_xs)"
unfolding substBinp_def using assms by simp

lemma substEnv_preserves_good[simp]:
assumes "good X" and "goodEnv rho"
shows "goodEnv (rho &[X / x]_xs)"
unfolding substEnv_def using assms by simp

lemmas substAll_preserve_good =
subst_preserves_good substAbs_preserves_good
substInp_preserves_good substBinp_preserves_good
substEnv_preserves_good

lemma vsubst_preserves_good[simp]:
assumes "good Y"
shows "good (Y #[x1 // x]_xs)"
unfolding vsubst_def using assms by simp

lemma vsubstAbs_preserves_good[simp]:
assumes "goodAbs A"
shows "goodAbs (A $[x1 // x]_xs)"
unfolding vsubstAbs_def using assms by simp

lemma vsubstInp_preserves_good[simp]:
assumes "goodInp inp"
shows "goodInp (inp %[x1 // x]_xs)"
unfolding vsubstInp_def using assms by simp

lemma vsubstBinp_preserves_good[simp]:
assumes "goodBinp binp"
shows "goodBinp (binp %%[x1 // x]_xs)"
unfolding vsubstBinp_def using assms by simp

lemma vsubstEnv_preserves_good[simp]:
assumes "goodEnv rho"
shows "goodEnv (rho &[x1 // x]_xs)"
unfolding vsubstEnv_def using assms by simp

lemmas vsubstAll_preserve_good =
vsubst_preserves_good vsubstAbs_preserves_good
vsubstInp_preserves_good vsubstBinp_preserves_good
vsubstEnv_preserves_good

lemmas all_preserve_good =
Cons_preserve_good
swapAll_preserve_good
psubstAll_preserve_good
envOps_preserve_good
substAll_preserve_good
vsubstAll_preserve_good

subsubsection {* The syntactic operators are almost constructors *}

text{* The only one that does not act precisely like a constructor is ``Abs". *}

theorem Var_inj[simp]:
"(((Var xs x)::('index,'bindex,'varSort,'var,'opSym)term) = Var ys y) =
 (xs = ys \<and> x = y)"
by (metis alpha_qVar_iff pick_Var_qVar qTerm.inject)

lemma Op_inj[simp]:
assumes "goodInp inp" and "goodBinp binp"
and "goodInp inp'" and "goodBinp binp'"
shows
"(Op delta inp binp = Op delta' inp' binp') =
 (delta = delta' \<and> inp = inp' \<and> binp = binp')"
using assms pickInp_alphaInp_iff_equal pickBinp_alphaBinp_iff_equal 
goodInp_imp_qGoodInp_pickInp goodBinp_imp_qGoodBinp_pickBinp 
unfolding Op_def by (fastforce simp: asTerm_equal_iff_alpha) 

text{* ``Abs" is almost injective (``ainj"), with almost injectivity expressed
   in two ways:
   \\- maximally, using "forall" -- this is suitable for elimination of ``Abs" equalities;
   \\- minimally, using "exists" -- this is suitable for introduction of ``Abs" equalities.
 *}

lemma Abs_ainj_all:
assumes good: "good X" and good': "good X'"
shows
"(Abs xs x X = Abs xs' x' X') =
 (xs = xs' \<and>
  (\<forall> y. (y = x \<or> fresh xs y X) \<and> (y = x' \<or> fresh xs y X') \<longrightarrow>
        (X #[y \<and> x]_xs) = (X' #[y \<and> x']_xs)))"
proof-
  let ?qX = "pick X"  let ?qX' = "pick X'"
  have qgood: "qGood ?qX \<and> qGood ?qX'" using good good' good_imp_qGood_pick by auto
  hence qgood_qXyx: "\<forall> y. qGood (?qX #[[y \<and> x]]_xs)"
  using qSwap_preserves_qGood by auto
  have "qGoodAbs(qAbs xs x ?qX)" using qgood by simp
  hence "(Abs xs x X = Abs xs' x' X') = (qAbs xs x ?qX $= qAbs xs' x' ?qX')"
  unfolding Abs_def by (auto simp add: asAbs_equal_iff_alphaAbs)
  also
  have "\<dots> = (xs = xs' \<and>
             (\<forall> y. (y = x \<or> qFresh xs y ?qX) \<and> (y = x' \<or> qFresh xs y ?qX') \<longrightarrow>
                   (?qX #[[y \<and> x]]_xs) #= (?qX' #[[y \<and> x']]_xs)))"
  using qgood alphaAbs_qAbs_iff_all_equal_or_qFresh[of ?qX ?qX'] by blast
  also
  have "\<dots> = (xs = xs' \<and>
             (\<forall> y. (y = x \<or> fresh xs y X) \<and> (y = x' \<or> fresh xs y X') \<longrightarrow>
                   (X #[y \<and> x]_xs) = (X' #[y \<and> x']_xs)))"
  unfolding fresh_def swap_def using qgood_qXyx by (auto simp add: asTerm_equal_iff_alpha)
  finally show ?thesis .
qed

lemma Abs_ainj_ex:
assumes good: "good X" and good': "good X'"
shows
"(Abs xs x X = Abs xs' x' X') =
 (xs = xs' \<and>
  (\<exists> y. y \<notin> {x,x'} \<and> fresh xs y X \<and> fresh xs y X' \<and>
        (X #[y \<and> x]_xs) = (X' #[y \<and> x']_xs)))"
proof-
  let ?qX = "pick X"  let ?qX' = "pick X'"
  have qgood: "qGood ?qX \<and> qGood ?qX'" using good good' good_imp_qGood_pick by auto
  hence qgood_qXyx: "\<forall> y. qGood (?qX #[[y \<and> x]]_xs)"
  using qSwap_preserves_qGood by auto
  have "qGoodAbs(qAbs xs x ?qX)" using qgood by simp
  hence "(Abs xs x X = Abs xs' x' X') = (qAbs xs x ?qX $= qAbs xs' x' ?qX')"
  unfolding Abs_def by (auto simp add: asAbs_equal_iff_alphaAbs)
  also
  have "\<dots> =  (xs = xs' \<and>
              (\<exists> y. y \<notin> {x,x'} \<and> qFresh xs y ?qX \<and> qFresh xs y ?qX' \<and>
                    (?qX #[[y \<and> x]]_xs) #= (?qX' #[[y \<and> x']]_xs)))"
  using qgood alphaAbs_qAbs_iff_ex_distinct_qFresh[of ?qX xs x xs' x' ?qX'] by blast
  also
  have "\<dots> =  (xs = xs' \<and>
               (\<exists> y. y \<notin> {x,x'} \<and> fresh xs y X \<and> fresh xs y X' \<and>
                     (X #[y \<and> x]_xs) = (X' #[y \<and> x']_xs)))"
  unfolding fresh_def swap_def using qgood_qXyx asTerm_equal_iff_alpha by auto
  finally show ?thesis .
qed

lemma Abs_cong[fundef_cong]:
assumes good: "good X" and good': "good X'"
and y: "fresh xs y X" and y': "fresh xs y X'"
and eq: "(X #[y \<and> x]_xs) = (X' #[y \<and> x']_xs)"
shows "Abs xs x X = Abs xs x' X'"
proof-
  let ?qX = "pick X"  let ?qX' = "pick X'"
  have qgood: "qGood ?qX \<and> qGood ?qX'" using good good' good_imp_qGood_pick by auto
  hence qgood_qXyx: "\<forall> y. qGood (?qX #[[y \<and> x]]_xs)"
  using qSwap_preserves_qGood by auto
  have qEq: "(?qX #[[y \<and> x]]_xs) #= (?qX' #[[y \<and> x']]_xs)"
  using eq unfolding fresh_def swap_def
  using qgood_qXyx asTerm_equal_iff_alpha by auto
  have "(qAbs xs x ?qX $= qAbs xs x' ?qX')"
  apply(rule alphaAbs_ex_equal_or_qFresh_imp_alphaAbs_qAbs)
  using qgood apply simp
  unfolding alphaAbs_ex_equal_or_qFresh_def using y y' qEq
  unfolding fresh_def by auto
  moreover have "qGoodAbs(qAbs xs x ?qX)" using qgood by simp
  ultimately show "Abs xs x X = Abs xs x' X'"
  unfolding Abs_def by (auto simp add: asAbs_equal_iff_alphaAbs)
qed

lemma Abs_swap_fresh:
assumes good_X: "good X" and fresh: "fresh xs x' X"
shows "Abs xs x X = Abs xs x' (X #[x' \<and> x]_xs)"
proof-
  let ?x'x = "swap xs x' x"   let ?qx'x = "qSwap xs x' x"
  have good_pickX: "qGood (pick X)" using good_X good_imp_qGood_pick by auto
  hence good_qAbs_pickX: "qGoodAbs (qAbs xs x (pick X))" by simp
  have good_x'x_pickX: "qGood (?qx'x (pick X))"
  using good_pickX qSwap_preserves_qGood by auto
  (*  *)
  have "Abs xs x X = asAbs (qAbs xs x (pick X))" unfolding Abs_def by simp
  also
  {have "qAbs xs x (pick X) $= qAbs xs x' (?qx'x (pick X))"
   using good_pickX fresh unfolding fresh_def using qAbs_alphaAbs_qSwap_qFresh by fastforce
   moreover
   {have "?qx'x (pick X) #= pick (?x'x X)"
    using good_X by (auto simp add: pick_swap_qSwap alpha_sym)
    hence "qAbs xs x' (?qx'x (pick X)) $= qAbs xs x' (pick (?x'x X))"
    using good_x'x_pickX qAbs_preserves_alpha by fastforce
   }
   ultimately have "qAbs xs x (pick X) $= qAbs xs x' (pick (?x'x X))"
   using good_qAbs_pickX alphaAbs_trans by blast
   hence "asAbs (qAbs xs x (pick X)) = asAbs (qAbs xs x' (pick (?x'x X)))"
   using good_qAbs_pickX by (auto simp add: asAbs_equal_iff_alphaAbs)
  }
  also have "asAbs (qAbs xs x' (pick (?x'x X))) = Abs xs x' (?x'x X)"
  unfolding Abs_def by auto
  finally show ?thesis .
qed

lemma Var_diff_Op[simp]:
"Var xs x \<noteq> Op delta inp binp"
by (simp add: Op_def Var_def asTerm_equal_iff_alpha)

lemma Op_diff_Var[simp]:
"Op delta inp binp \<noteq> Var xs x"
using Var_diff_Op[of _ _ _ inp] by blast

theorem term_nchotomy:
assumes "good X"
shows
"(\<exists> xs x. X = Var xs x) \<or>
 (\<exists> delta inp binp. goodInp inp \<and> goodBinp binp \<and> X = Op delta inp binp)"
proof-
  let ?qX = "pick X"
  have good_qX: "qGood ?qX" using assms good_imp_qGood_pick by auto
  have X: "X = asTerm ?qX" using assms asTerm_pick by auto
  show ?thesis
  proof(cases "?qX")
    fix xs x  assume Case1: "?qX = qVar xs x"
    have "X = Var xs x" unfolding Var_def using X Case1 by simp
    thus ?thesis by blast
  next
    fix delta qinp qbinp assume Case2: "?qX = qOp delta qinp qbinp"
    hence good_qinp: "qGoodInp qinp \<and> qGoodBinp qbinp" using good_qX by simp
    let ?inp = "asInp qinp"  let ?binp = "asBinp qbinp"
    have "qinp %= pickInp ?inp \<and> qbinp %%= pickBinp ?binp"
    using good_qinp pickInp_asInp alphaInp_sym pickBinp_asBinp alphaBinp_sym by blast
    hence "qOp delta qinp qbinp #= qOp delta (pickInp ?inp) (pickBinp ?binp)" by simp
    hence "asTerm (qOp delta qinp qbinp) = Op delta ?inp ?binp"
    unfolding Op_def using Case2 good_qX by (auto simp add: asTerm_equal_iff_alpha)
    hence "X = Op delta ?inp ?binp" using X Case2 by auto
    moreover have "goodInp ?inp \<and> goodBinp ?binp"
    using good_qinp qGoodInp_iff_goodInp_asInp qGoodBinp_iff_goodBinp_asBinp by auto
    ultimately show ?thesis by blast
  qed
qed

theorem abs_nchotomy:
assumes "goodAbs A"
shows "\<exists> xs x X. good X \<and> A = Abs xs x X"
by (metis Abs_asTerm_asAbs_qAbs asAbs_pick assms 
     goodAbs_imp_qGoodAbs_pick qGoodAbs.elims(2) qGood_iff_good_asTerm)
 
lemmas good_freeCons =
Op_inj Var_diff_Op Op_diff_Var

subsection {* Properties lifted from quasi-terms to terms *}

subsubsection {* Simplification rules *}

theorem swap_Var_simp[simp]:
"((Var xs x) #[y1 \<and> y2]_ys) = Var xs (x @xs[y1 \<and> y2]_ys)"
by (metis QuasiTerms_Swap_Fresh.qSwapAll_simps(1) Var_def asTerm_qSwap_swap qItem_simps(9))

lemma swap_Op_simp[simp]:
assumes "goodInp inp"  "goodBinp binp"
shows "((Op delta inp binp) #[x1 \<and> x2]_xs) =
       Op delta (inp %[x1 \<and> x2]_xs) (binp %%[x1 \<and> x2]_xs)"
by (metis Op_asInp_asTerm_qOp Op_def asTerm_qSwap_swap assms(1) assms(2) goodBinp_imp_qGoodBinp_pickBinp goodInp_imp_qGoodInp_pickInp qGood_qGoodInp qSwapBinp_preserves_qGoodBinp 
     qSwapInp_preserves_qGoodInp qSwap_qSwapInp swapBinp_def2 swapInp_def2)

lemma swapAbs_simp[simp]:
assumes "good X"
shows "((Abs xs x X) $[y1 \<and> y2]_ys) = Abs xs (x @xs[y1 \<and> y2]_ys) (X #[y1 \<and> y2]_ys)"
by (metis Abs_asTerm_asAbs_qAbs Abs_preserves_good alphaAbs_preserves_qGoodAbs2 asAbs_qSwapAbs_swapAbs assms goodAbs_imp_qGoodAbs_pick good_imp_qGood_pick local.Abs_def 
     local.swap_def qAbs_pick_Abs qSwapAbs.simps qSwap_preserves_qGood1)

lemmas good_swapAll_simps =
swap_Op_simp swapAbs_simp

theorem fresh_Var_simp[simp]:
"fresh ys y (Var xs x :: ('index,'bindex,'varSort,'var,'opSym)term) \<longleftrightarrow>
 (ys \<noteq> xs \<or> y \<noteq> x)"
by (simp add: Var_def fresh_asTerm_qFresh)
 
lemma fresh_Op_simp[simp]:
assumes "goodInp inp" "goodBinp binp"
shows
"fresh xs x (Op delta inp binp) \<longleftrightarrow>
 (freshInp xs x inp \<and> freshBinp xs x binp)"
by (metis Op_def Op_preserves_good assms(1) assms(2) freshBinp_def2 
freshInp_def2 fresh_asTerm_qFresh qFresh_qFreshInp qGood_iff_good_asTerm)
 
lemma freshAbs_simp[simp]:
assumes "good X"
shows "freshAbs ys y (Abs xs x X) \<longleftrightarrow> (ys = xs \<and> y = x \<or> fresh ys y X)"
proof-
  let ?fr = "fresh ys y"  let ?qfr = "qFresh ys y"
  let ?frA = "freshAbs ys y"  let ?qfrA = "qFreshAbs ys y"
  have "qGood (pick X)" using assms by(auto simp add: good_imp_qGood_pick)
  hence good_qAbs_pick_X: "qGoodAbs (qAbs xs x (pick X))"
  using assms good_imp_qGood_pick by auto
  (*  *)
  have "?frA (Abs xs x X) = ?qfrA ((pick o asAbs) (qAbs xs x (pick X)))"
  unfolding freshAbs_def Abs_def by simp
  also
  {have "(pick o asAbs) (qAbs xs x (pick X)) $= qAbs xs x (pick X)"
   using good_qAbs_pick_X pick_asAbs by fastforce
   hence "?qfrA ((pick o asAbs) (qAbs xs x (pick X))) = ?qfrA (qAbs xs x (pick X))"
   using good_qAbs_pick_X qFreshAbs_preserves_alphaAbs by blast
  }
  also have "?qfrA(qAbs xs x (pick X)) = (ys = xs \<and> y = x \<or> ?qfr (pick X))" by simp
  also have "\<dots> = (ys = xs \<and> y = x \<or> ?fr X)" unfolding fresh_def by simp
  finally show ?thesis .
qed

lemmas good_freshAll_simps =
fresh_Op_simp freshAbs_simp

theorem skel_Var_simp[simp]:
"skel (Var xs x) = Branch Map.empty Map.empty"
by (metis alpha_qSkel pick_Var_qVar qSkel.simps(1) skel_def) 

lemma skel_Op_simp[simp]:
assumes "goodInp inp" and "goodBinp binp"
shows "skel (Op delta inp binp) = Branch (skelInp inp) (skelBinp binp)"
by (metis (no_types, lifting) alpha_qSkel assms 
      qOp_pickInp_pick_Op qSkel_qSkelInp skelBinp_def skelInp_def skel_def)

lemma skelAbs_simp[simp]:
assumes "good X"
shows "skelAbs (Abs xs x X) = Branch (\<lambda>i. Some (skel X)) Map.empty"
by (metis alphaAll_qSkelAll assms qAbs_pick_Abs qSkelAbs.simps skelAbs_def skel_def)

lemmas good_skelAll_simps =
skel_Op_simp skelAbs_simp

lemma psubst_Var:
assumes "goodEnv rho"
shows "((Var xs x) #[rho]) =
        (case rho xs x of None \<Rightarrow> Var xs x
                         |Some X \<Rightarrow> X)"
proof-
  let ?X = "Var xs x"  let ?qX = "qVar xs x"
  let ?qrho = "pickE rho"
  have good_qX: "qGood ?qX" using assms by simp
  moreover have good_qrho: "qGoodEnv ?qrho" using assms goodEnv_imp_qGoodEnv_pickE by auto
  ultimately have good_qXrho: "qGood (?qX #[[?qrho]])"
  using assms qPsubst_preserves_qGood by(auto simp del: qGoodAll_simps qPsubst.simps)
  (*  *)
  have "(?X #[rho]) = asTerm ((pick (asTerm ?qX)) #[[?qrho]])"
  unfolding Var_def psubst_def by simp
  also
  {have "?qX  #= pick (asTerm ?qX)" using good_qX pick_asTerm alpha_sym by fastforce
   hence "(?qX #[[?qrho]]) #= ((pick (asTerm ?qX)) #[[?qrho]])"
   using good_qrho good_qX qPsubst_preserves_alpha1[of _ ?qX] by fastforce
   hence "asTerm ((pick (asTerm ?qX))  #[[?qrho]]) = asTerm (?qX #[[?qrho]])"
   using good_qXrho asTerm_equal_iff_alpha[of "?qX #[[?qrho]]"] by blast
  }
  also have "asTerm (?qX #[[?qrho]]) =
             asTerm (case ?qrho xs x of None \<Rightarrow> qVar xs x
                                       |Some qY \<Rightarrow> qY)" unfolding Var_def by simp
  finally have 1: "(?X #[rho]) =  asTerm (case ?qrho xs x of None \<Rightarrow> qVar xs x
                                                            |Some qY \<Rightarrow> qY)" .
  show ?thesis
  proof(cases "rho xs x")
    assume Case1: "rho xs x = None"
    hence "?qrho xs x = None" unfolding pickE_def lift_def by simp
    thus ?thesis using 1 Case1 unfolding Var_def by simp
  next
    fix X assume Case2: "rho xs x = Some X"
    hence "good X" using assms unfolding goodEnv_def liftAll_def by auto
    hence "asTerm (pick X) = X" using asTerm_pick by auto
    moreover have qrho: "?qrho xs x = Some (pick X)"
    using Case2 unfolding pickE_def lift_def by simp
    ultimately show ?thesis using 1 Case2 unfolding Var_def by simp
  qed
qed

corollary psubst_Var_simp1[simp]:
assumes "goodEnv rho" and "rho xs x = None"
shows "((Var xs x) #[rho]) = Var xs x"
using assms by(simp add: psubst_Var)

corollary psubst_Var_simp2[simp]:
assumes "goodEnv rho" and "rho xs x = Some X"
shows "((Var xs x) #[rho]) = X"
using assms by(simp add: psubst_Var)

lemma psubst_Op_simp[simp]:
assumes good_inp: "goodInp inp"  "goodBinp binp"
and good_rho: "goodEnv rho"
shows
"((Op delta inp binp) #[rho]) = Op delta (inp %[rho]) (binp %%[rho])"
proof-
  let ?qrho = "pickE rho"
  let ?sbs = "psubst rho"   let ?qsbs = "qPsubst ?qrho"
  let ?sbsI = "psubstInp rho"  let ?qsbsI = "qPsubstInp ?qrho"
  let ?sbsB = "psubstBinp rho"  let ?qsbsB = "qPsubstBinp ?qrho"
  let ?op = "Op delta"   let ?qop = "qOp delta"
  have good_qop_pickInp_inp: "qGood (?qop (pickInp inp) (pickBinp binp))"
  using good_inp goodInp_imp_qGoodInp_pickInp
                 goodBinp_imp_qGoodBinp_pickBinp by auto
  hence "qGood ((pick o asTerm) (?qop (pickInp inp) (pickBinp binp)))"
  using good_imp_qGood_pick qGood_iff_good_asTerm by fastforce
  moreover have good_qrho: "qGoodEnv ?qrho"
  using good_rho goodEnv_imp_qGoodEnv_pickE by auto
  ultimately have good: "qGood (?qsbs((pick o asTerm) (?qop (pickInp inp) (pickBinp binp))))"
  using qPsubst_preserves_qGood by auto
  (*  *)
  have "?sbs (?op inp binp) =
        asTerm (?qsbs ((pick o asTerm) (?qop (pickInp inp) (pickBinp binp))))"
  unfolding psubst_def Op_def by simp
  also
  {have "(pick o asTerm) (?qop (pickInp inp) (pickBinp binp)) #=
         ?qop (pickInp inp) (pickBinp binp)"
   using good_qop_pickInp_inp pick_asTerm by fastforce
   hence "?qsbs((pick o asTerm) (?qop (pickInp inp) (pickBinp binp))) #=
          ?qsbs(?qop (pickInp inp) (pickBinp binp))"
   using good_qop_pickInp_inp good_qrho qPsubst_preserves_alpha1 by fastforce
   moreover have "?qsbs (?qop (pickInp inp) (pickBinp binp)) =
                  ?qop (?qsbsI (pickInp inp)) (?qsbsB (pickBinp binp))" by simp
   moreover
   {have "?qsbsI (pickInp inp) %= pickInp (?sbsI inp) \<and>
          ?qsbsB (pickBinp binp) %%= pickBinp (?sbsB binp)"
    using good_rho good_inp pickInp_psubstInp_qPsubstInp[of inp rho]
          pickBinp_psubstBinp_qPsubstBinp[of binp rho] alphaInp_sym alphaBinp_sym by auto
    hence "?qop (?qsbsI (pickInp inp)) (?qsbsB (pickBinp binp)) #=
           ?qop (pickInp (?sbsI inp)) (pickBinp (?sbsB binp))" by simp
   }
   ultimately have "?qsbs((pick o asTerm) (?qop (pickInp inp) (pickBinp binp))) #=
                    ?qop (pickInp (?sbsI inp)) (pickBinp (?sbsB binp))"
   using good alpha_trans by force
   hence "asTerm (?qsbs((pick o asTerm) (?qop (pickInp inp) (pickBinp binp)))) =
          asTerm (?qop (pickInp (?sbsI inp)) (pickBinp (?sbsB binp)))"
   using good by (auto simp add: asTerm_equal_iff_alpha)
  }
  also have "asTerm (?qop (pickInp (?sbsI inp)) (pickBinp (?sbsB binp))) =
             ?op (?sbsI inp) (?sbsB binp)" unfolding Op_def by simp
  finally show ?thesis .
qed

lemma psubstAbs_simp[simp]:
assumes good_X: "good X" and good_rho: "goodEnv rho" and
        x_fresh_rho: "freshEnv xs x rho"
shows "((Abs xs x X) $[rho]) = Abs xs x (X #[rho])"
proof-
  let ?qrho = "pickE rho"
  let ?sbs = "psubst rho"  let ?qsbs = "qPsubst ?qrho"
  let ?sbsA = "psubstAbs rho"  let ?qsbsA = "qPsubstAbs ?qrho"
  have good_qrho: "qGoodEnv ?qrho"
  using good_rho goodEnv_imp_qGoodEnv_pickE by auto
  have good_pick_X: "qGood (pick X)" using good_X good_imp_qGood_pick by auto
  hence good_qsbs_pick_X: "qGood(?qsbs (pick X))"
  using good_qrho qPsubst_preserves_qGood by auto
  have good_qAbs_pick_X: "qGoodAbs (qAbs xs x (pick X))"
  using good_X good_imp_qGood_pick by auto
  hence "qGoodAbs ((pick o asAbs) (qAbs xs x (pick X)))"
  using goodAbs_imp_qGoodAbs_pick qGoodAbs_iff_goodAbs_asAbs by fastforce
  hence good: "qGoodAbs (?qsbsA ((pick o asAbs) (qAbs xs x (pick X))))"
  using good_qrho qPsubstAbs_preserves_qGoodAbs by auto
  have x_fresh_qrho: "qFreshEnv xs x ?qrho"
  using x_fresh_rho unfolding freshEnv_def2 by auto
  (*  *)
  have "?sbsA (Abs xs x X) = asAbs (?qsbsA ((pick o asAbs) (qAbs xs x (pick X))))"
  unfolding psubstAbs_def Abs_def by simp
  also
  {have "(pick o asAbs) (qAbs xs x (pick X)) $= qAbs xs x (pick X)"
   using good_qAbs_pick_X pick_asAbs by fastforce
   hence "?qsbsA((pick o asAbs) (qAbs xs x (pick X))) $= ?qsbsA(qAbs xs x (pick X))"
   using good_qAbs_pick_X good_qrho qPsubstAbs_preserves_alphaAbs1 by force
   moreover have "?qsbsA(qAbs xs x (pick X)) $= qAbs xs x (?qsbs (pick X))"
   using qFresh_qPsubst_commute_qAbs good_pick_X good_qrho x_fresh_qrho by auto
   moreover
   {have "?qsbs (pick X) #= pick (?sbs X)"
    using good_rho good_X pick_psubst_qPsubst alpha_sym by fastforce
    hence "qAbs xs x (?qsbs (pick X)) $= qAbs xs x (pick (?sbs X))"
    using good_qsbs_pick_X qAbs_preserves_alpha by fastforce
   }
   ultimately
   have "?qsbsA((pick o asAbs) (qAbs xs x (pick X))) $= qAbs xs x (pick (?sbs X))"
   using good alphaAbs_trans by blast
   hence "asAbs (?qsbsA((pick o asAbs) (qAbs xs x (pick X)))) =
          asAbs (qAbs xs x (pick (?sbs X)))"
   using good asAbs_equal_iff_alphaAbs by auto
  }
  also have "asAbs (qAbs xs x (pick (?sbs X))) = Abs xs x (?sbs X)"
  unfolding Abs_def by simp
  finally show ?thesis .
qed

lemmas good_psubstAll_simps =
psubst_Var_simp1 psubst_Var_simp2
psubst_Op_simp psubstAbs_simp

theorem getEnv_idEnv[simp]: "idEnv xs x = None"
unfolding idEnv_def by simp

lemma getEnv_updEnv[simp]:
"(rho [x \<leftarrow> X]_xs) ys y = (if ys = xs \<and> y = x then Some X else rho ys y)"
unfolding updEnv_def by auto

theorem getEnv_updEnv1:
"ys \<noteq> xs \<or> y \<noteq> x \<Longrightarrow> (rho [x \<leftarrow> X]_xs) ys y = rho ys y"
by auto

theorem getEnv_updEnv2:
"(rho [x \<leftarrow> X]_xs) xs x = Some X"
by auto

lemma subst_Var_simp1[simp]:
assumes "good Y"
and "ys \<noteq> xs \<or> y \<noteq> x"
shows "((Var xs x) #[Y / y]_ys) = Var xs x"
using assms unfolding subst_def by auto

lemma subst_Var_simp2[simp]:
assumes "good Y"
shows "((Var xs x) #[Y / x]_xs) = Y"
using assms unfolding subst_def by auto

lemma subst_Op_simp[simp]:
assumes "good Y"
and "goodInp inp" and "goodBinp binp"
shows
"((Op delta inp binp) #[Y / y]_ys) =
 Op delta (inp %[Y / y]_ys) (binp %%[Y / y]_ys)"
using assms unfolding subst_def substInp_def substBinp_def by auto

lemma substAbs_simp[simp]:
assumes good: "good Y" and good_X: "good X" and
        x_dif_y: "xs \<noteq> ys \<or> x \<noteq> y" and x_fresh: "fresh xs x Y"
shows "((Abs xs x X) $[Y / y]_ys) = Abs xs x (X #[Y / y]_ys)"
proof-
  have "freshEnv xs x (idEnv [y \<leftarrow> Y]_ys)" unfolding freshEnv_def liftAll_def
  using x_dif_y x_fresh by auto
  thus ?thesis using assms unfolding subst_def substAbs_def by auto
qed

lemmas good_substAll_simps =
subst_Var_simp1 subst_Var_simp2
subst_Op_simp substAbs_simp

theorem vsubst_Var_simp[simp]:
"((Var xs x) #[y1 // y]_ys) = Var xs (x @xs[y1 / y]_ys)"
unfolding vsubst_def
apply(case_tac "ys = xs \<and> y = x") by simp_all

lemma vsubst_Op_simp[simp]:
assumes "goodInp inp" and "goodBinp binp"
shows
"((Op delta inp binp) #[y1 // y]_ys) =
 Op delta (inp %[y1 // y]_ys) (binp %%[y1 // y]_ys)"
using assms unfolding vsubst_def vsubstInp_def vsubstBinp_def by auto

lemma vsubstAbs_simp[simp]:
assumes "good X" and
        "xs \<noteq> ys \<or> x \<notin> {y,y1}"
shows "((Abs xs x X) $[y1 // y]_ys) = Abs xs x (X #[y1 // y]_ys)"
using assms unfolding vsubst_def vsubstAbs_def by auto

lemmas good_vsubstAll_simps =
vsubst_Op_simp vsubstAbs_simp

lemmas good_allOpers_simps =
good_swapAll_simps
good_freshAll_simps
good_skelAll_simps
good_psubstAll_simps
good_substAll_simps
good_vsubstAll_simps

subsubsection {* The ability to pick fresh variables *}

lemma single_non_fresh_ordLess_var:
"good X \<Longrightarrow> |{x. \<not> fresh xs x X}| <o |UNIV :: 'var set|"
unfolding fresh_def
by(auto simp add: good_imp_qGood_pick single_non_qFresh_ordLess_var)

lemma single_non_freshAbs_ordLess_var:
"goodAbs A \<Longrightarrow> |{x. \<not> freshAbs xs x A}| <o |UNIV :: 'var set|"
unfolding freshAbs_def
by(auto simp add: goodAbs_imp_qGoodAbs_pick single_non_qFreshAbs_ordLess_var)

lemma obtain_fresh1:
fixes XS::"('index,'bindex,'varSort,'var,'opSym)term set" and
      Rho::"('index,'bindex,'varSort,'var,'opSym)env set" and rho
assumes Vvar: "|V| <o |UNIV :: 'var set| \<or> finite V" and XSvar: "|XS| <o |UNIV :: 'var set| \<or> finite XS" and
        good: "\<forall> X \<in> XS. good X" and
        Rhovar: "|Rho| <o |UNIV :: 'var set| \<or> finite Rho" and RhoGood: "\<forall> rho \<in> Rho. goodEnv rho"
shows
"\<exists> z. z \<notin> V \<and>
 (\<forall> X \<in> XS. fresh xs z X) \<and>
 (\<forall> rho \<in> Rho. freshEnv xs z rho)"
proof-
  let ?qXS = "pick ` XS"    let ?qRho = "pickE ` Rho"
  have "|?qXS| \<le>o |XS|" using card_of_image by auto
  hence 1: "|?qXS| <o |UNIV :: 'var set| \<or> finite ?qXS"
  using ordLeq_ordLess_trans card_of_ordLeq_finite XSvar by blast
  have "|?qRho| \<le>o |Rho|" using card_of_image by auto
  hence 2: "|?qRho| <o |UNIV :: 'var set| \<or> finite ?qRho"
  using ordLeq_ordLess_trans card_of_ordLeq_finite Rhovar by blast
  have 3: "\<forall> qX \<in> ?qXS. qGood qX" using good good_imp_qGood_pick by auto
  have "\<forall> qrho \<in> ?qRho. qGoodEnv qrho" using RhoGood goodEnv_imp_qGoodEnv_pickE by auto
  then obtain z where
  "z \<notin> V \<and> (\<forall> qX \<in> ?qXS. qFresh xs z qX) \<and>
   (\<forall> qrho \<in> ?qRho. qFreshEnv xs z qrho)"
  using Vvar 1 2 3 obtain_qFreshEnv[of V ?qXS ?qRho] by fastforce
  thus ?thesis unfolding fresh_def freshEnv_def2 by auto
qed

lemma obtain_fresh:
fixes V::"'var set" and
      XS::"('index,'bindex,'varSort,'var,'opSym)term set" and
      AS::"('index,'bindex,'varSort,'var,'opSym)abs set" and
      Rho::"('index,'bindex,'varSort,'var,'opSym)env set"
assumes Vvar: "|V| <o |UNIV :: 'var set| \<or> finite V" and
        XSvar: "|XS| <o |UNIV :: 'var set| \<or> finite XS" and
        ASvar: "|AS| <o |UNIV :: 'var set| \<or> finite AS" and
        Rhovar: "|Rho| <o |UNIV :: 'var set| \<or> finite Rho" and
        good: "\<forall> X \<in> XS. good X" and
        ASGood: "\<forall> A \<in> AS. goodAbs A" and
        RhoGood: "\<forall> rho \<in> Rho. goodEnv rho"
shows
"\<exists> z. z \<notin> V \<and>
     (\<forall> X \<in> XS. fresh xs z X) \<and>
     (\<forall> A \<in> AS. freshAbs xs z A) \<and>
     (\<forall> rho \<in> Rho. freshEnv xs z rho)"
proof-
  have XS: "|XS| <o |UNIV :: 'var set|" and AS: "|AS| <o |UNIV :: 'var set|"
  using XSvar ASvar finite_ordLess_var by auto
  let ?phi = "% A Y. (good Y \<and> (EX ys y. A = Abs ys y Y))"
  {fix A assume "A \<in> AS"
   hence "goodAbs A" using ASGood by simp
   hence "EX Y. ?phi A Y" using abs_nchotomy[of A] by auto
  }
  then obtain f where 1: "ALL A : AS. ?phi A (f A)"
  using bchoice[of AS ?phi] by auto
  let ?YS = "f ` AS"
  have 2: "ALL Y : ?YS. good Y" using 1 by simp
  have "|?YS| <=o |AS|" using card_of_image by auto
  hence "|?YS| <o |UNIV :: 'var set|"
  using AS ordLeq_ordLess_trans by blast
  hence "|XS Un ?YS| <o |UNIV :: 'var set|"
  using XS by (auto simp add: var_infinite_INNER card_of_Un_ordLess_infinite)
  then obtain z where z: "z \<notin> V"
  and XSYS: "\<forall> X \<in> XS Un ?YS. fresh xs z X"
  and Rho: "\<forall> rho \<in> Rho. freshEnv xs z rho"
  using Vvar Rhovar good 2 RhoGood
        obtain_fresh1[of V "XS Un ?YS" Rho xs] by blast
  moreover
  {fix A
   obtain Y where Y_def: "Y = f A" by blast
   assume "A : AS"
   hence "fresh xs z Y" unfolding Y_def using XSYS by simp
   moreover obtain ys y where Y: "good Y" and A: "A = Abs ys y Y"
   unfolding Y_def using `A : AS` 1 by auto
   ultimately have "freshAbs xs z A" unfolding A using z by auto
  }
  ultimately show ?thesis by auto
qed

subsubsection {* Compositionality *}

lemma swap_ident[simp]:
assumes "good X"
shows "(X #[x \<and> x]_xs) = X"
using assms asTerm_pick qSwap_ident unfolding swap_def by auto

lemma swap_compose:
assumes good_X: "good X"
shows "((X #[x \<and> y]_zs) #[x' \<and> y']_zs') =
       ((X #[x' \<and> y']_zs') #[(x @zs[x' \<and> y']_zs') \<and> (y @zs[x' \<and> y']_zs')]_zs)"
using assms qSwap_compose[of _ _ _ _ _ _ "pick X"] by(auto simp add: double_swap_qSwap)

lemma swap_commute:
"\<lbrakk>good X; zs \<noteq> zs' \<or> {x,y} \<inter> {x',y'} = {}\<rbrakk> \<Longrightarrow>
 ((X #[x \<and> y]_zs) #[x' \<and> y']_zs') = ((X #[x' \<and> y']_zs') #[x \<and> y]_zs)"
using swap_compose[of X  zs' x' y' zs x y] by(auto simp add: sw_def)

lemma swap_involutive[simp]:
assumes good_X: "good X"
shows "((X #[x \<and> y]_zs) #[x \<and> y]_zs) = X"
using assms asTerm_pick[of X] by (auto simp add: double_swap_qSwap)

theorem swap_sym: "(X #[x \<and> y]_zs) = (X #[y \<and> x]_zs)"
unfolding swap_def by(auto simp add: qSwap_sym)

lemma swap_involutive2[simp]:
assumes "good X"
shows "((X #[x \<and> y]_zs) #[y \<and> x]_zs) = X"
using assms by(simp add: swap_sym)

lemma swap_preserves_fresh[simp]:
assumes "good X"
shows "fresh xs (x @xs[y1 \<and> y2]_ys) (X #[y1 \<and> y2]_ys) = fresh xs x X"
unfolding fresh_def[of _ _ X] using assms qSwap_preserves_qFresh[of _ _ _ _ _ "pick X"]
by(auto simp add: fresh_swap_qFresh_qSwap)

lemma swap_preserves_fresh_distinct:
assumes "good X" and
       "xs \<noteq> ys \<or> x \<notin> {y1,y2}"
shows "fresh xs x (X #[y1 \<and> y2]_ys) = fresh xs x X"
unfolding fresh_def[of _ _ X] using assms  
by(auto simp: fresh_swap_qFresh_qSwap qSwap_preserves_qFresh_distinct)

lemma fresh_swap_exchange1:
assumes "good X"
shows "fresh xs x2 (X #[x1 \<and> x2]_xs) = fresh xs x1 X"
unfolding fresh_def[of _ _ X]
using assms by(auto simp: fresh_swap_qFresh_qSwap qFresh_qSwap_exchange1)

lemma fresh_swap_exchange2:
assumes "good X" and "{x1,x2} \<subseteq> var xs"
shows "fresh xs x2 (X #[x2 \<and> x1]_xs) = fresh xs x1 X"
using assms by(simp add: fresh_swap_exchange1 swap_sym)

(* Note: the lemmas swap_preserves_fresh_distinct, fresh_swap_exchange1 and
   fresh_swap_exchange2 do cover all possibilities of simplifying an
   expression of the form "fresh ys y (X #[x2 \<and> x1]_xs)".   *)

lemma fresh_swap_id[simp]:
assumes "good X" and "fresh xs x1 X" "fresh xs x2 X"
shows "(X #[x1 \<and> x2]_xs) = X"
by (metis (no_types, lifting)  assms alpha_imp_asTerm_equal alpha_qFresh_qSwap_id asTerm_pick   
      fresh_def good_imp_qGood_pick local.swap_def qSwap_preserves_qGood1)

lemma freshAbs_swapAbs_id[simp]:
assumes "goodAbs A" "freshAbs xs x1 A"  "freshAbs xs x2 A"
shows "(A $[x1 \<and> x2]_xs) = A"
using assms 
by (meson alphaAbs_qFreshAbs_qSwapAbs_id alphaAll_trans freshAbs_def goodAbs_imp_qGoodAbs_pick 
    pick_alphaAbs_iff_equal pick_swapAbs_qSwapAbs swapAbs_preserves_good)
 
lemma fresh_swap_compose:
assumes "good X" "fresh xs y X" "fresh xs z X"
shows "((X #[y \<and> x]_xs) #[z \<and> y]_xs) = (X #[z \<and> x]_xs)"
using assms by (simp add: sw_def swap_compose)

lemma skel_swap:
assumes "good X"
shows "skel (X #[x1 \<and> x2]_xs) = skel X"
using assms by (metis alpha_qSkel pick_swap_qSwap qSkel_qSwap skel_def)

subsubsection {* Compositionality for environments *}

lemma swapEnv_ident[simp]:
assumes "goodEnv rho"
shows "(rho &[x \<and> x]_xs) = rho"
using assms unfolding swapEnv_defs lift_def  
by (intro ext) (auto simp: option.case_eq_if) 

lemma swapEnv_compose:
assumes good: "goodEnv rho"
shows "((rho &[x \<and> y]_zs) &[x' \<and> y']_zs') =
       ((rho &[x' \<and> y']_zs') &[(x @zs[x' \<and> y']_zs') \<and> (y @zs[x' \<and> y']_zs')]_zs)"
proof(rule ext)+
  let ?xsw = "x @zs[x' \<and> y']_zs'"  let ?ysw = "y @zs[x' \<and> y']_zs'"
  let ?xswsw = "?xsw @zs[x' \<and> y']_zs'"  let ?yswsw = "?ysw @zs[x' \<and> y']_zs'"
  let ?rhosw1 = "rho &[x \<and> y]_zs"   let ?rhosw11 = "?rhosw1 &[x' \<and> y']_zs'"
  let ?rhosw2 = "rho &[x' \<and> y']_zs'" let ?rhosw22 = "?rhosw2 &[?xsw \<and> ?ysw]_zs"
  let ?Sw1 = "\<lambda>X. (X #[x \<and> y]_zs)"  let ?Sw11 = "\<lambda>X. ((?Sw1 X) #[x' \<and> y']_zs')"
  let ?Sw2 = "\<lambda>X. (X #[x' \<and> y']_zs')"  let ?Sw22 = "\<lambda>X. ((?Sw2 X) #[?xsw \<and> ?ysw]_zs)"
  fix us u
  let ?usw1 = "u @us [x' \<and> y']_zs'" let ?usw11 = "?usw1 @us [x \<and> y]_zs"
  let ?usw2 = "u @us [?xsw \<and> ?ysw]_zs" let ?usw22 = "?usw2 @us [x' \<and> y']_zs'"
  have "(?xsw @zs[x' \<and> y']_zs') = x" and "(?ysw @zs[x' \<and> y']_zs') = y" by auto
  have "?usw22 = (?usw1 @us[?xswsw \<and> ?yswsw]_zs)" using sw_compose .
  hence *: "?usw22 = ?usw11" by simp
  show "?rhosw11 us u = ?rhosw22 us u"
  proof(cases "rho us ?usw11")
    case None
    hence "?rhosw11 us u = None" unfolding swapEnv_defs lift_def by simp
    also have "\<dots> = ?rhosw22 us u"
    using None unfolding * swapEnv_defs lift_def by simp
    finally show ?thesis .
  next
    case (Some X)
    hence "good X" using good unfolding goodEnv_def liftAll_def by simp
    have "?rhosw11 us u = Some(?Sw11 X)" using Some unfolding swapEnv_defs lift_def by simp
    also have "?Sw11 X = ?Sw22 X"
    using `good X` by(rule swap_compose)
    also have "Some(?Sw22 X) = ?rhosw22 us u"
    using Some unfolding * swapEnv_defs lift_def by simp
    finally show ?thesis .
  qed
qed

lemma swapEnv_commute:
"\<lbrakk>goodEnv rho; {x,y} \<subseteq> var zs; zs \<noteq> zs' \<or> {x,y} \<inter> {x',y'} = {}\<rbrakk> \<Longrightarrow>
 ((rho &[x \<and> y]_zs) &[x' \<and> y']_zs') = ((rho &[x' \<and> y']_zs') &[x \<and> y]_zs)"
using swapEnv_compose[of rho zs' x' y' zs x y] by(auto simp add: sw_def)

lemma swapEnv_involutive[simp]:
assumes "goodEnv rho"
shows "((rho &[x \<and> y]_zs) &[x \<and> y]_zs) = rho"
using assms unfolding swapEnv_defs lift_def  
by (fastforce simp: option.case_eq_if) 

theorem swapEnv_sym: "(rho &[x \<and> y]_zs) = (rho &[y \<and> x]_zs)"
proof(intro ext)
  fix us u
  have *: "(u @us[x \<and> y]_zs) = (u @us[y \<and> x]_zs)" using sw_sym by fastforce
  show "(rho &[x \<and> y]_zs) us u = (rho &[y \<and> x]_zs) us u"
  unfolding swapEnv_defs lift_def *
  by(cases "rho us (u @us[y \<and> x]_zs)") (auto simp: swap_sym)
qed

lemma swapEnv_involutive2[simp]:
assumes good: "goodEnv rho"
shows "((rho &[x \<and> y]_zs) &[y \<and> x]_zs) = rho"
using assms by(simp add: swapEnv_sym)

lemma swapEnv_preserves_freshEnv[simp]:
assumes good: "goodEnv rho"
shows "freshEnv xs (x @xs[y1 \<and> y2]_ys) (rho &[y1 \<and> y2]_ys) = freshEnv xs x rho"
proof-
 let ?xsw = "x @xs[y1 \<and> y2]_ys"  let ?xswsw = "?xsw @xs[y1 \<and> y2]_ys"
 let ?rhosw = "rho &[y1 \<and> y2]_ys"
 let ?Left = "freshEnv xs ?xsw ?rhosw"
 let ?Right = "freshEnv xs x rho"
 have "(?rhosw xs ?xsw = None) = (rho xs x = None)"
 unfolding freshEnv_def swapEnv_defs
 by(simp add: lift_None sw_involutive)
 moreover
 have "(\<forall> zs z' Z'. ?rhosw zs z' = Some Z' \<longrightarrow> fresh xs ?xsw Z') =
       (\<forall> zs z Z. rho zs z = Some Z \<longrightarrow> fresh xs x Z)"
 proof(rule iff_allI, auto)
   fix zs z Z assume *: "\<forall> z' Z'. ?rhosw zs z' = Some Z' \<longrightarrow> fresh xs ?xsw Z'"
   and **: "rho zs z = Some Z"  let ?z' = "z @zs[y1 \<and> y2]_ys"  let ?Z' = "Z #[y1 \<and> y2]_ys"
   have "?rhosw zs ?z' = Some ?Z'" using ** unfolding swapEnv_defs lift_def
   by(simp add: sw_involutive)
   hence "fresh xs ?xsw ?Z'" using * by simp
   moreover have "good Z" using ** good unfolding goodEnv_def liftAll_def by simp
   ultimately show "fresh xs x Z" using swap_preserves_fresh by auto
 next
   fix zs z' Z'
   assume *: "\<forall>z Z. rho zs z = Some Z \<longrightarrow> fresh xs x Z" and **: "?rhosw zs z' = Some Z'"
   let ?z = "z' @zs[y1 \<and> y2]_ys"
   obtain Z where rho: "rho zs ?z = Some Z" and Z': "Z' = Z #[y1 \<and> y2]_ys"
   using ** unfolding swapEnv_defs lift_def by(cases "rho zs ?z", auto)
   hence "fresh xs x Z" using * by simp
   moreover have "good Z" using rho good unfolding goodEnv_def liftAll_def by simp
   ultimately show "fresh xs ?xsw Z'" unfolding Z' using swap_preserves_fresh by auto
 qed
 ultimately show ?thesis unfolding freshEnv_def swapEnv_defs
 unfolding liftAll_def by simp
qed

lemma swapEnv_preserves_freshEnv_distinct:
assumes "goodEnv rho" and
       "xs \<noteq> ys \<or> x \<notin> {y1,y2}"
shows "freshEnv xs x (rho &[y1 \<and> y2]_ys) = freshEnv xs x rho"
by (metis assms sw_simps3 swapEnv_preserves_freshEnv)

lemma freshEnv_swapEnv_exchange1:
assumes "goodEnv rho"
shows "freshEnv xs x2 (rho &[x1 \<and> x2]_xs) = freshEnv xs x1 rho"
by (metis assms sw_simps1 swapEnv_preserves_freshEnv)

lemma freshEnv_swapEnv_exchange2:
assumes "goodEnv rho"
shows "freshEnv xs x2 (rho &[x2 \<and> x1]_xs) = freshEnv xs x1 rho"
using assms by(simp add: freshEnv_swapEnv_exchange1 swapEnv_sym)

lemma freshEnv_swapEnv_id[simp]:
assumes good: "goodEnv rho" and
        fresh: "freshEnv xs x1 rho"  "freshEnv xs x2 rho"
shows "(rho &[x1 \<and> x2]_xs) = rho"
proof(intro ext)
  fix us u
  let ?usw = "u @us[x1 \<and> x2]_xs" let ?rhosw = "rho &[x1 \<and> x2]_xs"
  let ?Sw = "\<lambda> X. (X #[x1 \<and> x2]_xs)"
  show "?rhosw us u = rho us u"
  proof(cases "rho us u")
    case None
    hence "rho us ?usw = None" using fresh unfolding freshEnv_def sw_def by auto
    hence "?rhosw us u = None" unfolding swapEnv_defs lift_def by auto
    with None show ?thesis by simp
  next
   case (Some X)
   moreover have "?usw = u"  using fresh Some unfolding freshEnv_def sw_def by auto
   ultimately have "?rhosw us u = Some (?Sw X)" unfolding swapEnv_defs lift_def by auto
   moreover
   {have "good X" using Some good unfolding goodEnv_def liftAll_def by auto
    moreover have "fresh xs x1 X" and "fresh xs x2 X"
    using Some fresh unfolding freshEnv_def liftAll_def by auto
    ultimately have "?Sw X = X" by simp
   }
   ultimately show ?thesis using Some by simp
  qed
qed

lemma freshEnv_swapEnv_compose:
assumes good: "goodEnv rho" and
        fresh: "freshEnv xs y rho"  "freshEnv xs z rho"
shows "((rho &[y \<and> x]_xs) &[z \<and> y]_xs) = (rho &[z \<and> x]_xs)"
by (simp add: fresh good sw_def swapEnv_compose)

lemmas good_swapAll_freshAll_otherSimps =
swap_ident swap_involutive swap_involutive2 swap_preserves_fresh fresh_swap_id
freshAbs_swapAbs_id
swapEnv_ident swapEnv_involutive swapEnv_involutive2 swapEnv_preserves_freshEnv freshEnv_swapEnv_id

subsubsection {* Properties of the relation of being swapped *}

theorem swap_swapped: "(X, X #[x \<and> y]_zs) \<in> swapped"
by(auto simp add: swapped.Refl swapped.Swap)

lemma swapped_preserves_good:
assumes "good X" and "(X,Y) \<in> swapped"
shows "good Y"
using assms(2,1) by (induct rule: swapped.induct) auto

lemma swapped_skel:
assumes "good X" and "(X,Y) \<in> swapped"
shows "skel Y = skel X"
using assms(2,1) 
by (induct rule: swapped.induct) (auto simp: swapped_preserves_good skel_swap)

lemma obtain_rep:
assumes GOOD: "good X" and FRESH: "fresh xs x' X"
shows "\<exists> X'. (X,X') \<in> swapped \<and> good X' \<and> Abs xs x X = Abs xs x' X'"
using Abs_swap_fresh FRESH GOOD swap_preserves_good swap_swapped by blast

subsection {* Induction  *}

subsubsection {* Induction lifted from quasi-terms  *}

lemma term_templateInduct[case_names rel Var Op Abs]:
fixes X::"('index,'bindex,'varSort,'var,'opSym)term" and
      A::"('index,'bindex,'varSort,'var,'opSym)abs" and phi phiAbs rel
assumes
rel: "\<And> X Y. \<lbrakk>good X; (X,Y) \<in> rel\<rbrakk> \<Longrightarrow> good Y \<and> skel Y = skel X" and
var: "\<And> xs x. phi (Var xs x)" and
op: "\<And> delta inp binp. \<lbrakk>goodInp inp; goodBinp binp; liftAll phi inp; liftAll phiAbs binp\<rbrakk>
                       \<Longrightarrow> phi (Op delta inp binp)" and
abs: "\<And> xs x X. \<lbrakk>good X; \<And> Y. (X,Y) \<in> rel \<Longrightarrow> phi Y\<rbrakk>
                \<Longrightarrow> phiAbs (Abs xs x X)"
shows "(good X \<longrightarrow> phi X) \<and> (goodAbs A \<longrightarrow> phiAbs A)"
proof-
  let ?qX = "pick X"   let ?qA = "pick A"
  let ?qphi = "phi o asTerm"   let ?qphiAbs = "phiAbs o asAbs"
  let ?qrel = "{(qY, qY')| qY qY'. (asTerm qY, asTerm qY') \<in> rel}"
  (*   *)
  have "(good X \<longrightarrow> qGood ?qX) \<and> (goodAbs A \<longrightarrow> qGoodAbs ?qA)"
  using good_imp_qGood_pick goodAbs_imp_qGoodAbs_pick by auto
  moreover
  have "(good X \<longrightarrow> (?qphi ?qX = phi X)) \<and> (goodAbs A \<longrightarrow> (?qphiAbs ?qA = phiAbs A))"
  using asTerm_pick asAbs_pick by fastforce
  moreover
  have "(qGood ?qX \<longrightarrow> ?qphi ?qX) \<and> (qGoodAbs ?qA \<longrightarrow> ?qphiAbs ?qA)"
  proof(induction rule: qGood_qTerm_templateInduct[of ?qrel])
    case (Rel qX qY)
    thus ?case using qGood_iff_good_asTerm pick_asTerm unfolding skel_def 
    using rel skel_asTerm_qSkel   
    by simp (smt qGood_iff_good_asTerm skel_asTerm_qSkel)  
  next
    case (Var xs x)
    then show ?case using var unfolding Var_def by simp
  next
    case (Op delta qinp qbinp) 
    hence good_qinp: "qGoodInp qinp \<and> qGoodBinp qbinp"
    unfolding qGoodInp_def qGoodBinp_def liftAll_def by simp
    let ?inp = "asInp qinp"   let ?binp = "asBinp qbinp"
    have good_inp: "goodInp ?inp \<and> goodBinp ?binp"
    using good_qinp qGoodInp_iff_goodInp_asInp qGoodBinp_iff_goodBinp_asBinp by auto
    have 1: "Op delta ?inp ?binp = asTerm (qOp delta qinp qbinp)"
    using good_qinp Op_asInp_asTerm_qOp by fastforce
    {fix i X
     assume inp: "?inp i = Some X"
     then obtain qX where qinp: "qinp i = Some qX" and X: "X = asTerm qX"
     unfolding asInp_def lift_def by(cases "qinp i", auto)
     have "qGood qX \<and> phi (asTerm qX)" using qinp Op.IH by (simp add: liftAll_def)
     hence "good X \<and> phi X" unfolding X using qGood_iff_good_asTerm by auto
    }
    moreover
    {fix i A
     assume binp: "?binp i = Some A"
     then obtain qA where qbinp: "qbinp i = Some qA" and A: "A = asAbs qA"
     unfolding asBinp_def lift_def by(cases "qbinp i", auto)
     have "qGoodAbs qA \<and> phiAbs (asAbs qA)" using qbinp Op.IH by (simp add: liftAll_def)
     hence "goodAbs A \<and> phiAbs A" unfolding A using qGoodAbs_iff_goodAbs_asAbs by auto
    }
    ultimately show ?case
    using op[of ?inp ?binp delta] good_inp unfolding 1 liftAll_def by simp
  next
    case (Abs xs x qX) 
    have "good (asTerm qX)" using `qGood qX` qGood_iff_good_asTerm by auto
    moreover
    {fix Y   assume *: "(asTerm qX, Y) \<in> rel"
     obtain qY where qY: "qY = pick Y" by blast
     have "good (asTerm qX)" using `qGood qX` qGood_iff_good_asTerm by auto
     hence "good Y" using * rel by auto 
     hence Y: "Y = asTerm qY" unfolding qY using asTerm_pick by auto
     have "phi Y" using * Abs.IH unfolding Y by simp
    }
    ultimately have "phiAbs (Abs xs x (asTerm qX))" using abs by simp
    thus ?case using `qGood qX` Abs_asTerm_asAbs_qAbs by fastforce
  qed
  (*  *)
  ultimately show ?thesis by blast
qed

lemma term_rawInduct[case_names Var Op Abs]:
fixes X::"('index,'bindex,'varSort,'var,'opSym)term" and
      A::"('index,'bindex,'varSort,'var,'opSym)abs" and phi phiAbs
assumes
Var: "\<And> xs x. phi (Var xs x)" and
Op: "\<And> delta inp binp. \<lbrakk>goodInp inp; goodBinp binp; liftAll phi inp; liftAll phiAbs binp\<rbrakk>
                       \<Longrightarrow> phi (Op delta inp binp)" and
Abs: "\<And> xs x X. \<lbrakk>good X; phi X\<rbrakk> \<Longrightarrow> phiAbs (Abs xs x X)"
shows "(good X \<longrightarrow> phi X) \<and> (goodAbs A \<longrightarrow> phiAbs A)"
by(rule term_templateInduct[of Id], auto simp add: assms)

lemma term_induct[case_names Var Op Abs]:
fixes X::"('index,'bindex,'varSort,'var,'opSym)term" and
      A::"('index,'bindex,'varSort,'var,'opSym)abs" and phi phiAbs
assumes
Var: "\<And> xs x. phi (Var xs x)" and
Op: "\<And> delta inp binp. \<lbrakk>goodInp inp; goodBinp binp; liftAll phi inp; liftAll phiAbs binp\<rbrakk>
                       \<Longrightarrow> phi (Op delta inp binp)" and
Abs: "\<And> xs x X. \<lbrakk>good X;
                 \<And> Y. (X,Y) \<in> swapped \<Longrightarrow> phi Y;
                 \<And> Y. \<lbrakk>good Y; skel Y = skel X\<rbrakk> \<Longrightarrow> phi Y\<rbrakk>
                \<Longrightarrow> phiAbs (Abs xs x X)"
shows "(good X \<longrightarrow> phi X) \<and> (goodAbs A \<longrightarrow> phiAbs A)"
apply(induct rule: term_templateInduct[of "swapped \<union> {(X,Y). good Y \<and> skel Y = skel X}"])
by(auto simp: assms swapped_skel swapped_preserves_good) 

subsubsection {* Fresh induction *}

text{* First a general situation, where parameters are of an unspecified type (that should be given by the user):  *}
 
lemma term_fresh_forall_induct[case_names PAR Var Op Abs]:
fixes X::"('index,'bindex,'varSort,'var,'opSym)term" and A::"('index,'bindex,'varSort,'var,'opSym)abs" 
and phi and phiAbs and varsOf :: "'param \<Rightarrow> 'varSort \<Rightarrow> 'var set" 
assumes
PAR: "\<And> p xs. ( |varsOf xs p| <o |UNIV::'var set| )" and
var: "\<And> xs x p. phi (Var xs x) p" and
op: "\<And> delta inp binp p.  
   \<lbrakk>|{i. inp i \<noteq> None}| <o |UNIV::'var set|; |{i. binp i \<noteq> None}| <o |UNIV::'var set|;
    liftAll (\<lambda> X. good X \<and> (\<forall> q. phi X p)) inp; liftAll (\<lambda> A. goodAbs A \<and> (\<forall> q. phiAbs A p)) binp\<rbrakk>
   \<Longrightarrow> phi (Op delta inp binp) p" and
abs: "\<And> xs x X p. \<lbrakk>good X; x \<notin> varsOf p xs; phi X p\<rbrakk> \<Longrightarrow> phiAbs (Abs xs x X) p"
shows "(good X \<longrightarrow> (\<forall> p. phi X p)) \<and> (goodAbs A \<longrightarrow> (\<forall> p. phiAbs A p))"
proof(induction rule: term_templateInduct[of swapped])
  case (Abs xs x X)
  show ?case proof safe 
    fix p 
    obtain x' where x'_freshP: "x' \<notin> varsOf p xs" and x'_fresh_X: "fresh xs x' X"
    using `good X` PAR obtain_fresh[of "varsOf p xs" "{X}" "{}" "{}" xs] by auto
    then obtain X' where XX': "(X, X') \<in> swapped" and good_X': "good X'" and
    Abs_eq: "Abs xs x X = Abs xs x' X'"
    using `good X` x'_freshP x'_fresh_X using obtain_rep[of X xs x' x] by auto
    thus "phiAbs (Abs xs x X) p"
    unfolding Abs_eq using x'_freshP good_X' abs Abs.IH by simp
  qed
qed(insert assms swapped_preserves_good swapped_skel, 
   unfold liftAll_def goodInp_def goodBinp_def, auto)

  
lemma term_templateInduct_fresh[case_names PAR Var Op Abs]:
fixes X::"('index,'bindex,'varSort,'var,'opSym)term" and
      A::"('index,'bindex,'varSort,'var,'opSym)abs" and
      rel and phi and phiAbs and
      vars :: "'varSort \<Rightarrow> 'var set" and
      terms :: "('index,'bindex,'varSort,'var,'opSym)term set" and
      abs :: "('index,'bindex,'varSort,'var,'opSym)abs set" and
      envs :: "('index,'bindex,'varSort,'var,'opSym)env set"
assumes
PAR:
"\<And> xs.
   ( |vars xs| <o |UNIV :: 'var set| \<or> finite (vars xs)) \<and>
   ( |terms| <o |UNIV :: 'var set| \<or> finite terms) \<and> (\<forall> X \<in> terms. good X) \<and>
   ( |abs| <o |UNIV :: 'var set| \<or> finite abs) \<and> (\<forall> A \<in> abs. goodAbs A) \<and>
   ( |envs| <o |UNIV :: 'var set| \<or> finite envs) \<and> (\<forall> rho \<in> envs. goodEnv rho)" and
rel: "\<And> X Y. \<lbrakk>good X; (X,Y) \<in> rel\<rbrakk> \<Longrightarrow> good Y \<and> skel Y = skel X" and
Var: "\<And> xs x. phi (Var xs x)" and
Op:
"\<And> delta inp binp.
   \<lbrakk>goodInp inp; goodBinp binp;
    liftAll phi inp; liftAll phiAbs binp\<rbrakk>
   \<Longrightarrow> phi (Op delta inp binp)" and
abs:
"\<And> xs x X.
  \<lbrakk>good X;
   x \<notin> vars xs;
   \<And> Y. Y \<in> terms \<Longrightarrow> fresh xs x Y;
   \<And> A. A \<in> abs \<Longrightarrow> freshAbs xs x A;
   \<And> rho. rho \<in> envs \<Longrightarrow> freshEnv xs x rho;
   \<And> Y. (X,Y) \<in> rel \<Longrightarrow> phi Y\<rbrakk>
  \<Longrightarrow> phiAbs (Abs xs x X)"
shows
"(good X \<longrightarrow> phi X) \<and>
 (goodAbs A \<longrightarrow> phiAbs A)"
proof(induction rule: term_templateInduct[of "swapped O rel"])
  case (Abs xs x X) note good_X = `good X`  
  have "|{X} \<union> terms| <o |UNIV :: 'var set| \<or> finite ({X} \<union> terms)"
  apply(cases "finite terms", auto simp add: PAR)
  using PAR var_infinite_INNER card_of_Un_singl_ordLess_infinite by force
  then obtain x' where x'_not: "x' \<notin> vars xs" and
  x'_fresh_X: "fresh xs x' X" and
  x'_freshP: "(\<forall> Y \<in> terms. fresh xs x' Y) \<and>
              (\<forall> A \<in> abs. freshAbs xs x' A) \<and>
              (\<forall> rho \<in> envs. freshEnv xs x' rho)"
  using good_X PAR
  using obtain_fresh[of "vars xs" "{X} \<union> terms" abs envs xs] by auto
  then obtain X' where XX': "(X, X') \<in> swapped" and good_X': "good X'" and
  Abs_eq: "Abs xs x X = Abs xs x' X'"
  using good_X x'_not x'_fresh_X using obtain_rep[of X xs x' x] by auto
  have "\<And>Y. (X', Y) \<in> rel \<Longrightarrow> phi Y" using XX' Abs.IH by auto 
  thus ?case
  unfolding Abs_eq using x'_not x'_freshP good_X' abs by auto
qed(insert Op rel, unfold relcomp_unfold liftAll_def, simp_all add: Var, 
     metis rel swapped_preserves_good swapped_skel) 

text{* A version of the above not employing any relation for the bound-argument case: *}

lemma term_rawInduct_fresh[case_names Par Var Op Obs]:
fixes X::"('index,'bindex,'varSort,'var,'opSym)term" and
      A::"('index,'bindex,'varSort,'var,'opSym)abs" and
      vars :: "'varSort \<Rightarrow> 'var set" and
      terms :: "('index,'bindex,'varSort,'var,'opSym)term set" and
      abs :: "('index,'bindex,'varSort,'var,'opSym)abs set" and
      envs :: "('index,'bindex,'varSort,'var,'opSym)env set"
assumes
PAR:
"\<And> xs.
   ( |vars xs| <o |UNIV :: 'var set| \<or> finite (vars xs)) \<and>
   ( |terms| <o |UNIV :: 'var set| \<or> finite terms) \<and> (\<forall> X \<in> terms. good X) \<and>
   ( |abs| <o |UNIV :: 'var set| \<or> finite abs) \<and> (\<forall> A \<in> abs. goodAbs A) \<and>
   ( |envs| <o |UNIV :: 'var set| \<or> finite envs) \<and> (\<forall> rho \<in> envs. goodEnv rho)" and
Var: "\<And> xs x. phi (Var xs x)" and
Op:
"\<And> delta inp binp.
   \<lbrakk>goodInp inp; goodBinp binp;
    liftAll phi inp; liftAll phiAbs binp\<rbrakk>
   \<Longrightarrow> phi (Op delta inp binp)" and
Abs:
"\<And> xs x X.
  \<lbrakk>good X;
   x \<notin> vars xs;
   \<And> Y. Y \<in> terms \<Longrightarrow> fresh xs x Y;
   \<And> A. A \<in> abs \<Longrightarrow> freshAbs xs x A;
   \<And> rho. rho \<in> envs \<Longrightarrow> freshEnv xs x rho;
   phi X\<rbrakk>
  \<Longrightarrow> phiAbs (Abs xs x X)"
shows
"(good X \<longrightarrow> phi X) \<and>
 (goodAbs A \<longrightarrow> phiAbs A)"
apply(induct rule: term_templateInduct_fresh[of vars terms abs envs Id])
using assms by auto

(* Note that here, since we avoid variable-capture and hence will
 not typically need to swap, term-inductRaw_fresh will suffice in proofs.
 Therefore we do not prove a swapped-and-skel version of fresh induction, although such a version
 could be easily inferred from ``term-templateInduct". *)

text{* The typical raw induction with freshness is one dealing with
   finitely many variables, terms, abstractions and environments as parameters --
   we have all these condensed in the notion of a parameter (type
   constructor ``param"): *}

lemma term_induct_fresh[case_names Par Var Op Abs]:
fixes X :: "('index,'bindex,'varSort,'var,'opSym)term" and
      A :: "('index,'bindex,'varSort,'var,'opSym)abs" and
      P :: "('index,'bindex,'varSort,'var,'opSym)param"
assumes
goodP: "goodPar P" and
Var: "\<And> xs x. phi (Var xs x)" and
Op:
"\<And> delta inp binp.
   \<lbrakk>goodInp inp; goodBinp binp;
    liftAll phi inp; liftAll phiAbs binp\<rbrakk>
   \<Longrightarrow> phi (Op delta inp binp)" and
Abs:
"\<And> xs x X.
   \<lbrakk>good X;
    x \<notin> varsOf P;
    \<And> Y. Y \<in> termsOf P \<Longrightarrow> fresh xs x Y;
    \<And> A. A \<in> absOf P \<Longrightarrow> freshAbs xs x A;
    \<And> rho. rho \<in> envsOf P \<Longrightarrow> freshEnv xs x rho;
    phi X\<rbrakk>
   \<Longrightarrow> phiAbs (Abs xs x X)"
shows
"(good X \<longrightarrow> phi X) \<and>
 (goodAbs A \<longrightarrow> phiAbs A)"
proof(induct rule: term_rawInduct_fresh
      [of "\<lambda> xs. varsOf P" "termsOf P" "absOf P" "envsOf P"])
  case (Par xs)
  then show ?case unfolding goodPar_def  
  using goodP by(cases P) simp
qed(insert assms, auto) 

end  (* context FixVars  *)

end
