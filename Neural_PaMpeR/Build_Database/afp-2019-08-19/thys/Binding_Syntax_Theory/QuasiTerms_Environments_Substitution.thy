section {* Environments and Substitution for Quasi-Terms  *}

theory QuasiTerms_Environments_Substitution
imports QuasiTerms_PickFresh_Alpha
begin

text{* Inside this theory, since anyway all the interesting properties hold only
modulo alpha, we forget completely about qAFresh and use only qFresh. *}

text{* In this section we define, for quasi-terms, parallel substitution according to
{\em environments}.
This is the most general kind of substitution -- an environment, i.e., a partial
map from variables
to quasi-terms, indicates which quasi-term (if any) to be substituted for each
variable; substitution
is then applied to a subject quasi-term and an environment.  In order to ``keep up"
with the notion
of good quasi-term, we define good environments and show that substitution
preserves goodness.  Since,
unlike swapping, substitution does not behave well w.r.t. quasi-terms
(but only w.r.t. terms, i.e., to alpha-equivalence classes),
here we prove the minimum amount of properties required for properly lifting
parallel substitution to terms. Then compositionality properties
of parallel substitution will be proved directly for terms.
*}

subsection {* Environments   *}

type_synonym ('index,'bindex,'varSort,'var,'opSym)qEnv =
      "'varSort \<Rightarrow> 'var \<Rightarrow> ('index,'bindex,'varSort,'var,'opSym)qTerm option"

(*********************************************)
context FixVars  (* scope all throughout the file *)
begin

definition qGoodEnv :: "('index,'bindex,'varSort,'var,'opSym)qEnv \<Rightarrow> bool"
where
"qGoodEnv rho ==
 (\<forall> xs. liftAll qGood (rho xs)) \<and>
 (\<forall> ys. |{y. rho ys y \<noteq> None}| <o |UNIV :: 'var set| )"

definition qFreshEnv where
"qFreshEnv zs z rho ==
 rho zs z = None \<and> (\<forall> xs. liftAll (qFresh zs z) (rho xs))"

definition alphaEnv where
"alphaEnv =
 {(rho,rho'). \<forall> xs. sameDom (rho xs) (rho' xs) \<and>
                      liftAll2 (\<lambda>X X'. X #= X') (rho xs) (rho' xs)}"

abbreviation alphaEnv_abbrev ::
"('index,'bindex,'varSort,'var,'opSym)qEnv \<Rightarrow>
 ('index,'bindex,'varSort,'var,'opSym)qEnv \<Rightarrow> bool" (infix "&=" 50)
where
"rho &= rho' == (rho,rho') \<in> alphaEnv"

definition pickQFreshEnv
where
"pickQFreshEnv xs V XS Rho ==
 pickQFresh xs (V \<union> (\<Union> rho \<in> Rho. {x. rho xs x \<noteq> None}))
               (XS \<union> (\<Union> rho \<in> Rho. {X. \<exists> ys y. rho ys y = Some X}))"

lemma qGoodEnv_imp_card_of_qTerm:
assumes "qGoodEnv rho"
shows "|{X. \<exists> y. rho ys y = Some X}| <o |UNIV :: 'var set|"
proof-
  let ?rel = "{(y,X). rho ys y = Some X}"
  let ?Left = "{X. \<exists> y. rho ys y = Some X}"
  let ?Left' = "{y. \<exists> X. rho ys y = Some X}"
  have "\<And> y X X'. (y,X) \<in> ?rel \<and> (y,X') \<in> ?rel \<longrightarrow> X = X'" by force
  hence "|?Left| \<le>o |?Left'|" using card_of_inj_rel[of ?rel] by auto
  moreover have "|?Left'| <o |UNIV :: 'var set|" using assms unfolding qGoodEnv_def by auto
  ultimately show ?thesis using ordLeq_ordLess_trans by blast
qed

lemma qGoodEnv_imp_card_of_qTerm2:
assumes "qGoodEnv rho"
shows "|{X. \<exists> ys y. rho ys y = Some X}| <o |UNIV :: 'var set|"
proof-
  let ?Left = "{X. \<exists> ys y. rho ys y = Some X}"
  let ?F = "\<lambda> ys. {X. \<exists> y. rho ys y = Some X}"
  have "?Left = (\<Union> ys. ?F ys)" by auto
  moreover have "\<forall> ys. |?F ys| <o |UNIV :: 'var set|"
  using assms qGoodEnv_imp_card_of_qTerm by auto
  ultimately show ?thesis
  using var_regular_INNER varSort_lt_var_INNER by(force simp add: regular_UNION)
qed

lemma qGoodEnv_iff:
"qGoodEnv rho =
 ((\<forall> xs. liftAll qGood (rho xs)) \<and>
  (\<forall> ys. |{y. rho ys y \<noteq> None}| <o |UNIV :: 'var set| ) \<and>
  |{X. \<exists> ys y. rho ys y = Some X}| <o |UNIV :: 'var set| )"
unfolding qGoodEnv_def apply auto
apply(rule qGoodEnv_imp_card_of_qTerm2) unfolding qGoodEnv_def by simp

lemma alphaEnv_refl:
"qGoodEnv rho \<Longrightarrow> rho &= rho"
using alpha_refl
unfolding alphaEnv_def qGoodEnv_def liftAll_def liftAll2_def sameDom_def by fastforce

lemma alphaEnv_sym:
"rho &= rho' \<Longrightarrow> rho' &= rho"
using alpha_sym unfolding alphaEnv_def liftAll2_def sameDom_def by fastforce

lemma alphaEnv_trans:
assumes good: "qGoodEnv rho" and
        alpha1: "rho &= rho'" and alpha2: "rho' &= rho''"
shows "rho &= rho''"
using assms unfolding alphaEnv_def
apply(auto)
using sameDom_trans apply blast
unfolding liftAll2_def proof(auto)
  fix xs x X X''
  assume rho: "rho xs x = Some X" and rho'': "rho'' xs x = Some X''"
  moreover have "(rho xs x = None) = (rho' xs x = None)"
  using alpha1 unfolding alphaEnv_def sameDom_def by auto
  ultimately obtain X' where rho': "rho' xs x = Some X'" by auto
  hence "X #= X'" using alpha1 rho unfolding alphaEnv_def liftAll2_def by auto
  moreover have "X' #= X''"
  using alpha2 rho' rho'' unfolding alphaEnv_def liftAll2_def by auto
  moreover have "qGood X" using good rho unfolding qGoodEnv_def liftAll_def by auto
  ultimately show "X #= X''" using alpha_trans by blast
qed

lemma pickQFreshEnv_card_of:
assumes Vvar: "|V| <o |UNIV :: 'var set|" and XSvar: "|XS| <o |UNIV :: 'var set|" and
        good: "\<forall> X \<in> XS. qGood X" and
        Rhovar: "|Rho| <o |UNIV :: 'var set|" and RhoGood: "\<forall> rho \<in> Rho. qGoodEnv rho"
shows
"pickQFreshEnv xs V XS Rho \<notin> V \<and>
 (\<forall> X \<in> XS. qFresh xs (pickQFreshEnv xs V XS Rho) X) \<and>
 (\<forall> rho \<in> Rho. qFreshEnv xs (pickQFreshEnv xs V XS Rho) rho)"
proof-
  let ?z =" pickQFreshEnv xs V XS Rho"
  let ?V2 = "\<Union> rho \<in> Rho. {x. rho xs x \<noteq> None}"  let ?W = "V \<union> ?V2"
  let ?XS2 = "\<Union> rho \<in> Rho. {X. \<exists> ys y. rho ys y = Some X}" let ?YS = "XS \<union> ?XS2"
  have "|?W| <o |UNIV :: 'var set|"
  proof-
    have "\<forall> rho \<in> Rho. |{x. rho xs x \<noteq> None}| <o |UNIV :: 'var set|"
    using RhoGood unfolding qGoodEnv_iff using qGoodEnv_iff by auto
    hence "|?V2| <o |UNIV :: 'var set|"
    using var_regular_INNER Rhovar by (auto simp add: regular_UNION)
    thus ?thesis using var_infinite_INNER Vvar card_of_Un_ordLess_infinite by auto
  qed
  moreover have "|?YS| <o |UNIV :: 'var set|"
  proof-
    have "\<forall> rho \<in> Rho. |{X. \<exists> ys y. rho ys y = Some X}| <o |UNIV :: 'var set|"
    using RhoGood unfolding qGoodEnv_iff by auto
    hence "|?XS2| <o |UNIV :: 'var set|"
    using var_regular_INNER Rhovar by (auto simp add: regular_UNION)
    thus ?thesis using var_infinite_INNER XSvar card_of_Un_ordLess_infinite by auto
  qed
  moreover have "\<forall> Y \<in> ?YS. qGood Y"
  using good RhoGood unfolding qGoodEnv_iff liftAll_def by blast
  ultimately
  have "?z \<notin> ?W \<and> (\<forall> Y \<in> ?YS. qFresh xs ?z Y)"
  unfolding pickQFreshEnv_def using pickQFresh_card_of[of ?W ?YS] by auto
  thus ?thesis unfolding qFreshEnv_def liftAll_def by(auto)
qed

lemma pickQFreshEnv:
assumes Vvar: "|V| <o |UNIV :: 'var set| \<or> finite V"
and XSvar: "|XS| <o |UNIV :: 'var set| \<or> finite XS"
and good: "\<forall> X \<in> XS. qGood X"
and Rhovar: "|Rho| <o |UNIV :: 'var set| \<or> finite Rho"
and RhoGood: "\<forall> rho \<in> Rho. qGoodEnv rho"
shows
"pickQFreshEnv xs V XS Rho \<notin> V \<and>
 (\<forall> X \<in> XS. qFresh xs (pickQFreshEnv xs V XS Rho) X) \<and>
 (\<forall> rho \<in> Rho. qFreshEnv xs (pickQFreshEnv xs V XS Rho) rho)"
proof-
  have 1: "|V| <o |UNIV :: 'var set| \<and> |XS| <o |UNIV :: 'var set| \<and> |Rho| <o |UNIV :: 'var set|"
  using assms var_infinite_INNER by(auto simp add: finite_ordLess_infinite2)
  show ?thesis
  apply(rule pickQFreshEnv_card_of)
  using assms 1 by auto
qed

corollary obtain_qFreshEnv:
fixes XS::"('index,'bindex,'varSort,'var,'opSym)qTerm set" and
      Rho::"('index,'bindex,'varSort,'var,'opSym)qEnv set" and rho
assumes Vvar: "|V| <o |UNIV :: 'var set| \<or> finite V"
and XSvar: "|XS| <o |UNIV :: 'var set| \<or> finite XS"
and good: "\<forall> X \<in> XS. qGood X"
and Rhovar: "|Rho| <o |UNIV :: 'var set| \<or> finite Rho"
and RhoGood: "\<forall> rho \<in> Rho. qGoodEnv rho"
shows
"\<exists> z. z \<notin> V \<and>
 (\<forall> X \<in> XS. qFresh xs z X) \<and> (\<forall> rho \<in> Rho. qFreshEnv xs z rho)"
apply(rule exI[of _ "pickQFreshEnv xs V XS Rho"])
using assms by(rule pickQFreshEnv)

subsection {* Parallel substitution *}

(* I shall prove only a *minimal* collection of facts for quasi-
[parallel substitution], just enough
  to show that substitution preserves alpha.  The other properties shall be proved
  for alpha-equivalence directly.   *)

definition aux_qPsubst_ignoreFirst ::
"('index,'bindex,'varSort,'var,'opSym)qEnv * ('index,'bindex,'varSort,'var,'opSym)qTerm +
 ('index,'bindex,'varSort,'var,'opSym)qEnv * ('index,'bindex,'varSort,'var,'opSym)qAbs
 \<Rightarrow> ('index,'bindex,'varSort,'var,'opSym)qTermItem"
where
"aux_qPsubst_ignoreFirst K ==
 case K of Inl (rho,X) \<Rightarrow> termIn X
          |Inr (rho,A) \<Rightarrow> absIn A"

lemma aux_qPsubst_ignoreFirst_qTermLessQSwapped_wf:
"wf(inv_image qTermQSwappedLess aux_qPsubst_ignoreFirst)"
using qTermQSwappedLess_wf wf_inv_image by auto

function
qPsubst ::
"('index,'bindex,'varSort,'var,'opSym)qEnv \<Rightarrow> ('index,'bindex,'varSort,'var,'opSym)qTerm \<Rightarrow>
 ('index,'bindex,'varSort,'var,'opSym)qTerm"
and
qPsubstAbs ::
"('index,'bindex,'varSort,'var,'opSym)qEnv \<Rightarrow> ('index,'bindex,'varSort,'var,'opSym)qAbs \<Rightarrow>
 ('index,'bindex,'varSort,'var,'opSym)qAbs"
where
"qPsubst rho (qVar xs x) = (case rho xs x of None \<Rightarrow> qVar xs x| Some X \<Rightarrow> X)"
|
"qPsubst rho (qOp delta inp binp) =
 qOp delta (lift (qPsubst rho) inp) (lift (qPsubstAbs rho) binp)"
|
"qPsubstAbs rho (qAbs xs x X) =
 (let x' = pickQFreshEnv xs {x} {X} {rho} in qAbs xs x' (qPsubst rho (X #[[x' \<and> x]]_xs)))"
by(pat_completeness, auto)
termination
apply(relation "inv_image qTermQSwappedLess aux_qPsubst_ignoreFirst")
apply(simp add: aux_qPsubst_ignoreFirst_qTermLessQSwapped_wf)
by(auto simp add: qTermQSwappedLess_def qTermLess_modulo_def
   aux_qPsubst_ignoreFirst_def qSwap_qSwapped)

abbreviation qPsubst_abbrev ::
"('index,'bindex,'varSort,'var,'opSym)qTerm \<Rightarrow> ('index,'bindex,'varSort,'var,'opSym)qEnv \<Rightarrow>
 ('index,'bindex,'varSort,'var,'opSym)qTerm" ("_ #[[_]]")
where "X #[[rho]] == qPsubst rho X"

abbreviation qPsubstAbs_abbrev ::
"('index,'bindex,'varSort,'var,'opSym)qAbs \<Rightarrow> ('index,'bindex,'varSort,'var,'opSym)qEnv \<Rightarrow>
 ('index,'bindex,'varSort,'var,'opSym)qAbs" ("_ $[[_]]")
where "A $[[rho]] == qPsubstAbs rho A"

lemma qPsubstAll_preserves_qGoodAll:
fixes X::"('index,'bindex,'varSort,'var,'opSym)qTerm" and
      A::"('index,'bindex,'varSort,'var,'opSym)qAbs" and rho
assumes GOOD_ENV: "qGoodEnv rho"
shows
"(qGood X \<longrightarrow> qGood (X #[[rho]])) \<and> (qGoodAbs A \<longrightarrow> qGoodAbs (A $[[rho]]))"
proof(induction rule: qTerm_induct[of _ _ X A])
  case (Var xs x)
  show ?case 
  using GOOD_ENV unfolding qGoodEnv_iff liftAll_def
  by(cases "rho xs x", auto)
next
  case (Op delta inp binp)
  show ?case proof safe
    assume g: "qGood (qOp delta inp binp)"
    hence 0: "liftAll qGood (lift (qPsubst rho) inp) \<and> 
              liftAll qGoodAbs (lift (qPsubstAbs rho) binp)"
    using Op unfolding liftAll_lift_comp comp_def
    by (simp_all add: Let_def liftAll_mp)
    have "{i. lift (qPsubst rho) inp i \<noteq> None} = {i. inp i \<noteq> None} \<and> 
     {i. lift (qPsubstAbs rho) binp i \<noteq> None} = {i. binp i \<noteq> None}"
    by simp (meson lift_Some)
    hence "|{i. \<exists>y. lift (qPsubst rho) inp i = Some y}| <o |UNIV:: 'var set|" 
    and "|{i. \<exists>y. lift (qPsubstAbs rho) binp i = Some y}| <o |UNIV:: 'var set|"
    using g by (auto simp: liftAll_def)
    thus "qGood qOp delta inp binp #[[rho]]" using 0 by simp
  qed
next
  case (Abs xs x X)
  show ?case proof safe
    assume g: "qGoodAbs (qAbs xs x X)"      
    let ?x' = "pickQFreshEnv xs {x} {X} {rho}"  let ?X' = "X #[[?x' \<and> x]]_xs"
    have "qGood ?X'" using g qSwap_preserves_qGood by auto
    moreover have "(X,?X') \<in> qSwapped" using qSwap_qSwapped by fastforce
    ultimately have "qGood (qPsubst rho ?X')" using Abs.IH by simp
    thus "qGoodAbs ((qAbs xs x X) $[[rho]])" by (simp add: Let_def)
  qed
qed 

corollary qPsubst_preserves_qGood:
"\<lbrakk>qGoodEnv rho; qGood X\<rbrakk> \<Longrightarrow> qGood (X #[[rho]])"
using qPsubstAll_preserves_qGoodAll by auto

corollary qPsubstAbs_preserves_qGoodAbs:
"\<lbrakk>qGoodEnv rho; qGoodAbs A\<rbrakk> \<Longrightarrow> qGoodAbs (A $[[rho]])"
using qPsubstAll_preserves_qGoodAll by auto

lemma qPsubstAll_preserves_qFreshAll:
fixes X::"('index,'bindex,'varSort,'var,'opSym)qTerm" and
      A::"('index,'bindex,'varSort,'var,'opSym)qAbs" and rho
assumes GOOD_ENV: "qGoodEnv rho"
shows
"(qFresh zs z X \<longrightarrow>
  (qGood X \<and> qFreshEnv zs z rho \<longrightarrow> qFresh zs z (X #[[rho]]))) \<and>
 (qFreshAbs zs z A \<longrightarrow>
  (qGoodAbs A \<and> qFreshEnv zs z rho \<longrightarrow> qFreshAbs zs z (A $[[rho]])))"
proof(induction rule: qTerm_induct[of _ _ X A])
  case (Var xs x)
  then show ?case
  unfolding qFreshEnv_def liftAll_def by (cases "rho xs x") auto 
next
  case (Op delta inp binp)
  thus ?case 
  by (auto simp add: lift_def liftAll_def qFreshEnv_def split: option.splits)
next 
  case (Abs xs x X)
  show ?case proof safe
    assume q: "qFreshAbs zs z (qAbs xs x X)"
    "qGoodAbs (qAbs xs x X)" "qFreshEnv zs z rho"
    let ?x' = "pickQFreshEnv xs {x} {X} {rho}"  let ?X' = "X #[[?x' \<and> x]]_xs"
    have x': "qFresh xs ?x' X \<and> qFreshEnv xs ?x' rho"
    using q GOOD_ENV by(auto simp add: pickQFreshEnv)
    hence goodX': "qGood ?X'" using q qSwap_preserves_qGood by auto
    have XX': "(X,?X') \<in> qSwapped" using qSwap_qSwapped by fastforce
    have  "(zs = xs \<and> z = ?x') \<or> qFresh zs z (qPsubst rho ?X')"
    by (meson qSwap_preserves_qFresh_distinct 
    Abs.IH(1) XX' goodX' q qAbs_alphaAbs_qSwap_qFresh qFreshAbs.simps 
    qFreshAbs_preserves_alphaAbs1 qSwap_preserves_qGood2 x')
    thus "qFreshAbs zs z ((qAbs xs x X) $[[rho]])"
    by simp (meson qFreshAbs.simps)+ 
  qed
qed

lemma qPsubst_preserves_qFresh:
"\<lbrakk>qGood X; qGoodEnv rho; qFresh zs z X; qFreshEnv zs z rho\<rbrakk>
 \<Longrightarrow> qFresh zs z (X #[[rho]])"
by(simp add: qPsubstAll_preserves_qFreshAll)

lemma qPsubstAbs_preserves_qFreshAbs:
"\<lbrakk>qGoodAbs A; qGoodEnv rho; qFreshAbs zs z A; qFreshEnv zs z rho\<rbrakk>
 \<Longrightarrow> qFreshAbs zs z (A $[[rho]])"
by(simp add: qPsubstAll_preserves_qFreshAll)

text{* While in general we try to avoid proving facts in parallel,
   here we seem to have no choice -- it is the first time we must use mutual 
induction:  *}

lemma qPsubstAll_preserves_alphaAll_qSwapAll:
fixes X::"('index,'bindex,'varSort,'var,'opSym)qTerm" and
      A::"('index,'bindex,'varSort,'var,'opSym)qAbs" and
      rho::"('index,'bindex,'varSort,'var,'opSym)qEnv"
assumes goodRho: "qGoodEnv rho"
shows
"(qGood X \<longrightarrow>
  (\<forall> Y. X #= Y \<longrightarrow> (X #[[rho]]) #= (Y #[[rho]])) \<and>
  (\<forall> xs z1 z2. qFreshEnv xs z1 rho \<and> qFreshEnv xs z2 rho \<longrightarrow>
               ((X #[[z1 \<and> z2]]_xs) #[[rho]]) #= ((X #[[rho]]) #[[z1 \<and> z2]]_xs))) \<and>
 (qGoodAbs A \<longrightarrow>
  (\<forall> B. A $= B \<longrightarrow> (A $[[rho]]) $= (B $[[rho]])) \<and>
  (\<forall> xs z1 z2. qFreshEnv xs z1 rho \<and> qFreshEnv xs z2 rho \<longrightarrow>
               ((A $[[z1 \<and> z2]]_xs) $[[rho]]) $= ((A $[[rho]]) $[[z1 \<and> z2]]_xs)))"
proof(induction rule: qGood_qTerm_induct_mutual)
  case (Var1 xs x)
  then show ?case  
  by (metis alpha_refl goodRho qGood.simps(1) qPsubst_preserves_qGood qVar_alpha_iff)
next
  case (Var2 xs x)
  show ?case proof safe
    fix s::'sort and zs z1 z2
    assume FreshEnv: "qFreshEnv zs z1 rho" "qFreshEnv zs z2 rho"
    hence n: "rho zs z1 = None \<and> rho zs z2 = None" unfolding qFreshEnv_def by simp
    let ?Left = "qPsubst rho ((qVar xs x) #[[z1 \<and> z2]]_zs)"
    let ?Right = "(qPsubst rho (qVar xs x)) #[[z1 \<and> z2]]_zs"
    have "qGood (qVar xs x)" by simp
    hence "qGood ((qVar xs x) #[[z1 \<and> z2]]_zs)"
    using qSwap_preserves_qGood by blast
    hence goodLeft: "qGood ?Left" using goodRho qPsubst_preserves_qGood by blast
    show "?Left #= ?Right"
    proof(cases "rho xs x")  
      case None
      hence "rho xs (x @xs[z1 \<and> z2]_zs) = None"
      using n unfolding sw_def by auto
      thus ?thesis using None by simp
    next
      case (Some X) 
      hence "xs \<noteq> zs \<or> x \<notin> {z1,z2}" using n by auto
      hence "(x @xs[z1 \<and> z2]_zs) = x" unfolding sw_def by auto
      moreover
      {have "qFresh zs z1 X \<and> qFresh zs z2 X"
       using Some FreshEnv unfolding qFreshEnv_def liftAll_def by auto
       moreover have "qGood X" using Some goodRho unfolding qGoodEnv_def liftAll_def by auto
       ultimately have "X #= (X #[[z1 \<and> z2]]_zs)"
       by(auto simp: alpha_qFresh_qSwap_id alpha_sym)
      }
      ultimately show ?thesis using Some by simp
    qed
  qed
next
  case (Op1 delta inp binp)
  show ?case proof safe
    fix Y assume q: "qOp delta inp binp #= Y" 
    then obtain inp' binp' where Y: "Y = qOp delta inp' binp'" and
       *: "(\<forall>i. (inp i = None) = (inp' i = None)) \<and>
           (\<forall>i. (binp i = None) = (binp' i = None))" and
       **: "(\<forall>i X X'. inp i = Some X \<and> inp' i = Some X' \<longrightarrow> X #= X') \<and>
            (\<forall>i A A'. binp i = Some A \<and> binp' i = Some A' \<longrightarrow> A $= A')"
    unfolding qOp_alpha_iff sameDom_def liftAll2_def by auto
    show "(qOp delta inp binp) #[[rho]] #= (Y #[[rho]])"  
    using Op1 **
    by (simp add: Y sameDom_def liftAll2_def)
       (fastforce simp add: * lift_None lift_Some 
        liftAll_def lift_def split: option.splits)
  qed
next
  case (Op2 delta inp binp)
  thus ?case  
  by (auto simp: sameDom_def liftAll2_def lift_None lift_def liftAll_def split: option.splits)  
next
  case (Abs1 xs x X)
  show ?case proof safe
    fix B
    assume alpha_xXB: "qAbs xs x X $= B"
    then obtain y Y where B: "B = qAbs xs y Y" unfolding qAbs_alphaAbs_iff by auto  
    have "qGoodAbs B" using `qGood X` alpha_xXB alphaAbs_preserves_qGoodAbs by force
    hence goodY: "qGood Y" unfolding B by simp
    let ?x' = "pickQFreshEnv xs {x} {X} {rho}"
    let ?y' = "pickQFreshEnv xs {y} {Y} {rho}"
    obtain x' and y' where x'y'_def: "x' = ?x'" "y' = ?y'" and
           x'y'_rev: "?x' = x'" "?y' = y'" by blast
    have x'y'_freshXY: "qFresh xs x' X \<and> qFresh xs y' Y"
    unfolding x'y'_def using `qGood X` goodY goodRho by (auto simp add: pickQFreshEnv)
    have x'y'_fresh_rho: "qFreshEnv xs x' rho \<and> qFreshEnv xs y' rho"
    unfolding x'y'_def using `qGood X` goodY goodRho by (auto simp add: pickQFreshEnv)
    have x'y'_not_xy: "x' \<noteq> x \<and> y' \<noteq> y"
    unfolding x'y'_def using `qGood X` goodY goodRho
    using pickQFreshEnv[of "{x}" "{X}"] pickQFreshEnv[of "{y}" "{Y}"] by force
    have goodXx'x: "qGood (X #[[x' \<and> x]]_xs)" using `qGood X` qSwap_preserves_qGood by auto
    hence good: "qGood(qPsubst rho (X #[[x' \<and> x]]_xs))"
    using goodRho qPsubst_preserves_qGood by auto
    have goodYy'y: "qGood (Y #[[y' \<and> y]]_xs)" using goodY qSwap_preserves_qGood by auto
    obtain z where z_not: "z \<notin> {x,y,x',y'}" and
    z_fresh_XY: "qFresh xs z X \<and> qFresh xs z Y"
    and z_fresh_rho: "qFreshEnv xs z rho" using `qGood X` goodY goodRho
    using obtain_qFreshEnv[of "{x,y,x',y'}" "{X,Y}" "{rho}"] by auto
    (* Notations: *)
    let ?Xx'x = "X #[[x' \<and> x]]_xs"   let ?Yy'y = "Y #[[y' \<and> y]]_xs"
    let ?Xx'xzx' = "?Xx'x #[[z \<and> x']]_xs" let ?Yy'yzy' = "?Yy'y #[[z \<and> y']]_xs"
    let ?Xzx = "X #[[z \<and> x]]_xs"   let ?Yzy = "Y #[[z \<and> y]]_xs"
    (* Preliminary facts: *)
    have goodXx'x: "qGood ?Xx'x" using `qGood X` qSwap_preserves_qGood by auto
    hence goodXx'xzx': "qGood ?Xx'xzx'" using qSwap_preserves_qGood by auto
    have "qGood (?Xx'x #[[rho]])" using goodXx'x goodRho qPsubst_preserves_qGood by auto
    hence goodXx'x_rho_zx': "qGood ((?Xx'x #[[rho]]) #[[z \<and> x']]_xs)"
    using qSwap_preserves_qGood by auto
    have goodYy'y: "qGood ?Yy'y" using goodY qSwap_preserves_qGood by auto
    (*  *)
    have skelXx'x: "qSkel ?Xx'x = qSkel X" using qSkel_qSwap by fastforce
    hence skelXx'xzx': "qSkel ?Xx'xzx' = qSkel X" by (auto simp add: qSkel_qSwap)
    have "qSkelAbs B = qSkelAbs (qAbs xs x X)"
    using alpha_xXB alphaAll_qSkelAll by fastforce
    hence "qSkel Y = qSkel X" unfolding B by(auto simp add: fun_eq_iff)
    hence skelYy'y: "qSkel ?Yy'y = qSkel X" by(auto simp add: qSkel_qSwap)
    (* Main proof: *)
    have "((?Xx'x #[[rho]]) #[[z \<and> x']]_xs) #= (?Xx'xzx' #[[rho]])"
    using skelXx'x goodXx'x z_fresh_rho x'y'_fresh_rho
          Abs1.IH(2)[of "?Xx'x"] by (auto simp add: alpha_sym)
    moreover
    {have "?Xx'xzx' #= ?Xzx"
     using `qGood X` x'y'_freshXY z_fresh_XY alpha_qFresh_qSwap_compose by fastforce
     moreover have "?Xzx #= ?Yzy" using alpha_xXB unfolding B
     using z_fresh_XY `qGood X` goodY
     by (simp only: alphaAbs_qAbs_iff_all_qFresh)
     moreover have "?Yzy #= ?Yy'yzy'" using goodY x'y'_freshXY z_fresh_XY
     by(auto simp add: alpha_qFresh_qSwap_compose alpha_sym)
     ultimately have "?Xx'xzx' #= ?Yy'yzy'" using goodXx'xzx' alpha_trans by blast
     hence "(?Xx'xzx' #[[rho]]) #= (?Yy'yzy' #[[rho]])"
     using goodXx'xzx' skelXx'xzx' Abs1.IH(1) by auto
    }  
    moreover have "(?Yy'yzy' #[[rho]]) #= ((?Yy'y #[[rho]]) #[[z \<and> y']]_xs)"
    using skelYy'y goodYy'y z_fresh_rho x'y'_fresh_rho
          Abs1.IH(2)[of "?Yy'y"] alpha_sym by fastforce
    ultimately
    have "((?Xx'x #[[rho]]) #[[z \<and> x']]_xs) #= ((?Yy'y #[[rho]]) #[[z \<and> y']]_xs)"
    using goodXx'x_rho_zx' alpha_trans by blast  
    thus "(qAbs xs x X) $[[rho]] $= (B $[[rho]])"
    unfolding B apply simp unfolding Let_def 
    unfolding x'y'_rev
    using good z_not apply(simp only: alphaAbs_qAbs_iff_ex_qFresh)
    by (auto intro!: exI[of _ z]
    simp: alphaAbs_qAbs_iff_ex_qFresh goodRho goodXx'x qPsubstAll_preserves_qFreshAll 
    qSwap_preserves_qFresh_distinct z_fresh_XY goodYy'y qPsubst_preserves_qFresh z_fresh_rho)
  qed 
next
  case (Abs2 xs x X)
  show ?case proof safe 
    fix zs z1 z2
    assume z1z2_fresh_rho: "qFreshEnv zs z1 rho" "qFreshEnv zs z2 rho" 
    let ?x' = "pickQFreshEnv xs {x @xs[z1 \<and> z2]_zs} {X #[[z1 \<and> z2]]_zs} {rho}"
    let ?x'' = "pickQFreshEnv xs {x} {X} {rho}"
    obtain x' x'' where x'x''_def: "x' = ?x'" "x'' = ?x''" and
           x'x''_rev: "?x' = x'" "?x'' = x''" by blast
    let ?xa = "x @xs[z1 \<and> z2]_zs"  let ?xa'' = "x'' @xs[z1 \<and> z2]_zs"
    obtain u where "u \<notin> {x,x',x'',z1,z2}" and
    u_fresh_X: "qFresh xs u X" and u_fresh_rho: "qFreshEnv xs u rho"
    using `qGood X` goodRho using obtain_qFreshEnv[of "{x,x',x'',z1,z2}" "{X}" "{rho}"] by auto
    hence u_not: "u \<notin> {x,x',x'',z1,z2,?xa,?xa''}" unfolding sw_def by auto
    let ?ua = "u @xs [z1 \<and> z2]_zs"
    let ?Xz1z2 = "X #[[z1 \<and> z2]]_zs"  
      let ?Xz1z2x'xa = "?Xz1z2 #[[x' \<and> ?xa]]_xs"
        let ?Xz1z2x'xa_rho = "?Xz1z2x'xa #[[rho]]"
          let ?Xz1z2x'xa_rho_ux' = "?Xz1z2x'xa_rho #[[u \<and> x']]_xs"
        let ?Xz1z2x'xaux' = "?Xz1z2x'xa #[[u \<and> x']]_xs"
          let ?Xz1z2x'xaux'_rho = "?Xz1z2x'xaux' #[[rho]]"
      let ?Xz1z2uxa = "?Xz1z2 #[[u \<and> ?xa]]_xs"
      let ?Xz1z2uaxa = "?Xz1z2 #[[?ua \<and> ?xa]]_xs"
    let ?Xux = "X #[[u \<and> x]]_xs"
      let ?Xuxz1z2 = "?Xux #[[z1 \<and> z2]]_zs"
    let ?Xx''x = "X #[[x'' \<and> x]]_xs"
      let ?Xx''xux'' = "?Xx''x #[[u \<and> x'']]_xs"
        let ?Xx''xux''z1z2 = "?Xx''xux'' #[[z1 \<and> z2]]_zs"
      let ?Xx''xz1z2 = "?Xx''x #[[z1 \<and> z2]]_zs"
        let ?Xx''xz1z2uaxa'' = "?Xx''xz1z2 #[[?ua \<and> ?xa'']]_xs"
          let ?Xx''xz1z2uaxa''_rho = "?Xx''xz1z2uaxa'' #[[rho]]"
        let ?Xx''xz1z2uxa'' = "?Xx''xz1z2 #[[u \<and> ?xa'']]_xs"
          let ?Xx''xz1z2uxa''_rho = "?Xx''xz1z2uxa'' #[[rho]]"
        let ?Xx''xz1z2_rho = "?Xx''xz1z2 #[[rho]]"
          let ?Xx''xz1z2_rho_uxa'' = "?Xx''xz1z2_rho #[[u \<and> ?xa'']]_xs"
      let ?Xx''x_rho = "?Xx''x #[[rho]]"
        let ?Xx''x_rho_z1z2 = "?Xx''x_rho #[[z1 \<and> z2]]_zs"
          let ?Xx''x_rho_z1z2uxa'' = "?Xx''x_rho_z1z2 #[[u \<and> ?xa'']]_xs"
    (* Facts about x', x'', ?xa, ?ua, ?xa'': *)
    have goodXz1z2: "qGood ?Xz1z2" using `qGood X` qSwap_preserves_qGood by auto
    have x'x''_fresh_Xz1z2: "qFresh xs x' ?Xz1z2 \<and> qFresh xs x'' X"
    unfolding x'x''_def using `qGood X` goodXz1z2 goodRho by (auto simp add: pickQFreshEnv)
    have x'x''_fresh_rho: "qFreshEnv xs x' rho \<and> qFreshEnv xs x'' rho"
    unfolding x'x''_def using `qGood X` goodXz1z2 goodRho by (auto simp add: pickQFreshEnv)
    have ua_eq_u: "?ua = u" using u_not unfolding sw_def by auto
    (* Good: *)
    have goodXz1z2x'xa: "qGood ?Xz1z2x'xa" using goodXz1z2 qSwap_preserves_qGood by auto
    have goodXux: "qGood ?Xux" using `qGood X` qSwap_preserves_qGood by auto
    hence goodXuxz1z2: "qGood ?Xuxz1z2" using qSwap_preserves_qGood by auto
    have goodXx''x: "qGood ?Xx''x" using `qGood X` qSwap_preserves_qGood by auto
    hence goodXx''xz1z2: "qGood ?Xx''xz1z2" using qSwap_preserves_qGood by auto
    hence "qGood ?Xx''xz1z2_rho" using goodRho qPsubst_preserves_qGood by auto
    hence goodXx''xz1z2_rho: "qGood ?Xx''xz1z2_rho"
    using goodRho qPsubst_preserves_qGood by auto
    have goodXz1z2x'xaux': "qGood ?Xz1z2x'xaux'"
    using goodXz1z2x'xa qSwap_preserves_qGood by auto
    have goodXz1z2x'xa_rho: "qGood ?Xz1z2x'xa_rho"
    using goodXz1z2x'xa goodRho qPsubst_preserves_qGood by auto
    hence goodXz1z2x'xa_rho_ux': "qGood ?Xz1z2x'xa_rho_ux'"
    using qSwap_preserves_qGood by auto
    (* Fresh: *)
    have xa''_fresh_rho: "qFreshEnv xs ?xa'' rho"
    using x'x''_fresh_rho z1z2_fresh_rho unfolding sw_def by auto
    have u_fresh_Xz1z2: "qFresh xs u ?Xz1z2"
    using u_fresh_X u_not by(auto simp add: qSwap_preserves_qFresh_distinct)
    hence "qFresh xs u ?Xz1z2x'xa" using u_not by(auto simp add: qSwap_preserves_qFresh_distinct)
    hence u_fresh_Xz1z2x'xa_rho: "qFresh xs u ?Xz1z2x'xa_rho"
    using u_fresh_rho u_fresh_X goodRho goodXz1z2x'xa qPsubst_preserves_qFresh by auto
    have "qFresh xs u ?Xx''x"
    using u_fresh_X u_not by(auto simp add: qSwap_preserves_qFresh_distinct)
    hence "qFresh xs u ?Xx''x_rho" using goodRho goodXx''x u_fresh_rho
    by(auto simp add: qPsubst_preserves_qFresh)
    hence u_fresh_Xx''x_rho_z1z2: "qFresh xs u ?Xx''x_rho_z1z2"
    using u_not by(auto simp add: qSwap_preserves_qFresh_distinct)
    (* Skeleton: *)
    have skel_Xz1z2x'xa: "qSkel ?Xz1z2x'xa = qSkel X" by(auto simp add: qSkel_qSwap)
    hence skel_Xz1z2x'xaux': "qSkel ?Xz1z2x'xaux' = qSkel X" by(auto simp add: qSkel_qSwap)
    have skel_Xx''x: "qSkel ?Xx''x = qSkel X" by(auto simp add: qSkel_qSwap)
    hence skel_Xx''xz1z2: "qSkel ?Xx''xz1z2 = qSkel X" by(auto simp add: qSkel_qSwap)
    (* Main proof: *)     
    have "?Xz1z2x'xaux'_rho #= ?Xz1z2x'xa_rho_ux'"
    using x'x''_fresh_rho u_fresh_rho skel_Xz1z2x'xa goodXz1z2x'xa
    using Abs2.IH(2)[of ?Xz1z2x'xa] by auto
    hence "?Xz1z2x'xa_rho_ux' #= ?Xz1z2x'xaux'_rho" using alpha_sym by auto
    moreover
    {have "?Xz1z2x'xaux' #= ?Xz1z2uxa"
     using goodXz1z2 u_fresh_Xz1z2 x'x''_fresh_Xz1z2
     using alpha_qFresh_qSwap_compose by fastforce
     moreover have "?Xz1z2uxa = ?Xuxz1z2"
     using ua_eq_u qSwap_compose[of zs z1 z2 xs x u X] by(auto simp: qSwap_sym)
     moreover
     {have "?Xux #= ?Xx''xux''"
      using `qGood X` u_fresh_X x'x''_fresh_Xz1z2
      by(auto simp: alpha_qFresh_qSwap_compose alpha_sym)
      hence "?Xuxz1z2 #= ?Xx''xux''z1z2"
      using goodXux by (auto simp add: qSwap_preserves_alpha)
     }
     moreover have "?Xx''xux''z1z2 = ?Xx''xz1z2uxa''"
     using ua_eq_u qSwap_compose[of zs z1 z2 _  _ _ ?Xx''x] by auto
     ultimately have "?Xz1z2x'xaux' #= ?Xx''xz1z2uxa''"
     using goodXz1z2x'xaux' alpha_trans by auto
     hence "?Xz1z2x'xaux'_rho #= ?Xx''xz1z2uxa''_rho"
     using goodXz1z2x'xaux' skel_Xz1z2x'xaux' Abs2.IH(1) by auto
    }
    moreover have "?Xx''xz1z2uxa''_rho #= ?Xx''xz1z2_rho_uxa''"
    using xa''_fresh_rho u_fresh_rho skel_Xx''xz1z2 goodXx''xz1z2
    using Abs2.IH(2)[of ?Xx''xz1z2] by auto
    moreover
    {have "?Xx''xz1z2_rho #= ?Xx''x_rho_z1z2"
     using z1z2_fresh_rho skel_Xx''x goodXx''x
     using Abs2.IH(2)[of ?Xx''x] by auto
     hence "?Xx''xz1z2_rho_uxa'' #= ?Xx''x_rho_z1z2uxa''"
     using goodXx''xz1z2_rho by(auto simp add: qSwap_preserves_alpha)
    }
    ultimately have "?Xz1z2x'xa_rho_ux' #= ?Xx''x_rho_z1z2uxa''"
    using goodXz1z2x'xa_rho_ux' alpha_trans by blast
    thus "((qAbs xs x X) $[[z1 \<and> z2]]_zs) $[[rho]] $= 
          (((qAbs xs x X) $[[rho]]) $[[z1 \<and> z2]]_zs)"
    using goodXz1z2x'xa_rho    
    goodXz1z2x'xa u_not u_fresh_Xz1z2x'xa_rho u_fresh_Xx''x_rho_z1z2 
    apply(simp add: Let_def x'x''_rev del: alpha.simps alphaAbs.simps ) 
    by (auto simp only: Let_def alphaAbs_qAbs_iff_ex_qFresh)
  qed
qed

corollary qPsubst_preserves_alpha1:
assumes "qGoodEnv rho" and "qGood X \<or> qGood Y" and "X #= Y"
shows "(X #[[rho]]) #= (Y #[[rho]])"
using alpha_preserves_qGood assms qPsubstAll_preserves_alphaAll_qSwapAll by blast
 
corollary qPsubstAbs_preserves_alphaAbs1:
assumes "qGoodEnv rho" and "qGoodAbs A \<or> qGoodAbs B" and "A $= B"
shows "(A $[[rho]]) $= (B $[[rho]])"
using alphaAbs_preserves_qGoodAbs assms qPsubstAll_preserves_alphaAll_qSwapAll by blast

corollary alpha_qFreshEnv_qSwap_qPsubst_commute:
"\<lbrakk>qGoodEnv rho; qGood X; qFreshEnv zs z1 rho; qFreshEnv zs z2 rho\<rbrakk> \<Longrightarrow>
 ((X #[[z1 \<and> z2]]_zs) #[[rho]]) #= ((X #[[rho]]) #[[z1 \<and> z2]]_zs)"
by(simp add: qPsubstAll_preserves_alphaAll_qSwapAll)

corollary alphaAbs_qFreshEnv_qSwapAbs_qPsubstAbs_commute:
"\<lbrakk>qGoodEnv rho; qGoodAbs A;
  qFreshEnv zs z1 rho; qFreshEnv zs z2 rho\<rbrakk> \<Longrightarrow>
 ((A $[[z1 \<and> z2]]_zs) $[[rho]]) $= ((A $[[rho]]) $[[z1 \<and> z2]]_zs)"
by(simp add: qPsubstAll_preserves_alphaAll_qSwapAll)

lemma qPsubstAll_preserves_alphaAll2:
fixes X::"('index,'bindex,'varSort,'var,'opSym)qTerm" and
      A::"('index,'bindex,'varSort,'var,'opSym)qAbs" and
      rho'::"('index,'bindex,'varSort,'var,'opSym)qEnv" and rho''
assumes rho'_alpha_rho'': "rho' &= rho''" and
        goodRho': "qGoodEnv rho'" and goodRho'': "qGoodEnv rho''"
shows
"(qGood X \<longrightarrow> (X #[[rho']]) #= (X #[[rho'']])) \<and>
 (qGoodAbs A \<longrightarrow> (A $[[rho']]) $= (A $[[rho'']]))"
proof(induction rule: qGood_qTerm_induct)
  case (Var xs x)
  then show ?case 
  proof (cases "rho' xs x") 
    case None
    hence "rho'' xs x = None" using rho'_alpha_rho'' unfolding alphaEnv_def sameDom_def by auto
    thus ?thesis using None by simp
  next
    case (Some X')
    then obtain X'' where rho'': "rho'' xs x = Some X''"
    using assms unfolding alphaEnv_def sameDom_def by force
    hence "X' #= X''" using Some rho'_alpha_rho''
    unfolding alphaEnv_def liftAll2_def by auto
    thus ?thesis using Some rho'' by simp
  qed 
next
  case (Op delta inp binp)
  then show ?case 
  by (auto simp: lift_def liftAll_def liftAll2_def sameDom_def Let_def
      split: option.splits)
next
  case (Abs xs x X)   
  let ?x' = "pickQFreshEnv xs {x} {X} {rho'}"
  let ?x'' = "pickQFreshEnv xs {x} {X} {rho''}"
  obtain x' x'' where x'x''_def: "x' = ?x'" "x'' = ?x''" and
          x'x''_rev: "?x' = x'" "?x'' = x''" by blast
  have x'x''_fresh_X: "qFresh xs x' X \<and> qFresh xs x'' X"
  unfolding x'x''_def using `qGood X` goodRho' goodRho'' by (auto simp add: pickQFreshEnv)
  have x'_fresh_rho': "qFreshEnv xs x' rho'"
  unfolding x'x''_def using `qGood X` goodRho' goodRho'' by (auto simp add: pickQFreshEnv)
  have x''_fresh_rho'': "qFreshEnv xs x'' rho''"
  unfolding x'x''_def using `qGood X` goodRho' goodRho'' by (auto simp add: pickQFreshEnv)
  obtain u where u_not: "u \<notin> {x,x',x''}" and
  u_fresh_X: "qFresh xs u X" and
  u_fresh_rho': "qFreshEnv xs u rho'" and u_fresh_rho'': "qFreshEnv xs u rho''"
  using `qGood X` goodRho' goodRho''
  using obtain_qFreshEnv[of "{x,x',x''}" "{X}" "{rho',rho''}"] by auto
  (* Preliminary facts and notations: *)
  let ?Xx'x = "X #[[x' \<and> x]]_xs"
    let ?Xx'x_rho' = "?Xx'x #[[rho']]"
      let ?Xx'x_rho'_ux' = "?Xx'x_rho' #[[u \<and> x']]_xs"
    let ?Xx'xux' = "?Xx'x #[[u \<and> x']]_xs"
      let ?Xx'xux'_rho' = "?Xx'xux' #[[rho']]"
  let ?Xux = "X #[[u \<and> x]]_xs"
    let ?Xux_rho' = "?Xux #[[rho']]"
    let ?Xux_rho'' = "?Xux #[[rho'']]"
  let ?Xx''x = "X #[[x'' \<and> x]]_xs"
    let ?Xx''xux'' = "?Xx''x #[[u \<and> x'']]_xs"
      let ?Xx''xux''_rho'' = "?Xx''xux'' #[[rho'']]"
    let ?Xx''x_rho'' = "?Xx''x #[[rho'']]"
      let ?Xx''x_rho''_ux'' = "?Xx''x_rho'' #[[u \<and> x'']]_xs"
  (* Good: *)
  have goodXx'x: "qGood ?Xx'x" using `qGood X` qSwap_preserves_qGood by auto
  hence goodXx'x_rho': "qGood ?Xx'x_rho'" using `qGood X` goodRho' qPsubst_preserves_qGood by auto
  hence goodXx'x_rho'_ux': "qGood ?Xx'x_rho'_ux'"
  using `qGood X` qSwap_preserves_qGood by auto
  have goodXx'xux': "qGood ?Xx'xux'" using goodXx'x qSwap_preserves_qGood by auto
  have goodXux: "qGood ?Xux" using `qGood X` qSwap_preserves_qGood by auto
  have goodXx''x: "qGood ?Xx''x" using `qGood X` qSwap_preserves_qGood by auto
  hence goodXx''x_rho'': "qGood ?Xx''x_rho''"
  using `qGood X` goodRho'' qPsubst_preserves_qGood by auto
  (* Fresh: *)
  have "qFresh xs u ?Xx'x" using u_not u_fresh_X
  by(auto simp add: qSwap_preserves_qFresh_distinct)
  hence fresh_Xx'x_rho': "qFresh xs u ?Xx'x_rho'"
  using u_fresh_rho'  goodXx'x goodRho' by(auto simp add: qPsubst_preserves_qFresh)
  have "qFresh xs u ?Xx''x" using u_not u_fresh_X
  by(auto simp add: qSwap_preserves_qFresh_distinct)
  hence fresh_Xx''x_rho'': "qFresh xs u ?Xx''x_rho''"
  using u_fresh_rho''  goodXx''x goodRho'' by(auto simp add: qPsubst_preserves_qFresh)
  (* qSwapped: *)
  have Xux: "(X,?Xux) :qSwapped" by(simp add: qSwap_qSwapped)
  (* Main proof: *)
  have "?Xx'x_rho'_ux' #= ?Xx'xux'_rho'"
  using goodRho' goodXx'x u_fresh_rho' x'_fresh_rho'
  by(auto simp: alpha_qFreshEnv_qSwap_qPsubst_commute alpha_sym)
  moreover
  {have "?Xx'xux' #= ?Xux" using `qGood X` u_fresh_X x'x''_fresh_X
   using alpha_qFresh_qSwap_compose by fastforce
   hence "?Xx'xux'_rho' #= ?Xux_rho'" using goodXx'xux' goodRho'
   using qPsubst_preserves_alpha1 by auto
  }
  moreover have "?Xux_rho' #= ?Xux_rho''" using Xux Abs.IH by auto
  moreover
  {have "?Xux #= ?Xx''xux''" using `qGood X` u_fresh_X x'x''_fresh_X
   by(auto simp add: alpha_qFresh_qSwap_compose alpha_sym)
   hence "?Xux_rho'' #= ?Xx''xux''_rho''" using goodXux goodRho''
   using qPsubst_preserves_alpha1 by auto
  }
  moreover have "?Xx''xux''_rho'' #= ?Xx''x_rho''_ux''"
  using goodRho'' goodXx''x u_fresh_rho'' x''_fresh_rho''
  by(auto simp: alpha_qFreshEnv_qSwap_qPsubst_commute)
  ultimately have "?Xx'x_rho'_ux' #= ?Xx''x_rho''_ux''"
  using goodXx'x_rho'_ux' alpha_trans by blast
  hence "qAbs xs ?x' (qPsubst rho' (X #[[?x' \<and> x]]_xs)) $=
         qAbs xs ?x''(qPsubst rho''(X #[[?x''\<and> x]]_xs))"
  unfolding x'x''_rev using goodXx'x_rho' fresh_Xx'x_rho' fresh_Xx''x_rho'' 
  by (auto simp only: alphaAbs_qAbs_iff_ex_qFresh)
  thus ?case by (metis qPsubstAbs.simps)
qed

corollary qPsubst_preserves_alpha2:
"\<lbrakk>qGood X; qGoodEnv rho'; qGoodEnv rho''; rho' &= rho''\<rbrakk>
 \<Longrightarrow> (X #[[rho']]) #= (X #[[rho'']])"
by(simp add: qPsubstAll_preserves_alphaAll2)

corollary qPsubstAbs_preserves_alphaAbs2:
"\<lbrakk>qGoodAbs A; qGoodEnv rho'; qGoodEnv rho''; rho' &= rho''\<rbrakk>
 \<Longrightarrow> (A $[[rho']]) $= (A $[[rho'']])"
by(simp add: qPsubstAll_preserves_alphaAll2)

lemma qPsubst_preserves_alpha:
assumes "qGood X \<or> qGood X'" and "qGoodEnv rho" and "qGoodEnv rho'" 
and "X #= X'" and "rho &= rho'"
shows "(X #[[rho]]) #= (X' #[[rho']])"
 by (metis (no_types, lifting) assms alpha_trans qPsubst_preserves_alpha1 
qPsubst_preserves_alpha2 qPsubst_preserves_qGood) 

lemma qPsubstAbs_preserves_alphaAbs:
assumes "qGoodAbs A \<or> qGoodAbs A'" and "qGoodEnv rho" and "qGoodEnv rho'" 
and "A $= A'" and "rho &= rho'"
shows "(A $[[rho]]) $= (A' $[[rho']])"
using assms 
by (meson alphaAbs_trans qPsubstAbs_preserves_alphaAbs1 
    qPsubstAbs_preserves_qGoodAbs qPsubstAll_preserves_alphaAll2)
 
lemma qFresh_qPsubst_commute_qAbs:
assumes good_X: "qGood X" and good_rho: "qGoodEnv rho" and
        x_fresh_rho: "qFreshEnv xs x rho"
shows "((qAbs xs x X) $[[rho]]) $= qAbs xs x (X #[[rho]])"
proof-
  (* Preliminary facts and notations: *)
  let ?x' = "pickQFreshEnv xs {x} {X} {rho}"
  obtain x' where x'_def: "x' = ?x'" and x'_rev: "?x' = x'" by blast
  have x'_not: "x' \<noteq> x" unfolding x'_def
  using assms pickQFreshEnv[of "{x}" "{X}"] by auto
  have x'_fresh_X: "qFresh xs x' X"  unfolding x'_def
  using assms pickQFreshEnv[of "{x}" "{X}"] by auto
  have x'_fresh_rho: "qFreshEnv xs x' rho"  unfolding x'_def
  using assms pickQFreshEnv[of "{x}" "{X}"] by auto
  obtain u where u_not: "u \<notin> {x,x'}" and
  u_fresh_X: "qFresh xs u X" and u_fresh_rho: "qFreshEnv xs u rho"
  using good_X good_rho obtain_qFreshEnv[of "{x,x'}" "{X}" "{rho}"] by auto
  let ?Xx'x = "X #[[x' \<and> x]]_xs"
    let ?Xx'x_rho = "?Xx'x #[[rho]]"
      let ?Xx'x_rho_ux' = "?Xx'x_rho #[[u \<and> x']]_xs"
    let ?Xx'xux' = "?Xx'x #[[u \<and> x']]_xs"
      let ?Xx'xux'_rho = "?Xx'xux' #[[rho]]"
  let ?Xux = "X #[[u \<and> x]]_xs"
    let ?Xux_rho = "?Xux #[[rho]]"
  let ?Xrho = "X #[[rho]]"
    let ?Xrho_ux = "?Xrho #[[u \<and> x]]_xs"
  (* Good: *)
  have good_Xx'x: "qGood ?Xx'x" using good_X qSwap_preserves_qGood by auto
  hence good_Xx'x_rho: "qGood ?Xx'x_rho" using good_rho qPsubst_preserves_qGood by auto
  hence good_Xx'x_rho_ux': "qGood ?Xx'x_rho_ux'" using qSwap_preserves_qGood by auto
  have good_Xx'xux': "qGood ?Xx'xux'" using good_Xx'x qSwap_preserves_qGood by auto
  (* Fresh: *)
  have u_fresh_Xx'x: "qFresh xs u ?Xx'x"
  using u_fresh_X u_not by(auto simp add: qSwap_preserves_qFresh_distinct)
  hence u_fresh_Xx'x_rho: "qFresh xs u ?Xx'x_rho"
  using good_rho good_Xx'x u_fresh_rho by(auto simp add: qPsubst_preserves_qFresh)
  have u_fresh_Xrho: "qFresh xs u ?Xrho"
  using good_rho good_X u_fresh_X u_fresh_rho by(auto simp add: qPsubst_preserves_qFresh)
  (* Main proof: *)  -
  have "?Xx'x_rho_ux' #= ?Xx'xux'_rho"
  using good_Xx'x good_rho u_fresh_rho x'_fresh_rho
  using alpha_qFreshEnv_qSwap_qPsubst_commute alpha_sym by blast
  moreover
  {have "?Xx'xux' #= ?Xux"
   using good_X u_fresh_X x'_fresh_X by (auto simp add: alpha_qFresh_qSwap_compose)
   hence "?Xx'xux'_rho #= ?Xux_rho"
   using good_Xx'xux' good_rho qPsubst_preserves_alpha1 by auto
  }  
  moreover have "?Xux_rho #= ?Xrho_ux"
  using good_X good_rho u_fresh_rho x_fresh_rho
  using alpha_qFreshEnv_qSwap_qPsubst_commute by blast
  ultimately have "?Xx'x_rho_ux' #= ?Xrho_ux"
  using good_Xx'x_rho_ux' alpha_trans by blast
  thus ?thesis apply (simp add: Let_def del: alpha.simps alphaAbs.simps) 
  unfolding x'_rev using good_Xx'x_rho
  using u_fresh_Xx'x_rho u_fresh_Xrho by (auto simp only: alphaAbs_qAbs_iff_ex_qFresh) 
qed

end  (* context FixVars *)

end
