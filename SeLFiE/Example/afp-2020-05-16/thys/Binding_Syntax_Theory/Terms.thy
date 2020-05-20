section {* More on Terms *}

theory Terms imports Transition_QuasiTerms_Terms
begin

text{* In this section, we continue the study of terms, with stating and proving
properties specific to terms (while in the previous section we dealt with
lifting properties from quasi-terms).
Consequently, in this theory, not only the theorems, but neither the proofs
should mention quasi-items at all.
Among the properties specific to terms will
be the compositionality properties of substitution (while, by contrast, similar properties
of swapping also held for quasi-tems).
 *}

context FixVars (* scope all throughout the file *)
begin

declare qItem_simps[simp del]
declare qItem_versus_item_simps[simp del]

subsection {* Identity environment versus other operators *}

(* Recall theorem getEnv_idEnv. *)

theorem getEnv_updEnv_idEnv[simp]:
"(idEnv [x \<leftarrow> X]_xs) ys y = (if (ys = xs \<and> y = x) then Some X else None)"
unfolding idEnv_def updEnv_def by simp

theorem subst_psubst_idEnv:
"(X #[Y / y]_ys) = (X #[idEnv [y \<leftarrow> Y]_ys])"
unfolding subst_def idEnv_def updEnv_def psubst_def by simp

theorem vsubst_psubst_idEnv:
"(X #[z // y]_ys) = (X #[idEnv [y \<leftarrow> Var ys z]_ys])"
unfolding vsubst_def by(simp add: subst_psubst_idEnv)

theorem substEnv_psubstEnv_idEnv:
"(rho &[Y / y]_ys) = (rho &[idEnv [y \<leftarrow> Y]_ys])"
unfolding substEnv_def idEnv_def updEnv_def psubstEnv_def by simp

theorem vsubstEnv_psubstEnv_idEnv:
"(rho &[z // y]_ys) = (rho &[idEnv [y \<leftarrow> Var ys z]_ys])"
unfolding vsubstEnv_def by (simp add: substEnv_psubstEnv_idEnv)

theorem freshEnv_idEnv: "freshEnv xs x idEnv"
unfolding idEnv_def freshEnv_def liftAll_def by simp

theorem swapEnv_idEnv[simp]: "(idEnv &[x \<and> y]_xs) = idEnv"
unfolding idEnv_def swapEnv_def comp_def swapEnvDom_def swapEnvIm_def lift_def by simp

theorem psubstEnv_idEnv[simp]: "(idEnv &[rho]) = rho"
unfolding idEnv_def psubstEnv_def lift_def by simp

theorem substEnv_idEnv: "(idEnv &[X / x]_xs) = (idEnv [x \<leftarrow> X]_xs)"
unfolding substEnv_def using psubstEnv_idEnv by auto

theorem vsubstEnv_idEnv: "(idEnv &[y // x]_xs) = (idEnv [x \<leftarrow> (Var xs y)]_xs)"
unfolding vsubstEnv_def using substEnv_idEnv .

lemma psubstAll_idEnv:
fixes X::"('index,'bindex,'varSort,'var,'opSym)term" and
      A::"('index,'bindex,'varSort,'var,'opSym)abs"
shows
"(good X  \<longrightarrow> (X #[idEnv]) = X) \<and>
 (goodAbs A  \<longrightarrow> (A $[idEnv]) = A)"
apply(induct rule: term_rawInduct)   
unfolding psubstInp_def psubstBinp_def
using idEnv_preserves_good psubst_Var_simp1
by (simp_all del: getEnv_idEnv add: 
liftAll_lift_ext lift_ident freshEnv_idEnv psubstBinp_def psubstInp_def)
  fastforce+  

lemma psubst_idEnv[simp]:
"good X \<Longrightarrow> (X #[idEnv]) = X"
by(simp add: psubstAll_idEnv)

lemma psubstEnv_idEnv_id[simp]:
assumes "goodEnv rho"
shows "(rho &[idEnv]) = rho"
using assms unfolding psubstEnv_def lift_def goodEnv_def liftAll_def  
apply(intro ext) subgoal for xs x by(cases "rho xs x") auto .

subsection {* Environment update versus other operators *}

(* Recall theorem getEnv_updEnv. *)

theorem updEnv_overwrite[simp]: "((rho [x \<leftarrow> X]_xs) [x \<leftarrow> X']_xs) = (rho [x \<leftarrow> X']_xs)"
unfolding updEnv_def by fastforce

theorem updEnv_commute:
assumes "xs \<noteq> ys \<or> x \<noteq> y"
shows "((rho [x \<leftarrow> X]_xs) [y \<leftarrow> Y]_ys) = ((rho [y \<leftarrow> Y]_ys) [x \<leftarrow> X]_xs)"
using assms unfolding updEnv_def by fastforce

theorem freshEnv_updEnv_E1:
assumes "freshEnv xs y (rho [x \<leftarrow> X]_xs)"
shows "y \<noteq> x"
using assms unfolding freshEnv_def liftAll_def updEnv_def by auto

theorem freshEnv_updEnv_E2:
assumes "freshEnv ys y (rho [x \<leftarrow> X]_xs)"
shows "fresh ys y X"
using assms unfolding freshEnv_def liftAll_def updEnv_def 
by (auto split: if_splits) 

theorem freshEnv_updEnv_E3:
assumes "freshEnv ys y (rho [x \<leftarrow> X]_xs)"
shows "rho ys y = None"
using assms freshEnv_updEnv_E1[of ys y] unfolding freshEnv_def
by (metis getEnv_updEnv option.simps(3)) 

theorem freshEnv_updEnv_E4:
assumes "freshEnv ys y (rho [x \<leftarrow> X]_xs)"
and "zs \<noteq> xs \<or> z \<noteq> x" and "rho zs z = Some Z"
shows "fresh ys y Z"
using assms unfolding freshEnv_def liftAll_def 
by (metis getEnv_updEnv1)

theorem freshEnv_updEnv_I:
assumes "ys \<noteq> xs \<or> y \<noteq> x" and "fresh ys y X" and "rho ys y = None"
and "\<And> zs z Z. \<lbrakk>zs \<noteq> xs \<or> z \<noteq> x; rho zs z = Some Z\<rbrakk> \<Longrightarrow> fresh ys y Z"
shows "freshEnv ys y (rho [x \<leftarrow> X]_xs)"
unfolding freshEnv_def liftAll_def
using assms by auto 

theorem swapEnv_updEnv:
"((rho [x \<leftarrow> X]_xs) &[y1 \<and> y2]_ys) =
 ((rho &[y1 \<and> y2]_ys) [(x @xs[y1 \<and> y2]_ys) \<leftarrow> (X #[y1 \<and> y2]_ys)]_xs)"
unfolding swapEnv_defs sw_def lift_def
by(cases "xs = ys") fastforce+

lemma swapEnv_updEnv_fresh:
assumes "ys \<noteq> xs \<or> x \<notin> {y1,y2}" and "good X"
and "fresh ys y1 X" and "fresh ys y2 X"
shows "((rho [x \<leftarrow> X]_xs) &[y1 \<and> y2]_ys) =
       ((rho &[y1 \<and> y2]_ys) [x \<leftarrow> X]_xs)"
using assms by(simp add: swapEnv_updEnv)

theorem psubstEnv_updEnv:
"((rho [x \<leftarrow> X]_xs) &[rho']) = ((rho &[rho']) [x \<leftarrow> (X #[rho'])]_xs)"
unfolding psubstEnv_def by fastforce

theorem psubstEnv_updEnv_idEnv:
"((idEnv [x \<leftarrow> X]_xs) &[rho]) = (rho [x \<leftarrow> (X #[rho])]_xs)"
by(simp add: psubstEnv_updEnv)

theorem substEnv_updEnv:
"((rho [x \<leftarrow> X]_xs) &[Y / y]_ys) = ((rho &[Y / y]_ys) [x \<leftarrow> (X #[Y / y]_ys)]_xs)"
unfolding substEnv_def subst_def by(rule psubstEnv_updEnv)

theorem vsubstEnv_updEnv:
"((rho [x \<leftarrow> X]_xs) &[y1 // y]_ys) = ((rho &[y1 // y]_ys) [x \<leftarrow> (X #[y1 // y]_ys)]_xs)"
unfolding vsubstEnv_def vsubst_def using substEnv_updEnv .

subsection {* Environment ``get" versus other operators *}

text{* Currently, ``get" is just function application.  While the next
properties are immediate consequences of the definitions, it is worth stating
them because of their abstract character (since later, concrete terms
inferred from abstract terms by a presumptive package, ``get" will no longer
be function application). *}

theorem getEnv_ext:
assumes "\<And> xs x. rho xs x = rho' xs x"
shows "rho = rho'"
using assms by(simp add: ext)

theorem freshEnv_getEnv1[simp]:
"\<lbrakk>freshEnv ys y rho; rho xs x = Some X\<rbrakk> \<Longrightarrow> ys \<noteq> xs \<or> y \<noteq> x"
unfolding freshEnv_def by auto

theorem freshEnv_getEnv2[simp]:
"\<lbrakk>freshEnv ys y rho; rho xs x = Some X\<rbrakk> \<Longrightarrow> fresh ys y X"
unfolding freshEnv_def liftAll_def by simp

theorem freshEnv_getEnv[simp]:
"freshEnv ys y rho \<Longrightarrow> rho ys y = None"
unfolding freshEnv_def by simp

theorem getEnv_swapEnv1[simp]:
assumes "rho xs (x @xs [z1 \<and> z2]_zs) = None"
shows "(rho &[z1 \<and> z2]_zs) xs x = None"
using assms unfolding swapEnv_defs lift_def by simp

theorem getEnv_swapEnv2[simp]:
assumes "rho xs (x @xs [z1 \<and> z2]_zs) = Some X"
shows "(rho &[z1 \<and> z2]_zs) xs x = Some (X #[z1 \<and> z2]_zs)"
using assms unfolding swapEnv_defs lift_def by simp

theorem getEnv_psubstEnv_None[simp]:
assumes "rho xs x = None"
shows "(rho &[rho']) xs x = rho' xs x"
using assms unfolding psubstEnv_def by simp

theorem getEnv_psubstEnv_Some[simp]:
assumes "rho xs x = Some X"
shows "(rho &[rho']) xs x = Some (X #[rho'])"
using assms unfolding psubstEnv_def by simp

theorem getEnv_substEnv1[simp]:
assumes "ys \<noteq> xs \<or> y \<noteq> x" and "rho xs x = None"
shows "(rho &[Y / y]_ys) xs x = None"
using assms unfolding substEnv_def2 by auto

theorem getEnv_substEnv2[simp]:
assumes "ys \<noteq> xs \<or> y \<noteq> x" and "rho xs x = Some X"
shows "(rho &[Y / y]_ys) xs x = Some (X #[Y / y]_ys)"
using assms unfolding substEnv_def2 by auto

theorem getEnv_substEnv3[simp]:
"\<lbrakk>ys \<noteq> xs \<or> y \<noteq> x; freshEnv xs x rho\<rbrakk>
 \<Longrightarrow> (rho &[Y / y]_ys) xs x = None"
using getEnv_substEnv1 by auto

theorem getEnv_substEnv4[simp]:
"freshEnv ys y rho \<Longrightarrow> (rho &[Y / y]_ys) ys y = Some Y"
unfolding substEnv_psubstEnv_idEnv by simp

theorem getEnv_vsubstEnv1[simp]:
assumes "ys \<noteq> xs \<or> y \<noteq> x" and "rho xs x = None"
shows "(rho &[y1 // y]_ys) xs x = None"
using assms unfolding vsubstEnv_def by auto

theorem getEnv_vsubstEnv2[simp]:
assumes "ys \<noteq> xs \<or> y \<noteq> x" and "rho xs x = Some X"
shows "(rho &[y1 // y]_ys) xs x = Some (X #[y1 // y]_ys)"
using assms unfolding vsubstEnv_def vsubst_def by auto

theorem getEnv_vsubstEnv3[simp]:
"\<lbrakk>ys \<noteq> xs \<or> y \<noteq> x; freshEnv xs x rho\<rbrakk>
 \<Longrightarrow> (rho &[z // y]_ys) xs x = None"
using getEnv_vsubstEnv1 by auto

theorem getEnv_vsubstEnv4[simp]:
"freshEnv ys y rho \<Longrightarrow> (rho &[z // y]_ys) ys y = Some (Var ys z)"
unfolding vsubstEnv_psubstEnv_idEnv by simp

subsection {* Substitution versus other operators  *}

definition freshImEnvAt ::
"'varSort \<Rightarrow> 'var \<Rightarrow> ('index,'bindex,'varSort,'var,'opSym)env \<Rightarrow> 'varSort \<Rightarrow> 'var \<Rightarrow> bool"
where
"freshImEnvAt xs x rho ys y ==
 rho ys y = None \<and> (ys \<noteq> xs \<or> y \<noteq> x) \<or>
 (\<exists> Y. rho ys y = Some Y \<and> fresh xs x Y)"

lemma freshAll_psubstAll:
fixes X::"('index,'bindex,'varSort,'var,'opSym)term" and
      A::"('index,'bindex,'varSort,'var,'opSym)abs" and
      P::"('index,'bindex,'varSort,'var,'opSym)param" and x
assumes goodP: "goodPar P"
shows
"(good X \<longrightarrow> z \<in> varsOf P \<longrightarrow>
  (\<forall> rho \<in> envsOf P.
     fresh zs z (X #[rho]) =
     (\<forall> ys. \<forall> y. fresh ys y X \<or> freshImEnvAt zs z rho ys y)))
 \<and>
 (goodAbs A \<longrightarrow> z \<in> varsOf P \<longrightarrow>
  (\<forall> rho \<in> envsOf P.
     freshAbs zs z (A $[rho]) =
     (\<forall> ys. \<forall> y. freshAbs ys y A \<or> freshImEnvAt zs z rho ys y)))"
proof(induction rule: term_induct_fresh[of P])
  case Par
  then show ?case using goodP by simp
next
  case (Var ys y)
  thus ?case proof clarify 
    fix rho
    assume r: "rho \<in> envsOf P"
    hence g: "goodEnv rho" using goodP by simp    
    thus "fresh zs z (psubst rho (Var ys y)) = 
     (\<forall>ysa ya. fresh ysa ya (Var ys y) \<or> freshImEnvAt zs z rho ysa ya)" 
    unfolding freshImEnvAt_def
    by(cases "ys = zs \<and> y = z", (cases "rho ys y", auto)+)
  qed
next
  case (Op delta inp binp)
  show ?case proof clarify 
    fix rho 
    assume P: "z \<in> varsOf P" "rho \<in> envsOf P"
    let ?L1 = "liftAll (fresh zs z \<circ> psubst rho) inp"
    let ?L2 = "liftAll (freshAbs zs z \<circ> psubstAbs rho) binp"
    let ?R1 = "%ys y. liftAll (fresh ys y) inp"
    let ?R2 = "%ys y. liftAll (freshAbs ys y) binp"
    let ?R3 = "%ys y. freshImEnvAt zs z rho ys y"
    have "(?L1 \<and> ?L2) = (\<forall>ys y. ?R1 ys y \<and> ?R2 ys y \<or> ?R3 ys y)"
    using Op.IH P unfolding liftAll_def by simp blast
    thus "fresh zs z ((Op delta inp binp) #[rho]) =
           (\<forall>ys y. fresh ys y (Op delta inp binp) \<or> freshImEnvAt zs z rho ys y)" 
    by (metis (no_types, lifting) Op.hyps(1) Op.hyps(2) P(2) envsOf_preserves_good freshBinp_def freshInp_def fresh_Op_simp goodP liftAll_lift_comp psubstBinp_def psubstBinp_preserves_good 
     psubstInp_def psubstInp_preserves_good psubst_Op_simp)
  qed
next
  case (Abs xs x X)  
  thus ?case  
  using goodP by simp (metis (full_types) freshEnv_def freshImEnvAt_def)
qed 

corollary fresh_psubst:
assumes "good X" and "goodEnv rho"
shows
"fresh zs z (X #[rho]) =
 (\<forall> ys y. fresh ys y X \<or> freshImEnvAt zs z rho ys y)"
using assms freshAll_psubstAll[of "Par [z] [] [] [rho]"]
unfolding goodPar_def by simp

corollary fresh_psubst_E1:
assumes "good X" and "goodEnv rho"
and "rho ys y = None" and "fresh zs z (X #[rho])"
shows "fresh ys y X \<or> (ys \<noteq> zs \<or> y \<noteq> z)"
using assms fresh_psubst unfolding freshImEnvAt_def by fastforce

corollary fresh_psubst_E2:
assumes "good X" and "goodEnv rho"
and "rho ys y = Some Y" and "fresh zs z (X #[rho])"
shows "fresh ys y X \<or> fresh zs z Y"
using assms fresh_psubst[of X rho] unfolding freshImEnvAt_def by fastforce

corollary fresh_psubst_I1:
assumes "good X" and "goodEnv rho"
and "fresh zs z X" and "freshEnv zs z rho"
shows "fresh zs z (X #[rho])"
using assms apply(simp add: fresh_psubst)
unfolding freshEnv_def liftAll_def freshImEnvAt_def by auto

corollary psubstEnv_preserves_freshEnv:
assumes good: "goodEnv rho"  "goodEnv rho'"
and fresh: "freshEnv zs z rho"  "freshEnv zs z rho'"
shows "freshEnv zs z (rho &[rho'])"
using assms unfolding freshEnv_def liftAll_def  
by simp (smt Var_preserves_good fresh(2) fresh_psubst_I1 option.case_eq_if 
option.exhaust_sel option.sel psubstEnv_def psubst_Var_simp2 psubst_preserves_good)

corollary fresh_psubst_I:
assumes "good X" and "goodEnv rho"
and "rho zs z = None \<Longrightarrow> fresh zs z X" and
    "\<And> ys y Y. rho ys y = Some Y \<Longrightarrow> fresh ys y X \<or> fresh zs z Y"
shows "fresh zs z (X #[rho])"
using assms unfolding freshImEnvAt_def 
by (simp add: fresh_psubst) (metis freshImEnvAt_def not_None_eq)

lemma fresh_subst:
assumes "good X" and "good Y"
shows "fresh zs z (X #[Y / y]_ys) =
       (((zs = ys \<and> z = y) \<or> fresh zs z X) \<and> (fresh ys y X \<or> fresh zs z Y))"
using assms unfolding subst_def freshImEnvAt_def 
by (simp add: fresh_psubst) 
(metis (no_types, lifting) freshImEnvAt_def fresh_psubst fresh_psubst_E2 
getEnv_updEnv_idEnv idEnv_preserves_good option.simps(3) updEnv_preserves_good)

lemma fresh_vsubst:
assumes "good X"
shows "fresh zs z (X #[y1 // y]_ys) =
       (((zs = ys \<and> z = y) \<or> fresh zs z X) \<and> (fresh ys y X \<or> (zs \<noteq> ys \<or> z \<noteq> y1)))"
unfolding vsubst_def using assms by(auto simp: fresh_subst)

lemma subst_preserves_fresh:
assumes "good X" and "good Y"
and "fresh zs z X" and "fresh zs z Y"
shows "fresh zs z (X #[Y / y]_ys)"
using assms by(simp add: fresh_subst)

lemma substEnv_preserves_freshEnv_aux:
assumes rho: "goodEnv rho" and Y: "good Y"
and fresh_rho: "freshEnv zs z rho" and fresh_Y: "fresh zs z Y" and diff: "zs \<noteq> ys \<or> z \<noteq> y"
shows "freshEnv zs z (rho &[Y / y]_ys)"
using assms unfolding freshEnv_def liftAll_def 
by (simp add: option.case_eq_if substEnv_def2 subst_preserves_fresh)

lemma substEnv_preserves_freshEnv:
assumes rho: "goodEnv rho" and Y: "good Y"
and fresh_rho: "freshEnv zs z rho" and fresh_Y: "fresh zs z Y" and diff: "zs \<noteq> ys \<or> z \<noteq> y"
shows "freshEnv zs z (rho &[Y / y]_ys)"
using assms by(simp add: substEnv_preserves_freshEnv_aux)

lemma vsubst_preserves_fresh:
assumes "good X"
and "fresh zs z X" and "zs \<noteq> ys \<or> z \<noteq> y1"
shows "fresh zs z (X #[y1 // y]_ys)"
using assms by(simp add: fresh_vsubst)

lemma vsubstEnv_preserves_freshEnv:
assumes rho: "goodEnv rho"
and fresh_rho: "freshEnv zs z rho" and diff: "zs \<noteq> ys \<or> z \<notin> {y,y1}"
shows "freshEnv zs z (rho &[y1 // y]_ys)"
using assms unfolding vsubstEnv_def
by(simp add: substEnv_preserves_freshEnv)

lemma fresh_fresh_subst[simp]:
assumes "good Y" and "good X"
and "fresh ys y Y"
shows "fresh ys y (X #[Y / y]_ys)"
using assms by(simp add: fresh_subst)

lemma diff_fresh_vsubst[simp]:
assumes "good X"
and "y \<noteq> y1"
shows "fresh ys y (X #[y1 // y]_ys)"
using assms by(simp add: fresh_vsubst)

lemma fresh_subst_E1:
assumes "good X" and "good Y"
and "fresh zs z (X #[Y / y]_ys)" and "zs \<noteq> ys \<or> z \<noteq> y"
shows "fresh zs z X"
using assms by(auto simp add: fresh_subst)

lemma fresh_vsubst_E1:
assumes "good X"
and "fresh zs z (X #[y1 // y]_ys)" and "zs \<noteq> ys \<or> z \<noteq> y"
shows "fresh zs z X"
using assms by(auto simp add: fresh_vsubst)

lemma fresh_subst_E2:
assumes "good X" and "good Y"
and "fresh zs z (X #[Y / y]_ys)"
shows "fresh ys y X \<or> fresh zs z Y"
using assms by(simp add: fresh_subst)

lemma fresh_vsubst_E2:
assumes "good X"
and "fresh zs z (X #[y1 // y]_ys)"
shows "fresh ys y X \<or> zs \<noteq> ys \<or> z \<noteq> y1"
using assms by(simp add: fresh_vsubst)

lemma psubstAll_cong:
fixes X::"('index,'bindex,'varSort,'var,'opSym)term" and
      A::"('index,'bindex,'varSort,'var,'opSym)abs" and
      P::"('index,'bindex,'varSort,'var,'opSym)param"
assumes goodP: "goodPar P"
shows
"(good X \<longrightarrow>
  (\<forall> rho rho'. {rho, rho'} \<subseteq> envsOf P \<longrightarrow>
   (\<forall> ys. \<forall> y. fresh ys y X \<or> rho ys y = rho' ys y) \<longrightarrow>
               (X #[rho]) = (X #[rho'])))
\<and>
 (goodAbs A \<longrightarrow>
  (\<forall> rho rho'. {rho, rho'} \<subseteq> envsOf P \<longrightarrow>
   (\<forall> ys. \<forall> y. freshAbs ys y A \<or> rho ys y = rho' ys y) \<longrightarrow>
               (A $[rho]) = (A $[rho'])))"
proof(induction rule: term_induct_fresh[of P])
  case Par
  then show ?case using assms .
next  
  case (Var xs x)
  then show ?case using goodP by (auto simp: psubst_Var)
next
  case (Op delta inp binp)
  show ?case proof clarify
    fix rho rho'  
    assume envs: "{rho, rho'} \<subseteq> envsOf P"   
    hence goodEnv: "goodEnv rho \<and> goodEnv rho'" using goodP by simp
    assume "\<forall>ys y. fresh ys y (Op delta inp binp) \<or> rho ys y = rho' ys y"
    hence 1: "liftAll (\<lambda> X. \<forall>ys y. fresh ys y X \<or> rho ys y = rho' ys y) inp \<and>
            liftAll (\<lambda> A. \<forall>ys y. freshAbs ys y A \<or> rho ys y = rho' ys y) binp"
    using Op by simp (smt freshBinp_def freshInp_def liftAll_def)
    have "liftAll (\<lambda> X. (X #[rho]) = (X #[rho'])) inp \<and>
          liftAll (\<lambda> A. (A $[rho]) = (A $[rho'])) binp" 
    using Op.IH 1 envs by (auto simp: liftAll_def)
    thus "(Op delta inp binp) #[rho] = (Op delta inp binp) #[rho']" 
    using Op.IH 1
    by (simp add: Op.hyps goodEnv psubstBinp_def psubstInp_def liftAll_lift_ext)
  qed
next
  case (Abs xs x X)
  thus ?case
  using Abs goodP unfolding freshEnv_def liftAll_def 
  by simp (metis Abs.hyps(5) envsOf_preserves_good psubstAbs_simp)
qed

corollary psubst_cong[fundef_cong]:
assumes "good X" and "goodEnv rho" and "goodEnv rho'"
and "\<And> ys y. fresh ys y X \<or> rho ys y = rho' ys y"
shows "(X #[rho]) = (X #[rho'])"
using assms psubstAll_cong[of "Par [] [] [] [rho,rho']"]
unfolding goodPar_def by simp

(* Note: A congruence principle for ``psubstEnv" would not hold w.r.t. ``freshEnv",
and the one that would hold w.r.t. ``fresh" would be a mere rephrasing of the
definition of ``psubstEnv", not worth stating. *)

lemma fresh_psubst_updEnv:
assumes "good X" and "good Y" and "goodEnv rho"
and "fresh xs x Y"
shows "(Y #[rho [x \<leftarrow> X]_xs]) = (Y #[rho])"
using assms by (auto cong: psubst_cong)

lemma psubstAll_ident:
fixes X :: "('index,'bindex,'varSort,'var,'opSym)term" and
      A :: "('index,'bindex,'varSort,'var,'opSym)abs" and
      P :: "('index,'bindex,'varSort,'var,'opSym) Transition_QuasiTerms_Terms.param"
assumes P: "goodPar P"
shows
"(good X \<longrightarrow>
  (\<forall> rho \<in> envsOf P.
   (\<forall> zs z. freshEnv zs z rho \<or> fresh zs z X)
   \<longrightarrow> (X #[rho]) = X))
 \<and>
 (goodAbs A \<longrightarrow>
  (\<forall> rho \<in> envsOf P.
   (\<forall> zs z. freshEnv zs z rho \<or> freshAbs zs z A)
   \<longrightarrow> (A $[rho]) = A))"
proof(induction rule: term_induct_fresh)
  case (Var xs x)
  then show ?case  
  by (meson assms freshEnv_def fresh_Var_simp goodPar_def psubst_Var_simp1)
next
  case (Op delta inp binp)
  then show ?case  
  by (metis (no_types,lifting) Op_preserves_good assms envsOf_preserves_good 
   freshEnv_getEnv idEnv_def idEnv_preserves_good psubst_cong psubst_idEnv)
qed(insert P, fastforce+)

corollary freshEnv_psubst_ident[simp]:
fixes X :: "('index,'bindex,'varSort,'var,'opSym)term"
assumes "good X" and "goodEnv rho"
and "\<And> zs z. freshEnv zs z rho \<or> fresh zs z X"
shows "(X #[rho]) = X"
using assms psubstAll_ident[of "Par [] [] [] [rho]"]
unfolding goodPar_def by simp

lemma fresh_subst_ident[simp]:
assumes "good X" and "good Y" and "fresh xs x Y"
shows "(Y #[X / x]_xs) = Y"
by (simp add: assms fresh_psubst_updEnv subst_def)

corollary substEnv_updEnv_fresh:
assumes "good X" and "good Y" and "fresh ys y X"
shows "((rho [x \<leftarrow> X]_xs) &[Y / y]_ys) = ((rho &[Y / y]_ys) [x \<leftarrow> X]_xs)"
using assms by(simp add: substEnv_updEnv)

lemma fresh_substEnv_updEnv[simp]:
assumes rho: "goodEnv rho" and Y: "good Y"
and *: "freshEnv ys y rho"
shows "(rho &[Y / y]_ys) = (rho [y \<leftarrow> Y]_ys)"
apply (rule getEnv_ext) 
subgoal for xs x using assms by (cases "rho xs x") auto .

lemma fresh_vsubst_ident[simp]:
assumes "good Y" and "fresh xs x Y"
shows "(Y #[x1 // x]_xs) = Y"
using assms unfolding vsubst_def by simp

corollary vsubstEnv_updEnv_fresh:
assumes "good X" and "fresh ys y X"
shows "((rho [x \<leftarrow> X]_xs) &[y1 // y]_ys) = ((rho &[y1 // y]_ys) [x \<leftarrow> X]_xs)"
using assms by(simp add: vsubstEnv_updEnv)

lemma fresh_vsubstEnv_updEnv[simp]:
assumes rho: "goodEnv rho"
and *: "freshEnv ys y rho"
shows "(rho &[y1 // y]_ys) = (rho [y \<leftarrow> Var ys y1]_ys)"
using assms unfolding vsubstEnv_def by simp

lemma swapAll_psubstAll:
fixes X::"('index,'bindex,'varSort,'var,'opSym)term" and
      A::"('index,'bindex,'varSort,'var,'opSym)abs" and
      P::"('index,'bindex,'varSort,'var,'opSym)param"
assumes P: "goodPar P"
shows
"(good X \<longrightarrow>
  (\<forall> rho z1 z2. rho \<in> envsOf P \<and> {z1,z2} \<subseteq> varsOf P \<longrightarrow>
                ((X #[rho]) #[z1 \<and> z2]_zs) = ((X #[z1 \<and> z2]_zs) #[rho &[z1 \<and> z2]_zs])))
 \<and>
 (goodAbs A \<longrightarrow>
  (\<forall> rho z1 z2. rho \<in> envsOf P \<and> {z1,z2} \<subseteq> varsOf P \<longrightarrow>
                ((A $[rho]) $[z1 \<and> z2]_zs) = ((A $[z1 \<and> z2]_zs) $[rho &[z1 \<and> z2]_zs])))"
proof(induction rule: term_induct_fresh[of P])
  case (Var xs x)
  then show ?case using assms 
  by simp (smt Var_preserves_good envsOf_preserves_good getEnv_swapEnv1 getEnv_swapEnv2 option.case_eq_if option.exhaust_sel psubst_Var psubst_Var_simp2 swapEnv_preserves_good 
 swap_Var_simp swap_involutive2 swap_sym)
next
  case (Op delta inp binp)
  then show ?case 
  using assms  
  unfolding psubstInp_def swapInp_def psubstBinp_def swapBinp_def lift_comp
  unfolding liftAll_def lift_def  
  by simp (auto simp: lift_def psubstInp_def swapInp_def 
  psubstBinp_def swapBinp_def split: option.splits) 
qed(insert assms, auto)
 
lemma swap_psubst:
assumes "good X" and "goodEnv rho"
shows "((X #[rho]) #[z1 \<and> z2]_zs) = ((X #[z1 \<and> z2]_zs) #[rho &[z1 \<and> z2]_zs])"
using assms swapAll_psubstAll[of "Par [z1,z2] [] [] [rho]"]
unfolding goodPar_def by auto

lemma swap_subst:
assumes "good X" and "good Y"
shows "((X #[Y / y]_ys) #[z1 \<and> z2]_zs) =
       ((X #[z1 \<and> z2]_zs) #[(Y #[z1 \<and> z2]_zs) / (y @ys[z1 \<and> z2]_zs)]_ys)"
proof-
  have 1: "(idEnv [(y @ys[z1 \<and> z2]_zs) \<leftarrow> (Y #[z1 \<and> z2]_zs)]_ys) =
           ((idEnv [y \<leftarrow> Y]_ys) &[z1 \<and> z2]_zs)"
  by(simp add: swapEnv_updEnv)
  show ?thesis
  using assms unfolding subst_def 1 by (intro swap_psubst) auto
qed

lemma swap_vsubst:
assumes "good X"
shows "((X #[y1 // y]_ys) #[z1 \<and> z2]_zs) =
       ((X #[z1 \<and> z2]_zs) #[(y1 @ys[z1 \<and> z2]_zs) // (y @ys[z1 \<and> z2]_zs)]_ys)"
using assms unfolding vsubst_def
by(simp add: swap_subst)

lemma swapEnv_psubstEnv:
assumes "goodEnv rho" and "goodEnv rho'"
shows "((rho &[rho']) &[z1 \<and> z2]_zs) = ((rho &[z1 \<and> z2]_zs) &[rho' &[z1 \<and> z2]_zs])"  
using assms apply(intro ext)
subgoal for xs x
by (cases "rho xs (x @xs[z1 \<and> z2]_zs)")
   (auto simp: lift_def swapEnv_defs swap_psubst) .

lemma swapEnv_substEnv:
assumes "good Y" and "goodEnv rho"
shows "((rho &[Y / y]_ys) &[z1 \<and> z2]_zs) =
       ((rho &[z1 \<and> z2]_zs) &[(Y #[z1 \<and> z2]_zs) / (y @ys[z1 \<and> z2]_zs)]_ys)"
proof-
  have 1: "(idEnv [(y @ys[z1 \<and> z2]_zs) \<leftarrow> (Y #[z1 \<and> z2]_zs)]_ys) =
           ((idEnv [y \<leftarrow> Y]_ys) &[z1 \<and> z2]_zs)"
  by(simp add: swapEnv_updEnv)
  show ?thesis
  unfolding substEnv_def 1 
  using assms by (intro swapEnv_psubstEnv) auto
qed

lemma swapEnv_vsubstEnv:
assumes "goodEnv rho"
shows "((rho &[y1 // y]_ys) &[z1 \<and> z2]_zs) =
       ((rho &[z1 \<and> z2]_zs) &[(y1 @ys[z1 \<and> z2]_zs) // (y @ys[z1 \<and> z2]_zs)]_ys)"
using assms unfolding vsubstEnv_def by(simp add: swapEnv_substEnv)

lemma psubstAll_compose:
fixes X::"('index,'bindex,'varSort,'var,'opSym)term" and
      A::"('index,'bindex,'varSort,'var,'opSym)abs" and
      P::"('index,'bindex,'varSort,'var,'opSym)param"
assumes P: "goodPar P"
shows
"(good X \<longrightarrow>
  (\<forall> rho rho'. {rho,rho'} \<subseteq> envsOf P \<longrightarrow> ((X #[rho]) #[rho']) = (X #[(rho &[rho'])])))
\<and>
 (goodAbs A \<longrightarrow>
  (\<forall> rho rho'. {rho,rho'} \<subseteq> envsOf P \<longrightarrow> ((A $[rho]) $[rho']) = (A $[(rho &[rho'])])))"
proof(induction rule: term_induct_fresh[of P])
  case (Var xs x)
  then show ?case using assms 
  by simp (smt envsOf_preserves_good option.case_eq_if option.sel psubstEnv_def 
  psubstEnv_idEnv_id psubstEnv_preserves_good psubst_Var_simp1 psubst_Var_simp2)
next
  case (Op delta inp binp)
  then show ?case 
  using assms  
  unfolding psubstInp_def swapInp_def psubstBinp_def swapBinp_def lift_comp
  unfolding liftAll_def lift_def  
  by simp (auto simp: lift_def psubstInp_def swapInp_def 
  psubstBinp_def swapBinp_def split: option.splits) 
qed(insert assms, simp_all add: psubstEnv_preserves_freshEnv)

corollary psubst_compose:
assumes "good X" and "goodEnv rho" and "goodEnv rho'"
shows "((X #[rho]) #[rho']) = (X #[(rho &[rho'])])"
using assms psubstAll_compose[of "Par [] [] [] [rho, rho']"]
unfolding goodPar_def by auto

lemma psubstEnv_compose:
assumes "goodEnv rho" and "goodEnv rho'" and "goodEnv rho''"
shows "((rho &[rho']) &[rho'']) = (rho &[(rho' &[rho''])])"
using assms apply(intro ext)
subgoal for xs x
by (cases "rho xs x") (auto simp: lift_def psubstEnv_def  psubst_compose) . 
 
lemma psubst_subst_compose:
assumes "good X" and "good Y" and "goodEnv rho"
shows "((X #[Y / y]_ys) #[rho]) = (X #[(rho [y \<leftarrow> (Y #[rho])]_ys)])"
by (simp add: assms psubstEnv_updEnv_idEnv psubst_compose subst_psubst_idEnv)

lemma psubstEnv_substEnv_compose:
assumes "goodEnv rho" and "good Y" and "goodEnv rho'"
shows "((rho &[Y / y]_ys) &[rho']) = (rho &[(rho' [y \<leftarrow> (Y #[rho'])]_ys)])"
by (simp add: assms psubstEnv_compose psubstEnv_updEnv_idEnv substEnv_def)

lemma psubst_vsubst_compose:
assumes "good X" and "goodEnv rho"
shows "((X #[y1 // y]_ys) #[rho]) = (X #[(rho [y \<leftarrow> ((Var ys y1) #[rho])]_ys)])"
using assms unfolding vsubst_def by(simp add: psubst_subst_compose)

lemma psubstEnv_vsubstEnv_compose:
assumes "goodEnv rho" and "goodEnv rho'"
shows "((rho &[y1 // y]_ys) &[rho']) = (rho &[(rho' [y \<leftarrow> ((Var ys y1) #[rho'])]_ys)])"
using assms unfolding vsubstEnv_def by(simp add: psubstEnv_substEnv_compose)

lemma subst_psubst_compose:
assumes "good X" and "good Y" and "goodEnv rho"
shows "((X #[rho]) #[Y / y]_ys) = (X #[(rho &[Y / y]_ys)])"
unfolding subst_def substEnv_def using assms by(simp add: psubst_compose)

lemma substEnv_psubstEnv_compose:
assumes "goodEnv rho" and "good Y" and "goodEnv rho'"
shows "((rho &[rho']) &[Y / y]_ys) = (rho &[(rho' &[Y / y]_ys)])"
unfolding substEnv_def using assms by(simp add: psubstEnv_compose)

lemma psubst_subst_compose_freshEnv:
assumes "goodEnv rho" and "good X" and "good Y"
assumes "freshEnv ys y rho"
shows "((X #[Y / y]_ys) #[rho]) = ((X #[rho]) #[(Y #[rho]) / y]_ys)"
using assms by (simp add: subst_psubst_compose psubst_subst_compose)

lemma psubstEnv_substEnv_compose_freshEnv:
assumes "goodEnv rho" and "goodEnv rho'" and "good Y"
assumes "freshEnv ys y rho'"
shows "((rho &[Y / y]_ys) &[rho']) = ((rho &[rho']) &[(Y #[rho']) / y]_ys)"
using assms by (simp add: substEnv_psubstEnv_compose psubstEnv_substEnv_compose)

lemma vsubst_psubst_compose:
assumes "good X" and "goodEnv rho"
shows "((X #[rho]) #[y1 // y]_ys) = (X #[(rho &[y1 // y]_ys)])"
unfolding vsubst_def vsubstEnv_def using assms by(simp add: subst_psubst_compose)

lemma vsubstEnv_psubstEnv_compose:
assumes "goodEnv rho" and "goodEnv rho'"
shows "((rho &[rho']) &[y1 // y]_ys) = (rho &[(rho' &[y1 // y]_ys)])"
unfolding vsubstEnv_def using assms by(simp add: substEnv_psubstEnv_compose)

lemma subst_compose1:
assumes "good X" and "good Y1" and "good Y2"
shows "((X #[Y1 / y]_ys) #[Y2 / y]_ys) = (X #[(Y1 #[Y2 / y]_ys) / y]_ys)"
proof-
  have "goodEnv (idEnv [y \<leftarrow> Y1]_ys) \<and> goodEnv (idEnv [y \<leftarrow> Y2]_ys)" using assms by simp
  thus ?thesis using `good X` unfolding subst_def substEnv_def
  by(simp add: psubst_compose psubstEnv_updEnv)
qed

lemma substEnv_compose1:
assumes "goodEnv rho" and "good Y1" and "good Y2"
shows "((rho &[Y1 / y]_ys) &[Y2 / y]_ys) = (rho &[(Y1 #[Y2 / y]_ys) / y]_ys)"
by (simp add: assms psubstEnv_compose psubstEnv_updEnv_idEnv substEnv_def subst_psubst_idEnv)

lemma subst_vsubst_compose1:
assumes "good X" and "good Y" and "y \<noteq> y1"
shows "((X #[y1 // y]_ys) #[Y / y]_ys) = (X #[y1 // y]_ys)"
using assms unfolding vsubst_def by(simp add: subst_compose1)

lemma substEnv_vsubstEnv_compose1:
assumes "goodEnv rho" and "good Y" and "y \<noteq> y1"
shows "((rho &[y1 // y]_ys) &[Y / y]_ys) = (rho &[y1 // y]_ys)"
using assms unfolding vsubst_def vsubstEnv_def by(simp add: substEnv_compose1)

lemma vsubst_subst_compose1:
assumes "good X" and "good Y"
shows "((X #[Y / y]_ys) #[y1 // y]_ys) = (X #[(Y #[y1 // y]_ys) / y]_ys)"
using assms unfolding vsubst_def by(simp add: subst_compose1)

lemma vsubstEnv_substEnv_compose1:
assumes "goodEnv rho" and "good Y"
shows "((rho &[Y / y]_ys) &[y1 // y]_ys) = (rho &[(Y #[y1 // y]_ys) / y]_ys)"
using assms unfolding vsubst_def vsubstEnv_def by(simp add: substEnv_compose1)

lemma vsubst_compose1:
assumes "good X"
shows "((X #[y1 // y]_ys) #[y2 // y]_ys) = (X #[(y1 @ys[y2 / y]_ys) // y]_ys)"
using assms unfolding vsubst_def 
by(cases "y = y1") (auto simp: subst_compose1)

lemma vsubstEnv_compose1:
assumes "goodEnv rho"
shows "((rho &[y1 // y]_ys) &[y2 // y]_ys) = (rho &[(y1 @ys[y2 / y]_ys) // y]_ys)"
using assms unfolding vsubstEnv_def 
by(cases "y = y1") (auto simp: substEnv_compose1)

lemma subst_compose2:
assumes  "good X" and "good Y" and "good Z"
and "ys \<noteq> zs \<or> y \<noteq> z" and fresh: "fresh ys y Z"
shows "((X #[Y / y]_ys) #[Z / z]_zs) = ((X #[Z / z]_zs) #[(Y #[Z / z]_zs) / y]_ys)"
by (metis assms fresh freshEnv_getEnv freshEnv_getEnv2 freshEnv_idEnv freshEnv_updEnv_I idEnv_preserves_good psubst_subst_compose_freshEnv 
 subst_psubst_idEnv updEnv_preserves_good)
 
lemma substEnv_compose2:
assumes  "goodEnv rho" and "good Y" and "good Z"
and "ys \<noteq> zs \<or> y \<noteq> z" and fresh: "fresh ys y Z"
shows "((rho &[Y / y]_ys) &[Z / z]_zs) = ((rho &[Z / z]_zs) &[(Y #[Z / z]_zs) / y]_ys)"
  by (metis assms fresh freshEnv_updEnv_I getEnv_idEnv idEnv_preserves_good 
   option.discI psubstEnv_substEnv_compose_freshEnv substEnv_def 
  subst_psubst_idEnv updEnv_preserves_good)

lemma subst_vsubst_compose2:
assumes  "good X" and "good Z"
and "ys \<noteq> zs \<or> y \<noteq> z" and fresh: "fresh ys y Z"
shows "((X #[y1 // y]_ys) #[Z / z]_zs) = ((X #[Z / z]_zs) #[((Var ys y1) #[Z / z]_zs) / y]_ys)"
using assms unfolding vsubst_def by(simp add: subst_compose2)

lemma substEnv_vsubstEnv_compose2:
assumes  "goodEnv rho" and "good Z"
and "ys \<noteq> zs \<or> y \<noteq> z" and fresh: "fresh ys y Z"
shows "((rho &[y1 // y]_ys) &[Z / z]_zs) = ((rho &[Z / z]_zs) &[((Var ys y1) #[Z / z]_zs) / y]_ys)"
using assms unfolding vsubstEnv_def by(simp add: substEnv_compose2)

lemma vsubst_subst_compose2:
assumes  "good X" and "good Y"
and "ys \<noteq> zs \<or> y \<notin> {z,z1}"
shows "((X #[Y / y]_ys) #[z1 // z]_zs) = ((X #[z1 // z]_zs) #[(Y #[z1 // z]_zs) / y]_ys)"
using assms unfolding vsubst_def by(simp add: subst_compose2)

lemma vsubstEnv_substEnv_compose2:
assumes  "goodEnv rho" and "good Y"
and "ys \<noteq> zs \<or> y \<notin> {z,z1}"
shows "((rho &[Y / y]_ys) &[z1 // z]_zs) = ((rho &[z1 // z]_zs) &[(Y #[z1 // z]_zs) / y]_ys)"
using assms unfolding vsubst_def vsubstEnv_def by(simp add: substEnv_compose2)

lemma vsubst_compose2:
assumes  "good X"
and "ys \<noteq> zs \<or> y \<notin> {z,z1}"
shows "((X #[y1 // y]_ys) #[z1 // z]_zs) =
       ((X #[z1 // z]_zs) #[(y1 @ys[z1 / z]_zs) // y]_ys)"
by (metis vsubst_def Var_preserves_good assms vsubst_Var_simp vsubst_def 
    vsubst_subst_compose2) 

lemma vsubstEnv_compose2:
assumes "goodEnv rho"
and "ys \<noteq> zs \<or> y \<notin> {z,z1}"
shows "((rho &[y1 // y]_ys) &[z1 // z]_zs) =
       ((rho &[z1 // z]_zs) &[(y1 @ys[z1 / z]_zs) // y]_ys)"
by (metis Var_preserves_good assms 
vsubstEnv_def vsubstEnv_substEnv_compose2 vsubst_Var_simp)

subsection {* Properties specific to variable-for-variable substitution *}

(* Note: The results in this section cannot be lifted to environments, and therefore
we don't have ``environment versions" of these.  *)

lemma vsubstAll_ident:
fixes X::"('index,'bindex,'varSort,'var,'opSym)term" and
      A::"('index,'bindex,'varSort,'var,'opSym)abs" and
      P::"('index,'bindex,'varSort,'var,'opSym)param" and zs
assumes P: "goodPar P"
shows
"(good X \<longrightarrow>
  (\<forall> z. z \<in> varsOf P \<longrightarrow> (X #[z // z]_zs) = X))
\<and>
 (goodAbs A \<longrightarrow>
  (\<forall> z. z \<in> varsOf P \<longrightarrow> (A $[z // z]_zs) = A))"
proof(induct rule: term_induct_fresh[of P])
  case (Op delta inp binp)
  then show ?case
  using assms
  unfolding vsubst_def vsubstAbs_def liftAll_def lift_def  
  by simp (auto simp: lift_def substInp_def2 substBinp_def2 vsubstInp_def2 
        split: option.splits)   
next
  case (Abs xs x X)
  then show ?case
  by (metis empty_iff insert_iff vsubstAbs_simp)
qed(insert assms, simp_all)
 
corollary vsubst_ident[simp]:
assumes "good X"
shows "(X #[z // z]_zs) = X"
using assms vsubstAll_ident[of "Par [z] [] [] []" X]
unfolding goodPar_def by simp

corollary subst_ident[simp]:
assumes "good X"
shows "(X #[(Var zs z) / z]_zs) = X"
using assms vsubst_ident unfolding vsubst_def by auto

lemma vsubstAll_swapAll:
fixes X::"('index,'bindex,'varSort,'var,'opSym)term" and
      A::"('index,'bindex,'varSort,'var,'opSym)abs" and
      P::"('index,'bindex,'varSort,'var,'opSym)param" and ys
assumes P: "goodPar P"
shows
"(good X \<longrightarrow>
  (\<forall> y1 y2. {y1,y2} \<subseteq> varsOf P \<and> fresh ys y1 X \<longrightarrow>
            (X #[y1 // y2]_ys) = (X #[y1 \<and> y2]_ys)))
\<and>
 (goodAbs A \<longrightarrow>
  (\<forall> y1 y2. {y1,y2} \<subseteq> varsOf P \<and> freshAbs ys y1 A  \<longrightarrow>
            (A $[y1 // y2]_ys) = (A $[y1 \<and> y2]_ys)))"
apply(induction rule: term_induct_fresh[OF P])
subgoal by (force simp add: sw_def) 
subgoal by simp (auto 
  simp: vsubstInp_def substInp_def2 vsubst_def swapInp_def 
              vsubstBinp_def substBinp_def2 vsubstAbs_def swapBinp_def  
              freshInp_def  freshBinp_def lift_def liftAll_def
  split: option.splits) 
subgoal by simp (metis Var_preserves_good fresh_Var_simp substAbs_simp sw_def
  vsubstAbs_def vsubst_def) .

corollary vsubst_eq_swap:
assumes "good X" and "y1 = y2 \<or> fresh ys y1 X"
shows "(X #[y1 // y2]_ys) = (X #[y1 \<and> y2]_ys)"
apply(cases "y1 = y2")  
using assms vsubstAll_swapAll[of "Par [y1, y2] [] [] []" X]
unfolding goodPar_def by auto

lemma skelAll_vsubstAll:
fixes X::"('index,'bindex,'varSort,'var,'opSym)term" and
      A::"('index,'bindex,'varSort,'var,'opSym)abs" and
      P::"('index,'bindex,'varSort,'var,'opSym)param" and ys
assumes P: "goodPar P"
shows
"(good X \<longrightarrow>
  (\<forall> y1 y2. {y1,y2} \<subseteq> varsOf P \<longrightarrow>
            skel (X #[y1 // y2]_ys) = skel X))
\<and>
 (goodAbs A \<longrightarrow>
  (\<forall> y1 y2. {y1,y2} \<subseteq> varsOf P \<longrightarrow>
            skelAbs (A $[y1 // y2]_ys) = skelAbs A))"
proof(induction rule: term_induct_fresh[of P])
  case (Op delta inp binp)
  then show ?case 
  by (simp add: skelInp_def2 skelBinp_def2)
   (auto simp: vsubst_def vsubstInp_def substInp_def2
       vsubstAbs_def vsubstBinp_def substBinp_def2 lift_def liftAll_def
       split: option.splits) 
next
  case (Abs xs x X)
  then show ?case using assms  
  by simp (metis not_equals_and_not_equals_not_in 
     skelAbs_simp vsubstAbs_simp vsubst_preserves_good)
qed(insert assms, simp_all) 

corollary skel_vsubst:
assumes "good X"
shows "skel (X #[y1 // y2]_ys) = skel X"
using assms skelAll_vsubstAll[of "Par [y1, y2] [] [] []" X]
unfolding goodPar_def by simp

lemma subst_vsubst_trans:
assumes  "good X" and "good Y" and "fresh ys y1 X"
shows "((X #[y1 // y]_ys) #[Y / y1]_ys) = (X #[Y / y]_ys)"
using assms unfolding subst_def vsubst_def 
by (cases "y1 = y") (simp_all add: fresh_psubst_updEnv psubstEnv_updEnv_idEnv 
  psubst_compose updEnv_commute)

lemma vsubst_trans:
assumes  "good X" and "fresh ys y1 X"
shows "((X #[y1 // y]_ys) #[y2 // y1]_ys) = (X #[y2 // y]_ys)"
unfolding vsubst_def[of _ y2 y1] vsubst_def[of _ y2 y]
using assms by(simp add: subst_vsubst_trans)

lemma vsubst_commute:
assumes X: "good X"
and "xs \<noteq> xs' \<or> {x,y} \<inter> {x',y'} = {}" and "fresh xs x X" and "fresh xs' x' X"
shows "((X #[x // y]_xs) #[x' // y']_xs') = ((X #[x' // y']_xs') #[x // y]_xs)"
proof-
  have "fresh xs' x' (X #[x // y]_xs)"
  using assms by (intro vsubst_preserves_fresh) auto
  moreover have "fresh xs x (X #[x' // y']_xs')"
  using assms by (intro vsubst_preserves_fresh) auto
  ultimately show ?thesis using assms
  by (auto simp: vsubst_eq_swap intro!: swap_commute)
qed

subsection {* Abstraction versions of the properties *}

text{* Environment identity and update versus other operators: *}

lemma psubstAbs_idEnv[simp]:
"goodAbs A \<Longrightarrow> (A $[idEnv]) = A"
by(simp add: psubstAll_idEnv)

text{* Substitution versus other operators:  *}

corollary freshAbs_psubstAbs:
assumes "goodAbs A" and "goodEnv rho"
shows
"freshAbs zs z (A $[rho]) =
 (\<forall> ys y. freshAbs ys y A \<or> freshImEnvAt zs z rho ys y)"
using assms freshAll_psubstAll[of "Par [z] [] [] [rho]"]
unfolding goodPar_def by simp

corollary freshAbs_psubstAbs_E1:
assumes "goodAbs A" and "goodEnv rho"
and "rho ys y = None" and "freshAbs zs z (A $[rho])"
shows "freshAbs ys y A \<or> (ys \<noteq> zs \<or> y \<noteq> z)"
using assms freshAbs_psubstAbs unfolding freshImEnvAt_def by fastforce

corollary freshAbs_psubstAbs_E2:
assumes "goodAbs A" and "goodEnv rho"
and "rho ys y = Some Y" and "freshAbs zs z (A $[rho])"
shows "freshAbs ys y A \<or> fresh zs z Y"
using assms freshAbs_psubstAbs[of A rho] unfolding freshImEnvAt_def by fastforce

corollary freshAbs_psubstAbs_I1:
assumes "goodAbs A" and "goodEnv rho"
and "freshAbs zs z A" and "freshEnv zs z rho"
shows "freshAbs zs z (A $[rho])"
using assms apply(simp add: freshAbs_psubstAbs)
unfolding freshEnv_def liftAll_def freshImEnvAt_def by auto

corollary freshAbs_psubstAbs_I:
assumes "goodAbs A" and "goodEnv rho"
and "rho zs z = None \<Longrightarrow> freshAbs zs z A" and
    "\<And> ys y Y. rho ys y = Some Y \<Longrightarrow> freshAbs ys y A \<or> fresh zs z Y"
shows "freshAbs zs z (A $[rho])"
using assms using option.exhaust_sel 
by (simp add: freshAbs_psubstAbs freshImEnvAt_def) blast  

lemma freshAbs_substAbs:
assumes "goodAbs A" and "good Y"
shows "freshAbs zs z (A $[Y / y]_ys) =
       (((zs = ys \<and> z = y) \<or> freshAbs zs z A) \<and> (freshAbs ys y A \<or> fresh zs z Y))"
unfolding substAbs_def using assms 
by (auto simp: freshAbs_psubstAbs freshImEnvAt_def)

lemma freshAbs_vsubstAbs:
assumes "goodAbs A"
shows "freshAbs zs z (A $[y1 // y]_ys) =
       (((zs = ys \<and> z = y) \<or> freshAbs zs z A) \<and>
        (freshAbs ys y A \<or> (zs \<noteq> ys \<or> z \<noteq> y1)))"
unfolding vsubstAbs_def using assms by(auto simp: freshAbs_substAbs)

lemma substAbs_preserves_freshAbs:
assumes "goodAbs A" and "good Y"
and "freshAbs zs z A" and "fresh zs z Y"
shows "freshAbs zs z (A $[Y / y]_ys)"
using assms by(simp add: freshAbs_substAbs)

lemma vsubstAbs_preserves_freshAbs:
assumes "goodAbs A"
and "freshAbs zs z A" and "zs \<noteq> ys \<or> z \<noteq> y1"
shows "freshAbs zs z (A $[y1 // y]_ys)"
using assms by(simp add: freshAbs_vsubstAbs)

lemma fresh_freshAbs_substAbs[simp]:
assumes "good Y" and "goodAbs A"
and "fresh ys y Y"
shows "freshAbs ys y (A $[Y / y]_ys)"
using assms by(simp add: freshAbs_substAbs)

lemma diff_freshAbs_vsubstAbs[simp]:
assumes "goodAbs A"
and "y \<noteq> y1"
shows "freshAbs ys y (A $[y1 // y]_ys)"
using assms by(simp add: freshAbs_vsubstAbs)

lemma freshAbs_substAbs_E1:
assumes "goodAbs A" and "good Y"
and "freshAbs zs z (A $[Y / y]_ys)" and "zs \<noteq> ys \<or> z \<noteq> y"
shows "freshAbs zs z A"
using assms by(auto simp: freshAbs_substAbs)

lemma freshAbs_vsubstAbs_E1:
assumes "goodAbs A"
and "freshAbs zs z (A $[y1 // y]_ys)" and "zs \<noteq> ys \<or> z \<noteq> y"
shows "freshAbs zs z A"
using assms by(auto simp: freshAbs_vsubstAbs)

lemma freshAbs_substAbs_E2:
assumes "goodAbs A" and "good Y"
and "freshAbs zs z (A $[Y / y]_ys)"
shows "freshAbs ys y A \<or> fresh zs z Y"
using assms by(simp add: freshAbs_substAbs)

lemma freshAbs_vsubstAbs_E2:
assumes "goodAbs A"
and "freshAbs zs z (A $[y1 // y]_ys)"
shows "freshAbs ys y A \<or> zs \<noteq> ys \<or> z \<noteq> y1"
using assms by(simp add: freshAbs_vsubstAbs)

corollary psubstAbs_cong[fundef_cong]:
assumes "goodAbs A" and "goodEnv rho" and "goodEnv rho'"
and "\<And> ys y. freshAbs ys y A \<or> rho ys y = rho' ys y"
shows "(A $[rho]) = (A $[rho'])"
using assms psubstAll_cong[of "Par [] [] [] [rho,rho']"]
unfolding goodPar_def by simp

lemma freshAbs_psubstAbs_updEnv:
assumes "good X" and "goodAbs A" and "goodEnv rho"
and "freshAbs xs x A"
shows "(A $[rho [x \<leftarrow> X]_xs]) = (A $[rho])"
using assms by (intro psubstAbs_cong) auto

corollary freshEnv_psubstAbs_ident[simp]:
fixes A :: "('index,'bindex,'varSort,'var,'opSym)abs"
assumes "goodAbs A" and "goodEnv rho"
and "\<And> zs z. freshEnv zs z rho \<or> freshAbs zs z A"
shows "(A $[rho]) = A"
using assms psubstAll_ident[of "Par [] [] [] [rho]"]
unfolding goodPar_def by simp

lemma freshAbs_substAbs_ident[simp]:
assumes "good X" and "goodAbs A" and "freshAbs xs x A"
shows "(A $[X / x]_xs) = A"
by (simp add: assms freshAbs_psubstAbs_updEnv substAbs_def)

corollary substAbs_Abs[simp]:
assumes "good X" and "good Y"
shows "((Abs xs x X) $[Y / x]_xs) = Abs xs x X"
using assms by simp

lemma freshAbs_vsubstAbs_ident[simp]:
assumes "goodAbs A" and "freshAbs xs x A"
shows "(A $[x1 // x]_xs) = A"
using assms unfolding vsubstAbs_def by(auto simp: freshAbs_substAbs_ident)

lemma swapAbs_psubstAbs:
assumes "goodAbs A" and "goodEnv rho"
shows "((A $[rho]) $[z1 \<and> z2]_zs) = ((A $[z1 \<and> z2]_zs) $[rho &[z1 \<and> z2]_zs])"
using assms swapAll_psubstAll[of "Par [z1,z2] [] [] [rho]"]
unfolding goodPar_def by auto

lemma swapAbs_substAbs:
assumes "goodAbs A" and "good Y"
shows "((A $[Y / y]_ys) $[z1 \<and> z2]_zs) =
       ((A $[z1 \<and> z2]_zs) $[(Y #[z1 \<and> z2]_zs) / (y @ys[z1 \<and> z2]_zs)]_ys)"
proof-
  have 1: "(idEnv [(y @ys[z1 \<and> z2]_zs) \<leftarrow> (Y #[z1 \<and> z2]_zs)]_ys) =
           ((idEnv [y \<leftarrow> Y]_ys) &[z1 \<and> z2]_zs)"
  by(simp add: swapEnv_updEnv)
  show ?thesis
  unfolding substAbs_def 1 using assms by (intro swapAbs_psubstAbs) auto
qed

lemma swapAbs_vsubstAbs:
assumes "goodAbs A"
shows "((A $[y1 // y]_ys) $[z1 \<and> z2]_zs) =
       ((A $[z1 \<and> z2]_zs) $[(y1 @ys[z1 \<and> z2]_zs) // (y @ys[z1 \<and> z2]_zs)]_ys)"
using assms unfolding vsubstAbs_def
by(simp add: swapAbs_substAbs)

lemma psubstAbs_compose:
assumes "goodAbs A" and "goodEnv rho" and "goodEnv rho'"
shows "((A $[rho]) $[rho']) = (A $[(rho &[rho'])])"
using assms psubstAll_compose[of "Par [] [] [] [rho, rho']"]
unfolding goodPar_def by auto

lemma psubstAbs_substAbs_compose:
assumes "goodAbs A" and "good Y" and "goodEnv rho"
shows "((A $[Y / y]_ys) $[rho]) = (A $[(rho [y \<leftarrow> (Y #[rho])]_ys)])"
by (simp add: assms psubstAbs_compose psubstEnv_updEnv_idEnv substAbs_def)

lemma psubstAbs_vsubstAbs_compose:
assumes "goodAbs A" and "goodEnv rho"
shows "((A $[y1 // y]_ys) $[rho]) = (A $[(rho [y \<leftarrow> ((Var ys y1) #[rho])]_ys)])"
using assms unfolding vsubstAbs_def by(simp add: psubstAbs_substAbs_compose)

lemma substAbs_psubstAbs_compose:
assumes "goodAbs A" and "good Y" and "goodEnv rho"
shows "((A $[rho]) $[Y / y]_ys) = (A $[(rho &[Y / y]_ys)])"
unfolding substAbs_def substEnv_def using assms by(simp add: psubstAbs_compose)

lemma psubstAbs_substAbs_compose_freshEnv:
assumes "goodAbs A" and "goodEnv rho" and "good Y"
assumes "freshEnv ys y rho"
shows "((A $[Y / y]_ys) $[rho]) = ((A $[rho]) $[(Y #[rho]) / y]_ys)"
using assms by (simp add: substAbs_psubstAbs_compose psubstAbs_substAbs_compose)

lemma vsubstAbs_psubstAbs_compose:
assumes "goodAbs A" and "goodEnv rho"
shows "((A $[rho]) $[y1 // y]_ys) = (A $[(rho &[y1 // y]_ys)])"
unfolding vsubstAbs_def vsubstEnv_def using assms
by(simp add: substAbs_psubstAbs_compose)

lemma substAbs_compose1:
assumes "goodAbs A" and "good Y1" and "good Y2"
shows "((A $[Y1 / y]_ys) $[Y2 / y]_ys) = (A $[(Y1 #[Y2 / y]_ys) / y]_ys)"
by (metis assms idEnv_preserves_good psubstAbs_substAbs_compose substAbs_def 
  subst_psubst_idEnv updEnv_overwrite updEnv_preserves_good)

lemma substAbs_vsubstAbs_compose1:
assumes "goodAbs A" and "good Y" and "y \<noteq> y1"
shows "((A $[y1 // y]_ys) $[Y / y]_ys) = (A $[y1 // y]_ys)"
using assms unfolding vsubstAbs_def by(simp add: substAbs_compose1)

lemma vsubstAbs_substAbs_compose1:
assumes "goodAbs A" and "good Y"
shows "((A $[Y / y]_ys) $[y1 // y]_ys) = (A $[(Y #[y1 // y]_ys) / y]_ys)"
using assms unfolding vsubstAbs_def vsubst_def by(simp add: substAbs_compose1)

lemma vsubstAbs_compose1:
assumes "goodAbs A"
shows "((A $[y1 // y]_ys) $[y2 // y]_ys) = (A $[(y1 @ys[y2 / y]_ys) // y]_ys)"
using assms unfolding vsubstAbs_def  
by(cases "y = y1") (auto simp: substAbs_compose1)

lemma substAbs_compose2:
assumes  "goodAbs A" and "good Y" and "good Z"
and "ys \<noteq> zs \<or> y \<noteq> z" and fresh: "fresh ys y Z"
shows "((A $[Y / y]_ys) $[Z / z]_zs) = ((A $[Z / z]_zs) $[(Y #[Z / z]_zs) / y]_ys)"
by (metis assms fresh freshEnv_idEnv idEnv_preserves_good 
psubstAbs_substAbs_compose_freshEnv substAbs_def 
substEnv_idEnv substEnv_preserves_freshEnv_aux 
 subst_psubst_idEnv updEnv_preserves_good) 

lemma substAbs_vsubstAbs_compose2:
assumes "goodAbs A" and "good Z"
and "ys \<noteq> zs \<or> y \<noteq> z" and fresh: "fresh ys y Z"
shows "((A $[y1 // y]_ys) $[Z / z]_zs) = ((A $[Z / z]_zs) $[((Var ys y1) #[Z / z]_zs) / y]_ys)"
using assms unfolding vsubstAbs_def by(simp add: substAbs_compose2)

lemma vsubstAbs_substAbs_compose2:
assumes  "goodAbs A" and "good Y"
and "ys \<noteq> zs \<or> y \<notin> {z,z1}"
shows "((A $[Y / y]_ys) $[z1 // z]_zs) = ((A $[z1 // z]_zs) $[(Y #[z1 // z]_zs) / y]_ys)"
using assms unfolding vsubstAbs_def vsubst_def by(simp add: substAbs_compose2)

lemma vsubstAbs_compose2:
assumes  "goodAbs A"
and "ys \<noteq> zs \<or> y \<notin> {z,z1}"
shows "((A $[y1 // y]_ys) $[z1 // z]_zs) =
       ((A $[z1 // z]_zs) $[(y1 @ys[z1 / z]_zs) // y]_ys)"
unfolding vsubstAbs_def
by (smt Var_preserves_good assms fresh_Var_simp insertCI 
   substAbs_compose2 vsubst_Var_simp vsubst_def) 

text{* Properties specific to variable-for-variable substitution: *}

corollary vsubstAbs_ident[simp]:
assumes "goodAbs A"
shows "(A $[z // z]_zs) = A"
using assms vsubstAll_ident[of "Par [z] [] [] []" _ _ A]
unfolding goodPar_def by simp

corollary substAbs_ident[simp]:
assumes "goodAbs A"
shows "(A $[(Var zs z) / z]_zs) = A"
using assms vsubstAbs_ident unfolding vsubstAbs_def by auto

corollary vsubstAbs_eq_swapAbs:
assumes "goodAbs A" and "freshAbs ys y1 A"
shows "(A $[y1 // y2]_ys) = (A $[y1 \<and> y2]_ys)"
using assms vsubstAll_swapAll[of "Par [y1, y2] [] [] []" _ _ A]
unfolding goodPar_def by simp

corollary skelAbs_vsubstAbs:
assumes "goodAbs A"
shows "skelAbs (A $[y1 // y2]_ys) = skelAbs A"
using assms skelAll_vsubstAll[of "Par [y1, y2] [] [] []" _ _ A]
unfolding goodPar_def by simp

lemma substAbs_vsubstAbs_trans:
assumes  "goodAbs A" and "good Y" and "freshAbs ys y1 A"
shows "((A $[y1 // y]_ys) $[Y / y1]_ys) = (A $[Y / y]_ys)"
using assms unfolding substAbs_def vsubstAbs_def 
by (cases "y1 = y") (auto simp: freshAbs_psubstAbs_updEnv psubstAbs_compose 
  psubstEnv_updEnv_idEnv updEnv_commute)  

lemma vsubstAbs_trans:
assumes  "goodAbs A" and "freshAbs ys y1 A"
shows "((A $[y1 // y]_ys) $[y2 // y1]_ys) = (A $[y2 // y]_ys)"
unfolding vsubstAbs_def[of _ y2 y1] vsubstAbs_def[of _ y2 y]
using assms by(simp add: substAbs_vsubstAbs_trans)

lemmas good_psubstAll_freshAll_otherSimps =
psubst_idEnv psubstEnv_idEnv_id psubstAbs_idEnv
freshEnv_psubst_ident freshEnv_psubstAbs_ident

lemmas good_substAll_freshAll_otherSimps =
fresh_fresh_subst fresh_subst_ident fresh_substEnv_updEnv subst_ident
fresh_freshAbs_substAbs freshAbs_substAbs_ident substAbs_ident

lemmas good_vsubstAll_freshAll_otherSimps =
diff_fresh_vsubst fresh_vsubst_ident fresh_vsubstEnv_updEnv vsubst_ident
diff_freshAbs_vsubstAbs freshAbs_vsubstAbs_ident vsubstAbs_ident

lemmas good_allOpers_otherSimps =
good_swapAll_freshAll_otherSimps
good_psubstAll_freshAll_otherSimps
good_substAll_freshAll_otherSimps
good_vsubstAll_freshAll_otherSimps

lemmas good_item_simps =
param_simps
all_preserve_good
good_freeCons
good_allOpers_simps
good_allOpers_otherSimps

end  (* context FixVars *)

end
