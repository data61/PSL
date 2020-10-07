section {* Availability of Fresh Variables and Alpha-Equivalence *}

theory QuasiTerms_PickFresh_Alpha
imports QuasiTerms_Swap_Fresh 

begin

text{* Here we define good quasi-terms and alpha-equivalence on quasi-terms,
and prove relevant properties
such as the ability to pick fresh variables for good
quasi-terms and the fact that alpha is indeed an equivalence
and is compatible with all the operators.

We do most of the work on freshness and alpha-equivalence
unsortedly, for raw quasi-terms.  (And we do it in such a way that
it then applies immediately to sorted quasi-terms.)
We do need sortedness of variables (as well as a cardinality
assumption), however, for alpha-equivalence to have the desired properties.
Therefore we work in a locale.   *}

subsection {* The FixVars locale *}

definition var_infinite where
"var_infinite (_ :: 'var) ==
 infinite (UNIV :: 'var set)"

definition var_regular where
"var_regular (_ :: 'var) ==
 regular |UNIV :: 'var set|"

definition varSort_lt_var where
"varSort_lt_var (_ :: 'varSort) (_ :: 'var) ==
 |UNIV :: 'varSort set| <o |UNIV :: 'var set|"

locale FixVars =
  fixes dummyV :: 'var and dummyVS :: 'varSort
  assumes var_infinite: "var_infinite (undefined :: 'var)"
  and var_regular: "var_regular (undefined :: 'var)"
  and varSort_lt_var: "varSort_lt_var (undefined :: 'varSort) (undefined :: 'var)"

(*********************************************)
context FixVars
begin

lemma varSort_lt_var_INNER:
"|UNIV :: 'varSort set| <o |UNIV :: 'var set|"
using varSort_lt_var
unfolding varSort_lt_var_def by simp

lemma varSort_le_Var:
"|UNIV :: 'varSort set| \<le>o |UNIV :: 'var set|"
using varSort_lt_var_INNER ordLess_imp_ordLeq by auto

theorem var_infinite_INNER: "infinite (UNIV :: 'var set)"
using var_infinite unfolding var_infinite_def by simp

theorem var_regular_INNER: "regular |UNIV :: 'var set|"
using var_regular unfolding var_regular_def by simp

theorem infinite_var_regular_INNER:
"infinite (UNIV :: 'var set) \<and> regular |UNIV :: 'var set|"
by (simp add: var_infinite_INNER var_regular_INNER)

(* Below and elsewhere: We want both full generality and usefulness in one single 
theorem, and therefore we include as a disjunction the general condition w.r.t. the variable cardinality
and the stronger (most often needed) one of finiteness.  This way, we need not
invoke variable infiniteness each time we want to use the finiteness. *)

theorem finite_ordLess_var:
"( |S| <o |UNIV :: 'var set| \<or> finite S) = ( |S| <o |UNIV :: 'var set| )"
by (auto simp add: var_infinite_INNER finite_ordLess_infinite2)

subsection {* Good quasi-terms  *}

text {* Essentially, good quasi-term items
   will be those with meaningful binders and
   not too many variables.  Good quasi-terms are a concept intermediate
   between (raw) quasi-terms and sorted quasi-terms.  This concept was chosen to be strong
   enough to facilitate proofs of most of the desired properties of alpha-equivalence, avoiding,
   {\em for most of the hard part of the work},
   the overhead of sortedness.  Since we later prove that quasi-terms
   are good,
   all the results are then immediately transported to a sorted setting.    *}

function
qGood :: "('index,'bindex,'varSort,'var,'opSym)qTerm \<Rightarrow> bool"
and
qGoodAbs :: "('index,'bindex,'varSort,'var,'opSym)qAbs \<Rightarrow> bool"
where
"qGood (qVar xs x) = True"
|
"qGood (qOp delta inp binp) =
 (liftAll qGood inp \<and> liftAll qGoodAbs binp \<and>
  |{i. inp i \<noteq> None}| <o |UNIV :: 'var set| \<and>
  |{i. binp i \<noteq> None}| <o |UNIV :: 'var set| )"
|
"qGoodAbs (qAbs xs x X) = qGood X"
by (pat_completeness, auto)
termination
apply(relation qTermLess)
apply(simp_all add: qTermLess_wf)
by(auto simp add: qTermLess_def)

fun qGoodItem :: "('index,'bindex,'varSort,'var,'opSym)qTermItem \<Rightarrow> bool" where
"qGoodItem (Inl qX) = qGood qX"
|
"qGoodItem (Inr qA) = qGoodAbs qA"

lemma qSwapAll_preserves_qGoodAll1:
fixes X::"('index,'bindex,'varSort,'var,'opSym)qTerm" and
      A::"('index,'bindex,'varSort,'var,'opSym)qAbs" and zs x y
shows
"(qGood X \<longrightarrow> qGood (X #[[x \<and> y]]_zs)) \<and>
 (qGoodAbs A \<longrightarrow> qGoodAbs (A $[[x \<and> y]]_zs))"
apply(rule qTerm_induct[of _ _ X A])
apply(simp_all add: sw_def)
unfolding lift_def liftAll_def apply auto
apply(case_tac "inp i", auto)
apply(case_tac "binp i", auto)
proof-
  fix inp::"('index,('index,'bindex,'varSort,'var,'opSym)qTerm)input" and zs xs x y
  let ?K1 = "{i. \<exists>X. inp i = Some X}"
  let ?K2 = "{i. \<exists>X. (case inp i of None \<Rightarrow> None | Some X \<Rightarrow> Some (X #[[x \<and> y]]_zs))
                     = Some X}"
  assume "|?K1| <o |UNIV :: 'var set|"
  moreover have "?K1 = ?K2" by(auto, case_tac "inp x", auto)
  ultimately show "|?K2| <o |UNIV :: 'var set|" by simp
next
  fix binp::"('bindex,('index,'bindex,'varSort,'var,'opSym)qAbs)input" and zs xs x y
  let ?K1 = "{i. \<exists>A. binp i = Some A}"
  let ?K2 = "{i. \<exists>A. (case binp i of None \<Rightarrow> None | Some A \<Rightarrow> Some (A $[[x \<and> y]]_zs))
                     = Some A}"
  assume "|?K1| <o |UNIV :: 'var set|"
  moreover have "?K1 = ?K2" by(auto, case_tac "binp x", auto)
  ultimately show "|?K2| <o |UNIV :: 'var set|" by simp
qed

corollary qSwap_preserves_qGood1:
"qGood X \<Longrightarrow> qGood (X #[[x \<and> y]]_zs)"
by(simp add: qSwapAll_preserves_qGoodAll1)

corollary qSwapAbs_preserves_qGoodAbs1:
"qGoodAbs A \<Longrightarrow> qGoodAbs (A $[[x \<and> y]]_zs)"
by(simp add: qSwapAll_preserves_qGoodAll1)

lemma qSwap_preserves_qGood2:
assumes "qGood(X #[[x \<and> y]]_zs)"
shows "qGood X" 
by (metis assms qSwap_involutive qSwap_preserves_qGood1)

lemma qSwapAbs_preserves_qGoodAbs2:
assumes "qGoodAbs(A $[[x \<and> y]]_zs)"
shows "qGoodAbs A" 
by (metis assms qSwapAbs_preserves_qGoodAbs1 qSwapAll_involutive)
 
lemma qSwap_preserves_qGood: "(qGood (X #[[x \<and> y]]_zs)) = (qGood X)"
using qSwap_preserves_qGood1 qSwap_preserves_qGood2 by blast

lemma qSwapAbs_preserves_qGoodAbs:
"(qGoodAbs (A $[[x \<and> y]]_zs)) = (qGoodAbs A)"
using qSwapAbs_preserves_qGoodAbs1 qSwapAbs_preserves_qGoodAbs2 by blast

lemma qSwap_twice_preserves_qGood:
"(qGood ((X #[[x \<and> y]]_zs) #[[x' \<and> y']]_zs')) = (qGood X)"
by (simp add: qSwap_preserves_qGood)

lemma qSwapped_preserves_qGood:
"(X,Y) \<in> qSwapped \<Longrightarrow> qGood Y = qGood X"
apply (induct rule: qSwapped.induct) 
using qSwap_preserves_qGood by auto

lemma qGood_qTerm_templateInduct[case_names Rel Var Op Abs]:
fixes X::"('index,'bindex,'varSort,'var,'opSym)qTerm"
and A::"('index,'bindex,'varSort,'var,'opSym)qAbs" and phi phiAbs rel
assumes
REL: "\<And> X Y. \<lbrakk>qGood X; (X,Y) \<in> rel\<rbrakk> \<Longrightarrow> qGood Y \<and> qSkel Y = qSkel X" and
Var: "\<And> xs x. phi (qVar xs x)" and
Op: "\<And> delta inp binp. \<lbrakk>|{i. inp i \<noteq> None}| <o |UNIV :: 'var set|;
                        |{i. binp i \<noteq> None}| <o |UNIV :: 'var set|;
                        liftAll (\<lambda>X. qGood X \<and> phi X) inp;
                        liftAll (\<lambda>A. qGoodAbs A \<and> phiAbs A) binp\<rbrakk>
                   \<Longrightarrow> phi (qOp delta inp binp)" and
Abs: "\<And> xs x X. \<lbrakk>qGood X; \<And> Y. (X,Y) \<in> rel \<Longrightarrow> phi Y\<rbrakk>
                 \<Longrightarrow> phiAbs (qAbs xs x X)"
shows
"(qGood X \<longrightarrow> phi X) \<and> (qGoodAbs A \<longrightarrow> phiAbs A)"
apply(induct rule: qTerm_templateInduct[of "{(X,Y). qGood X \<and> (X,Y) \<in> rel}"]) 
using assms by (simp_all add: liftAll_def)

lemma qGood_qTerm_rawInduct[case_names Var Op Abs]:
fixes X :: "('index,'bindex,'varSort,'var,'opSym)qTerm"
and A::"('index,'bindex,'varSort,'var,'opSym)qAbs" and phi phiAbs
assumes
Var: "\<And> xs x. phi (qVar xs x)" and
Op: "\<And> delta inp binp. \<lbrakk>|{i. inp i \<noteq> None}| <o |UNIV :: 'var set|;
                        |{i. binp i \<noteq> None}| <o |UNIV :: 'var set|;
                        liftAll (\<lambda> X. qGood X \<and> phi X) inp;
                        liftAll (\<lambda> A. qGoodAbs A \<and> phiAbs A) binp\<rbrakk>
                       \<Longrightarrow> phi (qOp delta inp binp)" and
Abs: "\<And> xs x X. \<lbrakk>qGood X; phi X\<rbrakk>  \<Longrightarrow> phiAbs (qAbs xs x X)"
shows "(qGood X \<longrightarrow> phi X) \<and> (qGoodAbs A \<longrightarrow> phiAbs A)"
apply(induct rule: qGood_qTerm_templateInduct [of Id])
by(simp_all add: assms)

lemma qGood_qTerm_induct[case_names Var Op Abs]:
fixes X :: "('index,'bindex,'varSort,'var,'opSym)qTerm"
and A::"('index,'bindex,'varSort,'var,'opSym)qAbs" and phi phiAbs
assumes
Var: "\<And> xs x. phi (qVar xs x)" and
Op: "\<And> delta inp binp. \<lbrakk>|{i. inp i \<noteq> None}| <o |UNIV :: 'var set|;
                        |{i. binp i \<noteq> None}| <o |UNIV :: 'var set|;
                        liftAll (\<lambda> X. qGood X \<and> phi X) inp;
                        liftAll (\<lambda> A. qGoodAbs A \<and> phiAbs A) binp\<rbrakk>
                       \<Longrightarrow> phi (qOp delta inp binp)" and
Abs: "\<And> xs x X. \<lbrakk>qGood X;
                 \<And> Y. qGood Y \<and> qSkel Y = qSkel X \<Longrightarrow> phi Y;
                 \<And> Y. (X,Y) \<in> qSwapped \<Longrightarrow> phi Y\<rbrakk>
                 \<Longrightarrow> phiAbs (qAbs xs x X)"
shows
"(qGood X \<longrightarrow> phi X) \<and> (qGoodAbs A \<longrightarrow> phiAbs A)"
apply(induct rule: qGood_qTerm_templateInduct
           [of "qSwapped \<union> {(X,Y). qGood Y \<and> qSkel Y = qSkel X}"])
using qSwapped_qSkel qSwapped_preserves_qGood
by(auto simp add: assms)

text "A form specialized for mutual induction
(this time, without the cardinality hypotheses):"

lemma qGood_qTerm_induct_mutual[case_names Var1 Var2 Op1 Op2 Abs1 Abs2]:
fixes X :: "('index,'bindex,'varSort,'var,'opSym)qTerm"
and A::"('index,'bindex,'varSort,'var,'opSym)qAbs" and phi1 phi2 phiAbs1 phiAbs2
assumes
Var1: "\<And> xs x. phi1 (qVar xs x)" and
Var2: "\<And> xs x. phi2 (qVar xs x)" and
Op1: "\<And> delta inp binp. \<lbrakk>liftAll (\<lambda> X. qGood X \<and> phi1 X) inp;
                         liftAll (\<lambda> A. qGoodAbs A \<and> phiAbs1 A) binp\<rbrakk>
                        \<Longrightarrow> phi1 (qOp delta inp binp)" and
Op2: "\<And> delta inp binp. \<lbrakk>liftAll (\<lambda> X. qGood X \<and> phi2 X) inp;
                         liftAll (\<lambda> A. qGoodAbs A \<and> phiAbs2 A) binp\<rbrakk>
                        \<Longrightarrow> phi2 (qOp delta inp binp)" and
Abs1: "\<And> xs x X. \<lbrakk>qGood X;
                  \<And> Y. qGood Y \<and> qSkel Y = qSkel X \<Longrightarrow> phi1 Y;
                  \<And> Y. qGood Y \<and> qSkel Y = qSkel X \<Longrightarrow> phi2 Y;
                  \<And> Y. (X,Y) \<in> qSwapped \<Longrightarrow> phi1 Y;
                  \<And> Y. (X,Y) \<in> qSwapped \<Longrightarrow> phi2 Y\<rbrakk>
                 \<Longrightarrow> phiAbs1 (qAbs xs x X)" and
Abs2: "\<And> xs x X. \<lbrakk>qGood X;
                  \<And> Y. qGood Y \<and> qSkel Y = qSkel X \<Longrightarrow> phi1 Y;
                  \<And> Y. qGood Y \<and> qSkel Y = qSkel X \<Longrightarrow> phi2 Y;
                  \<And> Y. (X,Y) \<in> qSwapped \<Longrightarrow> phi1 Y;
                  \<And> Y. (X,Y) \<in> qSwapped \<Longrightarrow> phi2 Y;
                  phiAbs1 (qAbs xs x X)\<rbrakk>
                 \<Longrightarrow> phiAbs2 (qAbs xs x X)"
shows
"(qGood X \<longrightarrow> (phi1 X \<and> phi2 X)) \<and>
 (qGoodAbs A \<longrightarrow> (phiAbs1 A \<and> phiAbs2 A))"
apply(induct rule: qGood_qTerm_induct[of _ _ X A])
by(auto simp add: assms liftAll_and)

subsection {* The ability to pick fresh variables *}

lemma single_non_qAFreshAll_ordLess_var:
fixes X :: "('index,'bindex,'varSort,'var,'opSym)qTerm"
and A::"('index,'bindex,'varSort,'var,'opSym)qAbs"
shows
"(qGood X \<longrightarrow> |{x. \<not> qAFresh xs x X}| <o |UNIV :: 'var set| ) \<and>
 (qGoodAbs A \<longrightarrow> |{x. \<not> qAFreshAbs xs x A}| <o |UNIV :: 'var set| )"
proof(induct rule: qGood_qTerm_rawInduct)
  case (Var xs x)
  then show ?case using infinite_var_regular_INNER by simp
next
  case (Op delta inp binp) 
  let ?Left = "{x. \<not> qAFresh xs x (qOp delta inp binp)}"
  obtain J where J_def: "J = {i. \<exists> X. inp i = Some X}" by blast
  let ?S = "\<Union> i \<in> J. {x. \<exists> X. inp i = Some X \<and> \<not> qAFresh xs x X}"
  {fix i
   obtain K where K_def: "K = {X. inp i = Some X}" by blast
   have "finite K" unfolding K_def by (cases "inp i", auto)
   hence "|K| <o |UNIV :: 'var set|" using var_infinite_INNER finite_ordLess_infinite2 by auto
   moreover have "\<forall> X \<in> K. |{x. \<not> qAFresh xs x X}| <o |UNIV :: 'var set|"
   unfolding K_def using Op unfolding liftAll_def by simp
   ultimately have "|\<Union> X \<in> K. {x. \<not> qAFresh xs x X}| <o |UNIV :: 'var set|"
   using var_regular_INNER by (simp add: regular_UNION)
   moreover
   have "{x. \<exists>X. inp i = Some X \<and> \<not> qAFresh xs x X} =
         (\<Union> X \<in> K. {x. \<not> qAFresh xs x X})" unfolding K_def by blast
   ultimately
   have "|{x. \<exists>X. inp i = Some X \<and> \<not> qAFresh xs x X}| <o |UNIV :: 'var set|"
   by simp
  }
  moreover have "|J| <o |UNIV :: 'var set|" unfolding J_def 
  using Op unfolding liftAll_def by simp
  ultimately
  have 1: "|?S| <o |UNIV :: 'var set|"
  using var_regular_INNER by (simp add: regular_UNION)
  (*  *)
  obtain Ja where Ja_def: "Ja = {i. \<exists> A. binp i = Some A}" by blast
  let ?Sa = "\<Union> i \<in> Ja. {x. \<exists> A. binp i = Some A \<and> \<not> qAFreshAbs xs x A}"
  {fix i
   obtain K where K_def: "K = {A. binp i = Some A}" by blast
   have "finite K" unfolding K_def by (cases "binp i", auto)
   hence "|K| <o |UNIV :: 'var set|" using var_infinite_INNER finite_ordLess_infinite2 by auto
   moreover have "\<forall> A \<in> K. |{x. \<not> qAFreshAbs xs x A}| <o |UNIV :: 'var set|"
   unfolding K_def using Op unfolding liftAll_def by simp
   ultimately have "|\<Union> A \<in> K. {x. \<not> qAFreshAbs xs x A}| <o |UNIV :: 'var set|"
   using var_regular_INNER by (simp add: regular_UNION)
   moreover
   have "{x. \<exists>A. binp i = Some A \<and> \<not> qAFreshAbs xs x A} =
         (\<Union> A \<in> K. {x. \<not> qAFreshAbs xs x A})" unfolding K_def by blast
   ultimately
   have "|{x. \<exists>A. binp i = Some A \<and> \<not> qAFreshAbs xs x A}| <o |UNIV :: 'var set|"
   by simp
  }
  moreover have "|Ja| <o |UNIV :: 'var set|" 
  unfolding Ja_def using Op unfolding liftAll_def by simp
  ultimately have "|?Sa| <o |UNIV :: 'var set|" 
  using var_regular_INNER by (simp add: regular_UNION)
  with 1 have "|?S Un ?Sa| <o |UNIV :: 'var set|"
  using var_infinite_INNER card_of_Un_ordLess_infinite by auto
  moreover have "?Left = ?S Un ?Sa"
  by (auto simp: J_def Ja_def liftAll_def ) 
  ultimately show ?case by simp
next
  case (Abs xsa x X) 
  let ?Left = "{xa. xs = xsa \<and> xa = x \<or> \<not> qAFresh xs xa X}"
  have "|{x}| <o |UNIV :: 'var set|" by (auto simp add: var_infinite_INNER)
  hence "|{x} \<union> {x. \<not> qAFresh xs x X}| <o |UNIV :: 'var set|"
  using Abs var_infinite_INNER card_of_Un_ordLess_infinite by blast
  moreover
  {have "?Left \<subseteq> {x} \<union> {x. \<not> qAFresh xs x X}" by blast
   hence "|?Left| \<le>o |{x} \<union> {x. \<not> qAFresh xs x X}|" using card_of_mono1 by auto
  }
  ultimately show ?case using ordLeq_ordLess_trans by auto 
qed 

corollary single_non_qAFresh_ordLess_var:
"qGood X \<Longrightarrow> |{x. \<not> qAFresh xs x X}| <o |UNIV :: 'var set|"
by(simp add: single_non_qAFreshAll_ordLess_var)

corollary single_non_qAFreshAbs_ordLess_var:
"qGoodAbs A \<Longrightarrow> |{x. \<not> qAFreshAbs xs x A}| <o |UNIV :: 'var set|"
by(simp add: single_non_qAFreshAll_ordLess_var)

lemma single_non_qFresh_ordLess_var:
assumes "qGood X"
shows "|{x. \<not> qFresh xs x X}| <o |UNIV :: 'var set|"
using qAFresh_imp_qFresh card_of_mono1 single_non_qAFresh_ordLess_var 
ordLeq_ordLess_trans by (metis Collect_mono assms)

lemma single_non_qFreshAbs_ordLess_var:
assumes "qGoodAbs A"
shows "|{x. \<not> qFreshAbs xs x A}| <o |UNIV :: 'var set|"
using qAFreshAll_imp_qFreshAll card_of_mono1 single_non_qAFreshAbs_ordLess_var
ordLeq_ordLess_trans by (metis Collect_mono assms)

lemma non_qAFresh_ordLess_var:
assumes GOOD: "\<forall> X \<in> XS. qGood X" and Var: "|XS| <o |UNIV :: 'var set|"
shows "|{x| x X. X \<in> XS \<and> \<not> qAFresh xs x X}| <o |UNIV :: 'var set|"
proof-
  define K and F where "K \<equiv> {x| x X. X \<in> XS \<and> \<not> qAFresh xs x X}"  
  and "F \<equiv> (\<lambda> X. {x. X \<in> XS \<and> \<not> qAFresh xs x X})" 
  have "K = (\<Union> X \<in> XS. F X)" unfolding K_def F_def by auto
  moreover have "\<forall> X \<in> XS. |F X| <o |UNIV :: 'var set|"
  unfolding F_def using GOOD single_non_qAFresh_ordLess_var by auto
  ultimately have "|K| <o |UNIV :: 'var set|" using var_regular_INNER Var 
  by(auto simp add: regular_UNION)
  thus ?thesis unfolding K_def .
qed

lemma non_qAFresh_or_in_ordLess_var:
assumes Var: "|V| <o |UNIV :: 'var set|" and "|XS| <o |UNIV :: 'var set|" and "\<forall> X \<in> XS. qGood X"
shows "|{x| x X. (x \<in> V \<or> (X \<in> XS \<and> \<not> qAFresh xs x X))}| <o |UNIV :: 'var set|"
proof-
  define J and K where "J \<equiv> {x| x X. (x \<in> V \<or> (X \<in> XS \<and> \<not> qAFresh xs x X))}"  
  and "K \<equiv> {x| x X. X \<in> XS \<and> \<not> qAFresh xs x X}"  
  have "J \<subseteq> K \<union> V" unfolding J_def K_def by auto
  hence "|J| \<le>o |K \<union> V|" using card_of_mono1 by auto
  moreover
  {have "|K| <o |UNIV :: 'var set|" unfolding K_def using assms non_qAFresh_ordLess_var by auto
   hence "|K \<union> V| <o |UNIV :: 'var set|" using Var var_infinite_INNER card_of_Un_ordLess_infinite by auto
  }
  ultimately have "|J| <o |UNIV :: 'var set|" using ordLeq_ordLess_trans by blast
  thus ?thesis unfolding J_def .
qed

lemma obtain_set_qFresh_card_of:
assumes  "|V| <o |UNIV :: 'var set|" and "|XS| <o |UNIV :: 'var set|" and "\<forall> X \<in> XS. qGood X"
shows "\<exists> W. infinite W \<and> W Int V = {} \<and>
             (\<forall> x \<in> W. \<forall> X \<in> XS. qAFresh xs x X \<and> qFresh xs x X)"
proof-
  define J where "J \<equiv> {x| x X. (x \<in> V \<or> (X \<in> XS \<and> \<not> qAFresh xs x X))}" 
  let ?W = "UNIV - J"
  have "|J| <o |UNIV :: 'var set|"
  unfolding J_def using assms non_qAFresh_or_in_ordLess_var by auto
  hence  "infinite ?W" using var_infinite_INNER subset_ordLeq_diff_infinite[of _ J] by auto
  moreover
  have "?W \<inter> V = {} \<and> (\<forall> x \<in> ?W. \<forall> X \<in> XS. qAFresh xs x X \<and> qFresh xs x X)"
  unfolding J_def using qAFresh_imp_qFresh by fastforce
  ultimately show ?thesis by blast
qed

lemma obtain_set_qFresh:
assumes "finite V \<or> |V| <o |UNIV :: 'var set|" and "finite XS \<or> |XS| <o |UNIV :: 'var set|" and
        "\<forall> X \<in> XS. qGood X"
shows "\<exists> W. infinite W \<and> W Int V = {} \<and>
            (\<forall> x \<in> W. \<forall> X \<in> XS. qAFresh xs x X \<and> qFresh xs x X)"
using assms
by(fastforce simp add: var_infinite_INNER obtain_set_qFresh_card_of)

lemma obtain_qFresh_card_of:
assumes "|V| <o |UNIV :: 'var set|" and "|XS| <o |UNIV :: 'var set|" and "\<forall> X \<in> XS. qGood X"
shows "\<exists> x. x \<notin> V \<and> (\<forall> X \<in> XS. qAFresh xs x X \<and> qFresh xs x X)"
proof-
  obtain W where "infinite W" and
  *: "W \<inter> V = {} \<and> (\<forall> x \<in> W. \<forall> X \<in> XS. qAFresh xs x X \<and> qFresh xs x X)"
  using assms obtain_set_qFresh_card_of by blast
  then obtain x where "x \<in> W" using infinite_imp_nonempty by fastforce
  thus ?thesis using * by auto
qed

lemma obtain_qFresh:
assumes "finite V \<or> |V| <o |UNIV :: 'var set|" and "finite XS \<or> |XS| <o |UNIV :: 'var set|" and
        "\<forall> X \<in> XS. qGood X"
shows "\<exists> x. x \<notin> V \<and> (\<forall> X \<in> XS. qAFresh xs x X \<and> qFresh xs x X)"
using assms
by(fastforce simp add: var_infinite_INNER obtain_qFresh_card_of)

definition pickQFresh where
"pickQFresh xs V XS ==
 SOME x. x \<notin> V \<and> (\<forall> X \<in> XS. qAFresh xs x X \<and> qFresh xs x X)"

lemma pickQFresh_card_of:
assumes "|V| <o |UNIV :: 'var set|" and "|XS| <o |UNIV :: 'var set|" and "\<forall> X \<in> XS. qGood X"
shows "pickQFresh xs V XS \<notin> V \<and>
       (\<forall> X \<in> XS. qAFresh xs (pickQFresh xs V XS) X \<and> qFresh xs (pickQFresh xs V XS) X)"
unfolding pickQFresh_def apply(rule someI_ex)
using assms obtain_qFresh_card_of by blast

lemma pickQFresh:
assumes "finite V \<or> |V| <o |UNIV :: 'var set|" and "finite XS \<or> |XS| <o |UNIV :: 'var set|" and
        "\<forall> X \<in> XS. qGood X"
shows "pickQFresh xs V XS \<notin> V \<and>
       (\<forall> X \<in> XS. qAFresh xs (pickQFresh xs V XS) X \<and> qFresh xs (pickQFresh xs V XS) X)"
unfolding pickQFresh_def apply(rule someI_ex) 
using assms by(auto simp add: obtain_qFresh)

end (* context FixVars *)
(*****************************************)

subsection {* Alpha-equivalence *}

subsubsection {* Definition *}

definition aux_alpha_ignoreSecond ::
"('index,'bindex,'varSort,'var,'opSym)qTerm * ('index,'bindex,'varSort,'var,'opSym)qTerm +
 ('index,'bindex,'varSort,'var,'opSym)qAbs * ('index,'bindex,'varSort,'var,'opSym)qAbs
 \<Rightarrow>
 ('index,'bindex,'varSort,'var,'opSym)qTermItem"
where
"aux_alpha_ignoreSecond K ==
 case K of Inl(X,Y) \<Rightarrow> termIn X
          |Inr(A,B) \<Rightarrow> absIn A"

lemma aux_alpha_ignoreSecond_qTermLessQSwapped_wf:
"wf(inv_image qTermQSwappedLess aux_alpha_ignoreSecond)"
using qTermQSwappedLess_wf wf_inv_image by auto

(*  *)
function
alpha and alphaAbs
where
"alpha (qVar xs x) (qVar xs' x') \<longleftrightarrow> xs = xs' \<and> x = x'"
|
"alpha (qOp delta inp binp) (qOp delta' inp' binp') \<longleftrightarrow>
 delta = delta' \<and> sameDom inp inp' \<and> sameDom binp binp' \<and>
 liftAll2 alpha inp inp' \<and>
 liftAll2 alphaAbs binp binp'"
|
"alpha (qVar xs x) (qOp delta' inp' binp') \<longleftrightarrow> False"
|
"alpha (qOp delta inp binp) (qVar xs' x') \<longleftrightarrow> False"
|
"alphaAbs (qAbs xs x X) (qAbs xs' x' X') \<longleftrightarrow>
 xs = xs' \<and>
 (\<exists> y. y \<notin> {x,x'} \<and> qAFresh xs y X \<and> qAFresh xs' y X' \<and>
       alpha (X #[[y \<and> x]]_xs) (X' #[[y \<and> x']]_xs'))"
by(pat_completeness, auto)
termination
apply(relation "inv_image qTermQSwappedLess aux_alpha_ignoreSecond")
apply(simp add: aux_alpha_ignoreSecond_qTermLessQSwapped_wf)
by(auto simp add: qTermQSwappedLess_def qTermLess_modulo_def
   aux_alpha_ignoreSecond_def qSwap_qSwapped)

abbreviation alpha_abbrev (infix "#=" 50) where "X #= Y \<equiv> alpha X Y"
abbreviation alphaAbs_abbrev (infix "$=" 50) where "A $= B \<equiv> alphaAbs A B"

(*********************************************)
context FixVars
begin

subsubsection {* Simplification and elimination rules *}

lemma alpha_inp_None:
"qOp delta inp binp #= qOp delta' inp' binp' \<Longrightarrow>
 (inp i = None) = (inp' i = None)"
by(auto simp add: sameDom_def)

lemma alpha_binp_None:
"qOp delta inp binp #= qOp delta' inp' binp' \<Longrightarrow>
 (binp i = None) = (binp' i = None)"
by(auto simp add: sameDom_def)

lemma qVar_alpha_iff:
"qVar xs x #= X' \<longleftrightarrow> X' = qVar xs x"
by(cases X', auto)

lemma alpha_qVar_iff:
"X #= qVar xs' x' \<longleftrightarrow> X = qVar xs' x'"
by(cases X, auto)

lemma qOp_alpha_iff:
"qOp delta inp binp #= X' \<longleftrightarrow>
 (\<exists> inp' binp'.
    X' = qOp delta inp' binp' \<and> sameDom inp inp' \<and> sameDom binp binp' \<and>
    liftAll2 (\<lambda>Y Y'. Y #= Y') inp inp' \<and>
    liftAll2 (\<lambda>A A'. A $= A') binp binp')"
by(cases X') auto

lemma alpha_qOp_iff:
"X #= qOp delta' inp' binp' \<longleftrightarrow>
 (\<exists> inp binp. X = qOp delta' inp binp \<and> sameDom inp inp' \<and> sameDom binp binp' \<and>
    liftAll2 (\<lambda>Y Y'. Y #= Y') inp inp' \<and>
    liftAll2 (\<lambda>A A'. A $= A') binp binp')"
by(cases X) auto

lemma qAbs_alphaAbs_iff:
"qAbs xs x X $= A' \<longleftrightarrow>
 (\<exists> x' y X'. A' = qAbs xs x' X' \<and>
             y \<notin> {x,x'} \<and> qAFresh xs y X \<and> qAFresh xs y X' \<and>
             (X #[[y \<and> x]]_xs) #= (X' #[[y \<and> x']]_xs))"
by(cases A') auto

lemma alphaAbs_qAbs_iff:
"A $= qAbs xs' x' X' \<longleftrightarrow>
 (\<exists> x y X. A = qAbs xs' x X \<and>
            y \<notin> {x,x'} \<and> qAFresh xs' y X \<and> qAFresh xs' y X' \<and>
            (X #[[y \<and> x]]_xs') #= (X' #[[y \<and> x']]_xs'))"
by(cases A) auto

subsubsection {* Basic properties *}

text{*  In a nutshell: ``alpha" is included in the kernel of ``qSkel", is
an equivalence on good quasi-terms, preserves goodness,
and all operators and relations (except ``qAFresh") preserve alpha. *}

lemma alphaAll_qSkelAll:
fixes X::"('index,'bindex,'varSort,'var,'opSym)qTerm" and
      A::"('index,'bindex,'varSort,'var,'opSym)qAbs"
shows
"(\<forall> X'. X #= X' \<longrightarrow> qSkel X = qSkel X') \<and>
 (\<forall> A'. A $= A' \<longrightarrow> qSkelAbs A = qSkelAbs A')"
proof(induction rule: qTerm_induct)
  case (Var xs x)
  then show ?case unfolding qVar_alpha_iff by simp
next
  case (Op delta inp binp)
  show ?case proof safe
    fix X'
    assume "qOp delta inp binp #= X'" 
    then obtain inp' binp' where X'eq: "X' = qOp delta inp' binp'" and
       1: "sameDom inp inp' \<and> sameDom binp binp'" and
       2: "liftAll2 (\<lambda> Y Y'. Y #= Y') inp inp' \<and>
           liftAll2 (\<lambda> A A'. A $= A') binp binp'"
    unfolding qOp_alpha_iff by auto
    from Op.IH 1 2
    show "qSkel (qOp delta inp binp) = qSkel X'"     
    by (simp add: X'eq fun_eq_iff option.case_eq_if
        lift_def liftAll_def sameDom_def liftAll2_def)  
  qed
next
  case (Abs xs x X)
  show ?case
  proof safe
    fix A' assume "qAbs xs x X $= A'" 
    then obtain X' x' y where A'eq: "A' = qAbs xs x' X'" and
    *: "(X #[[y \<and> x]]_xs) #= (X' #[[y \<and> x']]_xs)" unfolding qAbs_alphaAbs_iff by auto
    moreover have "(X, X #[[y \<and> x]]_xs) \<in> qSwapped" using qSwap_qSwapped by fastforce
    ultimately have "qSkel(X #[[y \<and> x]]_xs) = qSkel(X' #[[y \<and> x']]_xs)" 
    using Abs.IH by blast
    hence "qSkel X = qSkel X'" by(auto simp add: qSkel_qSwap)
    thus "qSkelAbs (qAbs xs x X) = qSkelAbs A'" unfolding A'eq by simp
  qed
qed

corollary alpha_qSkel:
fixes X X' :: "('index,'bindex,'varSort,'var,'opSym)qTerm"
shows "X #= X' \<Longrightarrow> qSkel X = qSkel X'"
by(simp add: alphaAll_qSkelAll)

text{* Symmetry of alpha is a property that holds for arbitrary 
(not necessarily good) quasi-terms. *}

lemma alphaAll_sym:
fixes X::"('index,'bindex,'varSort,'var,'opSym)qTerm" and
      A::"('index,'bindex,'varSort,'var,'opSym)qAbs"
shows
"(\<forall> X'. X #= X' \<longrightarrow> X' #= X) \<and> (\<forall> A'. A $= A' \<longrightarrow> A' $= A)"
proof(induction rule: qTerm_induct)
  case (Var xs x)
  then show ?case unfolding qVar_alpha_iff by simp
next
  case (Op delta inp binp)
  show ?case proof safe
    fix X' assume "qOp delta inp binp #= X'" 
    then obtain inp' binp' where X': "X' = qOp delta inp' binp'" and
    1: "sameDom inp inp' \<and> sameDom binp binp'"
    and 2: "liftAll2 (\<lambda>Y Y'. Y #= Y') inp inp' \<and>
          liftAll2 (\<lambda>A A'. A $= A') binp binp'"
    unfolding qOp_alpha_iff by auto
    thus "X' #= qOp delta inp binp"
    unfolding X' using Op.IH 1 2
    by (auto simp add: fun_eq_iff option.case_eq_if
        lift_def liftAll_def sameDom_def liftAll2_def)
  qed
next
  case (Abs xs x X)
  show ?case proof safe 
    fix A' assume "qAbs xs x X $= A'"
    then obtain x' y X' where
    1: "A' = qAbs xs x' X' \<and> y \<notin> {x, x'} \<and> qAFresh xs y X \<and> qAFresh xs y X'" and
    "(X #[[y \<and> x]]_xs) #= (X' #[[y \<and> x']]_xs)"
    unfolding qAbs_alphaAbs_iff by auto
    moreover have "(X, X #[[y \<and> x]]_xs) \<in> qSwapped" by (simp add: qSwap_qSwapped)
    ultimately have "(X' #[[y \<and> x']]_xs) #= (X #[[y \<and> x]]_xs)" using Abs.IH by simp
    thus "A' $= qAbs xs x X" using 1 by auto
  qed
qed 

corollary alpha_sym:
fixes X X' :: "('index,'bindex,'varSort,'var,'opSym)qTerm"
shows "X #= X' \<Longrightarrow> X' #= X"
by(simp add: alphaAll_sym)

corollary alphaAbs_sym:
fixes A A' ::"('index,'bindex,'varSort,'var,'opSym)qAbs"
shows "A $= A' \<Longrightarrow> A' $= A"
by(simp add: alphaAll_sym)

text{* Reflexivity does not hold for arbitrary quasi-terms, but onl;y for good 
ones. Indeed, the proof requires picking a fresh variable,
   guaranteed to be possible only if the quasi-term is good. *}

lemma alphaAll_refl:
fixes X::"('index,'bindex,'varSort,'var,'opSym)qTerm" and
      A::"('index,'bindex,'varSort,'var,'opSym)qAbs"
shows
"(qGood X \<longrightarrow> X #= X) \<and> (qGoodAbs A \<longrightarrow> A $= A)"
apply(rule qGood_qTerm_induct, simp_all)
unfolding liftAll_def sameDom_def liftAll2_def apply auto
proof-
  fix xs x X
  assume "qGood X" and
        IH: "\<And>Y. (X,Y) \<in> qSwapped \<Longrightarrow> Y #= Y"
  then obtain y where 1: "y \<noteq> x \<and> qAFresh xs y X"
  using obtain_qFresh[of "{x}" "{X}"] by auto
  hence "(X, X #[[y \<and> x]]_xs) \<in> qSwapped" using qSwap_qSwapped by auto
  hence "(X #[[y \<and> x]]_xs) #= (X #[[y \<and> x]]_xs)" using IH by simp
  thus "\<exists>y. y \<noteq> x \<and> qAFresh xs y X \<and> (X #[[y \<and> x]]_xs) #= (X #[[y \<and> x]]_xs)"
  using 1 by blast
qed

corollary alpha_refl:
fixes X :: "('index,'bindex,'varSort,'var,'opSym)qTerm"
shows "qGood X \<Longrightarrow> X #= X"
by(simp add: alphaAll_refl)

corollary alphaAbs_refl:
fixes A ::"('index,'bindex,'varSort,'var,'opSym)qAbs"
shows "qGoodAbs A \<Longrightarrow> A $= A"
by(simp add: alphaAll_refl)

lemma alphaAll_preserves_qGoodAll1:
fixes X::"('index,'bindex,'varSort,'var,'opSym)qTerm" and
      A::"('index,'bindex,'varSort,'var,'opSym)qAbs"
shows
"(qGood X \<longrightarrow> (\<forall> X'. X #= X' \<longrightarrow> qGood X')) \<and>
 (qGoodAbs A \<longrightarrow> (\<forall> A'. A $= A' \<longrightarrow> qGoodAbs A'))"
apply(rule qTerm_induct, auto)
unfolding qVar_alpha_iff apply(auto)
proof-
  fix delta inp binp X'
  assume
  IH1: "liftAll (\<lambda>Y. qGood Y \<longrightarrow> (\<forall>Y'. Y #= Y' \<longrightarrow> qGood Y')) inp"
  and IH2: "liftAll (\<lambda>A. qGoodAbs A \<longrightarrow> (\<forall>A'. A $= A' \<longrightarrow> qGoodAbs A')) binp"
  and *: "liftAll qGood inp"  "liftAll qGoodAbs binp"
  and **: "|{i. \<exists>Y. inp i = Some Y}| <o |UNIV :: 'var set|"
          "|{i. \<exists>A. binp i = Some A}| <o |UNIV :: 'var set|"
  and "qOp delta inp binp #= X'"
  then obtain inp' binp' where
  X'eq: "X' = qOp delta inp' binp'" and
  2: "sameDom inp inp' \<and> sameDom binp binp'" and
  3: "liftAll2 (\<lambda>Y Y'. Y #= Y') inp inp' \<and>
      liftAll2 (\<lambda>A A'. A $= A') binp binp'"
  unfolding qOp_alpha_iff by auto
  show "qGood X'"
  unfolding X'eq apply simp unfolding liftAll_def apply auto
  proof-
    fix i Y' assume inp': "inp' i = Some Y'"
    then obtain Y where inp: "inp i = Some Y"
    using 2 unfolding sameDom_def by fastforce
    hence "Y #= Y'" using inp' 3 unfolding liftAll2_def by blast
    moreover have "qGood Y" using * inp unfolding liftAll_def by simp
    ultimately show "qGood Y'" using IH1 inp unfolding liftAll_def by blast
  next
    fix i A' assume binp': "binp' i = Some A'"
    then obtain A where binp: "binp i = Some A"
    using 2 unfolding sameDom_def by fastforce
    hence "A $= A'" using binp' 3 unfolding liftAll2_def by blast
    moreover have "qGoodAbs A" using * binp unfolding liftAll_def by simp
    ultimately show "qGoodAbs A'" using IH2 binp unfolding liftAll_def by blast
  next
    have "{i. \<exists>Y'. inp' i = Some Y'} = {i. \<exists>Y. inp i = Some Y}"
    using 2 unfolding sameDom_def by force
    thus "|{i. \<exists>Y'. inp' i = Some Y'}| <o |UNIV :: 'var set|" using ** by simp
  next
    have "{i. \<exists>A'. binp' i = Some A'} = {i. \<exists>A. binp i = Some A}"
    using 2 unfolding sameDom_def by force
    thus "|{i. \<exists>A'. binp' i = Some A'}| <o |UNIV :: 'var set|" using ** by simp
  qed
next
  fix xs x X A'
  assume IH: "\<And>Y. (X,Y) \<in> qSwapped \<Longrightarrow> qGood Y \<longrightarrow> (\<forall>X'. Y #= X' \<longrightarrow> qGood X')"
         and *: "qGood X" and "qAbs xs x X $= A'"
  then obtain x' y X' where "A' = qAbs xs x' X'" and
       1: "(X #[[y \<and> x]]_xs) #= (X' #[[y \<and> x']]_xs)"
  unfolding qAbs_alphaAbs_iff by auto
  thus "qGoodAbs A'"
  proof(auto)
    have "(X, X #[[y \<and> x]]_xs) \<in> qSwapped" by(auto simp add: qSwap_qSwapped)
    moreover have "qGood(X #[[y \<and> x]]_xs)" using * qSwap_preserves_qGood by auto
    ultimately have "qGood(X' #[[y \<and> x']]_xs)" using 1 IH by auto
    thus "qGood X'" using * qSwap_preserves_qGood by auto
  qed
qed

corollary alpha_preserves_qGood1:
"\<lbrakk>X #= X'; qGood X\<rbrakk> \<Longrightarrow> qGood X'"
using alphaAll_preserves_qGoodAll1 by blast

corollary alphaAbs_preserves_qGoodAbs1:
"\<lbrakk>A $= A'; qGoodAbs A\<rbrakk> \<Longrightarrow> qGoodAbs A'"
using alphaAll_preserves_qGoodAll1 by blast

lemma alpha_preserves_qGood2:
"\<lbrakk>X #= X'; qGood X'\<rbrakk> \<Longrightarrow> qGood X"
using alpha_sym alpha_preserves_qGood1 by blast

lemma alphaAbs_preserves_qGoodAbs2:
"\<lbrakk>A $= A'; qGoodAbs A'\<rbrakk> \<Longrightarrow> qGoodAbs A"
using alphaAbs_sym alphaAbs_preserves_qGoodAbs1 by blast

lemma alpha_preserves_qGood:
"X #= X' \<Longrightarrow> qGood X = qGood X'"
using alpha_preserves_qGood1 alpha_preserves_qGood2 by blast

lemma alphaAbs_preserves_qGoodAbs:
"A $= A' \<Longrightarrow> qGoodAbs A = qGoodAbs A'"
using alphaAbs_preserves_qGoodAbs1 alphaAbs_preserves_qGoodAbs2 by blast

lemma alpha_qSwap_preserves_qGood1:
assumes ALPHA: "(X #[[y \<and> x]]_zs) #= (X' #[[y' \<and> x']]_zs')" and
        GOOD: "qGood X"
shows "qGood X'"
proof-
  have "qGood(X #[[y \<and> x]]_zs)" using GOOD qSwap_preserves_qGood by auto
  hence "qGood (X' #[[y' \<and> x']]_zs')" using ALPHA alpha_preserves_qGood by auto
  thus "qGood X'" using qSwap_preserves_qGood by auto
qed

lemma alpha_qSwap_preserves_qGood2:
assumes ALPHA: "(X #[[y \<and> x]]_zs) #= (X' #[[y' \<and> x']]_zs')" and
        GOOD': "qGood X'"
shows "qGood X"
proof-
  have "qGood(X' #[[y' \<and> x']]_zs')" using GOOD' qSwap_preserves_qGood by auto
  hence "qGood (X #[[y \<and> x]]_zs)" using ALPHA alpha_preserves_qGood by auto
  thus "qGood X" using qSwap_preserves_qGood by auto
qed

lemma alphaAbs_qSwapAbs_preserves_qGoodAbs2:
assumes ALPHA: "(A $[[y \<and> x]]_zs) $= (A' $[[y' \<and> x']]_zs')" and
        GOOD': "qGoodAbs A'"
shows "qGoodAbs A"
proof-
  have "qGoodAbs(A' $[[y' \<and> x']]_zs')" using GOOD' qSwapAbs_preserves_qGoodAbs by auto
  hence "qGoodAbs (A $[[y \<and> x]]_zs)" using ALPHA alphaAbs_preserves_qGoodAbs by auto
  thus "qGoodAbs A" using qSwapAbs_preserves_qGoodAbs by auto
qed

lemma alpha_qSwap_preserves_qGood:
assumes ALPHA: "(X #[[y \<and> x]]_zs) #= (X' #[[y' \<and> x']]_zs')"
shows "qGood X = qGood X'"
using assms alpha_qSwap_preserves_qGood1
      alpha_qSwap_preserves_qGood2 by auto

lemma qSwapAll_preserves_alphaAll:
fixes X::"('index,'bindex,'varSort,'var,'opSym)qTerm" and
      A::"('index,'bindex,'varSort,'var,'opSym)qAbs" and z1 z2 zs
shows
"(qGood X \<longrightarrow> (\<forall> X' zs z1 z2. X #= X' \<longrightarrow>
                             (X #[[z1 \<and> z2]]_zs) #= (X' #[[z1 \<and> z2]]_zs))) \<and>
 (qGoodAbs A \<longrightarrow> (\<forall> A' zs z1 z2. A $= A' \<longrightarrow>
                                (A $[[z1 \<and> z2]]_zs) $= (A' $[[z1 \<and> z2]]_zs)))"
proof(induction rule: qGood_qTerm_induct)
  case (Var xs x)
  then show ?case unfolding qVar_alpha_iff by simp
next
  case (Op delta inp binp) 
  show ?case proof safe
    fix X' zs z1 z2
    assume "qOp delta inp binp #= X'" term X' term binp
    then obtain inp' binp' where X'eq: "X' = qOp delta inp' binp'" and
    1: "sameDom inp inp' \<and> sameDom binp binp'"
    and 2: "liftAll2 (\<lambda> Y Y'. Y #= Y') inp inp' \<and>
          liftAll2 (\<lambda> A A'. A $= A') binp binp'"
    unfolding qOp_alpha_iff by auto
    thus "((qOp delta inp binp) #[[z1 \<and> z2]]_zs) #= (X' #[[z1 \<and> z2]]_zs)"
    unfolding X'eq using Op.IH
    by (auto simp add: fun_eq_iff option.case_eq_if
       lift_def liftAll_def sameDom_def liftAll2_def)
  qed
next 
  case (Abs xs x X) 
  show ?case proof safe
    fix A' zs z1 z2 assume "qAbs xs x X $= A'"
    then obtain x' y X' where A': "A' = qAbs xs x' X'" and
    y_not: "y \<notin> {x, x'}" and y_fresh: "qAFresh xs y X \<and> qAFresh xs y X'" and
    alpha: "(X #[[y \<and> x]]_xs) #= (X' #[[y \<and> x']]_xs)"
    unfolding qAbs_alphaAbs_iff by auto
    hence goodX': "qGood X'" using `qGood X` alpha_qSwap_preserves_qGood by fastforce
    (* *)
    obtain u where u_notin: "u \<notin> {x,x',z1,z2,y}" and
                   u_freshXX': "qAFresh xs u X \<and> qAFresh xs u X'"
    using  `qGood X` goodX' obtain_qFresh[of "{x,x',z1,z2,y}" "{X,X'}"] by auto
    hence u_not: "u \<noteq> (x @xs[z1 \<and> z2]_zs) \<and> u \<noteq> (x' @xs[z1 \<and> z2]_zs)"
    unfolding sw_def using u_notin by auto
    have u_fresh: "qAFresh xs u (X #[[z1 \<and> z2]]_zs) \<and> qAFresh xs u (X' #[[z1 \<and> z2]]_zs)"
    using u_freshXX' u_notin by(auto simp add: qSwap_preserves_qAFresh_distinct)
    (*  *)
    have "((X #[[z1 \<and> z2]]_zs) #[[u \<and> (x @xs[z1 \<and> z2]_zs)]]_xs) =
          (((X #[[y \<and> x]]_xs) #[[u \<and> y]]_xs) #[[z1 \<and> z2]]_zs)"
    using y_fresh u_freshXX' u_notin by (simp add: qSwap_3commute)
    moreover
    {have 1: "(X, X #[[y \<and> x]]_xs) \<in> qSwapped" by(simp add: qSwap_qSwapped)
     hence "((X #[[y \<and> x]]_xs) #[[u \<and> y]]_xs) #= ((X' #[[y \<and> x']]_xs) #[[u \<and> y]]_xs)"
     using alpha Abs.IH by auto
     moreover have "(X, (X #[[y \<and> x]]_xs) #[[u \<and> y]]_xs) \<in> qSwapped"
     using 1 by(auto simp add: qSwapped.Swap)
     ultimately have "(((X #[[y \<and> x]]_xs) #[[u \<and> y]]_xs) #[[z1 \<and> z2]]_zs) #=
                      (((X' #[[y \<and> x']]_xs) #[[u \<and> y]]_xs) #[[z1 \<and> z2]]_zs)"
     using Abs.IH by auto
    }
    moreover
    have "(((X' #[[y \<and> x']]_xs) #[[u \<and> y]]_xs) #[[z1 \<and> z2]]_zs) =
          ((X' #[[z1 \<and> z2]]_zs) #[[u \<and> (x' @xs[z1 \<and> z2]_zs)]]_xs)"
    using y_fresh u_freshXX' u_notin by (auto simp add: qSwap_3commute)
    ultimately have "((X #[[z1 \<and> z2]]_zs) #[[u \<and> (x @xs[z1 \<and> z2]_zs)]]_xs) #=
                     ((X' #[[z1 \<and> z2]]_zs) #[[u \<and> (x' @xs[z1 \<and> z2]_zs)]]_xs)" by simp
    thus "((qAbs xs x X) $[[z1 \<and> z2]]_zs) $= (A' $[[z1 \<and> z2]]_zs)"
    unfolding A' using u_not u_fresh by auto
  qed
qed 

corollary qSwap_preserves_alpha:
assumes "qGood X \<or> qGood X'" and "X #= X'"
shows "(X #[[z1 \<and> z2]]_zs) #= (X' #[[z1 \<and> z2]]_zs)"
using assms alpha_preserves_qGood qSwapAll_preserves_alphaAll by blast

corollary qSwapAbs_preserves_alphaAbs:
assumes "qGoodAbs A \<or> qGoodAbs A'" and "A $= A'"
shows "(A $[[z1 \<and> z2]]_zs) $= (A' $[[z1 \<and> z2]]_zs)"
using assms alphaAbs_preserves_qGoodAbs qSwapAll_preserves_alphaAll by blast

lemma qSwap_twice_preserves_alpha:
assumes "qGood X \<or> qGood X'" and "X #= X'"
shows "((X #[[z1 \<and> z2]]_zs) #[[u1 \<and> u2]]_us) #= ((X' #[[z1 \<and> z2]]_zs) #[[u1 \<and> u2]]_us)"
  by (simp add: assms qSwap_preserves_alpha qSwap_preserves_qGood)

lemma alphaAll_trans:
fixes X::"('index,'bindex,'varSort,'var,'opSym)qTerm" and
      A::"('index,'bindex,'varSort,'var,'opSym)qAbs"
shows
"(qGood X \<longrightarrow> (\<forall> X' X''. X #= X' \<and> X' #= X'' \<longrightarrow> X #= X'')) \<and>
 (qGoodAbs A \<longrightarrow> (\<forall> A' A''. A $= A' \<and> A' $= A'' \<longrightarrow> A $= A''))"
proof(induction rule: qGood_qTerm_induct)
  case (Var xs x)
  then show ?case by (simp add: qVar_alpha_iff)
next
  case (Op delta inp binp) 
  show ?case proof safe
    fix X' X'' assume "qOp delta inp binp #= X'" and *: "X' #= X''"
    then obtain inp' binp' where
    1: "X' = qOp delta inp' binp'" and
    2: "sameDom inp inp' \<and> sameDom binp binp'" and
    3: "liftAll2 (\<lambda>Y Y'. Y #= Y') inp inp' \<and>
      liftAll2 (\<lambda>A A'. A $= A') binp binp'"
    unfolding qOp_alpha_iff by auto
    obtain inp'' binp'' where
    11: "X'' = qOp delta inp'' binp''" and
    22: "sameDom inp' inp'' \<and> sameDom binp' binp''" and
    33: "liftAll2 (\<lambda>Y' Y''. Y' #= Y'') inp' inp'' \<and>
         liftAll2 (\<lambda>A' A''. A' $= A'') binp' binp''"
    using * unfolding 1 unfolding qOp_alpha_iff by auto
    have "liftAll2 (#=) inp inp''" unfolding liftAll2_def proof safe
      fix i Y Y''
      assume inp: "inp i = Some Y" and inp'': "inp'' i = Some Y''"
      then obtain Y' where inp': "inp' i = Some Y'"
      using 2 unfolding sameDom_def by force
      hence "Y #= Y'" using inp 3 unfolding liftAll2_def by blast
      moreover have "Y' #= Y''" using inp' inp'' 33 unfolding liftAll2_def by blast
      ultimately show "Y #= Y''" using inp Op.IH unfolding liftAll_def by blast
    qed
    moreover have "liftAll2 ($=) binp binp''" unfolding liftAll2_def proof safe
      fix i A A''
      assume binp: "binp i = Some A" and binp'': "binp'' i = Some A''"
      then obtain A' where binp': "binp' i = Some A'"
      using 2 unfolding sameDom_def by force
      hence "A $= A'" using binp 3 unfolding liftAll2_def by blast
      moreover have "A' $= A''" using binp' binp'' 33 unfolding liftAll2_def by blast
      ultimately show "A $= A''" using binp Op.IH unfolding liftAll_def by blast
    qed
    ultimately show "qOp delta inp binp #= X''"
    by (simp add: 11 2 22 sameDom_trans[of inp inp'] sameDom_trans[of binp binp'])
  qed
next 
  case (Abs xs x X)
  show ?case proof safe  
    fix A' A''
    assume "qAbs xs x X $= A'" and *: "A' $= A''"
    then obtain x' y X' where A': "A' = qAbs xs x' X'" and y_not: "y \<notin> {x, x'}" and
    y_fresh: "qAFresh xs y X \<and> qAFresh xs y X'" and
    alpha: "(X #[[y \<and> x]]_xs) #= (X' #[[y \<and> x']]_xs)"
    unfolding qAbs_alphaAbs_iff by auto
    obtain x'' z X'' where A'': "A'' = qAbs xs x'' X''" and z_not: "z \<notin> {x', x''}" and
    z_fresh: "qAFresh xs z X' \<and> qAFresh xs z X''" and
    alpha': "(X' #[[z \<and> x']]_xs) #= (X'' #[[z \<and> x'']]_xs)"
    using * unfolding A' qAbs_alphaAbs_iff by auto
    have goodX': "qGood X'"
    using alpha `qGood X` alpha_qSwap_preserves_qGood by fastforce
    hence goodX'': "qGood X''"
    using alpha' alpha_qSwap_preserves_qGood by fastforce
    have good: "qGood((X #[[y \<and> x]]_xs)) \<and> qGood((X' #[[z \<and> x']]_xs))"
    using `qGood X` goodX' qSwap_preserves_qGood by auto
    (* *)   
    obtain u where u_not: "u \<notin> {x,x',x'',y,z}" and
             u_fresh: "qAFresh xs u X \<and> qAFresh xs u X' \<and> qAFresh xs u X''"
    using `qGood X` goodX' goodX''  
    using obtain_qFresh[of "{x,x',x'',y,z}" "{X, X', X''}"] by auto
    (*  *)
    {have "(X #[[u \<and> x]]_xs) = ((X #[[y \<and> x]]_xs) #[[u \<and> y]]_xs)"
     using u_fresh y_fresh by (auto simp add: qAFresh_qSwap_compose)
     moreover
     have "((X #[[y \<and> x]]_xs) #[[u \<and> y]]_xs) #= ((X' #[[y \<and> x']]_xs) #[[u \<and> y]]_xs)"
     using good alpha qSwap_preserves_alpha by fastforce
     moreover have "((X' #[[y \<and> x']]_xs) #[[u \<and> y]]_xs) = (X' #[[u \<and> x']]_xs)"
     using u_fresh y_fresh by (auto simp add: qAFresh_qSwap_compose)
     ultimately have "(X #[[u \<and> x]]_xs) #= (X' #[[u \<and> x']]_xs)" by simp
    }
    moreover
    {have "(X' #[[u \<and> x']]_xs) = ((X' #[[z \<and> x']]_xs) #[[u \<and> z]]_xs)"
     using u_fresh z_fresh by (auto simp add: qAFresh_qSwap_compose)
     moreover
     have "((X' #[[z \<and> x']]_xs) #[[u \<and> z]]_xs) #= ((X'' #[[z \<and> x'']]_xs) #[[u \<and> z]]_xs)"
     using good alpha' qSwap_preserves_alpha by fastforce
     moreover have "((X'' #[[z \<and> x'']]_xs) #[[u \<and> z]]_xs) = (X'' #[[u \<and> x'']]_xs)"
     using u_fresh z_fresh by (auto simp add: qAFresh_qSwap_compose)
     ultimately have "(X' #[[u \<and> x']]_xs) #= (X'' #[[u \<and> x'']]_xs)" by simp
    }
    moreover have "(X, X #[[u \<and> x]]_xs) \<in> qSwapped" by (simp add: qSwap_qSwapped)
    ultimately have "(X #[[u \<and> x]]_xs) #= (X'' #[[u \<and> x'']]_xs)"
    using Abs.IH by blast
    thus "qAbs xs x X $= A''"
    unfolding A'' using u_not u_fresh by auto
  qed
qed

corollary alpha_trans:
assumes "qGood X \<or> qGood X' \<or> qGood X''" "X #= X'"  "X' #= X''"
shows "X #= X''" 
by (meson alphaAll_trans alpha_preserves_qGood assms)

corollary alphaAbs_trans:
assumes "qGoodAbs A \<or> qGoodAbs A' \<or> qGoodAbs A''"
and "A $= A'"  "A' $= A''"
shows "A $= A''"
using assms alphaAbs_preserves_qGoodAbs alphaAll_trans by blast 

lemma alpha_trans_twice:
"\<lbrakk>qGood X \<or> qGood X' \<or> qGood X'' \<or> qGood X''';
  X #= X'; X' #= X''; X'' #= X'''\<rbrakk> \<Longrightarrow> X #= X'''"
using alpha_trans by blast

lemma alphaAbs_trans_twice:
"\<lbrakk>qGoodAbs A \<or> qGoodAbs A' \<or> qGoodAbs A'' \<or> qGoodAbs A''';
  A $= A'; A' $= A''; A'' $= A'''\<rbrakk> \<Longrightarrow> A $= A'''"
using alphaAbs_trans by blast

lemma qAbs_preserves_alpha:
assumes ALPHA: "X #= X'" and GOOD: "qGood X \<or> qGood X'"
shows "qAbs xs x X $= qAbs xs x X'"
proof-
  have "qGood X \<and> qGood X'" using GOOD ALPHA by(auto simp add: alpha_preserves_qGood)
  then obtain y where y_not: "y \<noteq> x" and
                      y_fresh: "qAFresh xs y X \<and> qAFresh xs y X'"
  using GOOD obtain_qFresh[of "{x}" "{X,X'}"] by auto
  hence "(X #[[y \<and> x]]_xs) #= (X' #[[y \<and> x]]_xs)"
  using ALPHA GOOD by(simp add: qSwap_preserves_alpha)
  thus ?thesis using y_not y_fresh by auto
qed

corollary qAbs_preserves_alpha2:
assumes ALPHA: "X #= X'" and GOOD: "qGoodAbs(qAbs xs x X) \<or> qGoodAbs (qAbs xs x X')"
shows "qAbs xs x X $= qAbs xs x X'"
using assms by (intro qAbs_preserves_alpha) auto

subsubsection {* Picking fresh representatives *}

lemma qAbs_alphaAbs_qSwap_qAFresh:
assumes GOOD: "qGood X" and FRESH: "qAFresh ys x' X"
shows "qAbs ys x X $= qAbs ys x' (X #[[x' \<and> x]]_ys)"
proof-
  obtain y where 1: "y \<notin> {x,x'}" and 2: "qAFresh ys y X"
  using GOOD obtain_qFresh[of "{x,x'}" "{X}"] by auto
  hence 3: "qAFresh ys y (X #[[x' \<and> x]]_ys)"
  by (auto simp add: qSwap_preserves_qAFresh_distinct)
  (*  *)
  have "(X #[[y \<and> x]]_ys) = ((X #[[x' \<and> x]]_ys) #[[y \<and> x']]_ys)"
  using FRESH 2 by (auto simp add: qAFresh_qSwap_compose)
  moreover have "qGood (X #[[y \<and> x]]_ys)"
  using 1 GOOD qSwap_preserves_qGood by auto
  ultimately have "(X #[[y \<and> x]]_ys) #= ((X #[[x' \<and> x]]_ys) #[[y \<and> x']]_ys)"
  using alpha_refl by simp
  (*  *)
  thus ?thesis using 1 2 3 assms by auto
qed

lemma qAbs_ex_qAFresh_rep:
assumes GOOD: "qGood X" and FRESH: "qAFresh xs x' X"
shows "\<exists> X'. qGood X' \<and> qAbs xs x X $= qAbs xs x' X'"
proof-
  have 1: "qGood (X #[[x' \<and> x]]_xs)" using assms qSwap_preserves_qGood by auto
  show ?thesis
  apply(rule exI[of _ "X #[[x' \<and> x]]_xs"])
  using assms 1 qAbs_alphaAbs_qSwap_qAFresh by fastforce
qed

subsection {* Properties of swapping and freshness modulo alpha  *}

lemma qFreshAll_imp_ex_qAFreshAll:
fixes X::"('index,'bindex,'varSort,'var,'opSym)qTerm" and
      A::"('index,'bindex,'varSort,'var,'opSym)qAbs" and zs fZs
assumes FIN: "finite V"
shows
"(qGood X \<longrightarrow>
  ((\<forall> z \<in> V. \<forall> zs \<in> fZs z. qFresh zs z X) \<longrightarrow>
   (\<exists> X'. X #= X' \<and> (\<forall> z \<in> V. \<forall> zs \<in> fZs z. qAFresh zs z X')))) \<and>
 (qGoodAbs A \<longrightarrow>
  ((\<forall> z \<in> V. \<forall> zs \<in> fZs z. qFreshAbs zs z A) \<longrightarrow>
   (\<exists> A'. A $= A' \<and> (\<forall> z \<in> V. \<forall> zs \<in> fZs z. qAFreshAbs zs z A'))))"
proof(induction rule: qGood_qTerm_induct)
  case (Var xs x)
  show ?case  
  by (metis alpha_qVar_iff qAFreshAll_simps(1) qFreshAll_simps(1))  
next
  case (Op delta inp binp)
  show ?case proof safe 
    assume *: "\<forall>z\<in>V. \<forall>zs\<in>fZs z. qFresh zs z (qOp delta inp binp)"
    define phi and phiAbs where  
    "phi \<equiv> (\<lambda>(Y::('index,'bindex,'varSort,'var,'opSym)qTerm) Y'.
            Y #= Y' \<and> (\<forall>z\<in>V. \<forall>zs\<in>fZs z. qAFresh zs z Y'))" and 
    "phiAbs \<equiv> (\<lambda>(A::('index,'bindex,'varSort,'var,'opSym)qAbs) A'.
               A $= A' \<and> (\<forall>z\<in>V. \<forall>zs\<in>fZs z. qAFreshAbs zs z A'))" 
    have ex_phi: "\<And> i Y. inp i = Some Y \<Longrightarrow> \<exists>Y'. phi Y Y'"
    unfolding phi_def using Op.IH * by (auto simp add: liftAll_def)
    have ex_phiAbs: "\<And> i A. binp i = Some A \<Longrightarrow> \<exists>A'. phiAbs A A'"
    unfolding phiAbs_def using Op.IH * by (auto simp add: liftAll_def)
    define inp' and binp' where  
    "inp' \<equiv> \<lambda> i. case inp i of Some Y \<Rightarrow> Some (SOME Y'. phi Y Y') |None \<Rightarrow> None" and  
    "binp' \<equiv> \<lambda> i. case binp i of Some A \<Rightarrow> Some (SOME A'. phiAbs A A') |None \<Rightarrow> None"
    show "\<exists>X'. qOp delta inp binp #= X' \<and> (\<forall>z\<in>V. \<forall>zs\<in>fZs z. qAFresh zs z X')"
    by (intro exI[of _ "qOp delta inp' binp'"])  
    (auto simp add: inp'_def binp'_def option.case_eq_if sameDom_def liftAll_def liftAll2_def,
    (meson ex_phi phi_def ex_phiAbs phiAbs_def some_eq_ex)+)
  qed
next 
  case (Abs xs x X)
  show ?case proof safe   
    assume *: "\<forall>z\<in>V. \<forall>zs\<in>fZs z. qFreshAbs zs z (qAbs xs x X)"
    obtain y where y_not_x: "y \<noteq> x" and y_not_V: "y \<notin> V"
    and y_afresh: "qAFresh xs y X"
    using FIN `qGood X` obtain_qFresh[of "V \<union> {x}" "{X}"] by auto
    hence y_fresh: "qFresh xs y X" using qAFresh_imp_qFresh by fastforce
    obtain Y where Y_def: "Y = (X #[[y \<and> x ]]_xs)" by blast
    have alphaXY: "qAbs xs x X $= qAbs xs y Y"
    using `qGood X` y_afresh qAbs_alphaAbs_qSwap_qAFresh unfolding Y_def by fastforce
    have "\<forall>z\<in>V. \<forall>zs \<in> fZs z. qFresh zs z Y"
    unfolding Y_def 
    by (metis * not_equals_and_not_equals_not_in qAFresh_imp_qFresh qAFresh_qSwap_exchange1 
        qFreshAbs.simps qSwap_preserves_qFresh_distinct y_afresh y_not_V)
    moreover have "(X,Y) \<in> qSwapped" unfolding Y_def by(simp add: qSwap_qSwapped)
    ultimately obtain Y' where "Y #= Y'" and **: "\<forall>z\<in>V. \<forall>zs \<in> fZs z. qAFresh zs z Y'"
    using Abs.IH by blast
    moreover have "qGood Y" unfolding Y_def using  `qGood X` qSwap_preserves_qGood by auto
    ultimately have "qAbs xs y Y $= qAbs xs y Y'" using qAbs_preserves_alpha by blast
    moreover have "qGoodAbs(qAbs xs x X)" using  `qGood X` by simp
    ultimately have "qAbs xs x X $= qAbs xs y Y'" using alphaXY alphaAbs_trans by blast
    moreover have "\<forall>z\<in>V. \<forall>zs \<in> fZs z. qAFreshAbs zs z (qAbs xs y Y')" using ** y_not_V by auto
    ultimately show "\<exists>A'. qAbs xs x X $= A' \<and> (\<forall>z\<in>V. \<forall>zs \<in> fZs z. qAFreshAbs zs z A')"
    by blast  
  qed
qed

corollary qFresh_imp_ex_qAFresh:
assumes "finite V" and "qGood X" and "\<forall> z \<in> V. \<forall>zs \<in> fZs z. qFresh zs z X"
shows "\<exists> X'. qGood X' \<and> X #= X' \<and> (\<forall> z \<in> V. \<forall>zs \<in> fZs z. qAFresh zs z X')"
by (metis alphaAll_preserves_qGoodAll1 assms qFreshAll_imp_ex_qAFreshAll)

corollary qFreshAbs_imp_ex_qAFreshAbs:
assumes "finite V" and "qGoodAbs A" and "\<forall> z \<in> V. \<forall>zs \<in> fZs z. qFreshAbs zs z A"
shows "\<exists> A'. qGoodAbs A' \<and> A $= A' \<and> (\<forall> z \<in> V. \<forall>zs \<in> fZs z. qAFreshAbs zs z A')"
by (metis alphaAll_preserves_qGoodAll1 assms qFreshAll_imp_ex_qAFreshAll)

lemma qFresh_imp_ex_qAFresh1:
assumes "qGood X" and "qFresh zs z X"
shows "\<exists> X'. qGood X' \<and> X #= X' \<and> qAFresh zs z X'"
using assms qFresh_imp_ex_qAFresh[of "{z}" _ "undefined(z := {zs})"] by fastforce

lemma qFreshAbs_imp_ex_qAFreshAbs1:
assumes "finite V" and "qGoodAbs A" and "qFreshAbs zs z A"
shows "\<exists> A'. qGoodAbs A' \<and> A $= A' \<and> qAFreshAbs zs z A'"
using assms qFreshAbs_imp_ex_qAFreshAbs[of "{z}" _ "undefined(z := {zs})"] by fastforce

lemma qFresh_imp_ex_qAFresh2:
assumes "qGood X" and "qFresh xs x X" and "qFresh ys y X"
shows "\<exists> X'. qGood X' \<and> X #= X' \<and> qAFresh xs x X' \<and> qAFresh ys y X'"
using assms
qFresh_imp_ex_qAFresh[of "{x}" _ "undefined(x := {xs,ys})"] 
qFresh_imp_ex_qAFresh[of "{x,y}" _ "(undefined(x := {xs}))(y := {ys})"] 
by (cases "x = y") auto

lemma qFreshAbs_imp_ex_qAFreshAbs2:
assumes "finite V" and "qGoodAbs A" and "qFreshAbs xs x A" and "qFreshAbs ys y A"
shows "\<exists> A'. qGoodAbs A' \<and> A $= A' \<and> qAFreshAbs xs x A' \<and> qAFreshAbs ys y A'"
using assms
qFreshAbs_imp_ex_qAFreshAbs[of "{x}" _ "undefined(x := {xs,ys})"] 
qFreshAbs_imp_ex_qAFreshAbs[of "{x,y}" _ "(undefined(x := {xs}))(y := {ys})"] 
by (cases "x = y") auto

lemma qAFreshAll_qFreshAll_preserves_alphaAll:
fixes X::"('index,'bindex,'varSort,'var,'opSym)qTerm" and
      A::"('index,'bindex,'varSort,'var,'opSym)qAbs" and zs z
shows
"(qGood X \<longrightarrow>
  (qAFresh zs z X \<longrightarrow> (\<forall> X'. X #= X' \<longrightarrow> qFresh zs z X'))) \<and>
 (qGoodAbs A \<longrightarrow>
  (qAFreshAbs zs z A \<longrightarrow> (\<forall> A'. A $= A' \<longrightarrow> qFreshAbs zs z A')))"
proof(induction rule: qGood_qTerm_induct)
  case (Var xs x)
  thus ?case unfolding qVar_alpha_iff by simp 
next
  case (Op delta inp binp) 
  show ?case proof safe
    fix X'  
    assume afresh: "qAFresh zs z (qOp delta inp binp)" 
    and "qOp delta inp binp #= X'" 
    then obtain inp' and binp' where X'eq: "X' = qOp delta inp' binp'" and
    *: "(\<forall>i. (inp i = None) = (inp' i = None)) \<and>
      (\<forall>i. (binp i = None) = (binp' i = None))" and
    **: "(\<forall>i Y Y'. inp i = Some Y \<and> inp' i = Some Y' \<longrightarrow> Y #= Y') \<and>
       (\<forall>i A A'. binp i = Some A \<and> binp' i = Some A' \<longrightarrow> A $= A')"
    unfolding qOp_alpha_iff sameDom_def liftAll2_def by auto
    {fix i Y' assume inp': "inp' i = Some Y'"
     then obtain Y where inp: "inp i = Some Y" using * by fastforce
     hence "Y #= Y'" using inp' ** by blast
     hence "qFresh zs z Y'" using inp Op.IH afresh by (auto simp: liftAll_def)  
    }
    moreover
    {fix i A' assume binp': "binp' i = Some A'"
     then obtain A where binp: "binp i = Some A" using * by fastforce
     hence "A $= A'" using binp' ** by blast
     hence "qFreshAbs zs z A'" using binp Op.IH afresh by (auto simp: liftAll_def) 
    }
    ultimately show "qFresh zs z X'"
    unfolding X'eq apply simp unfolding liftAll_def by simp
  qed
next
  case (Abs xs x X)
  show ?case proof safe 
    fix A'
    assume "qAbs xs x X $= A'" and afresh: "qAFreshAbs zs z (qAbs xs x X)"
    then obtain x' y X' where A'eq: "A' = qAbs xs x' X'" and
    ynot: "y \<notin> {x, x'}" and y_afresh: "qAFresh xs y X \<and> qAFresh xs y X'" and
    alpha: "(X #[[y \<and> x]]_xs) #= (X' #[[y \<and> x']]_xs)"
    unfolding qAbs_alphaAbs_iff by auto
    (*  *)
    have goodXxy: "qGood(X #[[y \<and> x]]_xs)" using `qGood X` qSwap_preserves_qGood by auto
    hence goodX'yx': "qGood(X' #[[y \<and> x']]_xs)" using alpha alpha_preserves_qGood by auto
    hence "qGood X'" using qSwap_preserves_qGood by auto
    then obtain u where u_afresh: "qAFresh xs u X \<and> qAFresh xs u X'"
    and unot: "u \<notin> {x,x',z}" using `qGood X` obtain_qFresh[of "{x,x',z}" "{X,X'}"] by auto
    (* *)
    have "(X #[[u \<and> x]]_xs) = ((X #[[y \<and> x]]_xs) #[[u \<and> y]]_xs) \<and>
          (X' #[[u \<and> x']]_xs) = ((X' #[[y \<and> x']]_xs) #[[u \<and> y]]_xs)"
    using u_afresh y_afresh qAFresh_qSwap_compose by fastforce
    moreover have "((X #[[y \<and> x]]_xs) #[[u \<and> y]]_xs) #= ((X' #[[y \<and> x']]_xs) #[[u \<and> y]]_xs)"
    using goodXxy goodX'yx' alpha qSwap_preserves_alpha by fastforce
    ultimately have alpha: "(X #[[u \<and> x]]_xs) #= (X' #[[u \<and> x']]_xs)" by simp
    (*  *)
    moreover have "(X, X #[[u \<and> x]]_xs) \<in> qSwapped" by (simp add: qSwap_qSwapped)
    moreover have "qAFresh zs z (X #[[u \<and> x]]_xs)"
    using unot afresh by(auto simp add: qSwap_preserves_qAFresh_distinct)
    ultimately have "qFresh zs z (X' #[[u \<and> x']]_xs)" using afresh Abs.IH by simp
    hence "zs = xs \<and> z = x' \<or> qFresh zs z X'"
    using unot afresh qSwap_preserves_qFresh_distinct[of zs xs z] by fastforce
    thus "qFreshAbs zs z A'" unfolding A'eq by simp
  qed
qed

corollary qAFresh_qFresh_preserves_alpha:
"\<lbrakk>qGood X; qAFresh zs z X; X #= X'\<rbrakk> \<Longrightarrow> qFresh zs z X'"
by(simp add: qAFreshAll_qFreshAll_preserves_alphaAll)

corollary qAFreshAbs_imp_qFreshAbs_preserves_alphaAbs:
"\<lbrakk>qGoodAbs A; qAFreshAbs zs z A; A $= A'\<rbrakk> \<Longrightarrow> qFreshAbs zs z A'"
by(simp add: qAFreshAll_qFreshAll_preserves_alphaAll)

lemma qFresh_preserves_alpha1:
assumes "qGood X" and "qFresh zs z X" and "X #= X'"
shows "qFresh zs z X'" 
by (meson alpha_sym alpha_trans assms qAFresh_qFresh_preserves_alpha qFresh_imp_ex_qAFresh1)

lemma qFreshAbs_preserves_alphaAbs1:
assumes "qGoodAbs A" and "qFreshAbs zs z A" and "A $= A'"
shows "qFreshAbs zs z A'" 
by (meson alphaAbs_sym alphaAbs_trans assms finite.emptyI 
  qAFreshAbs_imp_qFreshAbs_preserves_alphaAbs qFreshAbs_imp_ex_qAFreshAbs1)
 
lemma qFresh_preserves_alpha:
assumes "qGood X \<or> qGood X'" and "X #= X'"
shows "qFresh zs z X \<longleftrightarrow> qFresh zs z X'"
using alpha_preserves_qGood alpha_sym assms qFresh_preserves_alpha1 by blast
 
lemma qFreshAbs_preserves_alphaAbs:
assumes "qGoodAbs A \<or> qGoodAbs A'" and "A $= A'"
shows "qFreshAbs zs z A = qFreshAbs zs z A'"
using assms alphaAbs_preserves_qGoodAbs alphaAbs_sym qFreshAbs_preserves_alphaAbs1 by blast

lemma alpha_qFresh_qSwap_id:
assumes "qGood X" and "qFresh zs z1 X" and "qFresh zs z2 X"
shows "(X #[[z1 \<and> z2]]_zs) #= X"
proof-
  obtain X' where 1: "X #= X'" and "qAFresh zs z1 X' \<and> qAFresh zs z2 X'"
  using assms qFresh_imp_ex_qAFresh2 by force
  hence "(X' #[[z1 \<and> z2]]_zs) = X'" using qAFresh_qSwap_id by auto
  moreover have "(X #[[z1 \<and> z2]]_zs) #= (X' #[[z1 \<and> z2]]_zs)"
  using assms 1 by (auto simp add: qSwap_preserves_alpha)
  moreover have "X' #= X" using 1 alpha_sym by auto
  moreover have "qGood(X #[[z1 \<and> z2]]_zs)" using assms qSwap_preserves_qGood by auto
  ultimately show ?thesis using alpha_trans by auto
qed

lemma alphaAbs_qFreshAbs_qSwapAbs_id:
assumes "qGoodAbs A" and "qFreshAbs zs z1 A" and "qFreshAbs zs z2 A"
shows "(A $[[z1 \<and> z2]]_zs) $= A"
proof-
  obtain A' where 1: "A $= A'" and "qAFreshAbs zs z1 A' \<and> qAFreshAbs zs z2 A'"
  using assms qFreshAbs_imp_ex_qAFreshAbs2 by force
  hence "(A' $[[z1 \<and> z2]]_zs) = A'" using qAFreshAll_qSwapAll_id by fastforce
  moreover have "(A $[[z1 \<and> z2]]_zs) $= (A' $[[z1 \<and> z2]]_zs)"
  using assms 1 by (auto simp add: qSwapAbs_preserves_alphaAbs)
  moreover have "A' $= A" using 1 alphaAbs_sym by auto
  moreover have "qGoodAbs (A $[[z1 \<and> z2]]_zs)" using assms qSwapAbs_preserves_qGoodAbs by auto
  ultimately show ?thesis using alphaAbs_trans by auto
qed

lemma alpha_qFresh_qSwap_compose:
assumes GOOD: "qGood X" and "qFresh zs y X" and "qFresh zs z X"
shows "((X #[[y \<and> x]]_zs) #[[z \<and> y]]_zs) #= (X #[[z \<and> x]]_zs)"
proof-
  obtain X' where 1: "X #= X'" and "qAFresh zs y X' \<and> qAFresh zs z X'"
  using assms qFresh_imp_ex_qAFresh2 by force
  hence "((X' #[[y \<and> x]]_zs) #[[z \<and> y]]_zs) = (X' #[[z \<and> x]]_zs)"
  using qAFresh_qSwap_compose by auto
  moreover have "((X #[[y \<and> x]]_zs) #[[z \<and> y]]_zs) #= ((X' #[[y \<and> x]]_zs) #[[z \<and> y]]_zs)"
  using GOOD 1 by (auto simp add: qSwap_twice_preserves_alpha)
  moreover have "(X' #[[z \<and> x]]_zs) #= (X #[[z \<and> x]]_zs)"
  using GOOD 1 by (auto simp add: qSwap_preserves_alpha alpha_sym)
  moreover have "qGood ((X #[[y \<and> x]]_zs) #[[z \<and> y]]_zs)"
  using GOOD by (auto simp add: qSwap_twice_preserves_qGood)
  ultimately show ?thesis using alpha_trans by auto
qed

lemma qAbs_alphaAbs_qSwap_qFresh:
assumes GOOD: "qGood X" and FRESH: "qFresh xs x' X"
shows "qAbs xs x X $= qAbs xs x' (X #[[x' \<and> x]]_xs)"
proof-
  obtain Y where good_Y: "qGood Y" and alpha: "X #= Y" and fresh_Y: "qAFresh xs x' Y"
  using assms qFresh_imp_ex_qAFresh1 by fastforce
  hence "qAbs xs x Y $= qAbs xs x' (Y #[[x' \<and> x]]_xs)"
  using qAbs_alphaAbs_qSwap_qAFresh by blast
  moreover have "qAbs xs x X $= qAbs xs x Y"
  using GOOD alpha qAbs_preserves_alpha by fastforce
  moreover
  {have "Y #[[x' \<and> x]]_xs #= X #[[x' \<and> x]]_xs"
   using GOOD alpha by (auto simp add: qSwap_preserves_alpha alpha_sym)
   moreover have "qGood (Y #[[x' \<and> x]]_xs)" using good_Y qSwap_preserves_qGood by auto
   ultimately have "qAbs xs x' (Y #[[x' \<and> x]]_xs) $= qAbs xs x' (X #[[x' \<and> x]]_xs)"
   using qAbs_preserves_alpha by blast
  }
  moreover have "qGoodAbs (qAbs xs x X)" using GOOD by simp
  ultimately show ?thesis using alphaAbs_trans by blast
qed

lemma alphaAbs_qAbs_ex_qFresh_rep:
assumes GOOD: "qGood X" and FRESH: "qFresh xs x' X"
shows "\<exists> X'. (X,X') \<in> qSwapped \<and> qGood X' \<and> qAbs xs x X $= qAbs xs x' X'"
proof-
  have 1: "qGood (X #[[x' \<and> x]]_xs)" using assms qSwap_preserves_qGood by auto
  have 2: "(X,X #[[x' \<and> x]]_xs) \<in> qSwapped" by(simp add: qSwap_qSwapped)
  show ?thesis
  apply(rule exI[of _ "X #[[x' \<and> x]]_xs"])
  using assms 1 2 qAbs_alphaAbs_qSwap_qFresh by fastforce
qed
   
subsection {* Alternative statements of the alpha-clause for bound arguments  *}

text{* These alternatives are essentially variations with forall/exists and and qFresh/qAFresh. *}

(* FIXME: In this subsection I may have proved quite a few useless things. *)

subsubsection {* First for ``qAFresh"  *}

definition alphaAbs_ex_equal_or_qAFresh
where
"alphaAbs_ex_equal_or_qAFresh xs x X xs' x' X' ==
 (xs = xs' \<and>
 (\<exists> y. (y = x \<or> qAFresh xs y X) \<and> (y = x' \<or> qAFresh xs y X') \<and>
       (X #[[y \<and> x]]_xs) #= (X' #[[y \<and> x']]_xs)))"

definition alphaAbs_ex_qAFresh
where
"alphaAbs_ex_qAFresh xs x X xs' x' X' ==
 (xs = xs' \<and>
 (\<exists> y. qAFresh xs y X \<and> qAFresh xs y X' \<and>
       (X #[[y \<and> x]]_xs) #= (X' #[[y \<and> x']]_xs)))"

definition alphaAbs_ex_distinct_qAFresh
where
"alphaAbs_ex_distinct_qAFresh xs x X xs' x' X' ==
 (xs = xs' \<and>
 (\<exists> y. y \<notin> {x,x'} \<and> qAFresh xs y X \<and> qAFresh xs y X' \<and>
       (X #[[y \<and> x]]_xs) #= (X' #[[y \<and> x']]_xs)))"

definition alphaAbs_all_equal_or_qAFresh
where
"alphaAbs_all_equal_or_qAFresh xs x X xs' x' X' ==
 (xs = xs' \<and>
 (\<forall> y. (y = x \<or> qAFresh xs y X) \<and> (y = x' \<or> qAFresh xs y X') \<longrightarrow>
       (X #[[y \<and> x]]_xs) #= (X' #[[y \<and> x']]_xs)))"

definition alphaAbs_all_qAFresh
where
"alphaAbs_all_qAFresh xs x X xs' x' X' ==
 (xs = xs' \<and>
 (\<forall> y. qAFresh xs y X \<and> qAFresh xs y X' \<longrightarrow>
       (X #[[y \<and> x]]_xs) #= (X' #[[y \<and> x']]_xs)))"

definition alphaAbs_all_distinct_qAFresh
where
"alphaAbs_all_distinct_qAFresh xs x X xs' x' X' ==
 (xs = xs' \<and>
 (\<forall> y. y \<notin> {x,x'} \<and> qAFresh xs y X \<and> qAFresh xs y X' \<longrightarrow>
       (X #[[y \<and> x]]_xs) #= (X' #[[y \<and> x']]_xs)))"

lemma alphaAbs_weakestEx_imp_strongestAll:
assumes GOOD_X: "qGood X" and "alphaAbs_ex_equal_or_qAFresh xs x X xs' x' X'"
shows "alphaAbs_all_equal_or_qAFresh xs x X xs' x' X'"
proof-
  obtain y where xs: "xs = xs'" and
  yEqFresh: "(y = x \<or> qAFresh xs y X) \<and> (y = x' \<or> qAFresh xs y X')" and
  alpha: "(X #[[y \<and> x]]_xs) #= (X' #[[y \<and> x']]_xs)"
  using assms by (auto simp add: alphaAbs_ex_equal_or_qAFresh_def)
  show ?thesis
  using xs unfolding alphaAbs_all_equal_or_qAFresh_def
  proof(intro conjI allI impI, simp)
    fix z assume zFresh: "(z = x \<or> qAFresh xs z X) \<and> (z = x' \<or> qAFresh xs z X')"
    have "(X #[[z \<and> x]]_xs) = ((X #[[y \<and> x]]_xs) #[[z \<and> y]]_xs)"
    proof(cases "z = x")
      assume Case1: "z = x"
      thus ?thesis by(auto simp add: qSwap_sym)
    next
      assume Case2: "z \<noteq> x"
      hence z_fresh: "qAFresh xs z X" using zFresh by auto
      show ?thesis
      proof(cases "y = x")
        assume Case21: "y = x"
        show ?thesis unfolding Case21 by simp
      next
        assume Case22: "y \<noteq> x"
        hence "qAFresh xs y X" using yEqFresh by auto
        thus ?thesis using z_fresh qAFresh_qSwap_compose by fastforce
      qed
    qed
    moreover
    have "(X' #[[z \<and> x']]_xs) = ((X' #[[y \<and> x']]_xs) #[[z \<and> y]]_xs)"
    proof(cases "z = x'")
      assume Case1: "z = x'"
      thus ?thesis by(auto simp add: qSwap_sym)
    next
      assume Case2: "z \<noteq> x'"
      hence z_fresh: "qAFresh xs z X'" using zFresh by auto
      show ?thesis
      proof(cases "y = x'")
        assume Case21: "y = x'"
        show ?thesis unfolding Case21 by simp
      next
        assume Case22: "y \<noteq> x'"
        hence "qAFresh xs y X'" using yEqFresh by auto
        thus ?thesis using z_fresh qAFresh_qSwap_compose by fastforce
      qed
    qed
    moreover
    {have "qGood (X #[[y \<and> x]]_xs)" using GOOD_X qSwap_preserves_qGood by auto
     hence "((X #[[y \<and> x]]_xs) #[[z \<and> y]]_xs) #= ((X' #[[y \<and> x']]_xs) #[[z \<and> y]]_xs)"
     using alpha qSwap_preserves_alpha by fastforce
    }
    ultimately show "(X #[[z \<and> x]]_xs) #= (X' #[[z \<and> x']]_xs)" by simp
  qed
qed

lemma alphaAbs_weakestAll_imp_strongestEx:
assumes GOOD: "qGood X"  "qGood X'"
and "alphaAbs_all_distinct_qAFresh xs x X xs' x' X'"
shows "alphaAbs_ex_distinct_qAFresh xs x X xs' x' X'"
proof-
  have xs: "xs = xs'"
  using assms unfolding alphaAbs_all_distinct_qAFresh_def by auto
  obtain y where y_not:  "y \<notin> {x,x'}" and
                 yFresh: "qAFresh xs y X \<and> qAFresh xs y X'"
  using GOOD obtain_qFresh[of  "{x,x'}" "{X,X'}"] by auto
  hence "(X #[[y \<and> x]]_xs) #= (X' #[[y \<and> x']]_xs)"
  using assms unfolding alphaAbs_all_distinct_qAFresh_def by auto
  thus ?thesis unfolding alphaAbs_ex_distinct_qAFresh_def using xs y_not yFresh by auto
qed

(* Note: I do not infer the following from the previous two because
   I do not want to use "qGood X'": *)

lemma alphaAbs_weakestEx_imp_strongestEx:
assumes GOOD: "qGood X"
and "alphaAbs_ex_equal_or_qAFresh xs x X xs' x' X'"
shows "alphaAbs_ex_distinct_qAFresh xs x X xs' x' X'"
proof-
  obtain y where xs: "xs = xs'" and
  yEqFresh: "(y = x \<or> qAFresh xs y X) \<and> (y = x' \<or> qAFresh xs y X')" and
  alpha: "(X #[[y \<and> x]]_xs) #= (X' #[[y \<and> x']]_xs)"
  using assms unfolding alphaAbs_ex_equal_or_qAFresh_def by blast
  hence goodX': "qGood X'"
  using GOOD alpha_qSwap_preserves_qGood by fastforce
  then obtain z where zNot: "z \<notin> {x,x',y}" and
                      zFresh: "qAFresh xs z X \<and> qAFresh xs z X'"
  using GOOD obtain_qFresh[of "{x,x',y}" "{X,X'}"] by auto
  have "(X #[[z \<and> x]]_xs) = ((X #[[y \<and> x]]_xs) #[[z \<and> y]]_xs)"
  proof(cases "y = x", simp)
    assume "y \<noteq> x"  hence "qAFresh xs y X" using yEqFresh by auto
    thus ?thesis using zFresh qAFresh_qSwap_compose by fastforce
  qed
  moreover have "(X' #[[z \<and> x']]_xs) = ((X' #[[y \<and> x']]_xs) #[[z \<and> y]]_xs)"
  proof(cases "y = x'", simp add: qSwap_ident)
    assume "y \<noteq> x'"  hence "qAFresh xs y X'" using yEqFresh by auto
    thus ?thesis using zFresh qAFresh_qSwap_compose by fastforce
  qed
  moreover
  {have "qGood (X #[[y \<and> x]]_xs)" using GOOD qSwap_preserves_qGood by auto
   hence "((X #[[y \<and> x]]_xs) #[[z \<and> y]]_xs) #= ((X' #[[y \<and> x']]_xs) #[[z \<and> y]]_xs)"
   using alpha by (auto simp add: qSwap_preserves_alpha)
  }
  ultimately have "(X #[[z \<and> x]]_xs) #= (X' #[[z \<and> x']]_xs)" by simp
  thus ?thesis unfolding alphaAbs_ex_distinct_qAFresh_def using xs zNot zFresh by auto
qed

lemma alphaAbs_qAbs_iff_alphaAbs_ex_distinct_qAFresh:
"(qAbs xs x X $= qAbs xs' x' X') = alphaAbs_ex_distinct_qAFresh xs x X xs' x' X'"
unfolding alphaAbs_ex_distinct_qAFresh_def by auto

corollary alphaAbs_qAbs_iff_ex_distinct_qAFresh:
"(qAbs xs x X $= qAbs xs' x' X') =
 (xs = xs' \<and>
  (\<exists> y. y \<notin> {x,x'} \<and> qAFresh xs y X \<and> qAFresh xs y X' \<and>
         (X #[[y \<and> x]]_xs) #= (X' #[[y \<and> x']]_xs)))"
unfolding alphaAbs_qAbs_iff_alphaAbs_ex_distinct_qAFresh
          alphaAbs_ex_distinct_qAFresh_def by fastforce

lemma alphaAbs_qAbs_iff_alphaAbs_ex_equal_or_qAFresh:
assumes "qGood X"
shows "(qAbs xs x X $= qAbs xs' x' X') =
       alphaAbs_ex_equal_or_qAFresh xs x X xs' x' X'"
proof-
  let ?Left = "qAbs xs x X $= qAbs xs' x' X'"
  let ?Right = "alphaAbs_ex_equal_or_qAFresh xs x X xs' x' X'"
  have "?Left \<Longrightarrow> ?Right" unfolding alphaAbs_ex_equal_or_qAFresh_def by auto
  moreover have "?Right \<Longrightarrow> ?Left"
  using assms alphaAbs_qAbs_iff_alphaAbs_ex_distinct_qAFresh[of _ _ X]
        alphaAbs_weakestEx_imp_strongestEx by auto
  ultimately show ?thesis by auto
qed

corollary alphaAbs_qAbs_iff_ex_equal_or_qAFresh:
assumes "qGood X"
shows
"(qAbs xs x X $= qAbs xs' x' X') =
 (xs = xs' \<and>
  (\<exists> y. (y = x \<or> qAFresh xs y X) \<and> (y = x' \<or> qAFresh xs y X') \<and>
         (X #[[y \<and> x]]_xs) #= (X' #[[y \<and> x']]_xs)))"
proof-
  have "(qAbs xs x X $= qAbs xs' x' X') =
        alphaAbs_ex_equal_or_qAFresh xs x X xs' x' X'"
  using assms alphaAbs_qAbs_iff_alphaAbs_ex_equal_or_qAFresh by fastforce
  thus ?thesis unfolding alphaAbs_ex_equal_or_qAFresh_def .
qed

lemma alphaAbs_qAbs_iff_alphaAbs_ex_qAFresh:
assumes "qGood X"
shows "(qAbs xs x X $= qAbs xs' x' X') = alphaAbs_ex_qAFresh xs x X xs' x' X'"
proof-
  let ?Left = "qAbs xs x X $= qAbs xs' x' X'"
  let ?Middle = "alphaAbs_ex_equal_or_qAFresh xs x X xs' x' X'"
  let ?Right = "alphaAbs_ex_qAFresh xs x X xs' x' X'"
  have "?Left \<Longrightarrow> ?Right" unfolding alphaAbs_ex_qAFresh_def by auto
  moreover have "?Right \<Longrightarrow> ?Middle"
  unfolding alphaAbs_ex_qAFresh_def alphaAbs_ex_equal_or_qAFresh_def by auto
  moreover have "?Middle = ?Left"
  using assms alphaAbs_qAbs_iff_alphaAbs_ex_equal_or_qAFresh[of X] by fastforce
  ultimately show ?thesis by blast
qed

corollary alphaAbs_qAbs_iff_ex_qAFresh:
assumes "qGood X"
shows
"(qAbs xs x X $= qAbs xs' x' X') =
 (xs = xs' \<and>
  (\<exists> y. qAFresh xs y X \<and> qAFresh xs y X' \<and>
         (X #[[y \<and> x]]_xs) #= (X' #[[y \<and> x']]_xs)))"
proof-
  have "(qAbs xs x X $= qAbs xs' x' X') = alphaAbs_ex_qAFresh xs x X xs' x' X'"
  using assms alphaAbs_qAbs_iff_alphaAbs_ex_qAFresh by fastforce
  thus ?thesis unfolding alphaAbs_ex_qAFresh_def .
qed

lemma alphaAbs_qAbs_imp_alphaAbs_all_equal_or_qAFresh:
assumes "qGood X" and "qAbs xs x X $= qAbs xs' x' X'"
shows "alphaAbs_all_equal_or_qAFresh xs x X xs' x' X'"
using assms alphaAbs_qAbs_iff_alphaAbs_ex_equal_or_qAFresh
      alphaAbs_weakestEx_imp_strongestAll by fastforce

corollary alphaAbs_qAbs_imp_all_equal_or_qAFresh:
assumes "qGood X" and "(qAbs xs x X $= qAbs xs' x' X')"
shows
"(xs = xs' \<and>
  (\<forall> y. (y = x \<or> qAFresh xs y X) \<and> (y = x' \<or> qAFresh xs y X') \<longrightarrow>
        (X #[[y \<and> x]]_xs) #= (X' #[[y \<and> x']]_xs)))"
proof-
  have "alphaAbs_all_equal_or_qAFresh xs x X xs' x' X'"
  using assms alphaAbs_qAbs_imp_alphaAbs_all_equal_or_qAFresh by blast
  thus ?thesis unfolding alphaAbs_all_equal_or_qAFresh_def .
qed

lemma alphaAbs_qAbs_iff_alphaAbs_all_equal_or_qAFresh:
assumes "qGood X" and "qGood X'"
shows "(qAbs xs x X $= qAbs xs' x' X') =
       alphaAbs_all_equal_or_qAFresh xs x X xs' x' X'"
proof-
  let ?Left = "qAbs xs x X $= qAbs xs' x' X'"
  let ?MiddleEx = "alphaAbs_ex_distinct_qAFresh xs x X xs' x' X'"
  let ?MiddleAll = "alphaAbs_all_distinct_qAFresh xs x X xs' x' X'"
  let ?Right = "alphaAbs_all_equal_or_qAFresh xs x X xs' x' X'"
  have "?Left \<Longrightarrow> ?Right"
  using assms alphaAbs_qAbs_imp_alphaAbs_all_equal_or_qAFresh by blast
  moreover have "?Right \<Longrightarrow> ?MiddleAll"
  unfolding alphaAbs_all_equal_or_qAFresh_def alphaAbs_all_distinct_qAFresh_def by auto
  moreover have "?MiddleAll \<Longrightarrow> ?MiddleEx"
  using assms alphaAbs_weakestAll_imp_strongestEx by fastforce
  moreover have "?MiddleEx \<Longrightarrow> ?Left"
  using alphaAbs_qAbs_iff_alphaAbs_ex_distinct_qAFresh[of _ _ X] by fastforce
  ultimately show ?thesis by blast
qed

corollary alphaAbs_qAbs_iff_all_equal_or_qAFresh:
assumes "qGood X" and "qGood X'"
shows "(qAbs xs x X $= qAbs xs' x' X') =
       (xs = xs' \<and>
        (\<forall> y. (y = x \<or> qAFresh xs y X) \<and> (y = x' \<or> qAFresh xs y X') \<longrightarrow>
              (X #[[y \<and> x]]_xs) #= (X' #[[y \<and> x']]_xs)))"
proof-
  have "(qAbs xs x X $= qAbs xs' x' X') =
        alphaAbs_all_equal_or_qAFresh xs x X xs' x' X'"
  using assms alphaAbs_qAbs_iff_alphaAbs_all_equal_or_qAFresh by blast
  thus ?thesis unfolding alphaAbs_all_equal_or_qAFresh_def .
qed

lemma alphaAbs_qAbs_imp_alphaAbs_all_qAFresh:
assumes "qGood X" and "qAbs xs x X $= qAbs xs' x' X'"
shows "alphaAbs_all_qAFresh xs x X xs' x' X'"
proof-
  have "alphaAbs_all_equal_or_qAFresh xs x X xs' x' X'"
  using assms alphaAbs_qAbs_imp_alphaAbs_all_equal_or_qAFresh by blast
  thus ?thesis unfolding alphaAbs_all_qAFresh_def alphaAbs_all_equal_or_qAFresh_def by auto
qed

corollary alphaAbs_qAbs_imp_all_qAFresh:
assumes "qGood X" and "(qAbs xs x X $= qAbs xs' x' X')"
shows
"(xs = xs' \<and>
  (\<forall> y. qAFresh xs y X \<and> qAFresh xs y X' \<longrightarrow>
        (X #[[y \<and> x]]_xs) #= (X' #[[y \<and> x']]_xs)))"
proof-
  have "alphaAbs_all_qAFresh xs x X xs' x' X'"
  using assms alphaAbs_qAbs_imp_alphaAbs_all_qAFresh by blast
  thus ?thesis unfolding alphaAbs_all_qAFresh_def .
qed

lemma alphaAbs_qAbs_iff_alphaAbs_all_qAFresh:
assumes "qGood X" and "qGood X'"
shows "(qAbs xs x X $= qAbs xs' x' X') = alphaAbs_all_qAFresh xs x X xs' x' X'"
proof-
  let ?Left = "qAbs xs x X $= qAbs xs' x' X'"
  let ?MiddleEx = "alphaAbs_ex_distinct_qAFresh xs x X xs' x' X'"
  let ?MiddleAll = "alphaAbs_all_distinct_qAFresh xs x X xs' x' X'"
  let ?Right = "alphaAbs_all_qAFresh xs x X xs' x' X'"
  have "?Left \<Longrightarrow> ?Right" using assms alphaAbs_qAbs_imp_alphaAbs_all_qAFresh by blast
  moreover have "?Right \<Longrightarrow> ?MiddleAll"
  unfolding alphaAbs_all_qAFresh_def alphaAbs_all_distinct_qAFresh_def by auto
  moreover have "?MiddleAll \<Longrightarrow> ?MiddleEx"
  using assms alphaAbs_weakestAll_imp_strongestEx by fastforce
  moreover have "?MiddleEx \<Longrightarrow> ?Left"
  using assms alphaAbs_qAbs_iff_alphaAbs_ex_distinct_qAFresh[of _ _ X] by fastforce
  ultimately show ?thesis by blast
qed

corollary alphaAbs_qAbs_iff_all_qAFresh:
assumes "qGood X" and "qGood X'"
shows "(qAbs xs x X $= qAbs xs' x' X') =
       (xs = xs' \<and>
        (\<forall> y. qAFresh xs y X \<and> qAFresh xs y X' \<longrightarrow>
              (X #[[y \<and> x]]_xs) #= (X' #[[y \<and> x']]_xs)))"
proof-
  have "(qAbs xs x X $= qAbs xs' x' X') =
        alphaAbs_all_qAFresh xs x X xs' x' X'"
  using assms alphaAbs_qAbs_iff_alphaAbs_all_qAFresh by blast
  thus ?thesis unfolding alphaAbs_all_qAFresh_def .
qed

lemma alphaAbs_qAbs_imp_alphaAbs_all_distinct_qAFresh:
assumes "qGood X" and "qAbs xs x X $= qAbs xs' x' X'"
shows "alphaAbs_all_distinct_qAFresh xs x X xs' x' X'"
proof-
  have "alphaAbs_all_equal_or_qAFresh xs x X xs' x' X'"
  using assms alphaAbs_qAbs_imp_alphaAbs_all_equal_or_qAFresh by blast
  thus ?thesis
  unfolding alphaAbs_all_distinct_qAFresh_def alphaAbs_all_equal_or_qAFresh_def by auto
qed

corollary alphaAbs_qAbs_imp_all_distinct_qAFresh:
assumes "qGood X" and "(qAbs xs x X $= qAbs xs' x' X')"
shows
"(xs = xs' \<and>
  (\<forall> y. y \<notin> {x,x'} \<and> qAFresh xs y X \<and> qAFresh xs y X' \<longrightarrow>
        (X #[[y \<and> x]]_xs) #= (X' #[[y \<and> x']]_xs)))"
proof-
  have "alphaAbs_all_distinct_qAFresh xs x X xs' x' X'"
  using assms alphaAbs_qAbs_imp_alphaAbs_all_distinct_qAFresh by blast
  thus ?thesis unfolding alphaAbs_all_distinct_qAFresh_def .
qed

lemma alphaAbs_qAbs_iff_alphaAbs_all_distinct_qAFresh:
assumes "qGood X" and "qGood X'"
shows "(qAbs xs x X $= qAbs xs' x' X') =
       alphaAbs_all_distinct_qAFresh xs x X xs' x' X'"
proof-
  let ?Left = "qAbs xs x X $= qAbs xs' x' X'"
  let ?MiddleEx = "alphaAbs_ex_distinct_qAFresh xs x X xs' x' X'"
  let ?MiddleAll = "alphaAbs_all_distinct_qAFresh xs x X xs' x' X'"
  let ?Right = "alphaAbs_all_distinct_qAFresh xs x X xs' x' X'"
  have "?Left \<Longrightarrow> ?Right"
  using assms alphaAbs_qAbs_imp_alphaAbs_all_distinct_qAFresh by blast
  moreover have "?Right \<Longrightarrow> ?MiddleAll"
  unfolding alphaAbs_all_distinct_qAFresh_def alphaAbs_all_distinct_qAFresh_def by auto
  moreover have "?MiddleAll \<Longrightarrow> ?MiddleEx"
  using assms alphaAbs_weakestAll_imp_strongestEx by fastforce
  moreover have "?MiddleEx \<Longrightarrow> ?Left"
  using assms alphaAbs_qAbs_iff_alphaAbs_ex_distinct_qAFresh[of _ _ X] by fastforce
  ultimately show ?thesis by blast
qed

corollary alphaAbs_qAbs_iff_all_distinct_qAFresh:
assumes "qGood X" and "qGood X'"
shows "(qAbs xs x X $= qAbs xs' x' X') =
       (xs = xs' \<and>
        (\<forall> y. y \<notin> {x,x'} \<and> qAFresh xs y X \<and> qAFresh xs y X' \<longrightarrow>
              (X #[[y \<and> x]]_xs) #= (X' #[[y \<and> x']]_xs)))"
proof-
  have "(qAbs xs x X $= qAbs xs' x' X') =
        alphaAbs_all_distinct_qAFresh xs x X xs' x' X'"
  using assms alphaAbs_qAbs_iff_alphaAbs_all_distinct_qAFresh by blast
  thus ?thesis unfolding alphaAbs_all_distinct_qAFresh_def .
qed

subsubsection{* Then for ``qFresh" *}

definition alphaAbs_ex_equal_or_qFresh
where
"alphaAbs_ex_equal_or_qFresh xs x X xs' x' X' ==
 (xs = xs' \<and>
 (\<exists> y. (y = x \<or> qFresh xs y X) \<and> (y = x' \<or> qFresh xs y X') \<and>
       (X #[[y \<and> x]]_xs) #= (X' #[[y \<and> x']]_xs)))"

definition alphaAbs_ex_qFresh
where
"alphaAbs_ex_qFresh xs x X xs' x' X' ==
 (xs = xs' \<and>
 (\<exists> y. qFresh xs y X \<and> qFresh xs y X' \<and>
       (X #[[y \<and> x]]_xs) #= (X' #[[y \<and> x']]_xs)))"

definition alphaAbs_ex_distinct_qFresh
where
"alphaAbs_ex_distinct_qFresh xs x X xs' x' X' ==
 (xs = xs' \<and>
 (\<exists> y. y \<notin> {x,x'} \<and> qFresh xs y X \<and> qFresh xs y X' \<and>
       (X #[[y \<and> x]]_xs) #= (X' #[[y \<and> x']]_xs)))"

definition alphaAbs_all_equal_or_qFresh
where
"alphaAbs_all_equal_or_qFresh xs x X xs' x' X' ==
 (xs = xs' \<and>
 (\<forall> y. (y = x \<or> qFresh xs y X) \<and> (y = x' \<or> qFresh xs y X') \<longrightarrow>
       (X #[[y \<and> x]]_xs) #= (X' #[[y \<and> x']]_xs)))"

definition alphaAbs_all_qFresh
where
"alphaAbs_all_qFresh xs x X xs' x' X' ==
 (xs = xs' \<and>
 (\<forall> y. qFresh xs y X \<and> qFresh xs y X' \<longrightarrow>
       (X #[[y \<and> x]]_xs) #= (X' #[[y \<and> x']]_xs)))"

definition alphaAbs_all_distinct_qFresh
where
"alphaAbs_all_distinct_qFresh xs x X xs' x' X' ==
 (xs = xs' \<and>
 (\<forall> y. y \<notin> {x,x'} \<and> qFresh xs y X \<and> qFresh xs y X' \<longrightarrow>
       (X #[[y \<and> x]]_xs) #= (X' #[[y \<and> x']]_xs)))"

lemma alphaAbs_ex_equal_or_qAFresh_imp_qFresh:
"alphaAbs_ex_equal_or_qAFresh xs x X xs' x' X' \<Longrightarrow>
 alphaAbs_ex_equal_or_qFresh xs x X xs' x' X'"
unfolding alphaAbs_ex_equal_or_qAFresh_def alphaAbs_ex_equal_or_qFresh_def
using qAFresh_imp_qFresh[of _ _ X] qAFresh_imp_qFresh[of _ _ X'] by blast

lemma alphaAbs_ex_distinct_qAFresh_imp_qFresh:
"alphaAbs_ex_distinct_qAFresh xs x X xs' x' X' \<Longrightarrow>
 alphaAbs_ex_distinct_qFresh xs x X xs' x' X'"
unfolding alphaAbs_ex_distinct_qAFresh_def alphaAbs_ex_distinct_qFresh_def
using qAFresh_imp_qFresh[of _ _ X] qAFresh_imp_qFresh[of _ _ X'] by blast

lemma alphaAbs_ex_qAFresh_imp_qFresh:
"alphaAbs_ex_qAFresh xs x X xs' x' X' \<Longrightarrow>
 alphaAbs_ex_qFresh xs x X xs' x' X'"
unfolding alphaAbs_ex_qAFresh_def alphaAbs_ex_qFresh_def
using qAFresh_imp_qFresh[of _ _ X] qAFresh_imp_qFresh[of _ _ X'] by blast

lemma alphaAbs_all_equal_or_qFresh_imp_qAFresh:
"alphaAbs_all_equal_or_qFresh xs x X xs' x' X' \<Longrightarrow>
 alphaAbs_all_equal_or_qAFresh xs x X xs' x' X'"
unfolding alphaAbs_all_equal_or_qAFresh_def alphaAbs_all_equal_or_qFresh_def
using qAFresh_imp_qFresh[of _ _ X] qAFresh_imp_qFresh[of _ _ X'] by blast

lemma alphaAbs_all_distinct_qFresh_imp_qAFresh:
"alphaAbs_all_distinct_qFresh xs x X xs' x' X' \<Longrightarrow>
 alphaAbs_all_distinct_qAFresh xs x X xs' x' X'"
using qAFresh_imp_qFresh
unfolding alphaAbs_all_distinct_qAFresh_def alphaAbs_all_distinct_qFresh_def by fastforce

lemma alphaAbs_all_qFresh_imp_qAFresh:
"alphaAbs_all_qFresh xs x X xs' x' X' \<Longrightarrow>
 alphaAbs_all_qAFresh xs x X xs' x' X'"
using qAFresh_imp_qFresh
unfolding alphaAbs_all_qAFresh_def alphaAbs_all_qFresh_def by fastforce

lemma alphaAbs_ex_equal_or_qFresh_imp_alphaAbs_qAbs:
assumes GOOD: "qGood X" and "alphaAbs_ex_equal_or_qFresh xs x X xs' x' X'"
shows "qAbs xs x X $= qAbs xs' x' X'"
proof-
  obtain y where xs: "xs = xs'" and
  yEqFresh: "(y = x \<or> qFresh xs y X) \<and> (y = x' \<or> qFresh xs y X')" and
  alphaXX'yx: "(X #[[y \<and> x]]_xs) #= (X' #[[y \<and> x']]_xs)"
  using assms unfolding alphaAbs_ex_equal_or_qFresh_def by blast
  have "\<exists> Y. X #= Y \<and> (y = x \<or> qAFresh xs y Y)"
  proof(cases "y = x")
    assume Case1: "y = x" hence "X #= X" using GOOD alpha_refl by auto
    thus ?thesis using Case1 by fastforce
  next
    assume Case2: "y \<noteq> x" hence "qFresh xs y X" using yEqFresh by blast
    then obtain Y where "X #= Y" and "qAFresh xs y Y"
    using GOOD qFresh_imp_ex_qAFresh1 by fastforce
    thus ?thesis by auto
  qed
  then obtain Y where alphaXY: "X #= Y" and yEqAFresh: "y = x \<or> qAFresh xs y Y" by blast
  hence "(X #[[y \<and> x]]_xs) #= (Y #[[y \<and> x]]_xs)"
  using GOOD qSwap_preserves_alpha by fastforce
  hence alphaYXyx: "(Y #[[y \<and> x]]_xs) #= (X #[[y \<and> x]]_xs)" using alpha_sym by auto
  have goodY: "qGood Y" using alphaXY GOOD alpha_preserves_qGood by auto
  hence goodYyx: "qGood(Y #[[y \<and> x]]_xs)" using qSwap_preserves_qGood by auto
  (*  *)
  have good': "qGood X'"
  using GOOD alphaXX'yx alpha_qSwap_preserves_qGood by fastforce
  have "\<exists> Y'. X' #= Y' \<and> (y = x' \<or> qAFresh xs y Y')"
  proof(cases "y = x'")
    assume Case1: "y = x'" hence "X' #= X'" using good' alpha_refl by auto
    thus ?thesis using Case1 by fastforce
  next
    assume Case2: "y \<noteq> x'" hence "qFresh xs y X'" using yEqFresh by blast
    then obtain Y' where "X' #= Y'" and "qAFresh xs y Y'"
    using good' qFresh_imp_ex_qAFresh1 by fastforce
    thus ?thesis by auto
  qed
  then obtain Y' where alphaX'Y': "X' #= Y'" and
                       yEqAFresh': "y = x' \<or> qAFresh xs y Y'" by blast
  hence "(X' #[[y \<and> x']]_xs) #= (Y' #[[y \<and> x']]_xs)"
  using good' by (auto simp add: qSwap_preserves_alpha)
  hence "(Y #[[y \<and> x]]_xs) #= (Y' #[[y \<and> x']]_xs)"
  using goodYyx alphaYXyx alphaXX'yx alpha_trans by blast
  hence "alphaAbs_ex_equal_or_qAFresh xs x Y xs x' Y'"
  unfolding alphaAbs_ex_equal_or_qAFresh_def using yEqAFresh yEqAFresh' by fastforce
  hence "qAbs xs x Y $= qAbs xs x' Y'"
  using goodY alphaAbs_qAbs_iff_alphaAbs_ex_equal_or_qAFresh[of Y xs x xs] by fastforce
  moreover have "qAbs xs x X $= qAbs xs x Y"
  using alphaXY GOOD qAbs_preserves_alpha by fastforce
  moreover
  {have 1: "Y' #= X'" using alphaX'Y' alpha_sym by auto
   hence "qGood Y'" using good' alpha_preserves_qGood by auto
   hence "qAbs xs x' Y' $= qAbs xs x' X'"
   using 1 GOOD qAbs_preserves_alpha by fastforce
  }
  moreover have "qGoodAbs(qAbs xs x X)" using GOOD by simp
  ultimately have "qAbs xs x X $= qAbs xs x' X'"
  using alphaAbs_trans_twice by blast
  thus ?thesis using xs by simp
qed

lemma alphaAbs_qAbs_iff_alphaAbs_ex_equal_or_qFresh:
assumes GOOD: "qGood X"
shows "(qAbs xs x X $= qAbs xs' x' X') =
       alphaAbs_ex_equal_or_qFresh xs x X xs' x' X'"
proof-
  let ?Left = "qAbs xs x X $= qAbs xs' x' X'"
  let ?Middle = "alphaAbs_ex_equal_or_qAFresh xs x X xs' x' X'"
  let ?Right = "alphaAbs_ex_equal_or_qFresh xs x X xs' x' X'"
  have "?Right \<Longrightarrow> ?Left"
  using assms alphaAbs_ex_equal_or_qFresh_imp_alphaAbs_qAbs by blast
  moreover have "?Left \<Longrightarrow> ?Middle"
  using assms alphaAbs_qAbs_iff_alphaAbs_ex_equal_or_qAFresh by blast
  moreover have "?Middle \<Longrightarrow> ?Right" using
  alphaAbs_ex_equal_or_qAFresh_imp_qFresh by fastforce
  ultimately show ?thesis by blast
qed

corollary alphaAbs_qAbs_iff_ex_equal_or_qFresh:
assumes GOOD: "qGood X"
shows "(qAbs xs x X $= qAbs xs' x' X') =
        (xs = xs' \<and>
         (\<exists> y. (y = x \<or> qFresh xs y X) \<and> (y = x' \<or> qFresh xs y X') \<and>
               (X #[[y \<and> x]]_xs) #= (X' #[[y \<and> x']]_xs)))"
proof-
  have "(qAbs xs x X $= qAbs xs' x' X') =
        alphaAbs_ex_equal_or_qFresh xs x X xs' x' X'"
  using assms alphaAbs_qAbs_iff_alphaAbs_ex_equal_or_qFresh by blast
  thus ?thesis unfolding alphaAbs_ex_equal_or_qFresh_def .
qed

lemma alphaAbs_qAbs_iff_alphaAbs_ex_qFresh:
assumes GOOD: "qGood X"
shows "(qAbs xs x X $= qAbs xs' x' X') =
       alphaAbs_ex_qFresh xs x X xs' x' X'"
proof-
  let ?Left = "qAbs xs x X $= qAbs xs' x' X'"
  let ?Middle1 = "alphaAbs_ex_qAFresh xs x X xs' x' X'"
  let ?Middle2 = "alphaAbs_ex_equal_or_qFresh xs x X xs' x' X'"
  let ?Right = "alphaAbs_ex_qFresh xs x X xs' x' X'"
  have "?Left \<Longrightarrow> ?Middle1" unfolding alphaAbs_ex_qAFresh_def by auto
  moreover have "?Middle1 \<Longrightarrow> ?Right" using alphaAbs_ex_qAFresh_imp_qFresh by fastforce
  moreover have "?Right \<Longrightarrow> ?Middle2"
  unfolding alphaAbs_ex_qFresh_def alphaAbs_ex_equal_or_qFresh_def by auto
  moreover have "?Middle2 \<Longrightarrow> ?Left"
  using assms alphaAbs_ex_equal_or_qFresh_imp_alphaAbs_qAbs by fastforce
  ultimately show ?thesis by blast
qed

corollary alphaAbs_qAbs_iff_ex_qFresh:
assumes GOOD: "qGood X"
shows "(qAbs xs x X $= qAbs xs' x' X') =
        (xs = xs' \<and>
         (\<exists> y. qFresh xs y X \<and> qFresh xs y X' \<and>
               (X #[[y \<and> x]]_xs) #= (X' #[[y \<and> x']]_xs)))"
proof-
  have "(qAbs xs x X $= qAbs xs' x' X') =
        alphaAbs_ex_qFresh xs x X xs' x' X'"
  using assms alphaAbs_qAbs_iff_alphaAbs_ex_qFresh by blast
  thus ?thesis unfolding alphaAbs_ex_qFresh_def .
qed 

lemma alphaAbs_qAbs_iff_alphaAbs_ex_distinct_qFresh:
assumes GOOD: "qGood X"
shows "(qAbs xs x X $= qAbs xs' x' X') =
       alphaAbs_ex_distinct_qFresh xs x X xs' x' X'"
proof-
  let ?Left = "qAbs xs x X $= qAbs xs' x' X'"
  let ?Middle1 = "alphaAbs_ex_distinct_qAFresh xs x X xs' x' X'"
  let ?Middle2 = "alphaAbs_ex_equal_or_qFresh xs x X xs' x' X'"
  let ?Right = "alphaAbs_ex_distinct_qFresh xs x X xs' x' X'"
  have "?Left \<Longrightarrow> ?Middle1" unfolding alphaAbs_ex_distinct_qAFresh_def by auto
  moreover have "?Middle1 \<Longrightarrow> ?Right" using alphaAbs_ex_distinct_qAFresh_imp_qFresh by fastforce
  moreover have "?Right \<Longrightarrow> ?Middle2"
  unfolding alphaAbs_ex_distinct_qFresh_def alphaAbs_ex_equal_or_qFresh_def by auto
  moreover have "?Middle2 \<Longrightarrow> ?Left"
  using assms alphaAbs_ex_equal_or_qFresh_imp_alphaAbs_qAbs by fastforce
  ultimately show ?thesis by blast
qed

corollary alphaAbs_qAbs_iff_ex_distinct_qFresh:
assumes GOOD: "qGood X"
shows "(qAbs xs x X $= qAbs xs' x' X') =
        (xs = xs' \<and>
         (\<exists> y. y \<notin> {x, x'} \<and> qFresh xs y X \<and> qFresh xs y X' \<and>
               (X #[[y \<and> x]]_xs) #= (X' #[[y \<and> x']]_xs)))"
proof-
  have "(qAbs xs x X $= qAbs xs' x' X') =
        alphaAbs_ex_distinct_qFresh xs x X xs' x' X'"
  using assms alphaAbs_qAbs_iff_alphaAbs_ex_distinct_qFresh by blast
  thus ?thesis unfolding alphaAbs_ex_distinct_qFresh_def .
qed

lemma alphaAbs_qAbs_imp_alphaAbs_all_equal_or_qFresh:
assumes "qGood X" and "qAbs xs x X $= qAbs xs' x' X'"
shows "alphaAbs_all_equal_or_qFresh xs x X xs' x' X'"
proof-
  have "qGoodAbs(qAbs xs x X)" using assms by auto
  hence "qGoodAbs(qAbs xs' x' X')" using assms alphaAbs_preserves_qGoodAbs by blast
  hence GOOD: "qGood X \<and> qGood X'" using assms by auto
  have xs: "xs = xs'" using assms by auto
  show ?thesis
  unfolding alphaAbs_all_equal_or_qFresh_def using xs
  proof(intro conjI impI allI, simp)
    fix y
    assume yEqFresh: "(y = x \<or> qFresh xs y X) \<and> (y = x' \<or> qFresh xs y X')"
    have "\<exists> Y. X #= Y \<and> (y = x \<or> qAFresh xs y Y)"
    proof(cases "y = x")
      assume Case1: "y = x" hence "X #= X" using GOOD alpha_refl by auto
      thus ?thesis using Case1 by fastforce
    next
      assume Case2: "y \<noteq> x" hence "qFresh xs y X" using yEqFresh by blast
      then obtain Y where "X #= Y" and "qAFresh xs y Y"
      using GOOD qFresh_imp_ex_qAFresh1 by blast
      thus ?thesis by auto
    qed
    then obtain Y where alphaXY: "X #= Y" and yEqAFresh: "y = x \<or> qAFresh xs y Y" by blast
    hence alphaXYyx: "(X #[[y \<and> x]]_xs) #= (Y #[[y \<and> x]]_xs)"
    using GOOD by (auto simp add: qSwap_preserves_alpha)
    have goodY: "qGood Y" using GOOD alphaXY alpha_preserves_qGood by auto
    (*  *)
    have "\<exists> Y'. X' #= Y' \<and> (y = x' \<or> qAFresh xs y Y')"
    proof(cases "y = x'")
      assume Case1: "y = x'" hence "X' #= X'" using GOOD alpha_refl by auto
      thus ?thesis using Case1 by fastforce
    next
      assume Case2: "y \<noteq> x'" hence "qFresh xs y X'" using yEqFresh by blast
      then obtain Y' where "X' #= Y'" and "qAFresh xs y Y'"
      using GOOD qFresh_imp_ex_qAFresh1 by blast
      thus ?thesis by auto
    qed
    then obtain Y' where alphaX'Y': "X' #= Y'" and
                         yEqAFresh': "y = x' \<or> qAFresh xs y Y'" by blast
    hence "(X' #[[y \<and> x']]_xs) #= (Y' #[[y \<and> x']]_xs)"
    using GOOD by (auto simp add: qSwap_preserves_alpha)
    hence alphaY'X'yx': "(Y' #[[y \<and> x']]_xs) #= (X' #[[y \<and> x']]_xs)" using alpha_sym by auto
    have goodY': "qGood Y'" using GOOD alphaX'Y' alpha_preserves_qGood by auto
    (*  *)
    have 1: "Y #= X" using alphaXY alpha_sym by auto
    hence "qGood Y" using GOOD alpha_preserves_qGood by auto
    hence 2: "qAbs xs x Y $= qAbs xs x X"
    using 1 GOOD qAbs_preserves_alpha by blast
    moreover have "qAbs xs x' X' $= qAbs xs x' Y'"
    using alphaX'Y' GOOD qAbs_preserves_alpha by blast
    moreover
    {have "qGoodAbs(qAbs xs x X)" using GOOD by simp
     hence "qGoodAbs(qAbs xs x Y)" using 2 alphaAbs_preserves_qGoodAbs by fastforce
    }
    ultimately have "qAbs xs x Y $= qAbs xs x' Y'"
    using assms xs alphaAbs_trans_twice by blast
    hence "alphaAbs_all_equal_or_qAFresh xs x Y xs x' Y'"
    using goodY goodY' alphaAbs_qAbs_iff_alphaAbs_all_equal_or_qAFresh by blast
    hence "(Y #[[y \<and> x]]_xs) #= (Y' #[[y \<and> x']]_xs)"
    unfolding alphaAbs_all_equal_or_qAFresh_def
    using yEqAFresh yEqAFresh' by auto
    moreover have "qGood (X #[[y \<and> x]]_xs)" using GOOD qSwap_preserves_qGood by auto
    ultimately show "(X #[[y \<and> x]]_xs) #= (X' #[[y \<and> x']]_xs)"
    using alphaXYyx alphaY'X'yx' alpha_trans_twice by blast
  qed
qed

corollary alphaAbs_qAbs_imp_all_equal_or_qFresh:
assumes "qGood X" and "(qAbs xs x X $= qAbs xs' x' X')"
shows
"(xs = xs' \<and>
  (\<forall> y. (y = x \<or> qFresh xs y X) \<and> (y = x' \<or> qFresh xs y X') \<longrightarrow>
        (X #[[y \<and> x]]_xs) #= (X' #[[y \<and> x']]_xs)))"
proof-
  have "alphaAbs_all_equal_or_qFresh xs x X xs' x' X'"
  using assms alphaAbs_qAbs_imp_alphaAbs_all_equal_or_qFresh by blast
  thus ?thesis unfolding alphaAbs_all_equal_or_qFresh_def .
qed

lemma alphaAbs_qAbs_iff_alphaAbs_all_equal_or_qFresh:
assumes "qGood X" and "qGood X'"
shows "(qAbs xs x X $= qAbs xs' x' X') =
       alphaAbs_all_equal_or_qFresh xs x X xs' x' X'"
proof-
  let ?Left = "(qAbs xs x X $= qAbs xs' x' X')"
  let ?Middle = "alphaAbs_all_equal_or_qAFresh xs x X xs' x' X'"
  let ?Right = "alphaAbs_all_equal_or_qFresh xs x X xs' x' X'"
  have "?Left \<Longrightarrow> ?Right"
  using assms alphaAbs_qAbs_imp_alphaAbs_all_equal_or_qFresh by blast
  moreover have "?Right \<Longrightarrow> ?Middle"
  using alphaAbs_all_equal_or_qFresh_imp_qAFresh by fastforce
  moreover have "?Middle ==> ?Left"
  using assms alphaAbs_qAbs_iff_alphaAbs_all_equal_or_qAFresh by blast
  ultimately show ?thesis by blast
qed

corollary alphaAbs_qAbs_iff_all_equal_or_qFresh:
assumes "qGood X" and "qGood X'"
shows "(qAbs xs x X $= qAbs xs' x' X') =
       (xs = xs' \<and>
        (\<forall> y. (y = x \<or> qFresh xs y X) \<and> (y = x' \<or> qFresh xs y X') \<longrightarrow>
              (X #[[y \<and> x]]_xs) #= (X' #[[y \<and> x']]_xs)))"
proof-
  have "(qAbs xs x X $= qAbs xs' x' X') =
        alphaAbs_all_equal_or_qFresh xs x X xs' x' X'"
  using assms alphaAbs_qAbs_iff_alphaAbs_all_equal_or_qFresh by blast
  thus ?thesis unfolding alphaAbs_all_equal_or_qFresh_def .
qed

lemma alphaAbs_qAbs_imp_alphaAbs_all_qFresh:
assumes "qGood X" and "qAbs xs x X $= qAbs xs' x' X'"
shows "alphaAbs_all_qFresh xs x X xs' x' X'"
proof-
  let ?Left = "(qAbs xs x X $= qAbs xs' x' X')"
  let ?Middle = "alphaAbs_all_equal_or_qFresh xs x X xs' x' X'"
  let ?Right = "alphaAbs_all_qFresh xs x X xs' x' X'"
  have "?Left \<Longrightarrow> ?Middle"
  using assms alphaAbs_qAbs_imp_alphaAbs_all_equal_or_qFresh by blast
  moreover have "?Middle \<Longrightarrow> ?Right"
  unfolding alphaAbs_all_equal_or_qFresh_def alphaAbs_all_qFresh_def by auto
  ultimately show ?thesis using assms by blast
qed

corollary alphaAbs_qAbs_imp_all_qFresh:
assumes "qGood X" and "(qAbs xs x X $= qAbs xs' x' X')"
shows
"(xs = xs' \<and>
  (\<forall> y. qFresh xs y X \<and> qFresh xs y X' \<longrightarrow>
        (X #[[y \<and> x]]_xs) #= (X' #[[y \<and> x']]_xs)))"
proof-
  have "alphaAbs_all_qFresh xs x X xs' x' X'"
  using assms alphaAbs_qAbs_imp_alphaAbs_all_qFresh by blast
  thus ?thesis unfolding alphaAbs_all_qFresh_def .
qed

lemma alphaAbs_qAbs_iff_alphaAbs_all_qFresh:
assumes "qGood X" and "qGood X'"
shows "(qAbs xs x X $= qAbs xs' x' X') =
       alphaAbs_all_qFresh xs x X xs' x' X'"
proof-
  let ?Left = "(qAbs xs x X $= qAbs xs' x' X')"
  let ?Middle = "alphaAbs_all_qAFresh xs x X xs' x' X'"
  let ?Right = "alphaAbs_all_qFresh xs x X xs' x' X'"
  have "?Left \<Longrightarrow> ?Right"
  using assms alphaAbs_qAbs_imp_alphaAbs_all_qFresh by blast
  moreover have "?Right \<Longrightarrow> ?Middle"
  using alphaAbs_all_qFresh_imp_qAFresh by fastforce
  moreover have "?Middle \<Longrightarrow> ?Left"
  using assms alphaAbs_qAbs_iff_alphaAbs_all_qAFresh by blast
  ultimately show ?thesis by blast
qed

corollary alphaAbs_qAbs_iff_all_qFresh:
assumes "qGood X" and "qGood X'"
shows "(qAbs xs x X $= qAbs xs' x' X') =
       (xs = xs' \<and>
        (\<forall> y. qFresh xs y X \<and> qFresh xs y X' \<longrightarrow>
              (X #[[y \<and> x]]_xs) #= (X' #[[y \<and> x']]_xs)))"
proof-
  have "(qAbs xs x X $= qAbs xs' x' X') =
        alphaAbs_all_qFresh xs x X xs' x' X'"
  using assms alphaAbs_qAbs_iff_alphaAbs_all_qFresh by blast
  thus ?thesis unfolding alphaAbs_all_qFresh_def .
qed

end  (* context FixVars *)

end
