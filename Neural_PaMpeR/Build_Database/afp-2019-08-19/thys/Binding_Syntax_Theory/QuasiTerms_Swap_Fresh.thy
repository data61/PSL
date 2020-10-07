section {* Quasi-Terms with Swapping and Freshness *}

theory QuasiTerms_Swap_Fresh imports Preliminaries 
begin

text{*
This section defines and studies the (totally free) datatype of quasi-terms
and the notions of freshness and
swapping variables for them.
``Quasi" refers to the fact that these items are not (yet) factored to alpha-equivalence.
 We shall later call ``terms" those alpha-equivalence classes.  *}

subsection {* The datatype of quasi-terms with bindings *}

datatype
('index,'bindex,'varSort,'var,'opSym)qTerm =
   qVar 'varSort 'var
  |qOp 'opSym "('index, (('index,'bindex,'varSort,'var,'opSym)qTerm))input"
              "('bindex, (('index,'bindex,'varSort,'var,'opSym)qAbs)) input"
and
('index,'bindex,'varSort,'var,'opSym)qAbs =
  qAbs 'varSort 'var "('index,'bindex,'varSort,'var,'opSym)qTerm"

text{* Above:
\begin{itemize}
\item ``Var" stands for ``variable injection"
\item ``Op" stands for ``operation"
\item ``opSym" stands for ``operation symbol"
\item ``q" stands for ``quasi"
\item ``Abs" stands for ``abstraction"
\end{itemize}

Thus, a quasi-term is either (an injection of) a variable, or an operation symbol applied
to a term-input and an abstraction-input
(where, for any type $T$, $T$-inputs are partial
maps from indexes to $T$. A quasi-abstraction is
essentially a pair (variable,quasi-term).
 *}

type_synonym ('index,'bindex,'varSort,'var,'opSym)qTermItem =
"('index,'bindex,'varSort,'var,'opSym)qTerm +
 ('index,'bindex,'varSort,'var,'opSym)qAbs"

abbreviation termIn ::
"('index,'bindex,'varSort,'var,'opSym)qTerm \<Rightarrow> ('index,'bindex,'varSort,'var,'opSym)qTermItem"
where "termIn X == Inl X"

abbreviation absIn ::
"('index,'bindex,'varSort,'var,'opSym)qAbs \<Rightarrow> ('index,'bindex,'varSort,'var,'opSym)qTermItem"
where "absIn A == Inr A"

subsection {* Induction principles *}

definition qTermLess :: "('index,'bindex,'varSort,'var,'opSym)qTermItem rel"
where
"qTermLess == {(termIn X, termIn(qOp delta inp binp))| X delta inp binp i. inp i = Some X} \<union>
              {(absIn A, termIn(qOp delta inp binp))| A delta inp binp i. binp i = Some A} \<union>
              {(termIn X, absIn (qAbs xs x X))| X xs x. True}"

text{* This induction will be used only temporarily, until we
   get a better one, involving swapping:  *}

lemma qTerm_rawInduct[case_names Var Op Abs]:
fixes X :: "('index,'bindex,'varSort,'var,'opSym)qTerm" and
      A :: "('index,'bindex,'varSort,'var,'opSym)qAbs" and phi phiAbs
assumes
  Var: "\<And> xs x. phi (qVar xs x)" and
  Op: "\<And> delta inp binp. \<lbrakk>liftAll phi inp; liftAll phiAbs binp\<rbrakk> \<Longrightarrow> phi (qOp delta inp binp)" and
  Abs: "\<And> xs x X. phi X \<Longrightarrow> phiAbs (qAbs xs x X)"
shows "phi X \<and> phiAbs A"
by (induct rule: qTerm_qAbs.induct)
   (fastforce intro!: Var Op Abs rangeI simp: liftAll_def)+

lemma qTermLess_wf: "wf qTermLess" 
unfolding wf_def proof safe
  fix chi item
  assume *: "\<forall>item. (\<forall>item'. (item', item) \<in> qTermLess \<longrightarrow> chi item') \<longrightarrow> chi item"
  show "chi item"
  proof-
    {fix X A
     have "chi (termIn X) \<and> chi (absIn A)"
     apply(induct rule: qTerm_rawInduct)
     using * unfolding qTermLess_def liftAll_def by blast+
    }
    thus ?thesis by(cases item) auto
  qed
qed

lemma qTermLessPlus_wf: "wf (qTermLess ^+)"
using qTermLess_wf wf_trancl by auto

text{* The skeleton of a quasi-term item -- this is the generalization
   of the size function from the case of finitary syntax.
   We use the skeleton later for proving correct various recursive function definitions, notably that of ``alpha". *}

function
qSkel :: "('index,'bindex,'varSort,'var,'opSym)qTerm \<Rightarrow> ('index,'bindex)tree"
and
qSkelAbs :: "('index,'bindex,'varSort,'var,'opSym)qAbs \<Rightarrow> ('index,'bindex)tree"
where
"qSkel (qVar xs x) = Branch (\<lambda>i. None) (\<lambda>i. None)"
|
"qSkel (qOp delta inp binp) = Branch (lift qSkel inp) (lift qSkelAbs binp)"
|
"qSkelAbs (qAbs xs x X) = Branch (\<lambda>i. Some(qSkel X)) (\<lambda>i. None)"
by(pat_completeness, auto)
termination by(relation qTermLess, simp add: qTermLess_wf, auto simp add: qTermLess_def)

text{* Next is a template for generating induction principles whenever we come up
  with relation on terms included in the kernel of the skeleton operator.  *}

lemma qTerm_templateInduct[case_names Var Op Abs]:
fixes X :: "('index,'bindex,'varSort,'var,'opSym)qTerm"
and A :: "('index,'bindex,'varSort,'var,'opSym)qAbs"
and phi phiAbs and rel
assumes
REL: "\<And> X Y. (X,Y) \<in> rel \<Longrightarrow> qSkel Y = qSkel X" and
Var: "\<And> xs x. phi (qVar xs x)" and
Op: "\<And> delta inp binp. \<lbrakk>liftAll phi inp; liftAll phiAbs binp\<rbrakk>
                       \<Longrightarrow> phi (qOp delta inp binp)" and
Abs: "\<And> xs x X. (\<And> Y. (X,Y) \<in> rel \<Longrightarrow> phi Y) \<Longrightarrow> phiAbs (qAbs xs x X)"
shows "phi X \<and> phiAbs A" 
proof-
  {fix T
   have "\<forall> X A. (T = qSkel X \<longrightarrow> phi X) \<and> (T = qSkelAbs A \<longrightarrow> phiAbs A)"
   proof(induct rule: treeLess_induct)
     case (1 T')
     show ?case apply safe  
      subgoal for X _ 
      using assms 1 unfolding treeLess_def liftAll_def 
      by (cases X) (auto simp add: lift_def, metis option.simps(5))
     subgoal for _ A apply (cases A)
     using assms 1 unfolding treeLess_def by simp .       
   qed
  }
  thus ?thesis by blast
qed

text{* A modification of the canonical immediate-subterm
relation on quasi-terms, that takes into account a relation assumed included in the skeleton kernel.  *}

definition qTermLess_modulo ::
"('index,'bindex,'varSort,'var,'opSym)qTerm rel \<Rightarrow>
 ('index,'bindex,'varSort,'var,'opSym)qTermItem rel"
where
"qTermLess_modulo rel ==
 {(termIn X, termIn(qOp delta inp binp))| X delta inp binp i. inp i = Some X} \<union>
 {(absIn A, termIn(qOp delta inp binp))| A delta inp binp j. binp j = Some A} \<union>
 {(termIn Y, absIn (qAbs xs x X))| X Y xs x. (X,Y) \<in> rel}"

lemma qTermLess_modulo_wf:
fixes rel::"('index,'bindex,'varSort,'var,'opSym)qTerm rel"
assumes "\<And> X Y. (X,Y) \<in> rel \<Longrightarrow> qSkel Y = qSkel X"
shows "wf (qTermLess_modulo rel)"
proof(unfold wf_def, auto)
  fix chi item
  assume *:
  "\<forall>item. (\<forall>item'. (item', item) \<in> qTermLess_modulo rel  \<longrightarrow> chi item')
           \<longrightarrow> chi item"
  show "chi item"
  proof-
    obtain phi where phi_def: "phi = (\<lambda> X. chi (termIn X))" by blast
    obtain phiAbs where phiAbs_def: "phiAbs = (\<lambda> A. chi (absIn A))" by blast
    {fix X A
     have "chi (termIn X) \<and> chi (absIn A)"
     apply(induct rule: qTerm_templateInduct[of rel])
     using * assms unfolding qTermLess_modulo_def liftAll_def by blast+
    }
    thus ?thesis unfolding phi_def phiAbs_def
    by(cases item, auto)
  qed
qed

subsection {* Swap and substitution on variables  *}

definition sw :: "'varSort \<Rightarrow> 'var \<Rightarrow> 'var \<Rightarrow> 'varSort \<Rightarrow> 'var \<Rightarrow> 'var"
where
"sw ys y1 y2 xs x ==
 if ys = xs then if x = y1 then y2
            else if x = y2 then y1
                           else x
 else x"

abbreviation sw_abbrev :: "'var \<Rightarrow> 'varSort \<Rightarrow> 'var \<Rightarrow> 'var \<Rightarrow> 'varSort \<Rightarrow> 'var"
("_ @_[_ \<and> _]'__" 200)
where "(x @xs[y1 \<and> y2]_ys) == sw ys y1 y2 xs x"

definition sb :: "'varSort \<Rightarrow> 'var \<Rightarrow> 'var \<Rightarrow> 'varSort \<Rightarrow> 'var \<Rightarrow> 'var"
where
"sb ys y1 y2 xs x ==
 if ys = xs then if x = y2 then y1
                           else x
 else x"

abbreviation sb_abbrev :: "'var \<Rightarrow> 'varSort \<Rightarrow> 'var \<Rightarrow> 'var \<Rightarrow> 'varSort \<Rightarrow> 'var"
("_ @_[_ '/ _]'__" 200)
where "(x @xs[y1 / y2]_ys) == sb ys y1 y2 xs x"

theorem sw_simps1[simp]: "(x @xs[x \<and> y]_xs) = y"
unfolding sw_def by simp

theorem sw_simps2[simp]: "(x @xs[y \<and> x]_xs) = y"
unfolding sw_def by simp

theorem sw_simps3[simp]:
"(zs \<noteq> xs \<or> x \<notin> {z1,z2}) \<Longrightarrow> (x @xs[z1 \<and> z2]_zs) = x"
unfolding sw_def by simp

lemmas sw_simps = sw_simps1 sw_simps2 sw_simps3

theorem sw_ident[simp]: "(x @xs[y \<and> y]_ys) = x"
unfolding sw_def by auto

theorem sw_compose:
"((z @zs[x \<and> y]_xs) @zs[x' \<and> y']_xs') =
 ((z @zs[x' \<and> y']_xs') @zs[(x @xs[x' \<and> y']_xs') \<and> (y @xs[x' \<and> y']_xs')]_xs)"
by(unfold sw_def, auto)

theorem sw_commute:
assumes "zs \<noteq> zs' \<or> {x,y} Int {x',y'} = {}"
shows "((u @us[x \<and> y]_zs) @us[x' \<and> y']_zs') = ((u @us[x' \<and> y']_zs') @us[x \<and> y]_zs)"
using assms by(unfold sw_def, auto)

theorem sw_involutive[simp]:
"((z @zs[x \<and> y]_xs) @zs[x \<and> y]_xs) = z"
by(unfold sw_def, auto)

theorem sw_inj[simp]:
"((z @zs[x \<and> y]_xs) = (z' @zs[x \<and> y]_xs)) = (z = z')"
by (simp add: sw_def) 

lemma sw_preserves_mship[simp]:
assumes "{y1,y2} \<subseteq> Var ys"
shows "((x @xs[y1 \<and> y2]_ys) \<in> Var xs) = (x \<in> Var xs)"
using assms unfolding sw_def by auto

theorem sw_sym:
"(z @zs[x \<and> y]_xs) = (z @zs[y \<and> x]_xs)"
by (unfold sw_def) auto

theorem sw_involutive2[simp]:
"((z @zs[x \<and> y]_xs) @zs[y \<and> x]_xs) = z"
by (unfold sw_def) auto

theorem sw_trans:
"us \<noteq> zs \<or> u \<notin> {y,z} \<Longrightarrow>
 ((u @us[y \<and> x]_zs) @us[z \<and> y]_zs) = (u @us[z \<and> x]_zs)"
by (unfold sw_def) auto

lemmas sw_otherSimps =
sw_ident sw_involutive sw_inj sw_preserves_mship sw_involutive2

theorem sb_simps1[simp]: "(x @xs[y / x]_xs) = y"
unfolding sb_def by simp

theorem sb_simps2[simp]:
"(zs \<noteq> xs \<or> z2 \<noteq> x) \<Longrightarrow> (x @xs[z1 / z2]_zs) = x"
unfolding sb_def by auto

lemmas sb_simps = sb_simps1 sb_simps2

theorem sb_ident[simp]: "(x @xs[y / y]_ys) = x"
unfolding sb_def by auto

theorem sb_compose1:
"((z @zs[y1 / x]_xs) @zs[y2 / x]_xs) = (z @zs[(y1 @xs[y2 / x]_xs) / x]_xs)"
by(unfold sb_def, auto)

theorem sb_compose2:
"ys \<noteq> xs \<or> (x2 \<notin> {y1,y2}) \<Longrightarrow>
 ((z @zs[x1 / x2]_xs) @zs[y1 / y2]_ys) =
 ((z @zs[y1 / y2]_ys) @zs[(x1 @xs[y1 / y2]_ys) / x2]_xs)"
by (unfold sb_def) auto

theorem sb_commute:
assumes "zs \<noteq> zs' \<or> {x,y} Int {x',y'} = {}"
shows "((u @us[x / y]_zs) @us[x' / y']_zs') = ((u @us[x' / y']_zs') @us[x / y]_zs)"
using assms by (unfold sb_def) auto

theorem sb_idem[simp]:
"((z @zs[x / y]_xs) @zs[x / y]_xs) = (z @zs[x / y]_xs)"
by (unfold sb_def) auto

lemma sb_preserves_mship[simp]:
assumes "{y1,y2} \<subseteq> Var ys"
shows "((x @xs[y1 / y2]_ys) \<in> Var xs) = (x \<in> Var xs)"
using assms by (unfold sb_def) auto

theorem sb_trans:
"us \<noteq> zs \<or> u \<noteq> y \<Longrightarrow>
 ((u @us[y / x]_zs) @us[z / y]_zs) = (u @us[z / x]_zs)"
by (unfold sb_def) auto

lemmas sb_otherSimps =
sb_ident sb_idem sb_preserves_mship

subsection {* The swapping and freshness operators *}

text {* For establishing the preliminary results quickly, we use both the notion of
binding-sensitive freshness (operator ``qFresh")
       and that of ``absolute" freshness, ignoring bindings (operator ``qAFresh").  Later,
       for alpha-equivalence classes, ``qAFresh" will not make sense.  *}

definition
aux_qSwap_ignoreFirst3 ::
"'varSort * 'var * 'var * ('index,'bindex,'varSort,'var,'opSym)qTerm +
 'varSort * 'var * 'var * ('index,'bindex,'varSort,'var,'opSym)qAbs \<Rightarrow>
 ('index,'bindex,'varSort,'var,'opSym)qTermItem"
where
"aux_qSwap_ignoreFirst3 K =
 (case K of Inl(zs,x,y,X) \<Rightarrow> termIn X
           |Inr(zs,x,y,A) \<Rightarrow> absIn A)"

lemma qTermLess_ingoreFirst3_wf:
"wf(inv_image qTermLess aux_qSwap_ignoreFirst3)"
using qTermLess_wf wf_inv_image by auto

function
qSwap :: "'varSort \<Rightarrow> 'var \<Rightarrow> 'var \<Rightarrow> ('index,'bindex,'varSort,'var,'opSym)qTerm \<Rightarrow>
          ('index,'bindex,'varSort,'var,'opSym)qTerm"
and
qSwapAbs :: "'varSort \<Rightarrow> 'var \<Rightarrow> 'var \<Rightarrow> ('index,'bindex,'varSort,'var,'opSym)qAbs \<Rightarrow>
             ('index,'bindex,'varSort,'var,'opSym)qAbs"
where
"qSwap zs x y (qVar zs' z) = qVar zs' (z @zs'[x \<and> y]_zs)"
|
"qSwap zs x y (qOp delta inp binp) =
 qOp delta (lift (qSwap zs x y) inp) (lift (qSwapAbs zs x y) binp)"
|
"qSwapAbs zs x y (qAbs zs' z X) = qAbs zs' (z @zs'[x \<and> y]_zs) (qSwap zs x y X)"
by(pat_completeness, auto)
termination
by(relation "inv_image qTermLess aux_qSwap_ignoreFirst3",
   simp add: qTermLess_ingoreFirst3_wf,
   auto simp add: qTermLess_def aux_qSwap_ignoreFirst3_def)

lemmas qSwapAll_simps = qSwap.simps qSwapAbs.simps

abbreviation qSwap_abbrev ::
  "('index,'bindex,'varSort,'var,'opSym)qTerm \<Rightarrow> 'var \<Rightarrow> 'var \<Rightarrow> 'varSort \<Rightarrow>
   ('index,'bindex,'varSort,'var,'opSym)qTerm" ("_ #[[_ \<and> _]]'__" 200)
where "(X #[[z1 \<and> z2]]_zs) == qSwap zs z1 z2 X"

abbreviation qSwapAbs_abbrev ::
  "('index,'bindex,'varSort,'var,'opSym)qAbs \<Rightarrow> 'var \<Rightarrow> 'var \<Rightarrow> 'varSort \<Rightarrow>
   ('index,'bindex,'varSort,'var,'opSym)qAbs" ("_ $[[_ \<and> _]]'__" 200)
where "(A $[[z1 \<and> z2]]_zs) == qSwapAbs zs z1 z2 A"

definition
aux_qFresh_ignoreFirst2 ::
"'varSort * 'var * ('index,'bindex,'varSort,'var,'opSym)qTerm +
 'varSort * 'var * ('index,'bindex,'varSort,'var,'opSym)qAbs \<Rightarrow>
 ('index,'bindex,'varSort,'var,'opSym)qTermItem"
where
"aux_qFresh_ignoreFirst2 K =
 (case K of Inl(zs,x,X) \<Rightarrow> termIn X
           |Inr (zs,x,A) \<Rightarrow> absIn A)"

lemma qTermLess_ingoreFirst2_wf: "wf(inv_image qTermLess aux_qFresh_ignoreFirst2)"
using qTermLess_wf wf_inv_image by auto

text{* The quasi absolutely-fresh predicate:
  (note that this is not an oxymoron: ``quasi" refers
   to being an operator on quasi-terms, and not on
terms, i.e., on alpha-equivalence  classes;
   ``absolutely'' refers to not ignoring bindings in the notion of freshness,
and thus counting absolutely all the variables. *}

function
qAFresh :: "'varSort \<Rightarrow> 'var \<Rightarrow> ('index,'bindex,'varSort,'var,'opSym)qTerm \<Rightarrow> bool"
and
qAFreshAbs :: "'varSort \<Rightarrow> 'var \<Rightarrow> ('index,'bindex,'varSort,'var,'opSym)qAbs \<Rightarrow> bool"
where
"qAFresh xs x (qVar ys y) = (xs \<noteq> ys \<or> x \<noteq> y)"
|
"qAFresh xs x (qOp delta inp binp) =
 (liftAll (qAFresh xs x) inp \<and> liftAll (qAFreshAbs xs x) binp)"
|
"qAFreshAbs xs x (qAbs ys y X) = ((xs \<noteq> ys \<or> x \<noteq> y) \<and> qAFresh xs x X)"
by(pat_completeness, auto)
termination
by(relation "inv_image qTermLess aux_qFresh_ignoreFirst2",
   simp add: qTermLess_ingoreFirst2_wf,
   auto simp add: qTermLess_def aux_qFresh_ignoreFirst2_def)

lemmas qAFreshAll_simps = qAFresh.simps qAFreshAbs.simps

text{* The next is standard freshness -- note that its definition differs from that
of absolute freshness only at the clause for abstractions.  *}

function
qFresh :: "'varSort \<Rightarrow> 'var \<Rightarrow> ('index,'bindex,'varSort,'var,'opSym)qTerm \<Rightarrow> bool"
and
qFreshAbs :: "'varSort \<Rightarrow> 'var \<Rightarrow> ('index,'bindex,'varSort,'var,'opSym)qAbs \<Rightarrow> bool"
where
"qFresh xs x (qVar ys y) = (xs \<noteq> ys \<or> x \<noteq> y)"
|
"qFresh xs x (qOp delta inp binp) =
 (liftAll (qFresh xs x) inp \<and> liftAll (qFreshAbs xs x) binp)"
|
"qFreshAbs xs x (qAbs ys y X) = ((xs = ys \<and> x = y) \<or> qFresh xs x X)"
by(pat_completeness, auto)
termination
by(relation "inv_image qTermLess aux_qFresh_ignoreFirst2",
   simp add: qTermLess_ingoreFirst2_wf,
   auto simp add: qTermLess_def aux_qFresh_ignoreFirst2_def)

lemmas qFreshAll_simps = qFresh.simps qFreshAbs.simps

subsection {* Compositional properties of swapping  *}

lemma qSwapAll_ident:
fixes X::"('index,'bindex,'varSort,'var,'opSym)qTerm" and
      A::"('index,'bindex,'varSort,'var,'opSym)qAbs"
    shows "(X #[[x \<and> x]]_zs) = X \<and> (A $[[x \<and> x]]_zs) = A"
  by (induct rule: qTerm_rawInduct)
     (auto simp add: liftAll_def lift_cong lift_ident)

corollary qSwap_ident[simp]: "(X #[[x \<and> x]]_zs) = X"
by(simp add: qSwapAll_ident)

lemma qSwapAll_compose:
fixes X::"('index,'bindex,'varSort,'var,'opSym)qTerm"  and
      A::"('index,'bindex,'varSort,'var,'opSym)qAbs" and zs x y x' y'
shows
"((X #[[x \<and> y]]_zs) #[[x' \<and> y']]_zs') =
 ((X #[[x' \<and> y']]_zs') #[[(x @zs[x' \<and> y']_zs') \<and> (y @zs[x' \<and> y']_zs')]]_zs)
\<and>
 ((A $[[x \<and> y]]_zs) $[[x' \<and> y']]_zs') =
 ((A $[[x' \<and> y']]_zs') $[[(x @zs[x' \<and> y']_zs') \<and> (y @zs[x' \<and> y']_zs')]]_zs)"
proof(induct rule: qTerm_rawInduct[of _ _ X A])
  case (Op delta inp binp)
  then show ?case by (auto intro!: lift_cong simp: liftAll_def lift_comp)
qed (auto simp add: sw_def sw_compose)
  
corollary qSwap_compose:
"((X #[[x \<and> y]]_zs) #[[x' \<and> y']]_zs') =
 ((X #[[x' \<and> y']]_zs') #[[(x @zs[x' \<and> y']_zs') \<and> (y @zs[x' \<and> y']_zs')]]_zs)"
by (meson qSwapAll_compose)

lemma qSwap_commute:
assumes "zs \<noteq> zs' \<or> {x,y} Int {x',y'} = {}"
shows "((X #[[x \<and> y]]_zs) #[[x' \<and> y']]_zs') = ((X #[[x' \<and> y']]_zs') #[[x \<and> y]]_zs)"
by (metis assms disjoint_insert(1) qSwapAll_compose sw_simps3)

lemma qSwapAll_involutive:
fixes X::"('index,'bindex,'varSort,'var,'opSym)qTerm" and
      A::"('index,'bindex,'varSort,'var,'opSym)qAbs" and zs x y
shows "((X #[[x \<and> y]]_zs) #[[x \<and> y]]_zs) = X \<and>
       ((A $[[x \<and> y]]_zs) $[[x \<and> y]]_zs) = A"
proof(induct rule: qTerm_rawInduct[of _ _ X A])
  case (Op delta inp binp)
  then show ?case 
    unfolding qSwapAll_simps(2) liftAll_lift_ext
    lift_comp o_def
    by (simp add: lift_ident)
qed(auto)
  

corollary qSwap_involutive[simp]:
"((X #[[x \<and> y]]_zs) #[[x \<and> y]]_zs) = X"
by(simp add: qSwapAll_involutive)

lemma qSwapAll_sym:
fixes X::"('index,'bindex,'varSort,'var,'opSym)qTerm" and
      A::"('index,'bindex,'varSort,'var,'opSym)qAbs" and zs x y
shows "(X #[[x \<and> y]]_zs) = (X #[[y \<and> x]]_zs) \<and>
       (A $[[x \<and> y]]_zs) = (A $[[y \<and> x]]_zs)"
by (induct rule: qTerm_rawInduct[of _ _ X A])  
   (auto simp: sw_sym lift_comp liftAll_lift_ext)

corollary qSwap_sym:
"(X #[[x \<and> y]]_zs) = (X #[[y \<and> x]]_zs)"
by(simp add: qSwapAll_sym)

lemma qAFreshAll_qSwapAll_id:
fixes X::"('index,'bindex,'varSort,'var,'opSym)qTerm" and
      A::"('index,'bindex,'varSort,'var,'opSym)qAbs" and zs z1 z2
shows "(qAFresh zs z1 X \<and> qAFresh zs z2 X  \<longrightarrow> (X #[[z1 \<and> z2]]_zs) = X) \<and>
       (qAFreshAbs zs z1 A \<and> qAFreshAbs zs z2 A  \<longrightarrow> (A $[[z1 \<and> z2]]_zs) = A)"
by (induct rule: qTerm_rawInduct[of _ _ X A])
   (auto intro!: ext simp: liftAll_def lift_def option.case_eq_if)

corollary qAFresh_qSwap_id[simp]:
"\<lbrakk>qAFresh zs z1 X; qAFresh zs z2 X\<rbrakk>  \<Longrightarrow> (X #[[z1 \<and> z2]]_zs) = X"
by(simp add: qAFreshAll_qSwapAll_id)

lemma qAFreshAll_qSwapAll_compose:
fixes X::"('index,'bindex,'varSort,'var,'opSym)qTerm" and
      A::"('index,'bindex,'varSort,'var,'opSym)qAbs"and zs x y z
shows  "(qAFresh zs y X \<and> qAFresh zs z X \<longrightarrow>
         ((X #[[y \<and> x]]_zs) #[[z \<and> y]]_zs) = (X #[[z \<and> x]]_zs)) \<and>
        (qAFreshAbs zs y A \<and> qAFreshAbs zs z A \<longrightarrow>
         ((A $[[y \<and> x]]_zs) $[[z \<and> y]]_zs) = (A $[[z \<and> x]]_zs))"
by (induct rule: qTerm_rawInduct[of _ _ X A])
   (auto intro!: ext simp: sw_trans lift_comp lift_def liftAll_def option.case_eq_if)
   
corollary qAFresh_qSwap_compose:
"\<lbrakk>qAFresh zs y X; qAFresh zs z X\<rbrakk> \<Longrightarrow>
 ((X #[[y \<and> x]]_zs) #[[z \<and> y]]_zs) = (X #[[z \<and> x]]_zs)"
by(simp add: qAFreshAll_qSwapAll_compose)

subsection {* Induction and well-foundedness modulo swapping  *}

lemma qSkel_qSwapAll:
fixes  X::"('index,'bindex,'varSort,'var,'opSym)qTerm" and
       A::"('index,'bindex,'varSort,'var,'opSym)qAbs" and x y zs
shows "qSkel(X #[[x \<and> y]]_zs) = qSkel X \<and>
       qSkelAbs(A $[[x \<and> y]]_zs) = qSkelAbs A"
proof(induct rule: qTerm_rawInduct[of _ _ X A])
  case (Op delta inp binp)
  then show ?case 
    unfolding qSwapAll_simps(2) liftAll_lift_ext qSkel.simps(2)
    lift_comp comp_apply by simp
qed auto

corollary qSkel_qSwap: "qSkel(X #[[x \<and> y]]_zs) = qSkel X"
by(simp add: qSkel_qSwapAll)

text{*
  For induction modulo swapping, one may wish to swap not just once,
   but several times at the
   induction hypothesis (an example of this will be the proof of compatibility
   of ``qSwap" with alpha) -- for this, we introduce the following relation
  (the suffix ``Raw" signifies the fact that the involved variables are
  not required to be well-sorted):   *}

inductive_set qSwapped :: "('index,'bindex,'varSort,'var,'opSym)qTerm rel"
where
Refl: "(X,X) \<in> qSwapped"
|
Trans: "\<lbrakk>(X,Y) \<in> qSwapped; (Y,Z) \<in> qSwapped\<rbrakk> \<Longrightarrow> (X,Z) \<in> qSwapped"
|
Swap: "(X,Y) \<in> qSwapped \<Longrightarrow> (X, Y #[[x \<and> y]]_zs) \<in> qSwapped"

lemmas qSwapped_Clauses = qSwapped.Refl qSwapped.Trans qSwapped.Swap

lemma qSwap_qSwapped: "(X, X #[[x \<and> y]]_zs): qSwapped"
by (auto simp add: qSwapped_Clauses)

lemma qSwapped_qSkel:
"(X,Y) \<in> qSwapped  \<Longrightarrow> qSkel Y = qSkel X"
by(erule qSwapped.induct, auto simp add: qSkel_qSwap)

text{* The following is henceforth our main induction principle for quasi-terms.  At the
 clause for abstractions, the user may choose among the two
 induction hypotheses (IHs):
 \\-(1) IH for all swapped terms
 \\-(2) IH for all terms with the same skeleton.

The user may choose only one of the above, and ignore the others, but may of course also
assume both.  (2) is stronger than (1),
but we offer both of them for convenience in proofs.
Most of the times, (1) will be the most convenient. *}

lemma qTerm_induct[case_names Var Op Abs]:
fixes X :: "('index,'bindex,'varSort,'var,'opSym)qTerm"
and A :: "('index,'bindex,'varSort,'var,'opSym)qAbs"  and phi phiAbs
assumes
  Var: "\<And> xs x. phi (qVar xs x)" and
  Op: "\<And> delta inp binp. \<lbrakk>liftAll phi inp; liftAll phiAbs binp\<rbrakk>
                         \<Longrightarrow> phi (qOp delta inp binp)" and
  Abs: "\<And> xs x X. \<lbrakk>\<And> Y. (X,Y) \<in> qSwapped \<Longrightarrow> phi Y;
                    \<And> Y. qSkel Y = qSkel X \<Longrightarrow> phi Y\<rbrakk>
                    \<Longrightarrow> phiAbs (qAbs xs x X)"
shows "phi X \<and> phiAbs A"
  by (induct rule: qTerm_templateInduct[of "qSwapped \<union> {(X,Y). qSkel Y = qSkel X}"], 
      auto simp add: qSwapped_qSkel assms)


text{* The following relation will be needed for proving alpha-equivalence well-defined: *}

definition qTermQSwappedLess :: "('index,'bindex,'varSort,'var,'opSym)qTermItem rel"
where "qTermQSwappedLess = qTermLess_modulo qSwapped"

lemma qTermQSwappedLess_wf: "wf qTermQSwappedLess"
unfolding qTermQSwappedLess_def
using qSwapped_qSkel qTermLess_modulo_wf[of qSwapped] by blast


subsection{* More properties connecting swapping and freshness *}

lemma qSwap_3commute:
assumes *: "qAFresh ys y X" and **: "qAFresh ys y0 X"
and ***: "ys \<noteq> zs \<or> y0 \<notin> {z1,z2}"
shows "((X #[[z1 \<and> z2]]_zs) #[[y0 \<and> x @ys[z1 \<and> z2]_zs]]_ys) =
       (((X #[[y \<and> x]]_ys) #[[y0 \<and> y]]_ys) #[[z1 \<and> z2]]_zs)"
proof-
  have "y0 = (y0 @ys[z1 \<and> z2]_zs)" using *** unfolding sw_def by auto
  hence "((X #[[z1 \<and> z2]]_zs) #[[y0 \<and> x @ys[z1 \<and> z2]_zs]]_ys) =
         ((X #[[y0 \<and> x]]_ys) #[[z1 \<and> z2]]_zs)"
  by(simp add: qSwap_compose[of _ z1])
  also have "((X #[[y0 \<and> x]]_ys) #[[z1 \<and> z2]]_zs) =
             (((X #[[y \<and> x]]_ys) #[[y0 \<and> y]]_ys) #[[z1 \<and> z2]]_zs)"
  using * ** by (simp add: qAFresh_qSwap_compose)
  finally show ?thesis .
qed

lemma qAFreshAll_imp_qFreshAll:
fixes X::"('index,'bindex,'varSort,'var,'opSym)qTerm" and
      A::"('index,'bindex,'varSort,'var,'opSym)qAbs" and xs x
shows "(qAFresh xs x X \<longrightarrow> qFresh xs x X) \<and>
       (qAFreshAbs xs x A \<longrightarrow> qFreshAbs xs x A)"
by(induct rule: qTerm_rawInduct, auto simp add: liftAll_def)

corollary qAFresh_imp_qFresh:
"qAFresh xs x X \<Longrightarrow> qFresh xs x X"
by(simp add: qAFreshAll_imp_qFreshAll)

lemma qSwapAll_preserves_qAFreshAll:
fixes X::"('index,'bindex,'varSort,'var,'opSym)qTerm" and
      A::"('index,'bindex,'varSort,'var,'opSym)qAbs" and ys y zs z1 z2
shows
"(qAFresh ys (y @ys[z1 \<and> z2]_zs) (X #[[z1 \<and> z2]]_zs) = qAFresh ys y X) \<and>
 (qAFreshAbs ys (y @ys[z1 \<and> z2]_zs) (A $[[z1 \<and> z2]]_zs) = qAFreshAbs ys y A)"
proof(induct rule: qTerm_rawInduct[of _ _ X A])
  case (Op delta inp binp)
  then show ?case 
    unfolding qAFreshAll_simps(2) qSwapAll_simps(2) liftAll_lift_comp o_def 
    unfolding liftAll_def by presburger
qed(auto simp add: sw_def)

corollary qSwap_preserves_qAFresh[simp]:
"(qAFresh ys (y @ys[z1 \<and> z2]_zs) (X #[[z1 \<and> z2]]_zs) = qAFresh ys y X)"
by(simp add: qSwapAll_preserves_qAFreshAll)

lemma qSwap_preserves_qAFresh_distinct:
assumes "ys \<noteq> zs \<or> y \<notin> {z1,z2}"
shows "qAFresh ys y (X #[[z1 \<and> z2]]_zs) = qAFresh ys y X"
proof-
  have "y = (y @ys[z1 \<and> z2]_zs)" using assms unfolding sw_def by auto
  thus ?thesis using qSwap_preserves_qAFresh[of ys zs z1 z2 y] by auto
qed

lemma qAFresh_qSwap_exchange1:
"qAFresh zs z2 (X #[[z1 \<and> z2]]_zs) = qAFresh zs z1 X"
proof-
  have "z2 = (z1 @zs[z1 \<and> z2]_zs)" unfolding sw_def by auto
  thus ?thesis using qSwap_preserves_qAFresh[of zs zs z1 z2 z1 X] by auto
qed

lemma qAFresh_qSwap_exchange2:
"qAFresh zs z2 (X #[[z2 \<and> z1]]_zs) = qAFresh zs z1 X"
by(auto simp add: qAFresh_qSwap_exchange1 qSwap_sym)

lemma qSwapAll_preserves_qFreshAll:
fixes X::"('index,'bindex,'varSort,'var,'opSym)qTerm" and
      A::"('index,'bindex,'varSort,'var,'opSym)qAbs" and ys y zs z1 z2
shows
"(qFresh ys (y @ys[z1 \<and> z2]_zs) (X #[[z1 \<and> z2]]_zs) = qFresh ys y X) \<and>
 (qFreshAbs ys (y @ys[z1 \<and> z2]_zs) (A $[[z1 \<and> z2]]_zs) = qFreshAbs ys y A)"
proof(induct rule: qTerm_rawInduct[of _ _ X A])
  case (Op delta inp binp)
  then show ?case 
   unfolding qFreshAll_simps(2) qSwapAll_simps(2) liftAll_lift_comp o_def 
   unfolding liftAll_def by presburger
qed (auto simp add: sw_def)

corollary qSwap_preserves_qFresh:
"(qFresh ys (y @ys[z1 \<and> z2]_zs) (X #[[z1 \<and> z2]]_zs) = qFresh ys y X)"
by(simp add: qSwapAll_preserves_qFreshAll)

lemma qSwap_preserves_qFresh_distinct:
assumes "ys \<noteq> zs \<or> y \<notin> {z1,z2}"
shows "qFresh ys y (X #[[z1 \<and> z2]]_zs) = qFresh ys y X"
proof-
  have "y = (y @ys[z1 \<and> z2]_zs)" using assms unfolding sw_def by auto
  thus ?thesis using qSwap_preserves_qFresh[of ys zs z1 z2 y] by auto
qed

lemma qFresh_qSwap_exchange1:
"qFresh zs z2 (X #[[z1 \<and> z2]]_zs) = qFresh zs z1 X"
proof-
  have "z2 = (z1 @zs[z1 \<and> z2]_zs)" unfolding sw_def by auto
  thus ?thesis using qSwap_preserves_qFresh[of zs zs z1 z2 z1 X] by auto
qed

lemma qFresh_qSwap_exchange2:
"qFresh zs z1 X = qFresh zs z2 (X #[[z2 \<and> z1]]_zs)"
by (auto simp add: qFresh_qSwap_exchange1 qSwap_sym)

lemmas qSwap_qAFresh_otherSimps =
qSwap_ident qSwap_involutive qAFresh_qSwap_id qSwap_preserves_qAFresh

end
