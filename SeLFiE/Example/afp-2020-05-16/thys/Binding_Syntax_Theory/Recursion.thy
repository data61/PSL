section {* General Recursion *}

theory Recursion imports Iteration 
begin

text{* The initiality theorems from the previous section support iteration principles.
Next we extend the results to general recursion.  The difference between
general recursion and iteration is that the former also considers
the (source) ``items" (terms and abstractions), and not only the
(target) generalized items, appear in the recursive clauses.

(Here is an example illustrating the above difference for the standard case
of natural numbers:
\\- Given a number n, the operator ``add-n" can be defined by iteration:
\\--- ``add-n 0 = n",
\\--- ``add-n (Suc m) = Suc (add-n m)".

Notice that, in right-hand side of the recursive clause, ``m" is not used ``directly", but only
via ``add-n" -- this makes the definition iterative. By contrast, the following
definition of predecessor is trivial form of recursion (namely, case analysis),
but is {\em not} iteration:
\\--- ``pred 0 = 0",
\\--- ``pred (Suc n) = n".
)

We achieve our desired extension by augmenting the notion of model
and then essentially inferring recursion (as customary)
from
[iteration having as target the product between the term model and the original model].

As a matter of notation: remember we are using for generalized items
the same meta-variables as for ``items" (terms and abstractions).
But now the model operators will take both items and generalized items.
We shall prime the meta-variables for items (as in X', A', etc).
 *}

subsection {* Raw models  *}

record ('index,'bindex,'varSort,'sort,'opSym,'var,'gTerm,'gAbs)model =
  gWls :: "'sort \<Rightarrow> 'gTerm \<Rightarrow> bool"
  gWlsAbs :: "'varSort \<times> 'sort \<Rightarrow> 'gAbs \<Rightarrow> bool"
  (*  *)
  gVar :: "'varSort \<Rightarrow> 'var \<Rightarrow> 'gTerm"
  gAbs ::
  "'varSort \<Rightarrow> 'var \<Rightarrow>
   ('index,'bindex,'varSort,'var,'opSym)term \<Rightarrow> 'gTerm \<Rightarrow>
   'gAbs"
  gOp ::
  "'opSym \<Rightarrow>
   ('index,('index,'bindex,'varSort,'var,'opSym)term)input \<Rightarrow> ('index,'gTerm)input \<Rightarrow>
   ('bindex,('index,'bindex,'varSort,'var,'opSym)abs)input \<Rightarrow> ('bindex,'gAbs)input \<Rightarrow>
   'gTerm"
  (*  *)
  gFresh ::
  "'varSort \<Rightarrow> 'var \<Rightarrow> ('index,'bindex,'varSort,'var,'opSym)term \<Rightarrow> 'gTerm \<Rightarrow> bool"
  gFreshAbs ::
  "'varSort \<Rightarrow> 'var \<Rightarrow> ('index,'bindex,'varSort,'var,'opSym)abs \<Rightarrow> 'gAbs \<Rightarrow> bool"
  (*  *)
  gSwap ::
  "'varSort \<Rightarrow> 'var \<Rightarrow> 'var \<Rightarrow>
   ('index,'bindex,'varSort,'var,'opSym)term \<Rightarrow> 'gTerm \<Rightarrow>
   'gTerm"
  gSwapAbs ::
  "'varSort \<Rightarrow> 'var \<Rightarrow> 'var \<Rightarrow>
   ('index,'bindex,'varSort,'var,'opSym)abs \<Rightarrow> 'gAbs \<Rightarrow>
   'gAbs"
  (*   *)
  gSubst ::
  "'varSort \<Rightarrow>
   ('index,'bindex,'varSort,'var,'opSym)term \<Rightarrow> 'gTerm \<Rightarrow>
   'var \<Rightarrow>
   ('index,'bindex,'varSort,'var,'opSym)term \<Rightarrow> 'gTerm \<Rightarrow>
   'gTerm"
  gSubstAbs ::
  "'varSort \<Rightarrow>
   ('index,'bindex,'varSort,'var,'opSym)term \<Rightarrow> 'gTerm \<Rightarrow>
   'var \<Rightarrow>
   ('index,'bindex,'varSort,'var,'opSym)abs \<Rightarrow> 'gAbs \<Rightarrow>
   'gAbs"

subsection {* Well-sorted models of various kinds *}

text{*  Lifting the model operations to inputs *}

definition gFreshInp where
"gFreshInp MOD ys y inp' inp \<equiv> liftAll2 (gFresh MOD ys y) inp' inp"

definition gFreshBinp where
"gFreshBinp MOD ys y binp' binp \<equiv> liftAll2 (gFreshAbs MOD ys y) binp' binp"

definition gSwapInp where
"gSwapInp MOD zs z1 z2 inp' inp \<equiv> lift2 (gSwap MOD zs z1 z2) inp' inp"

definition gSwapBinp where
"gSwapBinp MOD zs z1 z2 binp' binp \<equiv> lift2 (gSwapAbs MOD zs z1 z2) binp' binp"

definition gSubstInp where
"gSubstInp MOD ys Y' Y y inp' inp \<equiv> lift2 (gSubst MOD ys Y' Y y) inp' inp"

definition gSubstBinp where
"gSubstBinp MOD ys Y' Y y binp' binp \<equiv> lift2 (gSubstAbs MOD ys Y' Y y) binp' binp"

(* *************************************************** *)
context FixSyn
begin

definition gWlsInp where
"gWlsInp MOD delta inp \<equiv>
 wlsOpS delta \<and> sameDom (arOf delta) inp \<and> liftAll2 (gWls MOD) (arOf delta) inp"

lemmas gWlsInp_defs = gWlsInp_def sameDom_def liftAll2_def

definition gWlsBinp where
"gWlsBinp MOD delta binp \<equiv>
 wlsOpS delta \<and> sameDom (barOf delta) binp \<and> liftAll2 (gWlsAbs MOD) (barOf delta) binp"

lemmas gWlsBinp_defs = gWlsBinp_def sameDom_def liftAll2_def

text{* Basic properties of the lifted model operations *}

text{* . for free inputs: *}

lemma sameDom_swapInp_gSwapInp[simp]:
assumes "wlsInp delta inp'" and "gWlsInp MOD delta inp"
shows "sameDom (swapInp zs z1 z2 inp') (gSwapInp MOD zs z1 z2 inp' inp)"
using assms by(simp add: wlsInp_iff gWlsInp_def swapInp_def gSwapInp_def
liftAll2_def lift_def lift2_def sameDom_def split: option.splits)

lemma sameDom_substInp_gSubstInp[simp]:
assumes "wlsInp delta inp'" and "gWlsInp MOD delta inp"
shows "sameDom (substInp ys Y' y inp') (gSubstInp MOD ys Y' Y y inp' inp)"
using assms by(simp add: wlsInp_iff gWlsInp_def substInp_def2 gSubstInp_def
liftAll2_def lift_def lift2_def sameDom_def split: option.splits)

text{* . for bound inputs: *}

lemma sameDom_swapBinp_gSwapBinp[simp]:
assumes "wlsBinp delta binp'" and "gWlsBinp MOD delta binp"
shows "sameDom (swapBinp zs z1 z2 binp') (gSwapBinp MOD zs z1 z2 binp' binp)"
using assms by(simp add: wlsBinp_iff gWlsBinp_def swapBinp_def gSwapBinp_def
liftAll2_def lift_def lift2_def sameDom_def split: option.splits)

lemma sameDom_substBinp_gSubstBinp[simp]:
assumes "wlsBinp delta binp'" and "gWlsBinp MOD delta binp"
shows "sameDom (substBinp ys Y' y binp') (gSubstBinp MOD ys Y' Y y binp' binp)"
using assms by(simp add: wlsBinp_iff gWlsBinp_def substBinp_def2 gSubstBinp_def
liftAll2_def lift_def lift2_def sameDom_def split: option.splits)

lemmas sameDom_gInput_simps =
sameDom_swapInp_gSwapInp sameDom_substInp_gSubstInp
sameDom_swapBinp_gSwapBinp sameDom_substBinp_gSubstBinp

text{* Domain disjointness: *}

definition gWlsDisj where
"gWlsDisj MOD \<equiv> \<forall> s s' X. gWls MOD s X \<and> gWls MOD s' X \<longrightarrow> s = s'"

definition gWlsAbsDisj where
"gWlsAbsDisj MOD \<equiv> \<forall> xs s xs' s' A.
    isInBar (xs,s) \<and> isInBar (xs',s') \<and>
    gWlsAbs MOD (xs,s) A \<and> gWlsAbs MOD (xs',s') A
    \<longrightarrow> xs = xs' \<and> s = s'"

definition gWlsAllDisj where
"gWlsAllDisj MOD \<equiv> gWlsDisj MOD \<and> gWlsAbsDisj MOD"

lemmas gWlsAllDisj_defs =
gWlsAllDisj_def gWlsDisj_def gWlsAbsDisj_def

text {* Abstraction domains inhabited only within bound arities: *}

definition gWlsAbsIsInBar where
"gWlsAbsIsInBar MOD \<equiv> \<forall> us s A. gWlsAbs MOD (us,s) A \<longrightarrow> isInBar (us,s)"

text{* Domain preservation by the operators *}

text{* The constructs preserve the domains: *}

definition gVarPresGWls where
"gVarPresGWls MOD \<equiv> \<forall> xs x. gWls MOD (asSort xs) (gVar MOD xs x)"

definition gAbsPresGWls where
"gAbsPresGWls MOD \<equiv> \<forall> xs s x X' X.
   isInBar (xs,s) \<and> wls s X' \<and> gWls MOD s X \<longrightarrow>
   gWlsAbs MOD (xs,s) (gAbs MOD xs x X' X)"

definition gOpPresGWls where
"gOpPresGWls MOD \<equiv> \<forall> delta inp' inp binp' binp.
   wlsInp delta inp' \<and> gWlsInp MOD delta inp \<and> wlsBinp delta binp' \<and> gWlsBinp MOD delta binp
   \<longrightarrow> gWls MOD (stOf delta) (gOp MOD delta inp' inp binp' binp)"

definition gConsPresGWls where
"gConsPresGWls MOD \<equiv> gVarPresGWls MOD \<and> gAbsPresGWls MOD \<and> gOpPresGWls MOD"

lemmas gConsPresGWls_defs = gConsPresGWls_def
gVarPresGWls_def gAbsPresGWls_def gOpPresGWls_def

text{* ``swap" preserves the domains: *}

definition gSwapPresGWls where
"gSwapPresGWls MOD \<equiv> \<forall> zs z1 z2 s X' X.
   wls s X' \<and> gWls MOD s X \<longrightarrow>
   gWls MOD s (gSwap MOD zs z1 z2 X' X)"

definition gSwapAbsPresGWlsAbs where
"gSwapAbsPresGWlsAbs MOD \<equiv> \<forall> zs z1 z2 us s A' A.
   isInBar (us,s) \<and> wlsAbs (us,s) A' \<and> gWlsAbs MOD (us,s) A \<longrightarrow>
   gWlsAbs MOD (us,s) (gSwapAbs MOD zs z1 z2 A' A)"

definition gSwapAllPresGWlsAll where
"gSwapAllPresGWlsAll MOD \<equiv> gSwapPresGWls MOD \<and> gSwapAbsPresGWlsAbs MOD"

lemmas gSwapAllPresGWlsAll_defs = 
gSwapAllPresGWlsAll_def gSwapPresGWls_def gSwapAbsPresGWlsAbs_def

text{* ``subst" preserves the domains: *}

definition gSubstPresGWls where
"gSubstPresGWls MOD \<equiv> \<forall> ys Y' Y y s X' X.
   wls (asSort ys) Y' \<and> gWls MOD (asSort ys) Y \<and> wls s X' \<and> gWls MOD s X \<longrightarrow>
   gWls MOD s (gSubst MOD ys Y' Y y X' X)"

definition gSubstAbsPresGWlsAbs where
"gSubstAbsPresGWlsAbs MOD \<equiv> \<forall> ys Y' Y y us s A' A.
   isInBar (us,s) \<and>
   wls (asSort ys) Y' \<and> gWls MOD (asSort ys) Y \<and> wlsAbs (us,s) A' \<and> gWlsAbs MOD (us,s) A \<longrightarrow>
   gWlsAbs MOD (us,s) (gSubstAbs MOD ys Y' Y y A' A)"

definition gSubstAllPresGWlsAll where
"gSubstAllPresGWlsAll MOD \<equiv> gSubstPresGWls MOD \<and> gSubstAbsPresGWlsAbs MOD"

lemmas gSubstAllPresGWlsAll_defs = 
gSubstAllPresGWlsAll_def gSubstPresGWls_def gSubstAbsPresGWlsAbs_def

text{* Clauses for fresh: *}

definition gFreshGVar where
"gFreshGVar MOD \<equiv> \<forall> ys y xs x.
   (ys \<noteq> xs \<or> y \<noteq> x) \<longrightarrow>
   gFresh MOD ys y (Var xs x) (gVar MOD xs x)"

definition gFreshGAbs1 where
"gFreshGAbs1 MOD \<equiv> \<forall> ys y s X' X.
   isInBar (ys,s) \<and> wls s X' \<and> gWls MOD s X \<longrightarrow>
   gFreshAbs MOD ys y (Abs ys y X') (gAbs MOD ys y X' X)"

definition gFreshGAbs2 where
"gFreshGAbs2 MOD \<equiv> \<forall> ys y xs x s X' X.
   isInBar (xs,s) \<and> wls s X' \<and> gWls MOD s X \<longrightarrow>
   fresh ys y X' \<and> gFresh MOD ys y X' X \<longrightarrow>
   gFreshAbs MOD ys y (Abs xs x X') (gAbs MOD xs x X' X)"

definition gFreshGOp where
"gFreshGOp MOD \<equiv> \<forall> ys y delta inp' inp binp' binp.
   wlsInp delta inp' \<and> gWlsInp MOD delta inp \<and> wlsBinp delta binp' \<and> gWlsBinp MOD delta binp \<longrightarrow>
   freshInp ys y inp' \<and> gFreshInp MOD ys y inp' inp \<and>
   freshBinp ys y binp' \<and> gFreshBinp MOD ys y binp' binp \<longrightarrow>
   gFresh MOD ys y (Op delta inp' binp') (gOp MOD delta inp' inp binp' binp)"

definition gFreshCls where
"gFreshCls MOD \<equiv> gFreshGVar MOD \<and> gFreshGAbs1 MOD \<and> gFreshGAbs2 MOD \<and> gFreshGOp MOD"

lemmas gFreshCls_defs = gFreshCls_def
gFreshGVar_def gFreshGAbs1_def gFreshGAbs2_def gFreshGOp_def

(* Clauses for swap: fully-conditional versions and less-conditional,
stronger versions (suffix ``STR") *)

definition gSwapGVar where
"gSwapGVar MOD \<equiv> \<forall> zs z1 z2 xs x.
   gSwap MOD zs z1 z2 (Var xs x) (gVar MOD xs x) =
   gVar MOD xs (x @xs[z1 \<and> z2]_zs)"

definition gSwapGAbs where
"gSwapGAbs MOD \<equiv> \<forall> zs z1 z2 xs x s X' X.
   isInBar (xs,s) \<and> wls s X' \<and> gWls MOD s X \<longrightarrow>
   gSwapAbs MOD zs z1 z2 (Abs xs x X') (gAbs MOD xs x X' X) =
   gAbs MOD xs (x @xs[z1 \<and> z2]_zs) (X' #[z1 \<and> z2]_zs) (gSwap MOD zs z1 z2 X' X)"

definition gSwapGOp where
"gSwapGOp MOD \<equiv> \<forall> zs z1 z2 delta inp' inp binp' binp.
   wlsInp delta inp' \<and> gWlsInp MOD delta inp \<and> wlsBinp delta binp' \<and> gWlsBinp MOD delta binp \<longrightarrow>
   gSwap MOD zs z1 z2 (Op delta inp' binp') (gOp MOD delta inp' inp binp' binp) =
   gOp MOD delta
     (inp' %[z1 \<and> z2]_zs) (gSwapInp MOD zs z1 z2 inp' inp)
     (binp' %%[z1 \<and> z2]_zs) (gSwapBinp MOD zs z1 z2 binp' binp)"

definition gSwapCls where
"gSwapCls MOD \<equiv> gSwapGVar MOD \<and> gSwapGAbs MOD \<and> gSwapGOp MOD"

lemmas gSwapCls_defs = gSwapCls_def
gSwapGVar_def gSwapGAbs_def gSwapGOp_def

(* Clauses for subst: *)

definition gSubstGVar1 where
"gSubstGVar1 MOD \<equiv> \<forall> ys y Y' Y xs x.
   wls (asSort ys) Y' \<and> gWls MOD (asSort ys) Y \<longrightarrow>
   (ys \<noteq> xs \<or> y \<noteq> x) \<longrightarrow>
   gSubst MOD ys Y' Y y (Var xs x) (gVar MOD xs x) =
   gVar MOD xs x"

definition gSubstGVar2 where
"gSubstGVar2 MOD \<equiv> \<forall> ys y Y' Y.
   wls (asSort ys) Y' \<and> gWls MOD (asSort ys) Y \<longrightarrow>
   gSubst MOD ys Y' Y y (Var ys y) (gVar MOD ys y) = Y"

definition gSubstGAbs where
"gSubstGAbs MOD \<equiv> \<forall> ys y Y' Y xs x s X' X.
   isInBar (xs,s) \<and>
   wls (asSort ys) Y' \<and> gWls MOD (asSort ys) Y \<and>
   wls s X' \<and> gWls MOD s X \<longrightarrow>
   (xs \<noteq> ys \<or> x \<noteq> y) \<and> fresh xs x Y' \<and> gFresh MOD xs x Y' Y \<longrightarrow>
   gSubstAbs MOD ys Y' Y y (Abs xs x X') (gAbs MOD xs x X' X) =
   gAbs MOD xs x (X' #[Y' / y]_ys) (gSubst MOD ys Y' Y y X' X)"

definition gSubstGOp where
"gSubstGOp MOD \<equiv> \<forall> ys y Y' Y delta inp' inp binp' binp.
   wls (asSort ys) Y' \<and> gWls MOD (asSort ys) Y \<and>
   wlsInp delta inp' \<and> gWlsInp MOD delta inp \<and>
   wlsBinp delta binp' \<and> gWlsBinp MOD delta binp \<longrightarrow>
   gSubst MOD ys Y' Y y (Op delta inp' binp') (gOp MOD delta inp' inp binp' binp) =
   gOp MOD delta
     (inp' %[Y' / y]_ys) (gSubstInp MOD ys Y' Y y inp' inp)
     (binp' %%[Y' / y]_ys) (gSubstBinp MOD ys Y' Y y binp' binp)"

definition gSubstCls where
"gSubstCls MOD \<equiv> gSubstGVar1 MOD \<and> gSubstGVar2 MOD \<and> gSubstGAbs MOD \<and> gSubstGOp MOD"

lemmas gSubstCls_defs = gSubstCls_def
gSubstGVar1_def gSubstGVar2_def gSubstGAbs_def gSubstGOp_def

(* Freshness-based congruence for abstractions: *)

(* ... employing swap: *)

definition gAbsCongS where
"gAbsCongS MOD \<equiv> \<forall> xs x x2 y s X' X X2' X2.
   isInBar (xs,s) \<and>
   wls s X' \<and> gWls MOD s X \<and>
   wls s X2' \<and> gWls MOD s X2 \<longrightarrow>
   fresh xs y X' \<and> gFresh MOD xs y X' X \<and>
   fresh xs y X2' \<and> gFresh MOD xs y X2' X2 \<and>
   (X' #[y \<and> x]_xs) = (X2' #[y \<and> x2]_xs) \<longrightarrow>
   gSwap MOD xs y x X' X = gSwap MOD xs y x2 X2' X2 \<longrightarrow>
   gAbs MOD xs x X' X = gAbs MOD xs x2 X2' X2"

(* ... Note: no need for congruence employing subst (as it is not used in the
definition of rmorphisms *)

(* Abstraction renaming: *)

definition gAbsRen where
"gAbsRen MOD \<equiv> \<forall> xs y x s X' X.
    isInBar (xs,s) \<and> wls s X' \<and> gWls MOD s X \<longrightarrow>
    fresh xs y X' \<and> gFresh MOD xs y X' X \<longrightarrow>
    gAbs MOD xs y (X' #[y // x]_xs) (gSubst MOD xs (Var xs y) (gVar MOD xs y) x X' X) =
    gAbs MOD xs x X' X"

text {* Well-sorted fresh-swap models: *}

definition wlsFSw where
"wlsFSw MOD \<equiv> gWlsAllDisj MOD \<and> gWlsAbsIsInBar MOD \<and>
 gConsPresGWls MOD \<and> gSwapAllPresGWlsAll MOD \<and>
 gFreshCls MOD \<and> gSwapCls MOD \<and> gAbsCongS MOD"

lemmas wlsFSw_defs1 = wlsFSw_def
gWlsAllDisj_def gWlsAbsIsInBar_def
gConsPresGWls_def gSwapAllPresGWlsAll_def
gFreshCls_def gSwapCls_def gAbsCongS_def

lemmas wlsFSw_defs = wlsFSw_def
gWlsAllDisj_defs gWlsAbsIsInBar_def
gConsPresGWls_defs gSwapAllPresGWlsAll_defs
gFreshCls_defs gSwapCls_defs gAbsCongS_def

text {* Well-sorted fresh-subst models: *}

definition wlsFSb where
"wlsFSb MOD \<equiv> gWlsAllDisj MOD \<and> gWlsAbsIsInBar MOD \<and>
 gConsPresGWls MOD \<and> gSubstAllPresGWlsAll MOD \<and>
 gFreshCls MOD \<and> gSubstCls MOD \<and> gAbsRen MOD"

lemmas wlsFSb_defs1 = wlsFSb_def
gWlsAllDisj_def gWlsAbsIsInBar_def
gConsPresGWls_def gSubstAllPresGWlsAll_def
gFreshCls_def gSubstCls_def gAbsRen_def

lemmas wlsFSb_defs = wlsFSb_def
gWlsAllDisj_defs gWlsAbsIsInBar_def
gConsPresGWls_defs gSubstAllPresGWlsAll_defs
gFreshCls_defs gSubstCls_defs gAbsRen_def

text {* Well-sorted fresh-swap-subst-models *}

definition wlsFSwSb where
"wlsFSwSb MOD \<equiv> wlsFSw MOD \<and> gSubstAllPresGWlsAll MOD \<and> gSubstCls MOD"

lemmas wlsFSwSb_defs1 = wlsFSwSb_def
wlsFSw_def gSubstAllPresGWlsAll_def gSubstCls_def

lemmas wlsFSwSb_defs = wlsFSwSb_def
wlsFSw_def gSubstAllPresGWlsAll_defs gSubstCls_defs

text {* Well-sorted fresh-subst-swap-models *}

definition wlsFSbSw where
"wlsFSbSw MOD \<equiv> wlsFSb MOD \<and> gSwapAllPresGWlsAll MOD \<and> gSwapCls MOD"

lemmas wlsFSbSw_defs1 = wlsFSbSw_def
wlsFSw_def gSwapAllPresGWlsAll_def gSwapCls_def

lemmas wlsFSbSw_defs = wlsFSbSw_def
wlsFSw_def gSwapAllPresGWlsAll_defs gSwapCls_defs

text{* Extension of domain preservation (by swap and subst) to inputs: *}

text {* First for free inputs: *}

definition gSwapInpPresGWlsInp where
"gSwapInpPresGWlsInp MOD \<equiv> \<forall> zs z1 z2 delta inp' inp.
   wlsInp delta inp' \<and> gWlsInp MOD delta inp \<longrightarrow>
   gWlsInp MOD delta (gSwapInp MOD zs z1 z2 inp' inp)"

definition gSubstInpPresGWlsInp where
"gSubstInpPresGWlsInp MOD \<equiv> \<forall> ys y Y' Y delta inp' inp.
   wls (asSort ys) Y' \<and> gWls MOD (asSort ys) Y \<and>
   wlsInp delta inp' \<and> gWlsInp MOD delta inp \<longrightarrow>
   gWlsInp MOD delta (gSubstInp MOD ys Y' Y y inp' inp)"

lemma imp_gSwapInpPresGWlsInp:
"gSwapPresGWls MOD \<Longrightarrow> gSwapInpPresGWlsInp MOD"
by (auto simp: lift2_def liftAll2_def sameDom_def wlsInp_iff gWlsInp_def 
gSwapPresGWls_def gSwapInpPresGWlsInp_def gSwapInp_def 
split: option.splits)

lemma imp_gSubstInpPresGWlsInp:
"gSubstPresGWls MOD \<Longrightarrow> gSubstInpPresGWlsInp MOD"
by (auto simp: lift2_def liftAll2_def sameDom_def wlsInp_iff gWlsInp_def 
gSubstPresGWls_def gSubstInpPresGWlsInp_def gSubstInp_def 
split: option.splits)

text {* Then for bound inputs: *}

definition gSwapBinpPresGWlsBinp where
"gSwapBinpPresGWlsBinp MOD \<equiv> \<forall> zs z1 z2 delta binp' binp.
   wlsBinp delta binp' \<and> gWlsBinp MOD delta binp \<longrightarrow>
   gWlsBinp MOD delta (gSwapBinp MOD zs z1 z2 binp' binp)"

definition gSubstBinpPresGWlsBinp where
"gSubstBinpPresGWlsBinp MOD \<equiv> \<forall> ys y Y' Y delta binp' binp.
   wls (asSort ys) Y' \<and> gWls MOD (asSort ys) Y \<and>
   wlsBinp delta binp' \<and> gWlsBinp MOD delta binp \<longrightarrow>
   gWlsBinp MOD delta (gSubstBinp MOD ys Y' Y y binp' binp)"

lemma imp_gSwapBinpPresGWlsBinp:
"gSwapAbsPresGWlsAbs MOD \<Longrightarrow> gSwapBinpPresGWlsBinp MOD"
by (auto simp: lift2_def liftAll2_def sameDom_def wlsBinp_iff gWlsBinp_def 
gSwapAbsPresGWlsAbs_def gSwapBinpPresGWlsBinp_def gSwapBinp_def 
split: option.splits)

lemma imp_gSubstBinpPresGWlsBinp:
"gSubstAbsPresGWlsAbs MOD \<Longrightarrow> gSubstBinpPresGWlsBinp MOD" 
by (auto simp: lift2_def liftAll2_def sameDom_def wlsBinp_iff gWlsBinp_def 
gSubstAbsPresGWlsAbs_def gSubstBinpPresGWlsBinp_def gSubstBinp_def 
split: option.splits)
 
subsection{* Model morphisms from the term model  *}

definition presWls where
"presWls h MOD \<equiv> \<forall> s X. wls s X \<longrightarrow> gWls MOD s (h X)"

definition presWlsAbs where
"presWlsAbs hA MOD \<equiv> \<forall> us s A. wlsAbs (us,s) A \<longrightarrow> gWlsAbs MOD (us,s) (hA A)"

definition presWlsAll where
"presWlsAll h hA MOD \<equiv> presWls h MOD \<and> presWlsAbs hA MOD"

lemmas presWlsAll_defs = presWlsAll_def presWls_def presWlsAbs_def

definition presVar where
"presVar h MOD \<equiv> \<forall> xs x. h (Var xs x) = gVar MOD xs x"

definition presAbs where
"presAbs h hA MOD \<equiv> \<forall> xs x s X.
   isInBar (xs,s) \<and> wls s X \<longrightarrow>
   hA (Abs xs x X) = gAbs MOD xs x X (h X)"

definition presOp where
"presOp h hA MOD \<equiv> \<forall> delta inp binp.
    wlsInp delta inp \<and> wlsBinp delta binp \<longrightarrow>
    h (Op delta inp binp) =
    gOp MOD delta inp (lift h inp) binp (lift hA binp)"

definition presCons where
"presCons h hA MOD \<equiv> presVar h MOD \<and> presAbs h hA MOD \<and> presOp h hA MOD"

lemmas presCons_defs = presCons_def
presVar_def presAbs_def presOp_def

definition presFresh where
"presFresh h MOD \<equiv> \<forall> ys y s X.
    wls s X \<longrightarrow>
    fresh ys y X \<longrightarrow> gFresh MOD ys y X (h X)"

definition presFreshAbs where
"presFreshAbs hA MOD \<equiv> \<forall> ys y us s A.
    wlsAbs (us,s) A \<longrightarrow>
    freshAbs ys y A \<longrightarrow> gFreshAbs MOD ys y A (hA A)"

definition presFreshAll where
"presFreshAll h hA MOD \<equiv> presFresh h MOD \<and> presFreshAbs hA MOD"

lemmas presFreshAll_defs = presFreshAll_def
presFresh_def presFreshAbs_def

definition presSwap where
"presSwap h MOD \<equiv> \<forall> zs z1 z2 s X.
    wls s X \<longrightarrow>
    h (X #[z1 \<and> z2]_zs) = gSwap MOD zs z1 z2 X (h X)"

definition presSwapAbs where
"presSwapAbs hA MOD \<equiv> \<forall> zs z1 z2 us s A.
    wlsAbs (us,s) A \<longrightarrow>
    hA (A $[z1 \<and> z2]_zs) = gSwapAbs MOD zs z1 z2 A (hA A)"

definition presSwapAll where
"presSwapAll h hA MOD \<equiv> presSwap h MOD \<and> presSwapAbs hA MOD"

lemmas presSwapAll_defs = presSwapAll_def
presSwap_def presSwapAbs_def

definition presSubst where
"presSubst h MOD \<equiv> \<forall> ys Y y s X.
    wls (asSort ys) Y \<and> wls s X \<longrightarrow>
    h (subst ys Y y X) = gSubst MOD ys Y (h Y) y X (h X)"

definition presSubstAbs where
"presSubstAbs h hA MOD \<equiv> \<forall> ys Y y us s A.
    wls (asSort ys) Y \<and> wlsAbs (us,s) A \<longrightarrow>
    hA (A $[Y / y]_ys) = gSubstAbs MOD ys Y (h Y) y A (hA A)"

definition presSubstAll where
"presSubstAll h hA MOD \<equiv> presSubst h MOD \<and> presSubstAbs h hA MOD"

lemmas presSubstAll_defs = presSubstAll_def
presSubst_def presSubstAbs_def

definition termFSwMorph where
"termFSwMorph h hA MOD \<equiv> presWlsAll h hA MOD \<and> presCons h hA MOD \<and>
 presFreshAll h hA MOD \<and> presSwapAll h hA MOD"

lemmas termFSwMorph_defs1 = termFSwMorph_def
presWlsAll_def presCons_def presFreshAll_def presSwapAll_def

lemmas termFSwMorph_defs = termFSwMorph_def
presWlsAll_defs presCons_defs presFreshAll_defs presSwapAll_defs

definition termFSbMorph where
"termFSbMorph h hA MOD \<equiv> presWlsAll h hA MOD \<and> presCons h hA MOD \<and>
 presFreshAll h hA MOD \<and> presSubstAll h hA MOD"

lemmas termFSbMorph_defs1 = termFSbMorph_def
presWlsAll_def presCons_def presFreshAll_def presSubstAll_def

lemmas termFSbMorph_defs = termFSbMorph_def
presWlsAll_defs presCons_defs presFreshAll_defs presSubstAll_defs

definition termFSwSbMorph where
"termFSwSbMorph h hA MOD \<equiv> termFSwMorph h hA MOD \<and> presSubstAll h hA MOD"

lemmas termFSwSbMorph_defs1 = termFSwSbMorph_def
termFSwMorph_def presSubstAll_def

lemmas termFSwSbMorph_defs = termFSwSbMorph_def
termFSwMorph_defs presSubstAll_defs

text{* Extension of domain preservation (by the morphisms) to inputs *}

text{* . for free inputs: *}

lemma presWls_wlsInp:
"wlsInp delta inp \<Longrightarrow> presWls h MOD \<Longrightarrow> gWlsInp MOD delta (lift h inp)"
by(auto simp: wlsInp_iff gWlsInp_def lift_def liftAll2_def sameDom_def 
presWls_def split: option.splits)
 

text{* . for bound inputs: *}

lemma presWls_wlsBinp:
"wlsBinp delta binp \<Longrightarrow> presWlsAbs hA MOD \<Longrightarrow> gWlsBinp MOD delta (lift hA binp)"
by(auto simp: wlsBinp_iff gWlsBinp_def lift_def liftAll2_def sameDom_def 
presWlsAbs_def split: option.splits) 

subsection {* From models to iterative models *}

text {* The transition map: *}

definition fromMOD ::
"('index,'bindex,'varSort,'sort,'opSym,'var,'gTerm,'gAbs) model
 \<Rightarrow>
 ('index,'bindex,'varSort,'sort,'opSym,'var,
  ('index,'bindex,'varSort,'var,'opSym)term \<times> 'gTerm,
  ('index,'bindex,'varSort,'var,'opSym)abs \<times> 'gAbs) Iteration.model"
where
"fromMOD MOD \<equiv>
 \<lparr>
  igWls = \<lambda>s X'X. wls s (fst X'X) \<and> gWls MOD s (snd X'X),
  igWlsAbs = \<lambda>us_s A'A. wlsAbs us_s (fst A'A) \<and> gWlsAbs MOD us_s (snd A'A),

  igVar = \<lambda>xs x. (Var xs x, gVar MOD xs x),
  igAbs = \<lambda>xs x X'X. (Abs xs x (fst X'X), gAbs MOD xs x (fst X'X) (snd X'X)),
  igOp =
  \<lambda>delta iinp biinp.
    (Op delta (lift fst iinp) (lift fst biinp),
     gOp MOD delta
       (lift fst iinp) (lift snd iinp)
       (lift fst biinp) (lift snd biinp)),

  igFresh =
  \<lambda>ys y X'X. fresh ys y (fst X'X) \<and> gFresh MOD ys y (fst X'X) (snd X'X),
  igFreshAbs =
  \<lambda>ys y A'A. freshAbs ys y (fst A'A) \<and> gFreshAbs MOD ys y (fst A'A) (snd A'A),

  igSwap =
  \<lambda>zs z1 z2 X'X. ((fst X'X) #[z1 \<and> z2]_zs, gSwap MOD zs z1 z2 (fst X'X) (snd X'X)),
  igSwapAbs =
  \<lambda>zs z1 z2 A'A. ((fst A'A) $[z1 \<and> z2]_zs, gSwapAbs MOD zs z1 z2 (fst A'A) (snd A'A)),

  igSubst =
  \<lambda>ys Y'Y y X'X.
    ((fst X'X) #[(fst Y'Y) / y]_ys,
     gSubst MOD ys (fst Y'Y) (snd Y'Y) y (fst X'X) (snd X'X)),
  igSubstAbs =
  \<lambda>ys Y'Y y A'A.
    ((fst A'A) $[(fst Y'Y) / y]_ys,
     gSubstAbs MOD ys (fst Y'Y) (snd Y'Y) y (fst A'A) (snd A'A))
 \<rparr>"

text{* Basic simplification rules: *}

lemma fromMOD_basic_simps[simp]:
"igWls (fromMOD MOD) s X'X =
 (wls s (fst X'X) \<and> gWls MOD s (snd X'X))"
(*  *)
"igWlsAbs (fromMOD MOD) us_s A'A =
 (wlsAbs us_s (fst A'A) \<and> gWlsAbs MOD us_s (snd A'A))"
(*  *)
"igVar (fromMOD MOD) xs x = (Var xs x, gVar MOD xs x)"
(*  *)
"igAbs (fromMOD MOD) xs x X'X = (Abs xs x (fst X'X), gAbs MOD xs x (fst X'X) (snd X'X))"
(*  *)
"igOp (fromMOD MOD) delta iinp biinp =
 (Op delta (lift fst iinp) (lift fst biinp),
  gOp MOD delta
    (lift fst iinp) (lift snd iinp)
    (lift fst biinp) (lift snd biinp))"
(*  *)
"igFresh (fromMOD MOD) ys y X'X =
 (fresh ys y (fst X'X) \<and> gFresh MOD ys y (fst X'X) (snd X'X))"
(*  *)
"igFreshAbs (fromMOD MOD) ys y A'A  =
 (freshAbs ys y (fst A'A) \<and> gFreshAbs MOD ys y (fst A'A) (snd A'A))"
(*  *)
"igSwap (fromMOD MOD) zs z1 z2 X'X =
 ((fst X'X) #[z1 \<and> z2]_zs, gSwap MOD zs z1 z2 (fst X'X) (snd X'X))"
(*  *)
"igSwapAbs (fromMOD MOD) zs z1 z2 A'A =
 ((fst A'A) $[z1 \<and> z2]_zs, gSwapAbs MOD zs z1 z2 (fst A'A) (snd A'A))"
(*  *)
"igSubst (fromMOD MOD) ys Y'Y y X'X =
 ((fst X'X) #[(fst Y'Y) / y]_ys,
  gSubst MOD ys (fst Y'Y) (snd Y'Y) y (fst X'X) (snd X'X))"
(*  *)
"igSubstAbs (fromMOD MOD) ys Y'Y y A'A =
 ((fst A'A) $[(fst Y'Y) / y]_ys,
  gSubstAbs MOD ys (fst Y'Y) (snd Y'Y) y (fst A'A) (snd A'A))"
unfolding fromMOD_def by auto

text{* Simps for inputs *}

text{* . for free inputs: *}

lemma igWlsInp_fromMOD[simp]:
"igWlsInp (fromMOD MOD) delta iinp \<longleftrightarrow>
 wlsInp delta (lift fst iinp) \<and> gWlsInp MOD delta (lift snd iinp)"
apply (intro iffI)
 subgoal apply(simp add: liftAll2_def lift_def sameDom_def 
   igWlsInp_def wlsInp_iff gWlsInp_def split: option.splits) .
 subgoal 
   unfolding liftAll2_def lift_def sameDom_def 
   igWlsInp_def wlsInp_iff gWlsInp_def 
   by simp (metis (no_types, lifting) eq_snd_iff fstI option.case_eq_if 
       option.distinct(1) option.simps(5)) .

lemma igFreshInp_fromMOD[simp]:
"igFreshInp (fromMOD MOD) ys y iinp \<longleftrightarrow> 
 freshInp ys y (lift fst iinp) \<and> gFreshInp MOD ys y (lift fst iinp) (lift snd iinp)"
by (auto simp: igFreshInp_def gFreshInp_def freshInp_def
liftAll2_def liftAll_def lift_def split: option.splits)

lemma igSwapInp_fromMOD[simp]:
"igSwapInp (fromMOD MOD) zs z1 z2 iinp = 
 lift2 Pair
   (swapInp zs z1 z2 (lift fst iinp))
   (gSwapInp MOD zs z1 z2 (lift fst iinp) (lift snd iinp))"
by(auto simp: igSwapInp_def swapInp_def gSwapInp_def lift_def lift2_def
split: option.splits) 

lemma igSubstInp_fromMOD[simp]:
"igSubstInp (fromMOD MOD) ys Y'Y y iinp =
 lift2 Pair
   (substInp ys (fst Y'Y) y (lift fst iinp))
   (gSubstInp MOD ys (fst Y'Y) (snd Y'Y) y (lift fst iinp) (lift snd iinp))"
by(auto simp: igSubstInp_def substInp_def2 gSubstInp_def lift_def lift2_def
split: option.splits) 

lemmas input_fromMOD_simps =
igWlsInp_fromMOD igFreshInp_fromMOD igSwapInp_fromMOD igSubstInp_fromMOD

text{* . for bound inputs: *}

lemma igWlsBinp_fromMOD[simp]:
"igWlsBinp (fromMOD MOD) delta biinp \<longleftrightarrow> 
 (wlsBinp delta (lift fst biinp) \<and> gWlsBinp MOD delta (lift snd biinp))"
apply (intro iffI)
 subgoal apply(simp add: liftAll2_def lift_def sameDom_def 
   igWlsBinp_def wlsBinp_iff gWlsBinp_def split: option.splits) .
 subgoal 
   unfolding liftAll2_def lift_def sameDom_def 
   igWlsBinp_def wlsBinp_iff gWlsBinp_def 
   by simp (metis (no_types, lifting) eq_snd_iff fstI option.case_eq_if 
       option.distinct(1) option.simps(5)) .

lemma igFreshBinp_fromMOD[simp]:
"igFreshBinp (fromMOD MOD) ys y biinp \<longleftrightarrow> 
 (freshBinp ys y (lift fst biinp) \<and>
  gFreshBinp MOD ys y (lift fst biinp) (lift snd biinp))"
by (auto simp: igFreshBinp_def gFreshBinp_def freshBinp_def
liftAll2_def liftAll_def lift_def split: option.splits)

lemma igSwapBinp_fromMOD[simp]:
"igSwapBinp (fromMOD MOD) zs z1 z2 biinp = 
 lift2 Pair
   (swapBinp zs z1 z2 (lift fst biinp))
   (gSwapBinp MOD zs z1 z2 (lift fst biinp) (lift snd biinp))"
by(auto simp: igSwapBinp_def swapBinp_def gSwapBinp_def lift_def lift2_def
split: option.splits) 

lemma igSubstBinp_fromMOD[simp]:
"igSubstBinp (fromMOD MOD) ys Y'Y y biinp =
 lift2 Pair
   (substBinp ys (fst Y'Y) y (lift fst biinp))
   (gSubstBinp MOD ys (fst Y'Y) (snd Y'Y) y (lift fst biinp) (lift snd biinp))"
by(auto simp: igSubstBinp_def substBinp_def2 gSubstBinp_def lift_def lift2_def
split: option.splits)

lemmas binput_fromMOD_simps =
igWlsBinp_fromMOD igFreshBinp_fromMOD igSwapBinp_fromMOD igSubstBinp_fromMOD

text{* Domain disjointness: *}

lemma igWlsDisj_fromMOD[simp]:
"gWlsDisj MOD \<Longrightarrow> igWlsDisj (fromMOD MOD)"
unfolding igWlsDisj_def gWlsDisj_def by auto

lemma igWlsAbsDisj_fromMOD[simp]:
"gWlsAbsDisj MOD \<Longrightarrow> igWlsAbsDisj (fromMOD MOD)"
unfolding igWlsAbsDisj_def gWlsAbsDisj_def by fastforce

lemma igWlsAllDisj_fromMOD[simp]:
"gWlsAllDisj MOD \<Longrightarrow> igWlsAllDisj (fromMOD MOD)"
unfolding igWlsAllDisj_def gWlsAllDisj_def by fastforce

lemmas igWlsAllDisj_fromMOD_simps =
igWlsDisj_fromMOD igWlsAbsDisj_fromMOD igWlsAllDisj_fromMOD

text{* Abstractions only within IsInBar: *}

lemma igWlsAbsIsInBar_fromMOD[simp]:
"gWlsAbsIsInBar MOD \<Longrightarrow> igWlsAbsIsInBar (fromMOD MOD)"
unfolding gWlsAbsIsInBar_def igWlsAbsIsInBar_def by simp

text{* The constructs preserve the domains: *}

lemma igVarIPresIGWls_fromMOD[simp]:
"gVarPresGWls MOD \<Longrightarrow> igVarIPresIGWls (fromMOD MOD)"
unfolding igVarIPresIGWls_def gVarPresGWls_def by simp

lemma igAbsIPresIGWls_fromMOD[simp]:
"gAbsPresGWls MOD \<Longrightarrow> igAbsIPresIGWls (fromMOD MOD)"
unfolding igAbsIPresIGWls_def gAbsPresGWls_def by simp

lemma igOpIPresIGWls_fromMOD[simp]:
"gOpPresGWls MOD \<Longrightarrow> igOpIPresIGWls (fromMOD MOD)"
unfolding igOpIPresIGWls_def gOpPresGWls_def by simp

lemma igConsIPresIGWls_fromMOD[simp]:
"gConsPresGWls MOD \<Longrightarrow> igConsIPresIGWls (fromMOD MOD)"
unfolding igConsIPresIGWls_def gConsPresGWls_def by simp

lemmas igConsIPresIGWls_fromMOD_simps =
igVarIPresIGWls_fromMOD igAbsIPresIGWls_fromMOD
igOpIPresIGWls_fromMOD igConsIPresIGWls_fromMOD

text{* Swap preserves the domains: *}

lemma igSwapIPresIGWls_fromMOD[simp]:
"gSwapPresGWls MOD \<Longrightarrow> igSwapIPresIGWls (fromMOD MOD)"
unfolding igSwapIPresIGWls_def gSwapPresGWls_def by simp

lemma igSwapAbsIPresIGWlsAbs_fromMOD[simp]:
"gSwapAbsPresGWlsAbs MOD \<Longrightarrow> igSwapAbsIPresIGWlsAbs (fromMOD MOD)"
unfolding igSwapAbsIPresIGWlsAbs_def gSwapAbsPresGWlsAbs_def by simp

lemma igSwapAllIPresIGWlsAll_fromMOD[simp]:
"gSwapAllPresGWlsAll MOD \<Longrightarrow> igSwapAllIPresIGWlsAll (fromMOD MOD)"
unfolding igSwapAllIPresIGWlsAll_def gSwapAllPresGWlsAll_def by simp

lemmas igSwapAllIPresIGWlsAll_fromMOD_simps =
igSwapIPresIGWls_fromMOD igSwapAbsIPresIGWlsAbs_fromMOD igSwapAllIPresIGWlsAll_fromMOD

text{* Subst preserves the domains: *}

lemma igSubstIPresIGWls_fromMOD[simp]:
"gSubstPresGWls MOD \<Longrightarrow> igSubstIPresIGWls (fromMOD MOD)"
unfolding igSubstIPresIGWls_def gSubstPresGWls_def by simp

lemma igSubstAbsIPresIGWlsAbs_fromMOD[simp]:
"gSubstAbsPresGWlsAbs MOD \<Longrightarrow> igSubstAbsIPresIGWlsAbs (fromMOD MOD)"
unfolding igSubstAbsIPresIGWlsAbs_def gSubstAbsPresGWlsAbs_def by simp

lemma igSubstAllIPresIGWlsAll_fromMOD[simp]:
"gSubstAllPresGWlsAll MOD \<Longrightarrow> igSubstAllIPresIGWlsAll (fromMOD MOD)"
unfolding igSubstAllIPresIGWlsAll_def gSubstAllPresGWlsAll_def by simp

lemmas igSubstAllIPresIGWlsAll_fromMOD_simps =
igSubstIPresIGWls_fromMOD igSubstAbsIPresIGWlsAbs_fromMOD igSubstAllIPresIGWlsAll_fromMOD

text{* The fresh clauses: *}

lemma igFreshIGVar_fromMOD[simp]:
"gFreshGVar MOD \<Longrightarrow> igFreshIGVar (fromMOD MOD)"
unfolding igFreshIGVar_def gFreshGVar_def by simp

lemma igFreshIGAbs1_fromMOD[simp]:
"gFreshGAbs1 MOD \<Longrightarrow> igFreshIGAbs1 (fromMOD MOD)"
unfolding igFreshIGAbs1_def gFreshGAbs1_def by auto

lemma igFreshIGAbs2_fromMOD[simp]:
"gFreshGAbs2 MOD \<Longrightarrow> igFreshIGAbs2 (fromMOD MOD)"
unfolding igFreshIGAbs2_def gFreshGAbs2_def by auto

lemma igFreshIGOp_fromMOD[simp]:
"gFreshGOp MOD \<Longrightarrow> igFreshIGOp (fromMOD MOD)"
unfolding igFreshIGOp_def gFreshGOp_def by simp

lemma igFreshCls_fromMOD[simp]:
"gFreshCls MOD \<Longrightarrow> igFreshCls (fromMOD MOD)"
unfolding igFreshCls_def gFreshCls_def by simp

lemmas igFreshCls_fromMOD_simps =
igFreshIGVar_fromMOD igFreshIGAbs1_fromMOD igFreshIGAbs2_fromMOD
igFreshIGOp_fromMOD igFreshCls_fromMOD

text{* The swap clauses *}

lemma igSwapIGVar_fromMOD[simp]:
"gSwapGVar MOD \<Longrightarrow> igSwapIGVar (fromMOD MOD)"
unfolding igSwapIGVar_def gSwapGVar_def by simp

lemma igSwapIGAbs_fromMOD[simp]:
"gSwapGAbs MOD \<Longrightarrow> igSwapIGAbs (fromMOD MOD)"
unfolding igSwapIGAbs_def gSwapGAbs_def by auto

lemma igSwapIGOp_fromMOD[simp]:
"gSwapGOp MOD \<Longrightarrow> igSwapIGOp (fromMOD MOD)"
by (auto simp: igSwapIGOp_def gSwapGOp_def lift_lift2)

lemma igSwapCls_fromMOD[simp]:
"gSwapCls MOD \<Longrightarrow> igSwapCls (fromMOD MOD)"
unfolding igSwapCls_def gSwapCls_def by simp

lemmas igSwapCls_fromMOD_simps =
igSwapIGVar_fromMOD igSwapIGAbs_fromMOD
igSwapIGOp_fromMOD igSwapCls_fromMOD

text{* The subst clauses *}

lemma igSubstIGVar1_fromMOD[simp]:
"gSubstGVar1 MOD \<Longrightarrow> igSubstIGVar1 (fromMOD MOD)"
unfolding igSubstIGVar1_def gSubstGVar1_def by simp

lemma igSubstIGVar2_fromMOD[simp]:
"gSubstGVar2 MOD \<Longrightarrow> igSubstIGVar2 (fromMOD MOD)"
unfolding igSubstIGVar2_def gSubstGVar2_def by simp

lemma igSubstIGAbs_fromMOD[simp]:
"gSubstGAbs MOD \<Longrightarrow> igSubstIGAbs (fromMOD MOD)"
unfolding igSubstIGAbs_def gSubstGAbs_def by fastforce+

lemma igSubstIGOp_fromMOD[simp]:
"gSubstGOp MOD \<Longrightarrow> igSubstIGOp (fromMOD MOD)"
by(auto simp: igSubstIGOp_def gSubstGOp_def lift_lift2)

lemma igSubstCls_fromMOD[simp]:
"gSubstCls MOD \<Longrightarrow> igSubstCls (fromMOD MOD)"
unfolding igSubstCls_def gSubstCls_def by simp

lemmas igSubstCls_fromMOD_simps =
igSubstIGVar1_fromMOD igSubstIGVar2_fromMOD igSubstIGAbs_fromMOD
igSubstIGOp_fromMOD igSubstCls_fromMOD

text{* Abstraction swapping congruence: *}

lemma igAbsCongS_fromMOD[simp]:
assumes "gAbsCongS MOD"
shows "igAbsCongS (fromMOD MOD)"
using assms
unfolding igAbsCongS_def gAbsCongS_def 
apply simp  
apply clarify
by (intro conjI, erule wls_Abs_swap_cong) blast+

text{* Abstraction renaming: *}

lemma igAbsRen_fromMOD[simp]:
"gAbsRen MOD \<Longrightarrow> igAbsRen (fromMOD MOD)"
unfolding igAbsRen_def gAbsRen_def vsubst_def by auto

text{* Models: *}

lemma iwlsFSw_fromMOD[simp]:
"wlsFSw MOD \<Longrightarrow> iwlsFSw (fromMOD MOD)"
unfolding iwlsFSw_def wlsFSw_def by simp

lemma iwlsFSb_fromMOD[simp]:
"wlsFSb MOD \<Longrightarrow> iwlsFSb (fromMOD MOD)"
unfolding iwlsFSb_def wlsFSb_def by simp

lemma iwlsFSwSb_fromMOD[simp]:
"wlsFSwSb MOD \<Longrightarrow> iwlsFSwSb (fromMOD MOD)"
unfolding iwlsFSwSb_def wlsFSwSb_def by simp

lemma iwlsFSbSw_fromMOD[simp]:
"wlsFSbSw MOD \<Longrightarrow> iwlsFSbSw (fromMOD MOD)"
unfolding iwlsFSbSw_def wlsFSbSw_def by simp

lemmas iwlsModel_fromMOD_simps =
iwlsFSw_fromMOD iwlsFSb_fromMOD
iwlsFSwSb_fromMOD iwlsFSbSw_fromMOD

(******************************)
lemmas fromMOD_predicate_simps =
igWlsAllDisj_fromMOD_simps
igConsIPresIGWls_fromMOD_simps
igSwapAllIPresIGWlsAll_fromMOD_simps
igSubstAllIPresIGWlsAll_fromMOD_simps
igFreshCls_fromMOD_simps
igSwapCls_fromMOD_simps
igSubstCls_fromMOD_simps
igAbsCongS_fromMOD
igAbsRen_fromMOD
iwlsModel_fromMOD_simps

lemmas fromMOD_simps =
fromMOD_basic_simps
input_fromMOD_simps
binput_fromMOD_simps
fromMOD_predicate_simps

subsection {* The recursion-iteration ``identity trick"  *}

text {* Here we show that any construct-preserving map from terms to ``fromMOD MOD"
is the identity on its first projection -- this is the main trick when
reducing recursion to iteration.  *}

lemma ipresCons_fromMOD_fst:
assumes "ipresCons h hA (fromMOD MOD)"
shows "(wls s X \<longrightarrow> fst (h X) = X) \<and> (wlsAbs (us,s') A \<longrightarrow> fst (hA A) = A)"
proof(induction rule: wls_rawInduct) 
next
  case (Op delta inp binp) 
  hence "lift (fst \<circ> h) inp = inp \<and> lift (fst \<circ> hA) binp = binp"
  by (simp add: lift_def fun_eq_iff liftAll2_def 
   wlsInp_iff wlsBinp_iff sameDom_def split: option.splits) 
  (metis not_Some_eq old.prod.exhaust) 
  then show ?case
  using assms Op by (auto simp: ipresCons_def ipresOp_def lift_comp)
qed(insert assms, auto simp: ipresVar_def ipresCons_def ipresAbs_def)

lemma ipresCons_fromMOD_fst_simps[simp]:
"\<lbrakk>ipresCons h hA (fromMOD MOD); wls s X\<rbrakk>
 \<Longrightarrow> fst (h X) = X"
(*  *)
"\<lbrakk>ipresCons h hA (fromMOD MOD); wlsAbs (us,s') A\<rbrakk>
 \<Longrightarrow> fst (hA A) = A"
using ipresCons_fromMOD_fst by blast+

lemma ipresCons_fromMOD_fst_inp[simp]:
"ipresCons h hA (fromMOD MOD) \<Longrightarrow> wlsInp delta inp \<Longrightarrow> lift (fst o h) inp = inp"
by (force simp add: lift_def fun_eq_iff liftAll2_def 
wlsInp_iff sameDom_def split: option.splits)
 

lemma ipresCons_fromMOD_fst_binp[simp]:
"ipresCons h hA (fromMOD MOD) \<Longrightarrow> wlsBinp delta binp \<Longrightarrow> lift (fst o hA) binp = binp"
by (force simp add: lift_def fun_eq_iff liftAll2_def 
wlsBinp_iff sameDom_def split: option.splits)

lemmas ipresCons_fromMOD_fst_all_simps =
ipresCons_fromMOD_fst_simps ipresCons_fromMOD_fst_inp ipresCons_fromMOD_fst_binp

subsection {* From iteration morphisms to morphisms *}

text{* The transition map: *}

definition fromIMor ::
"(('index,'bindex,'varSort,'var,'opSym)term \<Rightarrow>
  ('index,'bindex,'varSort,'var,'opSym)term \<times> 'gTerm)
 \<Rightarrow>
 (('index,'bindex,'varSort,'var,'opSym)term \<Rightarrow> 'gTerm)"
where "fromIMor h \<equiv> snd o h"

definition fromIMorAbs ::
"(('index,'bindex,'varSort,'var,'opSym)abs \<Rightarrow>
  ('index,'bindex,'varSort,'var,'opSym)abs \<times> 'gAbs)
 \<Rightarrow>
 (('index,'bindex,'varSort,'var,'opSym)abs \<Rightarrow> 'gAbs)"
where "fromIMorAbs hA \<equiv> snd o hA"

text{* Basic simplification rules: *}

lemma fromIMor[simp]: "fromIMor h X' = snd (h X')"
unfolding fromIMor_def by simp

lemma fromIMorAbs[simp]: "fromIMorAbs hA A' = snd (hA A')"
unfolding fromIMorAbs_def by simp

lemma fromIMor_snd_inp[simp]:
"wlsInp delta inp \<Longrightarrow> lift (fromIMor h) inp = lift (snd o h) inp"
by (auto simp: lift_def split: option.splits)

lemma fromIMorAbs_snd_binp[simp]:
"wlsBinp delta binp \<Longrightarrow> lift (fromIMorAbs hA) binp = lift (snd o hA) binp"
by (auto simp: lift_def split: option.splits)

lemmas fromIMor_basic_simps =
fromIMor fromIMorAbs fromIMor_snd_inp fromIMorAbs_snd_binp

text{* Predicate simplification rules *}

text{* Domain preservation *}

lemma presWls_fromIMor[simp]:
"ipresWls h (fromMOD MOD) \<Longrightarrow> presWls (fromIMor h) MOD"
unfolding ipresWls_def presWls_def by simp

lemma presWlsAbs_fromIMorAbs[simp]:
"ipresWlsAbs hA (fromMOD MOD) \<Longrightarrow> presWlsAbs (fromIMorAbs hA) MOD"
unfolding ipresWlsAbs_def presWlsAbs_def by simp

lemma presWlsAll_fromIMorAll[simp]:
"ipresWlsAll h hA (fromMOD MOD) \<Longrightarrow> presWlsAll (fromIMor h) (fromIMorAbs hA) MOD"
unfolding ipresWlsAll_def presWlsAll_def by simp

lemmas presWlsAll_fromIMorAll_simps =
presWls_fromIMor presWlsAbs_fromIMorAbs presWlsAll_fromIMorAll

text{* Preservation of the constructs *}

lemma presVar_fromIMor[simp]:
"ipresCons h hA (fromMOD MOD) \<Longrightarrow> presVar (fromIMor h) MOD"
unfolding ipresCons_def ipresVar_def presVar_def by simp

lemma presAbs_fromIMor[simp]:
assumes "ipresCons h hA (fromMOD MOD)"
shows "presAbs (fromIMor h) (fromIMorAbs hA) MOD"
using assms unfolding ipresCons_def ipresAbs_def presAbs_def
using assms by fastforce

lemma presOp_fromIMor[simp]:
assumes "ipresCons h hA (fromMOD MOD)"
shows "presOp (fromIMor h) (fromIMorAbs hA) MOD"
using assms unfolding ipresCons_def ipresOp_def presOp_def
using assms by (auto simp: lift_comp)

lemma presCons_fromIMor[simp]:
assumes "ipresCons h hA (fromMOD MOD)"
shows "presCons (fromIMor h) (fromIMorAbs hA) MOD"
unfolding ipresCons_def presCons_def using assms by simp

lemmas presCons_fromIMor_simps =
presVar_fromIMor presAbs_fromIMor presOp_fromIMor presCons_fromIMor

text{* Preservation of freshness *}

lemma presFresh_fromIMor[simp]:
"ipresCons h hA (fromMOD MOD) \<Longrightarrow> ipresFresh h (fromMOD MOD)
 \<Longrightarrow> presFresh (fromIMor h) MOD"
unfolding ipresFresh_def presFresh_def by simp

lemma presFreshAbs_fromIMor[simp]:
"ipresCons h hA (fromMOD MOD) \<Longrightarrow> ipresFreshAbs hA (fromMOD MOD) 
 \<Longrightarrow> presFreshAbs (fromIMorAbs hA) MOD"
unfolding ipresFreshAbs_def presFreshAbs_def by simp

lemma presFreshAll_fromIMor[simp]:
"ipresCons h hA (fromMOD MOD) \<Longrightarrow> ipresFreshAll h hA (fromMOD MOD) 
 \<Longrightarrow> presFreshAll (fromIMor h) (fromIMorAbs hA) MOD"

unfolding ipresFreshAll_def presFreshAll_def by simp

lemmas presFreshAll_fromIMor_simps =
presFresh_fromIMor presFreshAbs_fromIMor presFreshAll_fromIMor

text{* Preservation of swap *}

lemma presSwap_fromIMor[simp]:
"ipresCons h hA (fromMOD MOD) \<Longrightarrow> ipresSwap h (fromMOD MOD) 
 \<Longrightarrow> presSwap (fromIMor h) MOD"
unfolding ipresSwap_def presSwap_def by simp

lemma presSwapAbs_fromIMor[simp]:
"ipresCons h hA (fromMOD MOD) \<Longrightarrow> ipresSwapAbs hA (fromMOD MOD) 
 \<Longrightarrow> presSwapAbs (fromIMorAbs hA) MOD"
unfolding ipresSwapAbs_def presSwapAbs_def by simp

lemma presSwapAll_fromIMor[simp]:
"ipresCons h hA (fromMOD MOD) \<Longrightarrow> ipresSwapAll h hA (fromMOD MOD)
 \<Longrightarrow> presSwapAll (fromIMor h) (fromIMorAbs hA) MOD"
unfolding ipresSwapAll_def presSwapAll_def by simp

lemmas presSwapAll_fromIMor_simps =
presSwap_fromIMor presSwapAbs_fromIMor presSwapAll_fromIMor

text{* Preservation of subst *}

lemma presSubst_fromIMor[simp]:
"ipresCons h hA (fromMOD MOD) \<Longrightarrow> ipresSubst h (fromMOD MOD)
 \<Longrightarrow> presSubst (fromIMor h) MOD"
unfolding ipresSubst_def presSubst_def by auto

lemma presSubstAbs_fromIMor[simp]:
"ipresCons h hA (fromMOD MOD) \<Longrightarrow> ipresSubstAbs h hA (fromMOD MOD) 
 \<Longrightarrow> presSubstAbs (fromIMor h) (fromIMorAbs hA) MOD"
unfolding ipresSubstAbs_def presSubstAbs_def by auto

lemma presSubstAll_fromIMor[simp]:
"ipresCons h hA (fromMOD MOD) \<Longrightarrow> ipresSubstAll h hA (fromMOD MOD) 
 \<Longrightarrow> presSubstAll (fromIMor h) (fromIMorAbs hA) MOD"
unfolding ipresSubstAll_def presSubstAll_def by simp

lemmas presSubstAll_fromIMor_simps =
presSubst_fromIMor presSubstAbs_fromIMor presSubstAll_fromIMor

text{* Morphisms *}

lemma fromIMor_termFSwMorph[simp]:
"termFSwImorph h hA (fromMOD MOD) \<Longrightarrow> termFSwMorph (fromIMor h) (fromIMorAbs hA) MOD"
unfolding termFSwImorph_def termFSwMorph_def by simp

lemma fromIMor_termFSbMorph[simp]:
"termFSbImorph h hA (fromMOD MOD) \<Longrightarrow> termFSbMorph (fromIMor h) (fromIMorAbs hA) MOD"
unfolding termFSbImorph_def termFSbMorph_def by simp

lemma fromIMor_termFSwSbMorph[simp]:
assumes "termFSwSbImorph h hA (fromMOD MOD)"
shows "termFSwSbMorph (fromIMor h) (fromIMorAbs hA) MOD"
using assms unfolding termFSwSbImorph_defs1
using assms unfolding termFSwSbImorph_def termFSwSbMorph_def by simp

lemmas mor_fromIMor_simps =
fromIMor_termFSwMorph fromIMor_termFSbMorph fromIMor_termFSwSbMorph

(********************************)
lemmas fromIMor_predicate_simps =
presCons_fromIMor_simps
presFreshAll_fromIMor_simps
presSwapAll_fromIMor_simps
presSubstAll_fromIMor_simps
mor_fromIMor_simps

lemmas fromIMor_simps =
fromIMor_basic_simps fromIMor_predicate_simps

subsection {* The recursion theorem *}

text{* The recursion maps: *}

definition rec where "rec MOD \<equiv> fromIMor (iter (fromMOD MOD))"

definition recAbs where "recAbs MOD \<equiv> fromIMorAbs (iterAbs (fromMOD MOD))"

text{* Existence: *}

theorem wlsFSw_recAll_termFSwMorph:
"wlsFSw MOD \<Longrightarrow> termFSwMorph (rec MOD) (recAbs MOD) MOD"
by (simp add: rec_def recAbs_def iwlsFSw_iterAll_termFSwImorph)   

theorem wlsFSb_recAll_termFSbMorph:
"wlsFSb MOD \<Longrightarrow> termFSbMorph (rec MOD) (recAbs MOD) MOD"
by (simp add: rec_def recAbs_def iwlsFSb_iterAll_termFSbImorph)

theorem wlsFSwSb_recAll_termFSwSbMorph:
"wlsFSwSb MOD \<Longrightarrow> termFSwSbMorph (rec MOD) (recAbs MOD) MOD"
by (simp add: rec_def recAbs_def iwlsFSwSb_iterAll_termFSwSbImorph) 

theorem wlsFSbSw_recAll_termFSwSbMorph:
"wlsFSbSw MOD \<Longrightarrow> termFSwSbMorph (rec MOD) (recAbs MOD) MOD"
by (simp add: rec_def recAbs_def iwlsFSbSw_iterAll_termFSwSbImorph) 


text{* Uniqueness: *}

lemma presCons_unique:
assumes "presCons f fA MOD" and "presCons g gA MOD"
shows "(wls s X \<longrightarrow> f X = g X) \<and> (wlsAbs (us,s') A \<longrightarrow> fA A = gA A)"
proof(induction rule: wls_rawInduct)
  case (Op delta inp binp)
  hence "lift f inp = lift g inp \<and> lift fA binp = lift gA binp" 
  apply(simp add: lift_def wlsInp_iff wlsBinp_iff sameDom_def liftAll2_def fun_eq_iff split: option.splits)
  by (metis not_Some_eq old.prod.exhaust)
  then show ?case using assms Op unfolding presCons_def presOp_def by simp
qed(insert assms, auto simp: presVar_def presCons_def presAbs_def )

theorem wlsFSw_recAll_unique_presCons:
assumes "wlsFSw MOD" and "presCons h hA MOD"
shows "(wls s X \<longrightarrow> h X = rec MOD X) \<and> 
       (wlsAbs (us,s') A \<longrightarrow> hA A = recAbs MOD A)"
using assms wlsFSw_recAll_termFSwMorph 
by (intro presCons_unique) (auto simp: termFSwMorph_def)

theorem wlsFSb_recAll_unique_presCons:
assumes "wlsFSb MOD" and "presCons h hA MOD"
shows "(wls s X \<longrightarrow> h X = rec MOD X) \<and>
       (wlsAbs (us,s') A \<longrightarrow> hA A = recAbs MOD A)"
using assms wlsFSb_recAll_termFSbMorph 
by (intro presCons_unique) (auto simp: termFSbMorph_def) 

theorem wlsFSwSb_recAll_unique_presCons:
assumes "wlsFSwSb MOD" and "presCons h hA MOD"
shows "(wls s X \<longrightarrow> h X = rec MOD X) \<and>
       (wlsAbs (us,s') A \<longrightarrow> hA A = recAbs MOD A)"
using assms wlsFSw_recAll_unique_presCons unfolding wlsFSwSb_def by blast

theorem wlsFSbSw_recAll_unique_presCons:
assumes "wlsFSbSw MOD" and "presCons h hA MOD"
shows "(wls s X \<longrightarrow> h X = rec MOD X) \<and>
      (wlsAbs (us,s') A \<longrightarrow> hA A = recAbs MOD A)"
using assms wlsFSb_recAll_unique_presCons unfolding wlsFSbSw_def by blast

subsection{* Models that are even ``closer" to the term model *}

text{* We describe various conditions (later referred to as ``extra clauses"
or ``extra conditions")
that, when satisfied by models,
yield the recursive maps
(1) freshness-preserving and/or (2) injective and/or (3) surjective, thus bringing the
considered models ``closer" to (being isomorphic to) the term model.
The extreme case, when all of (1)-(3) above are ensured, means indeed isomorphism to
the term model -- this is in fact an abstract characterization of the term model.  *}

subsubsection {* Relevant predicates on models *}

text{* The fresh clauses reversed *}

definition gFreshGVarRev where
"gFreshGVarRev MOD \<equiv> \<forall> xs y x.
   gFresh MOD xs y (Var xs x) (gVar MOD xs x) \<longrightarrow> y \<noteq> x"

definition gFreshGAbsRev where
"gFreshGAbsRev MOD \<equiv> \<forall> ys y xs x s X' X.
   isInBar (xs,s) \<and> wls s X' \<and> gWls MOD s X \<longrightarrow>
   gFreshAbs MOD ys y (Abs xs x X') (gAbs MOD xs x X' X) \<longrightarrow>
   (ys = xs \<and> y = x) \<or> gFresh MOD ys y X' X"

definition gFreshGOpRev where
"gFreshGOpRev MOD \<equiv> \<forall> ys y delta inp' inp binp' binp.
   wlsInp delta inp' \<and> gWlsInp MOD delta inp \<and> wlsBinp delta binp' \<and> gWlsBinp MOD delta binp \<longrightarrow>
   gFresh MOD ys y (Op delta inp' binp') (gOp MOD delta inp' inp binp' binp) \<longrightarrow>
   gFreshInp MOD ys y inp' inp \<and> gFreshBinp MOD ys y binp' binp"

definition gFreshClsRev where
"gFreshClsRev MOD \<equiv> gFreshGVarRev MOD \<and> gFreshGAbsRev MOD \<and> gFreshGOpRev MOD"

lemmas gFreshClsRev_defs = gFreshClsRev_def
gFreshGVarRev_def gFreshGAbsRev_def gFreshGOpRev_def

text{* Injectiveness of the construct operators *}

definition gVarInj where
"gVarInj MOD \<equiv> \<forall> xs x y. gVar MOD xs x = gVar MOD xs y \<longrightarrow> x = y"

definition gAbsInj where
"gAbsInj MOD \<equiv> \<forall> xs s x X' X X1' X1.
   isInBar (xs,s) \<and> wls s X' \<and> gWls MOD s X \<and> wls s X1' \<and> gWls MOD s X1 \<and>
   gAbs MOD xs x X' X = gAbs MOD xs x X1' X1
   \<longrightarrow>
   X = X1"

definition gOpInj where
"gOpInj MOD \<equiv> \<forall> delta delta1 inp' binp' inp binp inp1' binp1' inp1 binp1.
   wlsInp delta inp' \<and> wlsBinp delta binp' \<and> gWlsInp MOD delta inp \<and> gWlsBinp MOD delta binp \<and>
   wlsInp delta1 inp1' \<and> wlsBinp delta1 binp1' \<and> gWlsInp MOD delta1 inp1 \<and> gWlsBinp MOD delta1 binp1 \<and>
   stOf delta = stOf delta1 \<and>
   gOp MOD delta inp' inp binp' binp = gOp MOD delta1 inp1' inp1 binp1' binp1
   \<longrightarrow>
   delta = delta1 \<and> inp = inp1 \<and> binp = binp1"

definition gVarGOpInj where
"gVarGOpInj MOD \<equiv> \<forall> xs x delta inp' binp' inp binp.
   wlsInp delta inp' \<and> wlsBinp delta binp' \<and> gWlsInp MOD delta inp \<and> gWlsBinp MOD delta binp \<and>
   asSort xs = stOf delta
   \<longrightarrow>
   gVar MOD xs x \<noteq> gOp MOD delta inp' inp binp' binp"

definition gConsInj where
"gConsInj MOD \<equiv> gVarInj MOD \<and> gAbsInj MOD \<and> gOpInj MOD \<and> gVarGOpInj MOD"

lemmas gConsInj_defs = gConsInj_def
gVarInj_def gAbsInj_def gOpInj_def gVarGOpInj_def

text{* Abstraction renaming for swapping *}

definition gAbsRenS where
"gAbsRenS MOD \<equiv> \<forall> xs y x s X' X.
    isInBar (xs,s) \<and> wls s X' \<and> gWls MOD s X \<longrightarrow>
    fresh xs y X' \<and> gFresh MOD xs y X' X \<longrightarrow>
    gAbs MOD xs y (X' #[y \<and> x]_xs) (gSwap MOD xs y x X' X) =
    gAbs MOD xs x X' X"

text{* Indifference to the general-recursive argument *}

text{* . This ``indifference" property says that the construct operators
from the model only depend on
the generalized item (i.e., generalized term or abstraction) argument,
and {\em not} on the ``item" (i.e., concrete term or abstraction) argument.
In other words, the model constructs correspond to {\em iterative clauses},
and not to the more general notion of ``general-recursive" clause.  *}

definition gAbsIndif where
"gAbsIndif MOD \<equiv> \<forall> xs s x X1' X2' X.
    isInBar (xs,s) \<and> wls s X1' \<and> wls s X2' \<and> gWls MOD s X \<longrightarrow>
    gAbs MOD xs x X1' X = gAbs MOD xs x X2' X"

definition gOpIndif where
"gOpIndif MOD \<equiv> \<forall> delta inp1' inp2' inp binp1' binp2' binp.
   wlsInp delta inp1' \<and> wlsBinp delta binp1' \<and> wlsInp delta inp2' \<and> wlsBinp delta binp2' \<and>
   gWlsInp MOD delta inp \<and> gWlsBinp MOD delta binp
   \<longrightarrow>
   gOp MOD delta inp1' inp binp1' binp = gOp MOD delta inp2' inp binp2' binp"

definition gConsIndif where
"gConsIndif MOD \<equiv> gOpIndif MOD \<and> gAbsIndif MOD"

lemmas gConsIndif_defs = gConsIndif_def gAbsIndif_def gOpIndif_def

text{* Inductiveness *}

text{* . Inductiveness of a model means the satisfaction of a minimal inductive
principle (``minimal" in the sense that no fancy swapping or freshness
induction-friendly conditions are involved).     *}

definition gInduct where
"gInduct MOD \<equiv> \<forall> phi phiAbs s X us s' A.
   (
    (\<forall> xs x. phi (asSort xs) (gVar MOD xs x))
    \<and>
    (\<forall> delta inp' inp binp' binp.
       wlsInp delta inp' \<and> wlsBinp delta binp' \<and> gWlsInp MOD delta inp \<and> gWlsBinp MOD delta binp \<and>
       liftAll2 phi (arOf delta) inp \<and> liftAll2 phiAbs (barOf delta) binp
       \<longrightarrow> phi (stOf delta) (gOp MOD delta inp' inp binp' binp))
    \<and>
    (\<forall> xs s x X' X.
        isInBar (xs,s) \<and> wls s X' \<and> gWls MOD s X \<and>
        phi s X
        \<longrightarrow> phiAbs (xs,s) (gAbs MOD xs x X' X))
   )
   \<longrightarrow>
   (gWls MOD s X \<longrightarrow> phi s X) \<and>
   (gWlsAbs MOD (us,s') A \<longrightarrow> phiAbs (us,s') A)"

lemma gInduct_elim:
assumes "gInduct MOD" and
Var: "\<And> xs x. phi (asSort xs) (gVar MOD xs x)" and
Op:
"\<And> delta inp' inp binp' binp.
    \<lbrakk>wlsInp delta inp'; wlsBinp delta binp'; gWlsInp MOD delta inp; gWlsBinp MOD delta binp;
     liftAll2 phi (arOf delta) inp; liftAll2 phiAbs (barOf delta) binp\<rbrakk>
    \<Longrightarrow> phi (stOf delta) (gOp MOD delta inp' inp binp' binp)" and
Abs:
"\<And> xs s x X' X.
   \<lbrakk>isInBar (xs,s); wls s X'; gWls MOD s X; phi s X\<rbrakk>
   \<Longrightarrow> phiAbs (xs,s) (gAbs MOD xs x X' X)"
shows
"(gWls MOD s X \<longrightarrow> phi s X) \<and>
 (gWlsAbs MOD (us,s') A \<longrightarrow> phiAbs (us,s') A)"
using assms unfolding gInduct_def
apply(elim allE[of _ phi] allE[of _ phiAbs] allE[of _ s] allE[of _ X]) 
apply(elim allE[of _ us] allE[of _ s'] allE[of _ A])
by blast

subsubsection {* Relevant predicates on maps from the term model *}

text{* Reflection of freshness *}

definition reflFresh where
"reflFresh h MOD \<equiv> \<forall> ys y s X.
   wls s X \<longrightarrow>
   gFresh MOD ys y X (h X) \<longrightarrow> fresh ys y X"

definition reflFreshAbs where
"reflFreshAbs hA MOD \<equiv> \<forall> ys y us s A.
   wlsAbs (us,s) A \<longrightarrow>
   gFreshAbs MOD ys y A (hA A) \<longrightarrow> freshAbs ys y A"

definition reflFreshAll where
"reflFreshAll h hA MOD \<equiv> reflFresh h MOD \<and> reflFreshAbs hA MOD"

lemmas reflFreshAll_defs = reflFreshAll_def
reflFresh_def reflFreshAbs_def

text{* Injectiveness *}

definition isInj where
"isInj h \<equiv> \<forall> s X Y.
   wls s X \<and> wls s Y \<longrightarrow>
   h X = h Y \<longrightarrow> X = Y"

definition isInjAbs where
"isInjAbs hA \<equiv> \<forall> us s A B.
   wlsAbs (us,s) A \<and> wlsAbs (us,s) B \<longrightarrow>
   hA A = hA B \<longrightarrow> A = B"

definition isInjAll where
"isInjAll h hA \<equiv> isInj h \<and> isInjAbs hA"

lemmas isInjAll_defs = isInjAll_def
isInj_def isInjAbs_def

text{* Surjectiveness *}

definition isSurj where
"isSurj h MOD \<equiv> \<forall> s X.
   gWls MOD s X \<longrightarrow>
   (\<exists> X'. wls s X' \<and> h X' = X)"

definition isSurjAbs where
"isSurjAbs hA MOD \<equiv> \<forall> us s A.
   gWlsAbs MOD (us,s) A \<longrightarrow>
   (\<exists> A'. wlsAbs (us,s) A' \<and> hA A' = A)"

definition isSurjAll where
"isSurjAll h hA MOD \<equiv> isSurj h MOD \<and> isSurjAbs hA MOD"

lemmas isSurjAll_defs = isSurjAll_def
isSurj_def isSurjAbs_def

subsubsection{* Criterion for the reflection of freshness *}

text{* First an auxiliary fact, independent of the type of model:  *}

lemma gFreshClsRev_recAll_reflFreshAll:
assumes pWls: "presWlsAll (rec MOD) (recAbs MOD) MOD"
and pCons: "presCons (rec MOD) (recAbs MOD) MOD"
and pFresh: "presFreshAll (rec MOD) (recAbs MOD) MOD"
and **: "gFreshClsRev MOD"
shows "reflFreshAll (rec MOD) (recAbs MOD) MOD"
proof-
  let ?h = "rec MOD"   let ?hA = "recAbs MOD"
  have pWlsInps[simp]:
  "\<And> delta inp. wlsInp delta inp \<Longrightarrow> gWlsInp MOD delta (lift ?h inp)"
  "\<And> delta binp. wlsBinp delta binp \<Longrightarrow> gWlsBinp MOD delta (lift ?hA binp)"
  using pWls presWls_wlsInp presWls_wlsBinp unfolding presWlsAll_def by auto
  {fix ys y s X us s' A
   have
   "(wls s X \<longrightarrow> gFresh MOD ys y X (rec MOD X) \<longrightarrow> fresh ys y X) \<and>
    (wlsAbs (us,s') A \<longrightarrow> gFreshAbs MOD ys y A (recAbs MOD A) \<longrightarrow> freshAbs ys y A)"
   proof(induction rule: wls_induct)
     case (Var xs x)
     then show ?case using assms 
     by (fastforce simp: presWlsAll_defs presCons_defs gFreshClsRev_def gFreshGVarRev_def)
   next
     case (Op delta inp binp)
     show ?case proof safe
       let ?ar = "arOf delta"   let ?bar = "barOf delta"  let ?st = "stOf delta" 
     let ?linp = "lift ?h inp"  let ?lbinp = "lift ?hA binp"
     assume "gFresh MOD ys y (Op delta inp binp) (rec MOD (Op delta inp binp))"
     hence "gFresh MOD ys y (Op delta inp binp) (gOp MOD delta inp ?linp binp ?lbinp)" 
     using assms Op by (simp add: presCons_def presOp_def)
     hence "gFreshInp MOD ys y inp ?linp \<and> gFreshBinp MOD ys y binp ?lbinp"
     using Op **  by (force simp:  gFreshClsRev_def gFreshGOpRev_def)
     with Op have freshInp: "freshInp ys y inp \<and> freshBinp ys y binp"     
     by (simp add: freshInp_def freshBinp_def liftAll_def gFreshInp_def gFreshBinp_def liftAll2_def lift_def 
     sameDom_def wlsInp_iff wlsBinp_iff split: option.splits) (metis eq_snd_iff not_Some_eq) 
     thus "fresh ys y (Op delta inp binp)" using Op by auto
   qed
 next
   case (Abs s xs x X)
   show ?case proof safe  
     have hX: "gWls MOD s (?h X)" using Abs pWls unfolding presWlsAll_defs by simp
     assume "gFreshAbs MOD ys y (Abs xs x X) (recAbs MOD (Abs xs x X))" 
     hence "gFreshAbs MOD ys y (Abs xs x X) (gAbs MOD xs x X (rec MOD X))" 
     using Abs by (metis pCons presAbs_def presCons_def)
     moreover have "?hA (Abs xs x X) = gAbs MOD xs x X (?h X)"
     using Abs pCons unfolding presCons_defs by blast
     ultimately have 1: "gFreshAbs MOD ys y (Abs xs x X) (gAbs MOD xs x X (?h X))" by simp
     show "freshAbs ys y (Abs xs x X)"
     using assms hX Abs ** unfolding gFreshClsRev_def gFreshGAbsRev_def using 1 by fastforce
   qed
  qed
  }
  thus ?thesis unfolding reflFreshAll_defs by blast
qed
 
text{* For fresh-swap models *}

theorem wlsFSw_recAll_reflFreshAll:
"wlsFSw MOD \<Longrightarrow> gFreshClsRev MOD \<Longrightarrow> reflFreshAll (rec MOD) (recAbs MOD) MOD"
using wlsFSw_recAll_termFSwMorph 
by (auto simp: termFSwMorph_def intro: gFreshClsRev_recAll_reflFreshAll)

text{* For fresh-subst models *}

theorem wlsFSb_recAll_reflFreshAll:
"wlsFSb MOD \<Longrightarrow> gFreshClsRev MOD \<Longrightarrow> reflFreshAll (rec MOD) (recAbs MOD) MOD"
using wlsFSb_recAll_termFSbMorph 
by (auto simp: termFSbMorph_def intro: gFreshClsRev_recAll_reflFreshAll)
 

(* Note: Here and below: No need for corresponding results for FSwSb and FSbSw models, as they
would follow at once from the above. *)

subsubsection{* Criterion for the injectiveness of the recursive map *}

text{* For fresh-swap models *}

theorem wlsFSw_recAll_isInjAll:
assumes *: "wlsFSw MOD"  "gAbsRenS MOD" and **: "gConsInj MOD"
shows "isInjAll (rec MOD) (recAbs MOD)"
proof-
  let ?h = "rec MOD"   let ?hA = "recAbs MOD"
  have 1: "termFSwMorph ?h ?hA MOD" using * wlsFSw_recAll_termFSwMorph by auto
  hence pWls: "presWlsAll ?h ?hA MOD"
  and pCons: "presCons ?h ?hA MOD"
  and pFresh: "presFreshAll ?h ?hA MOD"
  and pSwap: "presSwapAll ?h ?hA MOD" unfolding termFSwMorph_def by auto
  hence pWlsInps[simp]:
  "\<And> delta inp. wlsInp delta inp \<Longrightarrow> gWlsInp MOD delta (lift ?h inp)"
  "\<And> delta binp. wlsBinp delta binp \<Longrightarrow> gWlsBinp MOD delta (lift ?hA binp)"
  using presWls_wlsInp presWls_wlsBinp unfolding presWlsAll_def by auto
  {fix s X us s' A
   have
   "(wls s X \<longrightarrow> (\<forall> Y. wls s Y \<and> rec MOD X = rec MOD Y \<longrightarrow> X = Y)) \<and>
    (wlsAbs (us,s') A \<longrightarrow> (\<forall> B. wlsAbs (us,s') B \<and> recAbs MOD A = recAbs MOD B \<longrightarrow> A = B))"
   proof (induction rule: wls_induct) 
     case (Var xs x)
     show ?case proof clarify
       fix Y
       assume eq: "rec MOD (Var xs x) = rec MOD Y" and Y: "wls (asSort xs) Y"
       thus "Var xs x = Y" 
       proof-
         {fix ys y assume Y_def: "Y = Var ys y" and "asSort ys = asSort xs"
          hence ys_def: "ys = xs" by simp
          have rec_y_def: "rec MOD (Var ys y) = gVar MOD ys y"
          using pCons unfolding presCons_defs by simp
          have ?thesis
          using eq ** 1 unfolding Y_def rec_y_def gConsInj_def gVarInj_def
          unfolding ys_def by (simp add: termFSwMorph_defs)
         }
         moreover
         {fix delta1 inp1 binp1 assume inp1s: "wlsInp delta1 inp1"  "wlsBinp delta1 binp1"
          and Y_def: "Y = Op delta1 inp1 binp1" and st: "stOf delta1 = asSort xs"
          hence rec_Op_def:
          "rec MOD (Op delta1 inp1 binp1) =
           gOp MOD delta1 inp1 (lift ?h inp1) binp1 (lift ?hA binp1)"
          using pCons unfolding presCons_defs by simp
          have ?thesis
          using eq ** unfolding Y_def rec_Op_def gConsInj_def gVarGOpInj_def
          using inp1s st 1 by (simp add: termFSwMorph_defs)
         }
         ultimately show ?thesis using wls_nchotomy[of "asSort xs" Y] Y by blast
       qed 
     qed   
   next
     case (Op delta inp binp)
     show ?case proof clarify
       fix Y assume Y: "wls (stOf delta) Y"
       and "rec MOD (Op delta inp binp) = rec MOD Y"
       hence eq: "gOp MOD delta inp (lift ?h inp) binp (lift ?hA binp) = ?h Y"
       using 1 Op by (simp add: termFSwMorph_defs)
       show "Op delta inp binp = Y"
       proof-
         {fix ys y assume Y_def: "Y = Var ys y" and st: "asSort ys = stOf delta"
          have rec_y_def: "rec MOD (Var ys y) = gVar MOD ys y"
          using pCons unfolding presCons_defs by simp
          have ?thesis
          using eq[THEN sym] ** unfolding Y_def rec_y_def gConsInj_def gVarGOpInj_def
          using Op st by simp
         }
         moreover
         {fix delta1 inp1 binp1 assume inp1s: "wlsInp delta1 inp1"  "wlsBinp delta1 binp1"
          and Y_def: "Y = Op delta1 inp1 binp1" and st: "stOf delta1 = stOf delta"
          hence rec_Op_def:
          "rec MOD (Op delta1 inp1 binp1) =
           gOp MOD delta1 inp1 (lift ?h inp1) binp1 (lift ?hA binp1)"
          using pCons unfolding presCons_defs by simp
          have 0: "delta = delta1 \<and> lift ?h inp = lift ?h inp1 \<and> lift ?hA binp = lift ?hA binp1"
          using eq ** unfolding Y_def rec_Op_def gConsInj_def gOpInj_def
          using Op inp1s st apply clarify
          apply(erule allE[of _ delta])  apply(erule allE[of _ delta1]) by force
          hence delta1_def: "delta1 = delta" by simp
          have 1: "inp = inp1"   
          proof(rule ext)
            fix i
            show "inp i = inp1 i"  
            proof(cases "inp i")
              case None
              hence "lift ?h inp i = None" by(simp add: lift_None)
              hence "lift ?h inp1 i = None" using 0 by simp
              thus ?thesis unfolding None by(simp add: lift_None)
            next
              case (Some X) 
              hence "lift ?h inp i = Some (?h X)" unfolding lift_def by simp
              hence "lift ?h inp1 i = Some (?h X)" using 0 by simp
              then obtain Y where inp1_i: "inp1 i = Some Y" and hXY: "?h X = ?h Y"
              unfolding lift_def by(cases "inp1 i") auto
              then obtain s where ar_i: "arOf delta i = Some s"
              using inp1s unfolding delta1_def wlsInp_iff sameDom_def 
              by (cases "arOf delta i") auto
              hence Y: "wls s Y"
              using inp1s inp1_i unfolding delta1_def wlsInp_iff liftAll2_def by auto
              thus ?thesis 
              unfolding Some inp1_i using ar_i Some hXY Op.IH unfolding liftAll2_def by auto
            qed
          qed
          have 2: "binp = binp1"
          proof(rule ext)
            fix i
            show "binp i = binp1 i"
            proof(cases "binp i")
              case None
              hence "lift ?hA binp i = None" by(simp add: lift_None)
              hence "lift ?hA binp1 i = None" using 0 by simp
              thus ?thesis unfolding None by (simp add: lift_None)
            next
              case (Some A)
              hence "lift ?hA binp i = Some (?hA A)" unfolding lift_def by simp
              hence "lift ?hA binp1 i = Some (?hA A)" using 0 by simp
              then obtain B where binp1_i: "binp1 i = Some B" and hAB: "?hA A = ?hA B"
              unfolding lift_def by (cases "binp1 i") auto
              then obtain us s where bar_i: "barOf delta i = Some (us,s)"
              using inp1s unfolding delta1_def wlsBinp_iff sameDom_def
              by(cases "barOf delta i") auto
              hence B: "wlsAbs (us,s) B"
              using inp1s binp1_i unfolding delta1_def wlsBinp_iff liftAll2_def by auto
              thus ?thesis unfolding Some binp1_i  
              using bar_i Some hAB Op.IH unfolding liftAll2_def by fastforce
            qed
          qed
          have ?thesis unfolding Y_def delta1_def 1 2 by simp
         }
         ultimately show ?thesis using wls_nchotomy[of "stOf delta" Y] Y by blast
       qed
     qed
   next
     case (Abs s xs x X)
     show ?case proof clarify
       fix B
       assume B: "wlsAbs (xs,s) B" and "recAbs MOD (Abs xs x X) = recAbs MOD B"
       hence eq: "gAbs MOD xs x X (rec MOD X) = ?hA B" using 1 Abs by (simp add: termFSwMorph_defs)
       hence hX: "gWls MOD s (?h X)" using pWls Abs unfolding presWlsAll_defs by simp
       show "Abs xs x X = B"
       proof-
         let ?P = "ParS
          (\<lambda> xs'. [])
          (\<lambda> s'. if s' = s then [X] else [])
          (\<lambda> us_s. [])
          []"
         have P: "wlsPar ?P" using Abs unfolding wlsPar_def by simp
         {fix y Y assume Y: "wls s Y" and B_def: "B = Abs xs y Y"
          hence hY: "gWls MOD s (?h Y)" using pWls unfolding presWlsAll_defs by simp
          let ?Xsw = "X #[y \<and> x]_xs" let ?hXsw = "gSwap MOD xs y x X (?h X)"
          have hXsw: "gWls MOD s ?hXsw"
          using Abs hX using * unfolding wlsFSw_def gSwapAllPresGWlsAll_defs by simp
          assume "\<forall> s. \<forall> Y \<in> termsOfS ?P s. fresh xs y Y"
          hence y_fresh: "fresh xs y X" by simp
          hence "gFresh MOD xs y X (?h X)"
          using Abs pFresh unfolding presFreshAll_defs by simp
          hence "gAbs MOD xs y (?Xsw) ?hXsw = gAbs MOD xs x X (?h X)"
          using Abs hX y_fresh * unfolding gAbsRenS_def by fastforce 
          also have "\<dots> = ?hA B" using eq . 
          also have "recAbs MOD B = gAbs MOD xs y Y (?h Y)"          
          unfolding B_def using pCons Abs Y unfolding presCons_defs by blast 
          finally have "gAbs MOD xs y ?Xsw ?hXsw = gAbs MOD xs y Y (?h Y)" .
          hence "?hXsw = ?h Y"
          using ** Abs hX hXsw Y hY unfolding gConsInj_def gAbsInj_def
          apply clarify apply(erule allE[of _ xs]) apply(erule allE[of _ s])
          apply(erule allE[of _ y]) apply(erule allE[of _ ?Xsw]) by fastforce
          moreover have "?hXsw = ?h ?Xsw"
          using Abs pSwap unfolding presSwapAll_defs by simp
          ultimately have "?h ?Xsw = ?h Y" by simp
          moreover have "(X,?Xsw) \<in> swapped" using swap_swapped .
          ultimately have Y_def: "Y = ?Xsw" using Y Abs.IH by auto
          have ?thesis unfolding B_def Y_def
          using Abs y_fresh by simp
         }
         thus ?thesis using B P wlsAbs_fresh_nchotomy[of xs s B] by blast
       qed
     qed
   qed
  }
  thus ?thesis unfolding isInjAll_defs by blast
qed


text{* For fresh-subst models *}

theorem wlsFSb_recAll_isInjAll:
assumes *: "wlsFSb MOD" and **: "gConsInj MOD"
shows "isInjAll (rec MOD) (recAbs MOD)"
proof-
  let ?h = "rec MOD"   let ?hA = "recAbs MOD"
  have 1: "termFSbMorph ?h ?hA MOD" using * wlsFSb_recAll_termFSbMorph by auto
  hence pWls: "presWlsAll ?h ?hA MOD"
  and pCons: "presCons ?h ?hA MOD"
  and pFresh: "presFreshAll ?h ?hA MOD"
  and pSubst: "presSubstAll ?h ?hA MOD" unfolding termFSbMorph_def by auto
  hence pWlsInps[simp]:
  "\<And> delta inp. wlsInp delta inp \<Longrightarrow> gWlsInp MOD delta (lift ?h inp)"
  "\<And> delta binp. wlsBinp delta binp \<Longrightarrow> gWlsBinp MOD delta (lift ?hA binp)"
  using presWls_wlsInp presWls_wlsBinp unfolding presWlsAll_def by auto
  {fix s X us s' A
   have
   "(wls s X \<longrightarrow> (\<forall> Y. wls s Y \<and> rec MOD X = rec MOD Y \<longrightarrow> X = Y)) \<and>
    (wlsAbs (us,s') A \<longrightarrow> (\<forall> B. wlsAbs (us,s') B \<and> recAbs MOD A = recAbs MOD B \<longrightarrow> A = B))"
   proof(induction rule: wls_induct)
     case (Var xs x)
     show ?case proof clarify
       fix Y
       assume "rec MOD (Var xs x) = rec MOD Y" and Y: "wls (asSort xs) Y"
       hence eq: "gVar MOD xs x = rec MOD Y" using 1 by (simp add: termFSbMorph_defs)
       show "Var xs x = Y"
       proof-
         {fix ys y assume Y_def: "Y = Var ys y" and "asSort ys = asSort xs"
          hence ys_def: "ys = xs" by simp
          have rec_y_def: "rec MOD (Var ys y) = gVar MOD ys y"
          using pCons unfolding presCons_defs by simp
          have ?thesis
          using eq ** unfolding Y_def rec_y_def gConsInj_def gVarInj_def
          unfolding ys_def by simp
         }
         moreover
         {fix delta1 inp1 binp1 assume inp1s: "wlsInp delta1 inp1"  "wlsBinp delta1 binp1"
          and Y_def: "Y = Op delta1 inp1 binp1" and st: "stOf delta1 = asSort xs"
          hence rec_Op_def:
          "rec MOD (Op delta1 inp1 binp1) =
           gOp MOD delta1 inp1 (lift ?h inp1) binp1 (lift ?hA binp1)"
          using pCons unfolding presCons_defs by simp
          have ?thesis
          using eq ** unfolding Y_def rec_Op_def gConsInj_def gVarGOpInj_def
          using inp1s st by simp
         }
         ultimately show ?thesis using wls_nchotomy[of "asSort xs" Y] Y by blast
       qed
     qed
   next
     case (Op delta inp binp)
     show ?case proof clarify
       fix Y
       assume  "rec MOD (Op delta inp binp) = rec MOD Y" and Y: "wls (stOf delta) Y"
       hence eq: "gOp MOD delta inp (lift ?h inp) binp (lift ?hA binp) = ?h Y"
       using Op 1 by (simp add: termFSbMorph_defs)
       show "Op delta inp binp = Y"
       proof-
         {fix ys y assume Y_def: "Y = Var ys y" and st: "asSort ys = stOf delta"
          have rec_y_def: "rec MOD (Var ys y) = gVar MOD ys y"
          using pCons unfolding presCons_defs by simp
          have ?thesis
          using eq[THEN sym] ** unfolding Y_def rec_y_def gConsInj_def gVarGOpInj_def
          using Op st by simp
         }
         moreover
         {fix delta1 inp1 binp1 assume inp1s: "wlsInp delta1 inp1"  "wlsBinp delta1 binp1"
          and Y_def: "Y = Op delta1 inp1 binp1" and st: "stOf delta1 = stOf delta"
          hence rec_Op_def:
          "rec MOD (Op delta1 inp1 binp1) =
           gOp MOD delta1 inp1 (lift ?h inp1) binp1 (lift ?hA binp1)"
          using pCons unfolding presCons_defs by simp
          have 0: "delta = delta1 \<and> lift ?h inp = lift ?h inp1 \<and> lift ?hA binp = lift ?hA binp1"
          using eq ** unfolding Y_def rec_Op_def gConsInj_def gOpInj_def
          using Op inp1s st apply clarify
          apply(erule allE[of _ delta])  apply(erule allE[of _ delta1]) by force
          hence delta1_def: "delta1 = delta" by simp
          have 1: "inp = inp1"
          proof(rule ext)
            fix i
            show "inp i = inp1 i"
            proof(cases "inp i")
              case None
              hence "lift ?h inp i = None" by(simp add: lift_None)
              hence "lift ?h inp1 i = None" using 0 by simp
              thus ?thesis unfolding None by(simp add: lift_None)
            next
              case (Some X)
              hence "lift ?h inp i = Some (?h X)" unfolding lift_def by simp
              hence "lift ?h inp1 i = Some (?h X)" using 0 by simp
              then obtain Y where inp1_i: "inp1 i = Some Y" and hXY: "?h X = ?h Y"
              unfolding lift_def by (cases "inp1 i") auto
              then obtain s where ar_i: "arOf delta i = Some s"
              using inp1s unfolding delta1_def wlsInp_iff sameDom_def
              by (cases "arOf delta i") auto
              hence Y: "wls s Y"
              using inp1s inp1_i unfolding delta1_def wlsInp_iff liftAll2_def by auto
              thus ?thesis unfolding Some inp1_i  
              using ar_i Some hXY Op.IH unfolding liftAll2_def by auto
            qed
          qed
          have 2: "binp = binp1"
          proof(rule ext)
            fix i
            show "binp i = binp1 i"
            proof(cases "binp i")
              case None
              hence "lift ?hA binp i = None" by(simp add: lift_None)
              hence "lift ?hA binp1 i = None" using 0 by simp
              thus ?thesis unfolding None by(simp add: lift_None)
            next
              case (Some A)
              hence "lift ?hA binp i = Some (?hA A)" unfolding lift_def by simp
              hence "lift ?hA binp1 i = Some (?hA A)" using 0 by simp
              then obtain B where binp1_i: "binp1 i = Some B" and hAB: "?hA A = ?hA B"
              unfolding lift_def by(cases "binp1 i", auto)
              then obtain us s where bar_i: "barOf delta i = Some (us,s)"
              using inp1s unfolding delta1_def wlsBinp_iff sameDom_def
              by(cases "barOf delta i") auto
              hence B: "wlsAbs (us,s) B"
              using inp1s binp1_i unfolding delta1_def wlsBinp_iff liftAll2_def by auto
              thus ?thesis unfolding Some binp1_i 
              using bar_i Some hAB Op.IH
              unfolding liftAll2_def by fastforce
            qed
          qed
          have ?thesis unfolding Y_def delta1_def 1 2 by simp
         }
         ultimately show ?thesis using wls_nchotomy[of "stOf delta" Y] Y by blast
       qed
     qed
   next
     case (Abs s xs x X)
     show ?case proof clarify
       fix B
       assume B: "wlsAbs (xs,s) B" and "recAbs MOD (Abs xs x X) = recAbs MOD B"
       hence eq: "gAbs MOD xs x X (rec MOD X) = ?hA B" 
       using 1 Abs by (simp add: termFSbMorph_defs)
       hence hX: "gWls MOD s (?h X)" using pWls Abs unfolding presWlsAll_defs by simp
       show "Abs xs x X = B"
       proof-
         let ?P = "ParS
          (\<lambda> xs'. [])
          (\<lambda> s'. if s' = s then [X] else [])
          (\<lambda> us_s. [])
          []"
         have P: "wlsPar ?P" using Abs unfolding wlsPar_def by simp
         {fix y Y assume Y: "wls s Y" and B_def: "B = Abs xs y Y"
          hence hY: "gWls MOD s (?h Y)" using pWls unfolding presWlsAll_defs by simp
          let ?Xsb = "X #[y // x]_xs"
          let ?hXsb = "gSubst MOD xs (Var xs y) (gVar MOD xs y) x X (?h X)"
          have 1: "wls (asSort xs) (Var xs y) \<and> gWls MOD (asSort xs) (gVar MOD xs y)"
          using * unfolding wlsFSb_def gConsPresGWls_defs by simp
          hence hXsb: "gWls MOD s ?hXsb"
          using Abs hX using * unfolding wlsFSb_def gSubstAllPresGWlsAll_defs by simp
          assume "\<forall> s. \<forall> Y \<in> termsOfS ?P s. fresh xs y Y"
          hence y_fresh: "fresh xs y X" by simp
          hence "gFresh MOD xs y X (?h X)"
          using Abs pFresh unfolding presFreshAll_defs by simp
          hence "gAbs MOD xs y (?Xsb) ?hXsb = gAbs MOD xs x X (?h X)"
          using Abs hX y_fresh * unfolding wlsFSb_def gAbsRen_def by fastforce
          also have "\<dots> = ?hA B" using eq .
          also have "\<dots> = gAbs MOD xs y Y (?h Y)"
          unfolding B_def using pCons Abs Y unfolding presCons_defs by blast
          finally have
          "gAbs MOD xs y ?Xsb ?hXsb = gAbs MOD xs y Y (?h Y)" .
          hence "?hXsb = ?h Y"
          using ** Abs hX hXsb Y hY unfolding gConsInj_def gAbsInj_def
          apply clarify apply(erule allE[of _ xs]) apply(erule allE[of _ s])
          apply(erule allE[of _ y]) apply(erule allE[of _ ?Xsb]) by fastforce
          moreover have "?hXsb = ?h ?Xsb"
          using Abs pSubst 1 pCons unfolding presSubstAll_defs vsubst_def presCons_defs by simp
          ultimately have "?h ?Xsb = ?h Y" by simp
          hence Y_def: "Y = ?Xsb" using Y Abs.IH by (fastforce simp add: termFSbMorph_defs)
          have ?thesis unfolding B_def Y_def
          using Abs y_fresh by simp
         }
         thus ?thesis using B P wlsAbs_fresh_nchotomy[of xs s B] by blast
       qed
     qed
   qed 
  }
  thus ?thesis unfolding isInjAll_defs by blast
qed

subsubsection{* Criterion for the surjectiveness of the recursive map *}

text{* First an auxiliary fact, independent of the type of model:  *}

lemma gInduct_gConsIndif_recAll_isSurjAll:
assumes pWls: "presWlsAll (rec MOD) (recAbs MOD) MOD"
and pCons: "presCons (rec MOD) (recAbs MOD) MOD"
and "gConsIndif MOD" and *: "gInduct MOD"
shows "isSurjAll (rec MOD) (recAbs MOD) MOD"
proof-
  let ?h = "rec MOD"   let ?hA = "recAbs MOD"
  {fix s X us s' A
   from * have
   "(gWls MOD s X \<longrightarrow> (\<exists> X'. wls s X' \<and> rec MOD X' = X)) \<and>
    (gWlsAbs MOD (us,s') A \<longrightarrow> (\<exists> A'. wlsAbs (us,s') A' \<and> recAbs MOD A' = A))"
   proof (elim gInduct_elim, safe)
     fix xs x
     show "\<exists>X'. wls (asSort xs) X' \<and> rec MOD X' = gVar MOD xs x"
     using pWls pCons 
     by (auto simp: presWlsAll_defs presCons_defs intro: exI[of _ "Var xs x"]) 
   next
     fix delta inp' inp binp' binp
     let ?ar = "arOf delta"   let ?bar = "barOf delta"  let ?st = "stOf delta"
     assume inp': "wlsInp delta inp'" and binp': "wlsBinp delta binp'"
     and inp: "gWlsInp MOD delta inp" and binp: "gWlsBinp MOD delta binp"
     and IH: "liftAll2 (\<lambda>s X. \<exists>X'. wls s X' \<and> ?h X' = X) ?ar inp"
     and BIH: "liftAll2 (\<lambda>us_s A. \<exists>A'. wlsAbs us_s A' \<and> ?hA A' = A) ?bar binp"
     (*  *)
     let ?phi = "\<lambda> s X X'. wls s X' \<and> ?h X' = X"
     obtain inp1' where inp1'_def:
     "inp1' =
      (\<lambda> i.
         case (?ar i, inp i) of
           (None, None) \<Rightarrow> None
          |(Some s, Some X) \<Rightarrow> Some (SOME X'. ?phi s X X'))" by blast
     hence [simp]:
     "\<And> i. ?ar i = None \<and> inp i = None \<Longrightarrow> inp1' i = None"
     "\<And> i s X. ?ar i = Some s \<and> inp i = Some X \<Longrightarrow> inp1' i = Some (SOME X'. ?phi s X X')"
     unfolding inp1'_def by auto
     have inp1': "wlsInp delta inp1'"
     unfolding wlsInp_iff proof safe
       show "sameDom ?ar inp1'"
       unfolding sameDom_def proof clarify
         fix i
         have "(?ar i = None) = (inp i = None)"
         using inp unfolding gWlsInp_def sameDom_def by simp
         thus "(?ar i = None) = (inp1' i = None)"
         unfolding inp1'_def by auto
       qed
     next
       show "liftAll2 wls ?ar inp1'"
       unfolding liftAll2_def proof auto
         fix i s X1'
         assume ari: "?ar i = Some s" and inp1'i: "inp1' i = Some X1'"
         have "sameDom inp ?ar"
         using inp unfolding gWlsInp_def using sameDom_sym by blast
         then obtain X where inpi: "inp i = Some X"
         using ari unfolding sameDom_def by(cases "inp i") auto
         hence X1'_def: "X1' = (SOME X1'. ?phi s X X1')"
         using ari inp1'i unfolding inp1'_def by simp
         obtain X' where X': "?phi s X X'"
         using inpi ari IH unfolding liftAll2_def by blast
         hence "?phi s X X1'"
         unfolding X1'_def by(rule someI[of "?phi s X"])
         thus "wls s X1'" by simp
       qed
     qed(insert binp' wlsBinp.cases, blast)
     (* *)
     have lift_inp1': "lift ?h inp1' = inp"
     proof(rule ext)
       fix i let ?linp1' = "lift ?h inp1'"
       show "?linp1' i = inp i"
       proof(cases "inp i")
         case None
         hence "?ar i = None" using inp unfolding gWlsInp_def sameDom_def by simp
         hence "inp1' i = None" using None by simp 
         thus "lift (rec MOD) inp1' i = inp i" using None by (auto simp: lift_def)
       next
         case (Some X)
         then obtain s where ari: "?ar i = Some s"
         using inp unfolding gWlsInp_def sameDom_def by(cases "?ar i") auto
         let ?X1' = "SOME X1'. ?phi s X X1'"
         have inp1'i: "inp1' i = Some ?X1'" using ari Some by simp
         hence linp1'i: "?linp1' i = Some (?h ?X1')" unfolding lift_def by simp
         obtain X' where X': "?phi s X X'"
         using Some ari IH unfolding liftAll2_def by blast
         hence "?phi s X ?X1'" by(rule someI[of "?phi s X"])
         thus "lift (rec MOD) inp1' i = inp i" using Some linp1'i by (auto simp: lift_def)
       qed
     qed
     (*  *)
     let ?bphi = "\<lambda> (us,s) A A'. wlsAbs (us,s) A' \<and> ?hA A' = A"
     obtain binp1' where binp1'_def:
     "binp1' =
      (\<lambda> i.
         case (?bar i, binp i) of
           (None, None) \<Rightarrow> None
          |(Some (us,s), Some A) \<Rightarrow> Some (SOME A'. ?bphi (us,s) A A'))" by blast
     hence [simp]:
     "\<And> i. ?bar i = None \<and> binp i = None \<Longrightarrow> binp1' i = None"
     and *:
     "\<And> i us s A. ?bar i = Some (us,s) \<and> binp i = Some A \<Longrightarrow>
        binp1' i = Some (SOME A'. ?bphi (us,s) A A')"
     unfolding binp1'_def by auto
     have binp1': "wlsBinp delta binp1'"
     unfolding wlsBinp_iff proof safe
       show "sameDom ?bar binp1'"
       unfolding sameDom_def proof clarify
         fix i
         have "(?bar i = None) = (binp i = None)"
         using binp unfolding gWlsBinp_def sameDom_def by simp
         thus "(?bar i = None) = (binp1' i = None)"
         unfolding binp1'_def by auto
       qed
     next
       show "liftAll2 wlsAbs ?bar binp1'"
       unfolding liftAll2_def proof auto
         fix i us s A1'
         assume bari: "?bar i = Some (us,s)" and binp1'i: "binp1' i = Some A1'"
         have "sameDom binp ?bar"
         using binp unfolding gWlsBinp_def using sameDom_sym by blast
         then obtain A where binpi: "binp i = Some A"
         using bari unfolding sameDom_def by(cases "binp i", auto)
         hence A1'_def: "A1' = (SOME A1'. ?bphi (us,s) A A1')"
         using bari binp1'i unfolding binp1'_def by simp
         obtain A' where A': "?bphi (us,s) A A'"
         using binpi bari BIH unfolding liftAll2_def by fastforce
         hence "?bphi (us,s) A A1'"
         unfolding A1'_def by(rule someI[of "?bphi (us,s) A"])
         thus "wlsAbs (us,s) A1'" by simp
       qed    
     qed(insert binp' wlsBinp.cases, blast)
     (* *)
     have lift_binp1': "lift ?hA binp1' = binp"
     proof(rule ext)
       fix i let ?lbinp1' = "lift ?hA binp1'"
       show "?lbinp1' i = binp i"
       proof(cases "binp i")
         case None
         hence "?bar i = None" using binp unfolding gWlsBinp_def sameDom_def by simp
         hence "binp1' i = None" using None by simp
         thus "lift (recAbs MOD) binp1' i = binp i" using None by (simp add: lift_def)
       next
         case (Some A)
         then obtain us s where bari: "?bar i = Some (us,s)"
         using binp unfolding gWlsBinp_def sameDom_def by(cases "?bar i", auto)
         let ?A1' = "SOME A1'. ?bphi (us,s) A A1'"
         have binp1'i: "binp1' i = Some ?A1'" using bari Some *[of i us s A] by simp
         hence lbinp1'i: "?lbinp1' i = Some (?hA ?A1')" unfolding lift_def by simp
         obtain A' where A': "?bphi (us,s) A A'"
         using Some bari BIH unfolding liftAll2_def by fastforce
         hence "?bphi (us,s) A ?A1'" by(rule someI[of "?bphi (us,s) A"])
         thus "lift (recAbs MOD) binp1' i = binp i" using Some lbinp1'i by simp
       qed
     qed
     (*  *)
     let ?X' = "Op delta inp1' binp1'"
     have X': "wls ?st ?X'" using inp1' binp1' by simp
     have "?h ?X' = gOp MOD delta inp1' inp binp1' binp"
     using inp1' binp1' pCons lift_inp1' lift_binp1'
     unfolding presCons_defs by simp
     hence "?h ?X' = gOp MOD delta inp' inp binp' binp"
     using inp' inp1' inp binp' binp1' binp assms
     unfolding gConsIndif_defs by metis
     thus "\<exists>X'. wls (stOf delta) X' \<and> ?h X' = gOp MOD delta inp' inp binp' binp"
     using X' by blast
   next
     fix xs s x X' X1'
     assume xs_s: "isInBar (xs,s)" and X': "wls s X'" and
     hX1': "gWls MOD s (?h X1')" and X1': "wls s X1'"
     thus "\<exists>A'. wlsAbs (xs,s) A' \<and> ?hA A' = gAbs MOD xs x X' (?h X1')"
     apply(intro exI[of _ "Abs xs x X1'"])  
     using pCons unfolding presCons_def presAbs_def apply safe 
     apply(elim allE[of _ xs]) apply(elim allE[of _ x]) apply(elim allE[of _ s]) 
     apply simp_all   
     using assms unfolding gConsIndif_defs by blast
   qed
  }
  thus ?thesis unfolding isSurjAll_defs by blast
qed

text{* For fresh-swap models *}

theorem wlsFSw_recAll_isSurjAll:
"wlsFSw MOD \<Longrightarrow> gConsIndif MOD \<Longrightarrow> gInduct MOD
 \<Longrightarrow> isSurjAll (rec MOD) (recAbs MOD) MOD"
using wlsFSw_recAll_termFSwMorph 
by (auto simp: termFSwMorph_def intro: gInduct_gConsIndif_recAll_isSurjAll)

text{* For fresh-subst models *}

theorem wlsFSb_recAll_isSurjAll:
"wlsFSb MOD \<Longrightarrow> gConsIndif MOD \<Longrightarrow> gInduct MOD
 \<Longrightarrow> isSurjAll (rec MOD) (recAbs MOD) MOD"
using wlsFSb_recAll_termFSbMorph 
by (auto simp: termFSbMorph_def intro: gInduct_gConsIndif_recAll_isSurjAll)

(********************************************)
lemmas recursion_simps =
fromMOD_simps ipresCons_fromMOD_fst_all_simps fromIMor_simps

declare recursion_simps [simp del]

end (* context FixSyn *)
(************************************************)

end 
