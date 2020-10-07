section {* Iteration *}

theory Iteration imports Well_Sorted_Terms
begin

text{* In this section, we introduce first-order models (models, for short).
These are structures having operators that
match those for terms (including variable-injection, binding operations, freshness,
swapping and substitution) and satisfy some clauses,
and show that terms form initial models. This gives iteration principles.

As a matter of notation: the prefix
``g" will stand for ``generalized" -- elements of models are referred to as ``generalized terms".
The actual full prefix will be ``ig" (where ``i" stands for ``iteration"), symbolizing the fact that
the models from this section support iteration, and not general recursion.
The latter is dealt with by the models introduced in the next section, for which we
use the simple prefix ``g".
*}

subsection {* Models *}

text{* We have two basic kinds of models:
\\- fresh-swap (FSw) models, featuring operations corresponding to
the concrete syntactic constructs (``Var", ``Op", ``Abs"),
henceforth referred to simply as {\em the constructs}, and to fresh and swap;
\\- fresh-swap-subst (FSb) models, featuring substitution instead of swapping.

We also consider two combinations of the above, FSwSb-models and FSbSw-models.

To keep things structurally
simple, we use one single Isabelle for all the 4 kinds models,
allowing the most generous signature.
Since terms are the main actors of our theory, models being considered only
for the sake of recursive definitions, we call the items inhabiting these models
``generalized" terms, abstractions and inputs, and correspondingly
the operations; hence the prefix ``g" from the names of the type parameters and
operators.
(However,
we refer to the generalized items using the same notations as for
``concrete items": X, A,  etc.)
%
Indeed, a model can be regarded as implementing
a generalization/axiomatization of the term structure, where now the objects are
not terms, but do have term-like properties.
*}

subsubsection {* Raw models  *}

record ('index,'bindex,'varSort,'sort,'opSym,'var,'gTerm,'gAbs)model =
  igWls :: "'sort \<Rightarrow> 'gTerm \<Rightarrow> bool"
  igWlsAbs :: "'varSort \<times> 'sort \<Rightarrow> 'gAbs \<Rightarrow> bool"
  (*  *)
  igVar :: "'varSort \<Rightarrow> 'var \<Rightarrow> 'gTerm"
  igAbs :: "'varSort \<Rightarrow> 'var \<Rightarrow> 'gTerm \<Rightarrow> 'gAbs"
  igOp :: "'opSym \<Rightarrow> ('index,'gTerm)input \<Rightarrow> ('bindex,'gAbs)input \<Rightarrow> 'gTerm"
  (*  *)
  igFresh :: "'varSort \<Rightarrow> 'var \<Rightarrow> 'gTerm \<Rightarrow> bool"
  igFreshAbs :: "'varSort \<Rightarrow> 'var \<Rightarrow> 'gAbs \<Rightarrow> bool"
  (*  *)
  igSwap :: "'varSort \<Rightarrow> 'var \<Rightarrow> 'var \<Rightarrow> 'gTerm \<Rightarrow> 'gTerm"
  igSwapAbs :: "'varSort \<Rightarrow> 'var \<Rightarrow> 'var \<Rightarrow> 'gAbs \<Rightarrow> 'gAbs"
  (*   *)
  igSubst :: "'varSort \<Rightarrow> 'gTerm \<Rightarrow> 'var \<Rightarrow> 'gTerm \<Rightarrow> 'gTerm"
  igSubstAbs :: "'varSort \<Rightarrow> 'gTerm \<Rightarrow> 'var \<Rightarrow> 'gAbs \<Rightarrow> 'gAbs"

text{* \
\\- ``igSwap MOD zs z1 z2 X" swaps in X z1 and z2 (assumed of sorts zs).
\\- ``igSubst MOD ys Y x X" substitutes, in X, Y with y (assumed of sort ys). *}

definition igFreshInp where
"igFreshInp MOD ys y inp == liftAll (igFresh MOD ys y) inp"

definition igFreshBinp where
"igFreshBinp MOD ys y binp == liftAll (igFreshAbs MOD ys y) binp"

definition igSwapInp where
"igSwapInp MOD zs z1 z2 inp == lift (igSwap MOD zs z1 z2) inp"

definition igSwapBinp where
"igSwapBinp MOD zs z1 z2 binp == lift (igSwapAbs MOD zs z1 z2) binp"

definition igSubstInp where
"igSubstInp MOD ys Y y inp == lift (igSubst MOD ys Y y) inp"

definition igSubstBinp where
"igSubstBinp MOD ys Y y binp == lift (igSubstAbs MOD ys Y y) binp"

(* *************************************************** *)
context FixSyn
begin

(*  In this theory, new type variables are introduced into the context,
corresponding to 'gTerm and 'gAbs (making the locale polymorphic).  *)

subsubsection {* Well-sorted models of various kinds*}

text{* We define the following kinds of well-sorted models
\\- fresh-swap models (predicate ``iwlsFSw");
\\- fresh-subst models (``iwlsFSb");
\\- fresh-swap-subst models (``iwlsFSwSb");
\\- fresh-subst-swap models (``iwlsFSbSw").

All of these models are defined as raw models subject to various Horn conditions:
\\- For ``iwlsFSw":
\\--- definition-like clauses for ``fresh" and ``swap" in terms of the
      construct operators;
\\--- congruence for abstraction based on fresh and swap (mirroring the abstraction case in
the definition of alpha-equivalence for quasi-terms).
%
\footnote{Here, by ``congruence for abstraction" we do not mean the standard notion of congrunece
(satisfied by any operator once or ever), but a {\em stronger} notion: in order for two abstractions
to be equal, it is not required that their ariguments be equal, but that they be in a
``permutative" relationship based either on swapping or on substitution.}
%
\\- For ``iwlsFSb": the same as for ``iwlsFSw", except that:
\\--- ``swap" is replaced by ``subst";
%
\footnote{
Note that traditionally alpha-equivalence is defined using ``subst", not ``swap".
}
%
\\--- The [fresh and swap]-based congrunce clause is replaced by an ``abstraction-renaming" clause,
which is stronger than the corresponding [fresh and subst]-based congruence clause.
%
\footnote{
We also define the [fresh and subst]-based congruence clause, although we do not
employ it directly in the definition of any kind of model.
}
%
\\- For ``iwlsFSwSb": the clauses for ``iwlsFSw", plus some of the definition-like clauses for ``subst".
%
\footnote{Not all the ``subst" definition-like clauses from ``iwlsFSb" are required
for ``iwlsFSwSb" -- namely, the clause that
we call ``igSubstIGAbsCls2" is not required here.
}
%
\\- For ``iwlsFSbSw": the clauses for ``iwlsFSb", plus definition-like clauses for ``swap".

Thus, a fresh-swap-subst model is also a fresh-swap model, and
a fresh-subst-swap model is also a fresh-subst model.

For convenience, all these 4 kinds of models are defined on one single type, that of {\em raw models},
which interpret the most generous signature, comprizing all the operations and relations required by all
4 kinds of models.
Note that, although some operations (namely, ``subst" or ``swap") may not be involved in the clauses for certain kinds
of models, the extra structure is harmless to the development of their theory.

Note that for the models operations and relations we do not actually write ``fresh", ``swap" and ``subst", but
``igFresh", ``igSwap" and ``igSubst".

As usual, we shall have not only term versions, but also abstraction versions of the above
operations.

 *}

definition igWlsInp where
"igWlsInp MOD delta inp ==
 wlsOpS delta \<and> sameDom (arOf delta) inp \<and> liftAll2 (igWls MOD) (arOf delta) inp"

lemmas igWlsInp_defs = igWlsInp_def sameDom_def liftAll2_def

definition igWlsBinp where
"igWlsBinp MOD delta binp ==
 wlsOpS delta \<and> sameDom (barOf delta) binp \<and> liftAll2 (igWlsAbs MOD) (barOf delta) binp"

lemmas igWlsBinp_defs = igWlsBinp_def sameDom_def liftAll2_def

text{* Domain disjointness: *}

definition igWlsDisj where
"igWlsDisj MOD == \<forall> s s' X. igWls MOD s X \<and> igWls MOD s' X \<longrightarrow> s = s'"

definition igWlsAbsDisj where
"igWlsAbsDisj MOD ==
 \<forall> xs s xs' s' A.
    isInBar (xs,s) \<and> isInBar (xs',s') \<and>
    igWlsAbs MOD (xs,s) A \<and> igWlsAbs MOD (xs',s') A
    \<longrightarrow> xs = xs' \<and> s = s'"

definition igWlsAllDisj where
"igWlsAllDisj MOD ==
 igWlsDisj MOD \<and> igWlsAbsDisj MOD"

lemmas igWlsAllDisj_defs =
igWlsAllDisj_def
igWlsDisj_def igWlsAbsDisj_def

text {* Abstration domains inhabited only within bound arities: *}

definition igWlsAbsIsInBar where
"igWlsAbsIsInBar MOD ==
 \<forall> us s A. igWlsAbs MOD (us,s) A \<longrightarrow> isInBar (us,s)"

text{* Domain preservation by the operators: weak (``if") versions and strong (``iff") versions
(for the latter, we use the suffix ``STR"): *}

text{* The constructs preserve the domains: *}

definition igVarIPresIGWls where
"igVarIPresIGWls MOD ==
 \<forall> xs x. igWls MOD (asSort xs) (igVar MOD xs x)"

definition igAbsIPresIGWls where
"igAbsIPresIGWls MOD ==
 \<forall> xs s x X. isInBar (xs,s) \<and> igWls MOD s X \<longrightarrow>
             igWlsAbs MOD (xs,s) (igAbs MOD xs x X)"

definition igAbsIPresIGWlsSTR where
"igAbsIPresIGWlsSTR MOD ==
 \<forall> xs s x X. isInBar (xs,s) \<longrightarrow>
             igWlsAbs MOD (xs,s) (igAbs MOD xs x X) =
             igWls MOD s X"

lemma igAbsIPresIGWlsSTR_imp_igAbsIPresIGWls:
"igAbsIPresIGWlsSTR MOD \<Longrightarrow> igAbsIPresIGWls MOD"
unfolding igAbsIPresIGWlsSTR_def igAbsIPresIGWls_def by simp

definition igOpIPresIGWls where
"igOpIPresIGWls MOD ==
 \<forall> delta inp binp.
   igWlsInp MOD delta inp \<and> igWlsBinp MOD delta binp
   \<longrightarrow> igWls MOD (stOf delta) (igOp MOD delta inp binp)"

definition igOpIPresIGWlsSTR where
"igOpIPresIGWlsSTR MOD ==
 \<forall> delta inp binp.
    igWls MOD (stOf delta) (igOp MOD delta inp binp) =
    (igWlsInp MOD delta inp \<and> igWlsBinp MOD delta binp)"

lemma igOpIPresIGWlsSTR_imp_igOpIPresIGWls:
"igOpIPresIGWlsSTR MOD \<Longrightarrow> igOpIPresIGWls MOD"
unfolding igOpIPresIGWlsSTR_def igOpIPresIGWls_def by simp

definition igConsIPresIGWls where
"igConsIPresIGWls MOD ==
 igVarIPresIGWls MOD \<and>
 igAbsIPresIGWls MOD \<and>
 igOpIPresIGWls MOD"

lemmas igConsIPresIGWls_defs = igConsIPresIGWls_def
igVarIPresIGWls_def
igAbsIPresIGWls_def
igOpIPresIGWls_def

definition igConsIPresIGWlsSTR where
"igConsIPresIGWlsSTR MOD ==
 igVarIPresIGWls MOD \<and>
 igAbsIPresIGWlsSTR MOD \<and>
 igOpIPresIGWlsSTR MOD"

lemmas igConsIPresIGWlsSTR_defs = igConsIPresIGWlsSTR_def
igVarIPresIGWls_def
igAbsIPresIGWlsSTR_def
igOpIPresIGWlsSTR_def

lemma igConsIPresIGWlsSTR_imp_igConsIPresIGWls:
"igConsIPresIGWlsSTR MOD \<Longrightarrow> igConsIPresIGWls MOD"
unfolding igConsIPresIGWlsSTR_def igConsIPresIGWls_def
using
igAbsIPresIGWlsSTR_imp_igAbsIPresIGWls
igOpIPresIGWlsSTR_imp_igOpIPresIGWls
by auto

(* The notion of ``fresh" preserving well-sorted-ness does not make sense, since
``fresh" is a relation. *)

text{* ``swap" preserves the domains: *}

definition igSwapIPresIGWls where
"igSwapIPresIGWls MOD ==
 \<forall> zs z1 z2 s X. igWls MOD s X \<longrightarrow>
                 igWls MOD s (igSwap MOD zs z1 z2 X)"

definition igSwapIPresIGWlsSTR where
"igSwapIPresIGWlsSTR MOD ==
 \<forall> zs z1 z2 s X. igWls MOD s (igSwap MOD zs z1 z2 X) =
                 igWls MOD s X"

lemma igSwapIPresIGWlsSTR_imp_igSwapIPresIGWls:
"igSwapIPresIGWlsSTR MOD \<Longrightarrow> igSwapIPresIGWls MOD"
unfolding igSwapIPresIGWlsSTR_def igSwapIPresIGWls_def by simp

definition igSwapAbsIPresIGWlsAbs where
"igSwapAbsIPresIGWlsAbs MOD ==
 \<forall> zs z1 z2 us s A.
   isInBar (us,s) \<and> igWlsAbs MOD (us,s) A \<longrightarrow>
   igWlsAbs MOD (us,s) (igSwapAbs MOD zs z1 z2 A)"

definition igSwapAbsIPresIGWlsAbsSTR where
"igSwapAbsIPresIGWlsAbsSTR MOD ==
 \<forall> zs z1 z2 us s A.
   igWlsAbs MOD (us,s) (igSwapAbs MOD zs z1 z2 A) =
   igWlsAbs MOD (us,s) A"

lemma igSwapAbsIPresIGWlsAbsSTR_imp_igSwapAbsIPresIGWlsAbs:
"igSwapAbsIPresIGWlsAbsSTR MOD \<Longrightarrow> igSwapAbsIPresIGWlsAbs MOD"
unfolding igSwapAbsIPresIGWlsAbsSTR_def igSwapAbsIPresIGWlsAbs_def by simp

definition igSwapAllIPresIGWlsAll where
"igSwapAllIPresIGWlsAll MOD ==
 igSwapIPresIGWls MOD \<and> igSwapAbsIPresIGWlsAbs MOD"

lemmas igSwapAllIPresIGWlsAll_defs = igSwapAllIPresIGWlsAll_def
igSwapIPresIGWls_def igSwapAbsIPresIGWlsAbs_def

definition igSwapAllIPresIGWlsAllSTR where
"igSwapAllIPresIGWlsAllSTR MOD ==
 igSwapIPresIGWlsSTR MOD \<and> igSwapAbsIPresIGWlsAbsSTR MOD"

lemmas igSwapAllIPresIGWlsAllSTR_defs = igSwapAllIPresIGWlsAllSTR_def
igSwapIPresIGWlsSTR_def igSwapAbsIPresIGWlsAbsSTR_def

lemma igSwapAllIPresIGWlsAllSTR_imp_igSwapAllIPresIGWlsAll:
"igSwapAllIPresIGWlsAllSTR MOD \<Longrightarrow> igSwapAllIPresIGWlsAll MOD"
unfolding igSwapAllIPresIGWlsAllSTR_def igSwapAllIPresIGWlsAll_def
using
igSwapIPresIGWlsSTR_imp_igSwapIPresIGWls
igSwapAbsIPresIGWlsAbsSTR_imp_igSwapAbsIPresIGWlsAbs
by auto

text{* ``subst" preserves the domains: *}

definition igSubstIPresIGWls where
"igSubstIPresIGWls MOD ==
 \<forall> ys Y y s X. igWls MOD (asSort ys) Y \<and> igWls MOD s X \<longrightarrow>
               igWls MOD s (igSubst MOD ys Y y X)"

definition igSubstIPresIGWlsSTR where
"igSubstIPresIGWlsSTR MOD ==
 \<forall> ys Y y s X.
   igWls MOD s (igSubst MOD ys Y y X) =
   (igWls MOD (asSort ys) Y \<and> igWls MOD s X)"

lemma igSubstIPresIGWlsSTR_imp_igSubstIPresIGWls:
"igSubstIPresIGWlsSTR MOD \<Longrightarrow> igSubstIPresIGWls MOD"
unfolding igSubstIPresIGWlsSTR_def igSubstIPresIGWls_def by simp

definition igSubstAbsIPresIGWlsAbs where
"igSubstAbsIPresIGWlsAbs MOD ==
 \<forall> ys Y y us s A.
   isInBar (us,s) \<and> igWls MOD (asSort ys) Y \<and> igWlsAbs MOD (us,s) A \<longrightarrow>
   igWlsAbs MOD (us,s) (igSubstAbs MOD ys Y y A)"

definition igSubstAbsIPresIGWlsAbsSTR where
"igSubstAbsIPresIGWlsAbsSTR MOD ==
 \<forall> ys Y y us s A.
   igWlsAbs MOD (us,s) (igSubstAbs MOD ys Y y A) =
   (igWls MOD (asSort ys) Y \<and> igWlsAbs MOD (us,s) A)"

lemma igSubstAbsIPresIGWlsAbsSTR_imp_igSubstAbsIPresIGWlsAbs:
"igSubstAbsIPresIGWlsAbsSTR MOD \<Longrightarrow> igSubstAbsIPresIGWlsAbs MOD"
unfolding igSubstAbsIPresIGWlsAbsSTR_def igSubstAbsIPresIGWlsAbs_def by simp

definition igSubstAllIPresIGWlsAll where
"igSubstAllIPresIGWlsAll MOD ==
 igSubstIPresIGWls MOD \<and> igSubstAbsIPresIGWlsAbs MOD"

lemmas igSubstAllIPresIGWlsAll_defs = igSubstAllIPresIGWlsAll_def
igSubstIPresIGWls_def igSubstAbsIPresIGWlsAbs_def

definition igSubstAllIPresIGWlsAllSTR where
"igSubstAllIPresIGWlsAllSTR MOD ==
 igSubstIPresIGWlsSTR MOD \<and> igSubstAbsIPresIGWlsAbsSTR MOD"

lemmas igSubstAllIPresIGWlsAllSTR_defs = igSubstAllIPresIGWlsAllSTR_def
igSubstIPresIGWlsSTR_def igSubstAbsIPresIGWlsAbsSTR_def

lemma igSubstAllIPresIGWlsAllSTR_imp_igSubstAllIPresIGWlsAll:
"igSubstAllIPresIGWlsAllSTR MOD \<Longrightarrow> igSubstAllIPresIGWlsAll MOD"
unfolding igSubstAllIPresIGWlsAllSTR_def igSubstAllIPresIGWlsAll_def
using
igSubstIPresIGWlsSTR_imp_igSubstIPresIGWls
igSubstAbsIPresIGWlsAbsSTR_imp_igSubstAbsIPresIGWlsAbs
by auto

text{* Clauses for fresh: fully conditional versions and less conditional,
stronger versions (the latter having suffix ``STR"). *}

definition igFreshIGVar where
"igFreshIGVar MOD ==
 \<forall> ys y xs x.
   ys \<noteq> xs \<or> y \<noteq> x \<longrightarrow>
   igFresh MOD ys y (igVar MOD xs x)"

definition igFreshIGAbs1 where
"igFreshIGAbs1 MOD ==
 \<forall> ys y s X.
   isInBar (ys,s) \<and> igWls MOD s X \<longrightarrow>
   igFreshAbs MOD ys y (igAbs MOD ys y X)"

definition igFreshIGAbs1STR where
"igFreshIGAbs1STR MOD ==
 \<forall> ys y X. igFreshAbs MOD ys y (igAbs MOD ys y X)"

lemma igFreshIGAbs1STR_imp_igFreshIGAbs1:
"igFreshIGAbs1STR MOD \<Longrightarrow> igFreshIGAbs1 MOD"
unfolding igFreshIGAbs1STR_def igFreshIGAbs1_def by simp

definition igFreshIGAbs2 where
"igFreshIGAbs2 MOD ==
 \<forall> ys y xs x s X.
   isInBar (xs,s) \<and> igWls MOD s X \<longrightarrow>
   igFresh MOD ys y X \<longrightarrow> igFreshAbs MOD ys y (igAbs MOD xs x X)"

definition igFreshIGAbs2STR where
"igFreshIGAbs2STR MOD ==
 \<forall> ys y xs x X.
   igFresh MOD ys y X \<longrightarrow> igFreshAbs MOD ys y (igAbs MOD xs x X)"

lemma igFreshIGAbs2STR_imp_igFreshIGAbs2:
"igFreshIGAbs2STR MOD \<Longrightarrow> igFreshIGAbs2 MOD"
unfolding igFreshIGAbs2STR_def igFreshIGAbs2_def by simp

definition igFreshIGOp where
"igFreshIGOp MOD ==
 \<forall> ys y delta inp binp.
   igWlsInp MOD delta inp \<and> igWlsBinp MOD delta binp \<longrightarrow>
   (igFreshInp MOD ys y inp \<and> igFreshBinp MOD ys y binp) \<longrightarrow>
   igFresh MOD ys y (igOp MOD delta inp binp)"

definition igFreshIGOpSTR where
"igFreshIGOpSTR MOD ==
 \<forall> ys y delta inp binp.
   igFreshInp MOD ys y inp \<and> igFreshBinp MOD ys y binp \<longrightarrow>
   igFresh MOD ys y (igOp MOD delta inp binp)"

lemma igFreshIGOpSTR_imp_igFreshIGOp:
"igFreshIGOpSTR MOD \<Longrightarrow> igFreshIGOp MOD"
unfolding igFreshIGOpSTR_def igFreshIGOp_def by simp

definition igFreshCls where
"igFreshCls MOD ==
igFreshIGVar MOD \<and>
igFreshIGAbs1 MOD \<and> igFreshIGAbs2 MOD \<and>
igFreshIGOp MOD"

lemmas igFreshCls_defs = igFreshCls_def
igFreshIGVar_def
igFreshIGAbs1_def igFreshIGAbs2_def
igFreshIGOp_def

definition igFreshClsSTR where
"igFreshClsSTR MOD ==
igFreshIGVar MOD \<and>
igFreshIGAbs1STR MOD \<and> igFreshIGAbs2STR MOD \<and>
igFreshIGOpSTR MOD"

lemmas igFreshClsSTR_defs = igFreshClsSTR_def
igFreshIGVar_def
igFreshIGAbs1STR_def igFreshIGAbs2STR_def
igFreshIGOpSTR_def

lemma igFreshClsSTR_imp_igFreshCls:
"igFreshClsSTR MOD \<Longrightarrow> igFreshCls MOD"
unfolding igFreshClsSTR_def igFreshCls_def
using
igFreshIGAbs1STR_imp_igFreshIGAbs1 igFreshIGAbs2STR_imp_igFreshIGAbs2
igFreshIGOpSTR_imp_igFreshIGOp
by auto

(* Clauses for swap: fully-conditional versions and less-conditional,
stronger versions (suffix ``STR") *)

definition igSwapIGVar where
"igSwapIGVar MOD ==
 \<forall> zs z1 z2 xs x.
   igSwap MOD zs z1 z2 (igVar MOD xs x) = igVar MOD xs (x @xs[z1 \<and> z2]_zs)"

definition igSwapIGAbs where
"igSwapIGAbs MOD ==
 \<forall>  zs z1 z2 xs x s X.
   isInBar (xs,s) \<and> igWls MOD s X \<longrightarrow>
   igSwapAbs MOD zs z1 z2 (igAbs MOD xs x X) =
   igAbs MOD xs (x @xs[z1 \<and> z2]_zs) (igSwap MOD zs z1 z2 X)"

definition igSwapIGAbsSTR where
"igSwapIGAbsSTR MOD ==
 \<forall>  zs z1 z2 xs x X.
   igSwapAbs MOD zs z1 z2 (igAbs MOD xs x X) =
   igAbs MOD xs (x @xs[z1 \<and> z2]_zs) (igSwap MOD zs z1 z2 X)"

lemma igSwapIGAbsSTR_imp_igSwapIGAbs:
"igSwapIGAbsSTR MOD \<Longrightarrow> igSwapIGAbs MOD"
unfolding igSwapIGAbsSTR_def igSwapIGAbs_def by simp

definition igSwapIGOp where
"igSwapIGOp MOD ==
 \<forall>  zs z1 z2 delta inp binp.
   igWlsInp MOD delta inp \<and> igWlsBinp MOD delta binp \<longrightarrow>
   igSwap MOD zs z1 z2 (igOp MOD delta inp binp) =
   igOp MOD delta (igSwapInp MOD zs z1 z2 inp) (igSwapBinp MOD zs z1 z2 binp)"

definition igSwapIGOpSTR where
"igSwapIGOpSTR MOD ==
 \<forall>  zs z1 z2 delta inp binp.
   igSwap MOD zs z1 z2 (igOp MOD delta inp binp) =
   igOp MOD delta (igSwapInp MOD zs z1 z2 inp) (igSwapBinp MOD zs z1 z2 binp)"

lemma igSwapIGOpSTR_imp_igSwapIGOp:
"igSwapIGOpSTR MOD \<Longrightarrow> igSwapIGOp MOD"
unfolding igSwapIGOpSTR_def igSwapIGOp_def by simp

definition igSwapCls where
"igSwapCls MOD ==
igSwapIGVar MOD \<and>
igSwapIGAbs MOD \<and>
igSwapIGOp MOD"

lemmas igSwapCls_defs = igSwapCls_def
igSwapIGVar_def
igSwapIGAbs_def
igSwapIGOp_def

definition igSwapClsSTR where
"igSwapClsSTR MOD ==
igSwapIGVar MOD \<and>
igSwapIGAbsSTR MOD \<and>
igSwapIGOpSTR MOD"

lemmas igSwapClsSTR_defs = igSwapClsSTR_def
igSwapIGVar_def
igSwapIGAbsSTR_def
igSwapIGOpSTR_def

lemma igSwapClsSTR_imp_igSwapCls:
"igSwapClsSTR MOD \<Longrightarrow> igSwapCls MOD"
unfolding igSwapClsSTR_def igSwapCls_def
using
igSwapIGAbsSTR_imp_igSwapIGAbs
igSwapIGOpSTR_imp_igSwapIGOp
by auto

(* Clauses for subst: fully-conditional versions and less-conditional,
stronger versions (suffix ``STR") *)

definition igSubstIGVar1 where
"igSubstIGVar1 MOD ==
 \<forall> ys y Y xs x.
   igWls MOD (asSort ys) Y \<longrightarrow>
   (ys \<noteq> xs \<or> y \<noteq> x) \<longrightarrow>
   igSubst MOD ys Y y (igVar MOD xs x) = igVar MOD xs x"

definition igSubstIGVar1STR where
"igSubstIGVar1STR MOD ==
 (\<forall> ys y y1 xs x.
    (ys \<noteq> xs \<or> x \<noteq> y) \<longrightarrow>
    igSubst MOD ys (igVar MOD ys y1) y (igVar MOD xs x) = igVar MOD xs x)
 \<and>
 (\<forall> ys y Y xs x.
    igWls MOD (asSort ys) Y \<longrightarrow>
    (ys \<noteq> xs \<or> y \<noteq> x) \<longrightarrow>
    igSubst MOD ys Y y (igVar MOD xs x) = igVar MOD xs x)"

lemma igSubstIGVar1STR_imp_igSubstIGVar1:
"igSubstIGVar1STR MOD \<Longrightarrow> igSubstIGVar1 MOD"
unfolding igSubstIGVar1STR_def igSubstIGVar1_def by simp

definition igSubstIGVar2 where
"igSubstIGVar2 MOD ==
 \<forall> ys y Y.
   igWls MOD (asSort ys) Y \<longrightarrow>
   igSubst MOD ys Y y (igVar MOD ys y) = Y"

definition igSubstIGVar2STR where
"igSubstIGVar2STR MOD ==
 (\<forall> ys y y1.
    igSubst MOD ys (igVar MOD ys y1) y (igVar MOD ys y) = igVar MOD ys y1)
 \<and>
 (\<forall> ys y Y.
    igWls MOD (asSort ys) Y \<longrightarrow>
    igSubst MOD ys Y y (igVar MOD ys y) = Y)"

lemma igSubstIGVar2STR_imp_igSubstIGVar2:
"igSubstIGVar2STR MOD \<Longrightarrow> igSubstIGVar2 MOD"
unfolding igSubstIGVar2STR_def igSubstIGVar2_def by simp

definition igSubstIGAbs where
"igSubstIGAbs MOD ==
 \<forall> ys y Y xs x s X.
   isInBar (xs,s) \<and> igWls MOD (asSort ys) Y \<and> igWls MOD s X \<longrightarrow>
   (xs \<noteq> ys \<or> x \<noteq> y) \<and> igFresh MOD xs x Y \<longrightarrow>
   igSubstAbs MOD ys Y y (igAbs MOD xs x X) =
   igAbs MOD xs x (igSubst MOD ys Y y X)"

definition igSubstIGAbsSTR where
"igSubstIGAbsSTR MOD ==
 \<forall> ys y Y xs x X.
   (xs \<noteq> ys \<or> x \<noteq> y) \<and> igFresh MOD xs x Y \<longrightarrow>
   igSubstAbs MOD ys Y y (igAbs MOD xs x X) =
   igAbs MOD xs x (igSubst MOD ys Y y X)"

lemma igSubstIGAbsSTR_imp_igSubstIGAbs:
"igSubstIGAbsSTR MOD \<Longrightarrow> igSubstIGAbs MOD"
unfolding igSubstIGAbsSTR_def igSubstIGAbs_def by simp

definition igSubstIGOp where
"igSubstIGOp MOD ==
 \<forall> ys y Y delta inp binp.
   igWls MOD (asSort ys) Y \<and>
   igWlsInp MOD delta inp \<and> igWlsBinp MOD delta binp \<longrightarrow>
   igSubst MOD ys Y y (igOp MOD delta inp binp) =
   igOp MOD delta (igSubstInp MOD ys Y y inp) (igSubstBinp MOD ys Y y binp)"

definition igSubstIGOpSTR where
"igSubstIGOpSTR MOD ==
 (\<forall> ys y y1 delta inp binp.
    igSubst MOD ys (igVar MOD ys y1) y (igOp MOD delta inp binp) =
    igOp MOD delta (igSubstInp MOD ys (igVar MOD ys y1) y inp)
                  (igSubstBinp MOD ys (igVar MOD ys y1) y binp))
 \<and>
 (\<forall> ys y Y delta inp binp.
    igWls MOD (asSort ys) Y \<longrightarrow>
    igSubst MOD ys Y y (igOp MOD delta inp binp) =
    igOp MOD delta (igSubstInp MOD ys Y y inp) (igSubstBinp MOD ys Y y binp))"

lemma igSubstIGOpSTR_imp_igSubstIGOp:
"igSubstIGOpSTR MOD \<Longrightarrow> igSubstIGOp MOD"
unfolding igSubstIGOpSTR_def igSubstIGOp_def by simp

definition igSubstCls where
"igSubstCls MOD ==
 igSubstIGVar1 MOD \<and> igSubstIGVar2 MOD \<and>
 igSubstIGAbs MOD \<and>
 igSubstIGOp MOD"

lemmas igSubstCls_defs = igSubstCls_def
igSubstIGVar1_def igSubstIGVar2_def
igSubstIGAbs_def
igSubstIGOp_def

definition igSubstClsSTR where
"igSubstClsSTR MOD ==
 igSubstIGVar1STR MOD \<and> igSubstIGVar2STR MOD \<and>
 igSubstIGAbsSTR MOD \<and>
 igSubstIGOpSTR MOD"

lemmas igSubstClsSTR_defs = igSubstClsSTR_def
igSubstIGVar1STR_def igSubstIGVar2STR_def
igSubstIGAbsSTR_def
igSubstIGOpSTR_def

lemma igSubstClsSTR_imp_igSubstCls:
"igSubstClsSTR MOD \<Longrightarrow> igSubstCls MOD"
unfolding igSubstClsSTR_def igSubstCls_def
using
igSubstIGVar1STR_imp_igSubstIGVar1
igSubstIGVar2STR_imp_igSubstIGVar2
igSubstIGAbsSTR_imp_igSubstIGAbs
igSubstIGOpSTR_imp_igSubstIGOp
by auto

(* Freshness-based congruences for abstractions: *)

(* ... employing swap: *)

definition igAbsCongS where
"igAbsCongS MOD ==
 \<forall> xs x x' y s X X'.
   isInBar (xs,s) \<and> igWls MOD s X \<and> igWls MOD s X' \<longrightarrow>
   igFresh MOD xs y X \<and> igFresh MOD xs y X' \<and> igSwap MOD xs y x X = igSwap MOD xs y x' X' \<longrightarrow>
   igAbs MOD xs x X = igAbs MOD xs x' X'"

definition igAbsCongSSTR where
"igAbsCongSSTR MOD ==
 \<forall> xs x x' y X X'.
   igFresh MOD xs y X \<and> igFresh MOD xs y X' \<and> igSwap MOD xs y x X = igSwap MOD xs y x' X' \<longrightarrow>
   igAbs MOD xs x X = igAbs MOD xs x' X'"

lemma igAbsCongSSTR_imp_igAbsCongS:
"igAbsCongSSTR MOD \<Longrightarrow> igAbsCongS MOD"
unfolding igAbsCongSSTR_def igAbsCongS_def by auto

(* ... employing subst: *)

definition igAbsCongU where
"igAbsCongU MOD ==
 \<forall> xs x x' y s X X'.
   isInBar (xs,s) \<and> igWls MOD s X \<and> igWls MOD s X' \<longrightarrow>
   igFresh MOD xs y X \<and> igFresh MOD xs y X' \<and>
   igSubst MOD xs (igVar MOD xs y) x X = igSubst MOD xs (igVar MOD xs y) x' X' \<longrightarrow>
   igAbs MOD xs x X = igAbs MOD xs x' X'"

definition igAbsCongUSTR where
"igAbsCongUSTR MOD ==
 \<forall> xs x x' y X X'.
   igFresh MOD xs y X \<and> igFresh MOD xs y X' \<and>
   igSubst MOD xs (igVar MOD xs y) x X = igSubst MOD xs (igVar MOD xs y) x' X' \<longrightarrow>
   igAbs MOD xs x X = igAbs MOD xs x' X'"

lemma igAbsCongUSTR_imp_igAbsCongU:
"igAbsCongUSTR MOD \<Longrightarrow> igAbsCongU MOD"
unfolding igAbsCongUSTR_def igAbsCongU_def by auto

(* (Subst-based) renaming of the bound variable in abstractions (``abstraction renaming", for short): *)

definition igAbsRen where
"igAbsRen MOD ==
 \<forall> xs y x s X.
    isInBar (xs,s) \<and> igWls MOD s X \<longrightarrow>
    igFresh MOD xs y X \<longrightarrow>
    igAbs MOD xs y (igSubst MOD xs (igVar MOD xs y) x X) = igAbs MOD xs x X"

definition igAbsRenSTR where
"igAbsRenSTR MOD ==
 \<forall> xs y x X.
   igFresh MOD xs y X \<longrightarrow>
   igAbs MOD xs y (igSubst MOD xs (igVar MOD xs y) x X) = igAbs MOD xs x X"

lemma igAbsRenSTR_imp_igAbsRen:
"igAbsRenSTR MOD \<Longrightarrow> igAbsRen MOD"
unfolding igAbsRenSTR_def igAbsRen_def by simp

(* igAbsRenSTR is stronger than igAbsCongUSTR: *)

lemma igAbsRenSTR_imp_igAbsCongUSTR:
"igAbsRenSTR MOD \<Longrightarrow> igAbsCongUSTR MOD"
unfolding igAbsCongUSTR_def igAbsRenSTR_def by metis
  

text {* Well-sorted fresh-swap models: *}

definition iwlsFSw where
"iwlsFSw MOD ==
 igWlsAllDisj MOD \<and> igWlsAbsIsInBar MOD \<and>
 igConsIPresIGWls MOD \<and> igSwapAllIPresIGWlsAll MOD \<and>
 igFreshCls MOD \<and> igSwapCls MOD \<and> igAbsCongS MOD"

lemmas iwlsFSw_defs1 = iwlsFSw_def
igWlsAllDisj_def igWlsAbsIsInBar_def
igConsIPresIGWls_def igSwapAllIPresIGWlsAll_def
igFreshCls_def igSwapCls_def igAbsCongS_def

lemmas iwlsFSw_defs = iwlsFSw_def
igWlsAllDisj_defs igWlsAbsIsInBar_def
igConsIPresIGWls_defs igSwapAllIPresIGWlsAll_defs
igFreshCls_defs igSwapCls_defs igAbsCongS_def

definition iwlsFSwSTR where
"iwlsFSwSTR MOD ==
 igWlsAllDisj MOD \<and> igWlsAbsIsInBar MOD \<and>
 igConsIPresIGWlsSTR MOD \<and> igSwapAllIPresIGWlsAllSTR MOD \<and>
 igFreshClsSTR MOD \<and> igSwapClsSTR MOD \<and> igAbsCongSSTR MOD"

lemmas iwlsFSwSTR_defs1 = iwlsFSwSTR_def
igWlsAllDisj_def igWlsAbsIsInBar_def
igConsIPresIGWlsSTR_def igSwapAllIPresIGWlsAllSTR_def
igFreshClsSTR_def igSwapClsSTR_def igAbsCongSSTR_def

lemmas iwlsFSwSTR_defs = iwlsFSwSTR_def
igWlsAllDisj_defs igWlsAbsIsInBar_def
igConsIPresIGWlsSTR_defs igSwapAllIPresIGWlsAllSTR_defs
igFreshClsSTR_defs igSwapClsSTR_defs igAbsCongSSTR_def

lemma iwlsFSwSTR_imp_iwlsFSw:
"iwlsFSwSTR MOD \<Longrightarrow> iwlsFSw MOD"
unfolding iwlsFSwSTR_def iwlsFSw_def
using
igConsIPresIGWlsSTR_imp_igConsIPresIGWls
igSwapAllIPresIGWlsAllSTR_imp_igSwapAllIPresIGWlsAll
igFreshClsSTR_imp_igFreshCls
igSwapClsSTR_imp_igSwapCls
igAbsCongSSTR_imp_igAbsCongS
by auto

text {* Well-sorted fresh-subst models: *}

definition iwlsFSb where
"iwlsFSb MOD ==
 igWlsAllDisj MOD \<and> igWlsAbsIsInBar MOD \<and>
 igConsIPresIGWls MOD \<and> igSubstAllIPresIGWlsAll MOD \<and>
 igFreshCls MOD \<and> igSubstCls MOD \<and> igAbsRen MOD"

lemmas iwlsFSb_defs1 = iwlsFSb_def
igWlsAllDisj_def igWlsAbsIsInBar_def
igConsIPresIGWls_def igSubstAllIPresIGWlsAll_def
igFreshCls_def igSubstCls_def igAbsRen_def

lemmas iwlsFSb_defs = iwlsFSb_def
igWlsAllDisj_defs igWlsAbsIsInBar_def
igConsIPresIGWls_defs igSubstAllIPresIGWlsAll_defs
igFreshCls_defs igSubstCls_defs igAbsRen_def

definition iwlsFSbSwTR where
"iwlsFSbSwTR MOD ==
 igWlsAllDisj MOD \<and> igWlsAbsIsInBar MOD \<and>
 igConsIPresIGWlsSTR MOD \<and> igSubstAllIPresIGWlsAllSTR MOD \<and>
 igFreshClsSTR MOD \<and> igSubstClsSTR MOD \<and> igAbsRenSTR MOD"

lemmas wlsFSbSwSTR_defs1 = iwlsFSbSwTR_def
igWlsAllDisj_def igWlsAbsIsInBar_def
igConsIPresIGWlsSTR_def igSwapAllIPresIGWlsAllSTR_def
igFreshClsSTR_def igSwapClsSTR_def igAbsRenSTR_def

lemmas iwlsFSbSwTR_defs = iwlsFSbSwTR_def
igWlsAllDisj_defs igWlsAbsIsInBar_def
igConsIPresIGWlsSTR_defs igSwapAllIPresIGWlsAllSTR_defs
igFreshClsSTR_defs igSwapClsSTR_defs igAbsRenSTR_def

lemma iwlsFSbSwTR_imp_iwlsFSb:
"iwlsFSbSwTR MOD \<Longrightarrow> iwlsFSb MOD"
unfolding iwlsFSbSwTR_def iwlsFSb_def
using
igConsIPresIGWlsSTR_imp_igConsIPresIGWls
igSubstAllIPresIGWlsAllSTR_imp_igSubstAllIPresIGWlsAll
igFreshClsSTR_imp_igFreshCls
igSubstClsSTR_imp_igSubstCls
igAbsRenSTR_imp_igAbsRen
by auto

text {* Well-sorted fresh-swap-subst-models *}

(* "strong" versions not required for this kind of models *)

definition iwlsFSwSb where
"iwlsFSwSb MOD ==
 iwlsFSw MOD \<and> igSubstAllIPresIGWlsAll MOD \<and> igSubstCls MOD"

lemmas iwlsFSwSb_defs1 = iwlsFSwSb_def
iwlsFSw_def igSubstAllIPresIGWlsAll_def igSubstCls_def

lemmas iwlsFSwSb_defs = iwlsFSwSb_def
iwlsFSw_def igSubstAllIPresIGWlsAll_defs igSubstCls_defs

text {* Well-sorted fresh-subst-swap-models *}

(* "strong" versions not required for this kind of models *)

definition iwlsFSbSw where
"iwlsFSbSw MOD ==
 iwlsFSb MOD \<and> igSwapAllIPresIGWlsAll MOD \<and> igSwapCls MOD"

lemmas iwlsFSbSw_defs1 = iwlsFSbSw_def
iwlsFSw_def igSwapAllIPresIGWlsAll_def igSwapCls_def

lemmas iwlsFSbSw_defs = iwlsFSbSw_def
iwlsFSw_def igSwapAllIPresIGWlsAll_defs igSwapCls_defs

text{* Extension of domain preservation (by swap and subst) to inputs: *}

text {* First for free inputs: *}

definition igSwapInpIPresIGWlsInp where
"igSwapInpIPresIGWlsInp MOD ==
 \<forall> zs z1 z2 delta inp.
   igWlsInp MOD delta inp \<longrightarrow>
   igWlsInp MOD delta (igSwapInp MOD zs z1 z2 inp)"

definition igSwapInpIPresIGWlsInpSTR where
"igSwapInpIPresIGWlsInpSTR MOD ==
 \<forall> zs z1 z2 delta inp.
   igWlsInp MOD delta (igSwapInp MOD zs z1 z2 inp) =
   igWlsInp MOD delta inp"

definition igSubstInpIPresIGWlsInp where
"igSubstInpIPresIGWlsInp MOD ==
 \<forall> ys y Y delta inp.
   igWls MOD (asSort ys) Y \<and> igWlsInp MOD delta inp \<longrightarrow>
   igWlsInp MOD delta (igSubstInp MOD ys Y y inp)"

definition igSubstInpIPresIGWlsInpSTR where
"igSubstInpIPresIGWlsInpSTR MOD ==
 \<forall> ys y Y delta inp.
   igWls MOD (asSort ys) Y \<longrightarrow>
   igWlsInp MOD delta (igSubstInp MOD ys Y y inp) =
   igWlsInp MOD delta inp"

lemma imp_igSwapInpIPresIGWlsInp:
"igSwapIPresIGWls MOD \<Longrightarrow> igSwapInpIPresIGWlsInp MOD"
by (simp add: 
igSwapInpIPresIGWlsInp_def igWlsInp_def liftAll2_def  
igSwapIPresIGWls_def igSwapAbsIPresIGWlsAbs_def igSwapInp_def lift_def 
sameDom_def split: option.splits)  

lemma imp_igSwapInpIPresIGWlsInpSTR:
"igSwapIPresIGWlsSTR MOD \<Longrightarrow> igSwapInpIPresIGWlsInpSTR MOD"
by (simp add: 
igSwapIPresIGWlsSTR_def igWlsInp_def liftAll2_def  
igSwapIPresIGWls_def igSwapInpIPresIGWlsInpSTR_def igSwapInp_def lift_def 
sameDom_def split: option.splits)  
(smt option.distinct(1) option.exhaust) 

lemma imp_igSubstInpIPresIGWlsInp:
"igSubstIPresIGWls MOD \<Longrightarrow> igSubstInpIPresIGWlsInp MOD"
by (simp add : igSubstInp_def
igSubstIPresIGWls_def igSubstInpIPresIGWlsInp_def igWlsInp_def liftAll2_def 
lift_def sameDom_def split: option.splits)

lemma imp_igSubstInpIPresIGWlsInpSTR:
"igSubstIPresIGWlsSTR MOD \<Longrightarrow> igSubstInpIPresIGWlsInpSTR MOD"
by(simp add: 
igSubstInpIPresIGWlsInpSTR_def igSubstIPresIGWlsSTR_def igSubstInp_def
igWlsInp_def liftAll2_def lift_def sameDom_def 
split: option.splits) (smt option.distinct(1) option.exhaust) 

text {* Then for bound inputs:  *}

definition igSwapBinpIPresIGWlsBinp where
"igSwapBinpIPresIGWlsBinp MOD ==
 \<forall> zs z1 z2 delta binp.
   igWlsBinp MOD delta binp \<longrightarrow>
   igWlsBinp MOD delta (igSwapBinp MOD zs z1 z2 binp)"

definition igSwapBinpIPresIGWlsBinpSTR where
"igSwapBinpIPresIGWlsBinpSTR MOD ==
 \<forall> zs z1 z2 delta binp.
   igWlsBinp MOD delta (igSwapBinp MOD zs z1 z2 binp) =
   igWlsBinp MOD delta binp"

definition igSubstBinpIPresIGWlsBinp where
"igSubstBinpIPresIGWlsBinp MOD ==
 \<forall> ys y Y delta binp.
   igWls MOD (asSort ys) Y \<and> igWlsBinp MOD delta binp \<longrightarrow>
   igWlsBinp MOD delta (igSubstBinp MOD ys Y y binp)"

definition igSubstBinpIPresIGWlsBinpSTR where
"igSubstBinpIPresIGWlsBinpSTR MOD ==
 \<forall> ys y Y delta binp.
   igWls MOD (asSort ys) Y \<longrightarrow>
   igWlsBinp MOD delta (igSubstBinp MOD ys Y y binp) =
   igWlsBinp MOD delta binp"

lemma imp_igSwapBinpIPresIGWlsBinp:
"igSwapAbsIPresIGWlsAbs MOD \<Longrightarrow> igSwapBinpIPresIGWlsBinp MOD"
by(auto simp add: 
igSwapBinpIPresIGWlsBinp_def igSwapAbsIPresIGWlsAbs_def igSwapBinp_def
igWlsBinp_def liftAll2_def lift_def sameDom_def 
split: option.splits)  

lemma imp_igSwapBinpIPresIGWlsBinpSTR:
"igSwapAbsIPresIGWlsAbsSTR MOD \<Longrightarrow> igSwapBinpIPresIGWlsBinpSTR MOD"
by (simp add: 
igSwapBinpIPresIGWlsBinpSTR_def igSwapAbsIPresIGWlsAbsSTR_def igSwapBinp_def
igWlsBinp_def liftAll2_def lift_def sameDom_def 
split: option.splits) (smt option.distinct(1) option.exhaust surj_pair)

lemma imp_igSubstBinpIPresIGWlsBinp:
"igSubstAbsIPresIGWlsAbs MOD \<Longrightarrow> igSubstBinpIPresIGWlsBinp MOD"
by (auto simp add: 
igSubstBinpIPresIGWlsBinp_def igSubstAbsIPresIGWlsAbs_def igSubstBinp_def
igWlsBinp_def liftAll2_def lift_def sameDom_def 
split: option.splits) 

lemma imp_igSubstBinpIPresIGWlsBinpSTR:
"igSubstAbsIPresIGWlsAbsSTR MOD \<Longrightarrow> igSubstBinpIPresIGWlsBinpSTR MOD"
by (simp add: 
igSubstAbsIPresIGWlsAbsSTR_def igSubstBinpIPresIGWlsBinpSTR_def igSubstBinp_def
igWlsBinp_def liftAll2_def lift_def sameDom_def 
split: option.splits) (smt option.distinct(1) option.exhaust surj_pair) 

subsection {* Morphisms of models *}

text{*
The morphisms between models shall be the usual first-order-logic morphisms, i.e,, functions
commuting with the operations and preserving the (freshness) relations.  Because they involve the
same signature, the morphisms for fresh-swap-subst models (called fresh-swap-subst morphisms)
will be the same as those for fresh-subst-swap-models.
*}

subsubsection {* Preservation of the domains *}

definition ipresIGWls where
"ipresIGWls h MOD MOD' ==
 \<forall> s X. igWls MOD s X \<longrightarrow> igWls MOD' s (h X)"

definition ipresIGWlsAbs where
"ipresIGWlsAbs hA MOD MOD' ==
 \<forall> us s A. igWlsAbs MOD (us,s) A \<longrightarrow> igWlsAbs MOD' (us,s) (hA A)"

definition ipresIGWlsAll where
"ipresIGWlsAll h hA MOD MOD' ==
 ipresIGWls h MOD MOD' \<and>  ipresIGWlsAbs hA MOD MOD'"

lemmas ipresIGWlsAll_defs = ipresIGWlsAll_def
ipresIGWls_def ipresIGWlsAbs_def

subsubsection {* Preservation of the constructs *}

definition ipresIGVar where
"ipresIGVar h MOD MOD' ==
 \<forall> xs x. h (igVar MOD xs x) = igVar MOD' xs x"

definition ipresIGAbs where
"ipresIGAbs h hA MOD MOD' ==
 \<forall> xs x s X. isInBar (xs,s) \<and> igWls MOD s X \<longrightarrow>
             hA (igAbs MOD xs x X) = igAbs MOD' xs x (h X)"

definition ipresIGOp
where
"ipresIGOp h hA MOD MOD' ==
 \<forall> delta inp binp.
   igWlsInp MOD delta inp \<and> igWlsBinp MOD delta binp \<longrightarrow>
   h (igOp MOD delta inp binp) = igOp MOD' delta (lift h inp) (lift hA binp)"

definition ipresIGCons where
"ipresIGCons h hA MOD MOD' ==
 ipresIGVar h MOD MOD' \<and>
 ipresIGAbs h hA MOD MOD' \<and>
 ipresIGOp h hA MOD MOD'"

lemmas ipresIGCons_defs = ipresIGCons_def
ipresIGVar_def
ipresIGAbs_def
ipresIGOp_def

subsubsection {* Preservation of freshness *}

definition ipresIGFresh where
"ipresIGFresh h MOD MOD' ==
 \<forall> ys y s X.
    igWls MOD s X \<longrightarrow>
    igFresh MOD ys y X \<longrightarrow> igFresh MOD' ys y (h X)"

definition ipresIGFreshAbs where
"ipresIGFreshAbs hA MOD MOD' ==
 \<forall> ys y us s A.
    igWlsAbs MOD (us,s) A \<longrightarrow>
    igFreshAbs MOD ys y A \<longrightarrow> igFreshAbs MOD' ys y (hA A)"

definition ipresIGFreshAll where
"ipresIGFreshAll h hA MOD MOD' ==
 ipresIGFresh h MOD MOD' \<and> ipresIGFreshAbs hA MOD MOD'"

lemmas ipresIGFreshAll_defs = ipresIGFreshAll_def
ipresIGFresh_def ipresIGFreshAbs_def

subsubsection {* Preservation of swapping *}

definition ipresIGSwap where
"ipresIGSwap h MOD MOD' ==
 \<forall> zs z1 z2 s X.
    igWls MOD s X \<longrightarrow>
    h (igSwap MOD zs z1 z2 X) = igSwap MOD' zs z1 z2 (h X)"

definition ipresIGSwapAbs where
"ipresIGSwapAbs hA MOD MOD' ==
 \<forall> zs z1 z2 us s A.
    igWlsAbs MOD (us,s) A \<longrightarrow>
    hA (igSwapAbs MOD zs z1 z2 A) = igSwapAbs MOD' zs z1 z2 (hA A)"

definition ipresIGSwapAll where
"ipresIGSwapAll h hA MOD MOD' ==
 ipresIGSwap h MOD MOD' \<and> ipresIGSwapAbs hA MOD MOD'"

lemmas ipresIGSwapAll_defs = ipresIGSwapAll_def
ipresIGSwap_def ipresIGSwapAbs_def

subsubsection {* Preservation of subst *}

definition ipresIGSubst where
"ipresIGSubst h MOD MOD' ==
 \<forall> ys Y y s X.
    igWls MOD (asSort ys) Y \<and> igWls MOD s X \<longrightarrow>
    h (igSubst MOD ys Y y X) = igSubst MOD' ys (h Y) y (h X)"

definition ipresIGSubstAbs where
"ipresIGSubstAbs h hA MOD MOD' ==
 \<forall> ys Y y us s A.
    igWls MOD (asSort ys) Y \<and> igWlsAbs MOD (us,s) A \<longrightarrow>
    hA (igSubstAbs MOD ys Y y A) = igSubstAbs MOD' ys (h Y) y (hA A)"

definition ipresIGSubstAll where
"ipresIGSubstAll h hA MOD MOD' ==
 ipresIGSubst h MOD MOD' \<and>
 ipresIGSubstAbs h hA MOD MOD'"

lemmas ipresIGSubstAll_defs = ipresIGSubstAll_def
ipresIGSubst_def ipresIGSubstAbs_def

subsubsection {* Fresh-swap morphisms *}

definition FSwImorph where
"FSwImorph h hA MOD MOD' ==
 ipresIGWlsAll h hA MOD MOD' \<and> ipresIGCons h hA MOD MOD' \<and>
 ipresIGFreshAll h hA MOD MOD' \<and> ipresIGSwapAll h hA MOD MOD'"

lemmas FSwImorph_defs1 = FSwImorph_def
ipresIGWlsAll_def ipresIGCons_def
ipresIGFreshAll_def ipresIGSwapAll_def

lemmas FSwImorph_defs = FSwImorph_def
ipresIGWlsAll_defs ipresIGCons_defs
ipresIGFreshAll_defs ipresIGSwapAll_defs

subsubsection {* Fresh-subst morphisms *}

definition FSbImorph where
"FSbImorph h hA MOD MOD' ==
 ipresIGWlsAll h hA MOD MOD' \<and> ipresIGCons h hA MOD MOD' \<and>
 ipresIGFreshAll h hA MOD MOD' \<and> ipresIGSubstAll h hA MOD MOD'"

lemmas FSbImorph_defs1 = FSbImorph_def
ipresIGWlsAll_def ipresIGCons_def
ipresIGFreshAll_def ipresIGSubstAll_def

lemmas FSbImorph_defs = FSbImorph_def
ipresIGWlsAll_defs ipresIGCons_defs
ipresIGFreshAll_defs ipresIGSubstAll_defs

subsubsection {* Fresh-swap-subst morphisms *}

(* Note that FSwSb-morphisms are also igood for FSbSw-models. *)

definition FSwSbImorph where
"FSwSbImorph h hA MOD MOD' ==
 FSwImorph h hA MOD MOD' \<and> ipresIGSubstAll h hA MOD MOD'"

lemmas FSwSbImorph_defs1 = FSwSbImorph_def
FSwImorph_def ipresIGSubstAll_def

lemmas FSwSbImorph_defs = FSwSbImorph_def
FSwImorph_defs ipresIGSubstAll_defs

subsubsection {* Basic facts *}

text {* FSwSb morphisms are the same as FSbSw morphisms: *}

lemma FSwSbImorph_iff:
"FSwSbImorph h hA MOD MOD' =
 (FSbImorph h hA MOD MOD' \<and> ipresIGSwapAll h hA MOD MOD')"
unfolding FSwSbImorph_def FSbImorph_def FSwImorph_def by auto

text {* Some facts for free inpus:  *}

lemma igSwapInp_None[simp]:
"(igSwapInp MOD zs z1 z2 inp i = None) = (inp i = None)"
unfolding igSwapInp_def by(simp add: lift_None)

lemma igSubstInp_None[simp]:
"(igSubstInp MOD ys Y y inp i = None) = (inp i = None)"
unfolding igSubstInp_def by(simp add: lift_None)

lemma imp_igWlsInp:
"igWlsInp MOD delta inp \<Longrightarrow> ipresIGWls h MOD MOD' 
 \<Longrightarrow> igWlsInp MOD' delta (lift h inp)"
by (simp add: igWlsInp_def ipresIGWls_def liftAll2_def lift_def 
sameDom_def split: option.splits)

corollary FSwImorph_igWlsInp:
assumes "igWlsInp MOD delta inp" and "FSwImorph h hA MOD MOD'"
shows "igWlsInp MOD' delta (lift h inp)"
using assms unfolding FSwImorph_def ipresIGWlsAll_def
using imp_igWlsInp by auto

corollary FSbImorph_igWlsInp:
assumes "igWlsInp MOD delta inp" and "FSbImorph h hA MOD MOD'"
shows "igWlsInp MOD' delta (lift h inp)"
using assms unfolding FSbImorph_def ipresIGWlsAll_def
using imp_igWlsInp by auto

lemma FSwSbImorph_igWlsInp:
assumes "igWlsInp MOD delta inp" and "FSwSbImorph h hA MOD MOD'"
shows "igWlsInp MOD' delta (lift h inp)"
using assms unfolding FSwSbImorph_def using FSwImorph_igWlsInp by auto

text {* Similar facts for bound inpus:  *}

lemma igSwapBinp_None[simp]:
"(igSwapBinp MOD zs z1 z2 binp i = None) = (binp i = None)"
unfolding igSwapBinp_def by(simp add: lift_None)

lemma igSubstBinp_None[simp]:
"(igSubstBinp MOD ys Y y binp i = None) = (binp i = None)"
unfolding igSubstBinp_def by(simp add: lift_None)

lemma imp_igWlsBinp:
assumes *: "igWlsBinp MOD delta binp"
and **: "ipresIGWlsAbs hA MOD MOD'"
shows "igWlsBinp MOD' delta (lift hA binp)"
using assms by (simp add: igWlsBinp_def ipresIGWlsAbs_def liftAll2_def lift_def 
sameDom_def split: option.splits) 

corollary FSwImorph_igWlsBinp:
assumes "igWlsBinp MOD delta binp" and "FSwImorph h hA MOD MOD'"
shows "igWlsBinp MOD' delta (lift hA binp)"
using assms unfolding FSwImorph_def ipresIGWlsAll_def
using imp_igWlsBinp by auto

corollary FSbImorph_igWlsBinp:
assumes "igWlsBinp MOD delta binp" and "FSbImorph h hA MOD MOD'"
shows "igWlsBinp MOD' delta (lift hA binp)"
using assms unfolding FSbImorph_def ipresIGWlsAll_def
using imp_igWlsBinp by auto

lemma FSwSbImorph_igWlsBinp:
assumes "igWlsBinp MOD delta binp" and "FSwSbImorph h hA MOD MOD'"
shows "igWlsBinp MOD' delta (lift hA binp)"
using assms unfolding FSwSbImorph_def using FSwImorph_igWlsBinp by auto

lemmas input_igSwap_igSubst_None =
igSwapInp_None igSubstInp_None
igSwapBinp_None igSubstBinp_None

subsubsection {* Identity and composition  *}

lemma id_FSwImorph: "FSwImorph id id MOD MOD"
unfolding FSwImorph_defs by auto

lemma id_FSbImorph: "FSbImorph id id MOD MOD"
unfolding FSbImorph_defs by auto

lemma id_FSwSbImorph: "FSwSbImorph id id MOD MOD"
unfolding FSwSbImorph_def apply(auto simp add: id_FSwImorph)
unfolding ipresIGSubstAll_defs by auto

lemma comp_ipresIGWls:
assumes "ipresIGWls h MOD MOD'" and "ipresIGWls h' MOD' MOD''"
shows "ipresIGWls (h' o h) MOD MOD''"
using assms unfolding ipresIGWls_def by auto

lemma comp_ipresIGWlsAbs:
assumes "ipresIGWlsAbs hA MOD MOD'" and "ipresIGWlsAbs hA' MOD' MOD''"
shows "ipresIGWlsAbs (hA' o hA) MOD MOD''"
using assms unfolding ipresIGWlsAbs_def by auto

lemma comp_ipresIGWlsAll:
assumes "ipresIGWlsAll h hA MOD MOD'" and "ipresIGWlsAll h' hA' MOD' MOD''"
shows "ipresIGWlsAll (h' o h) (hA' o hA) MOD MOD''"
using assms unfolding ipresIGWlsAll_def
using comp_ipresIGWls comp_ipresIGWlsAbs by auto

lemma comp_ipresIGVar:
assumes "ipresIGVar h MOD MOD'" and "ipresIGVar h' MOD' MOD''"
shows "ipresIGVar (h' o h) MOD MOD''"
using assms unfolding ipresIGVar_def by auto

lemma comp_ipresIGAbs:
assumes "ipresIGWls h MOD MOD'"
and "ipresIGAbs h hA MOD MOD'" and "ipresIGAbs h' hA' MOD' MOD''"
shows "ipresIGAbs (h' o h) (hA' o hA) MOD MOD''"
using assms unfolding ipresIGWls_def ipresIGAbs_def by fastforce

lemma comp_ipresIGOp:
assumes ipres: "ipresIGWls h MOD MOD'" and ipresAbs: "ipresIGWlsAbs hA MOD MOD'"
and h: "ipresIGOp h hA MOD MOD'" and h': "ipresIGOp h' hA' MOD' MOD''"
shows "ipresIGOp (h' o h) (hA' o hA) MOD MOD''"
using assms by (auto simp: imp_igWlsInp imp_igWlsBinp ipresIGOp_def lift_comp)
 
lemma comp_ipresIGCons:
assumes "ipresIGWlsAll h hA MOD MOD'"
and "ipresIGCons h hA MOD MOD'" and "ipresIGCons h' hA' MOD' MOD''"
shows "ipresIGCons (h' o h) (hA' o hA) MOD MOD''"
using assms unfolding ipresIGWlsAll_def ipresIGCons_def
using comp_ipresIGVar comp_ipresIGAbs comp_ipresIGOp by auto

lemma comp_ipresIGFresh:
assumes "ipresIGWls h MOD MOD'"
and "ipresIGFresh h MOD MOD'" and "ipresIGFresh h' MOD' MOD''"
shows "ipresIGFresh (h' o h) MOD MOD''"
using assms unfolding ipresIGWls_def ipresIGFresh_def by fastforce

lemma comp_ipresIGFreshAbs:
assumes "ipresIGWlsAbs hA MOD MOD'"
and "ipresIGFreshAbs hA MOD MOD'" and "ipresIGFreshAbs hA' MOD' MOD''"
shows "ipresIGFreshAbs (hA' o hA) MOD MOD''"
using assms unfolding ipresIGWlsAbs_def ipresIGFreshAbs_def by fastforce

lemma comp_ipresIGFreshAll:
assumes "ipresIGWlsAll h hA MOD MOD'"
and "ipresIGFreshAll h hA MOD MOD'" and "ipresIGFreshAll h' hA'  MOD' MOD''"
shows "ipresIGFreshAll (h' o h) (hA' o hA) MOD MOD''"
using assms
unfolding ipresIGWlsAll_def ipresIGFreshAll_def
using comp_ipresIGFresh comp_ipresIGFreshAbs by auto

lemma comp_ipresIGSwap:
assumes "ipresIGWls h MOD MOD'"
and "ipresIGSwap h MOD MOD'" and "ipresIGSwap h' MOD' MOD''"
shows "ipresIGSwap (h' o h) MOD MOD''"
using assms unfolding ipresIGWls_def ipresIGSwap_def by fastforce

lemma comp_ipresIGSwapAbs:
assumes "ipresIGWlsAbs hA MOD MOD'"
and "ipresIGSwapAbs hA MOD MOD'" and "ipresIGSwapAbs hA' MOD' MOD''"
shows "ipresIGSwapAbs (hA' o hA) MOD MOD''"
using assms unfolding ipresIGWlsAbs_def ipresIGSwapAbs_def by fastforce

lemma comp_ipresIGSwapAll:
assumes "ipresIGWlsAll h hA MOD MOD'"
and "ipresIGSwapAll h hA MOD MOD'" and "ipresIGSwapAll h' hA'  MOD' MOD''"
shows "ipresIGSwapAll (h' o h) (hA' o hA) MOD MOD''"
using assms
unfolding ipresIGWlsAll_def ipresIGSwapAll_def
using comp_ipresIGSwap comp_ipresIGSwapAbs by auto

lemma comp_ipresIGSubst:
assumes "ipresIGWls h MOD MOD'"
and "ipresIGSubst h MOD MOD'" and "ipresIGSubst h' MOD' MOD''"
shows "ipresIGSubst (h' o h) MOD MOD''"
using assms unfolding ipresIGWls_def ipresIGSubst_def
apply auto by blast

lemma comp_ipresIGSubstAbs:
assumes *: "igWlsAbsIsInBar MOD"
and h: "ipresIGWls h MOD MOD'" and hA: "ipresIGWlsAbs hA MOD MOD'"
and hhA: "ipresIGSubstAbs h hA MOD MOD'" and h'hA': "ipresIGSubstAbs h' hA' MOD' MOD''"
shows "ipresIGSubstAbs (h' o h) (hA' o hA) MOD MOD''"
using assms by(fastforce simp: igWlsAbsIsInBar_def 
ipresIGSubstAbs_def ipresIGWls_def ipresIGWlsAbs_def) 
 
lemma comp_ipresIGSubstAll:
assumes "igWlsAbsIsInBar MOD"
and "ipresIGWlsAll h hA MOD MOD'"
and "ipresIGSubstAll h hA MOD MOD'" and "ipresIGSubstAll h' hA'  MOD' MOD''"
shows "ipresIGSubstAll (h' o h) (hA' o hA) MOD MOD''"
using assms unfolding ipresIGWlsAll_def ipresIGSubstAll_def
using comp_ipresIGSubst comp_ipresIGSubstAbs by auto

lemma comp_FSwImorph:
assumes *: "FSwImorph h hA MOD MOD'" and **: "FSwImorph h' hA' MOD' MOD''"
shows "FSwImorph (h' o h) (hA' o hA) MOD MOD''"
using assms unfolding FSwImorph_def
using comp_ipresIGWlsAll comp_ipresIGCons
comp_ipresIGFreshAll comp_ipresIGSwapAll by auto

lemma comp_FSbImorph:
assumes "igWlsAbsIsInBar MOD"
and "FSbImorph h hA MOD MOD'" and "FSbImorph h' hA' MOD' MOD''"
shows "FSbImorph (h' o h) (hA' o hA) MOD MOD''"
using assms unfolding FSbImorph_def
using comp_ipresIGWlsAll comp_ipresIGCons
comp_ipresIGFreshAll comp_ipresIGSubstAll by auto

lemma comp_FSwSbImorph:
assumes "igWlsAbsIsInBar MOD"
and "FSwSbImorph h hA MOD MOD'" and "FSwSbImorph h' hA' MOD' MOD''"
shows "FSwSbImorph (h' o h) (hA' o hA) MOD MOD''"
using assms unfolding FSwSbImorph_def  
using comp_FSwImorph FSwImorph_def comp_ipresIGSubstAll FixSyn_axioms by blast

subsection {* The term model *}

text {* We show that terms form fresh-swap-subst and fresh-subst-swap models. *}

subsubsection {* Definitions and simplification rules *}

definition termMOD where
"termMOD ==
 \<lparr>igWls = wls, igWlsAbs = wlsAbs,
  igVar = Var, igAbs = Abs, igOp = Op,
  igFresh = fresh, igFreshAbs = freshAbs,
  igSwap = swap, igSwapAbs = swapAbs,
  igSubst = subst, igSubstAbs = substAbs\<rparr>"

lemma igWls_termMOD[simp]: "igWls termMOD = wls"
unfolding termMOD_def by simp

lemma igWlsAbs_termMOD[simp]: "igWlsAbs termMOD = wlsAbs"
unfolding termMOD_def by simp

lemma igWlsInp_termMOD_wlsInp[simp]:
"igWlsInp termMOD delta inp = wlsInp delta inp"
unfolding igWlsInp_def wlsInp_iff by simp

lemma igWlsBinp_termMOD_wlsBinp[simp]:
"igWlsBinp termMOD delta binp = wlsBinp delta binp"
unfolding igWlsBinp_def wlsBinp_iff by simp

lemmas igWlsAll_termMOD_simps =
igWls_termMOD igWlsAbs_termMOD
igWlsInp_termMOD_wlsInp igWlsBinp_termMOD_wlsBinp

lemma igVar_termMOD[simp]: "igVar termMOD = Var"
unfolding termMOD_def by simp

lemma igAbs_termMOD[simp]: "igAbs termMOD = Abs"
unfolding termMOD_def by simp

lemma igOp_termMOD[simp]: "igOp termMOD = Op"
unfolding termMOD_def by simp

lemmas igCons_termMOD_simps =
igVar_termMOD igAbs_termMOD igOp_termMOD

lemma igFresh_termMOD[simp]: "igFresh termMOD = fresh"
unfolding termMOD_def by simp

lemma igFreshAbs_termMOD[simp]: "igFreshAbs termMOD = freshAbs"
unfolding termMOD_def by simp

lemma igFreshInp_termMOD[simp]: "igFreshInp termMOD = freshInp"
unfolding igFreshInp_def[abs_def] freshInp_def[abs_def] by simp

lemma igFreshBinp_termMOD[simp]: "igFreshBinp termMOD = freshBinp"
unfolding igFreshBinp_def[abs_def] freshBinp_def[abs_def] by simp

lemmas igFreshAll_termMOD_simps =
igFresh_termMOD igFreshAbs_termMOD
igFreshInp_termMOD igFreshBinp_termMOD

lemma igSwap_termMOD[simp]: "igSwap termMOD = swap"
unfolding termMOD_def by simp

lemma igSwapAbs_termMOD[simp]: "igSwapAbs termMOD = swapAbs"
unfolding termMOD_def by simp

lemma igSwapInp_termMOD[simp]: "igSwapInp termMOD = swapInp"
unfolding igSwapInp_def[abs_def] swapInp_def[abs_def] by simp

lemma igSwapBinp_termMOD[simp]: "igSwapBinp termMOD = swapBinp"
unfolding igSwapBinp_def[abs_def] swapBinp_def[abs_def] by simp

lemmas igSwapAll_termMOD_simps =
igSwap_termMOD igSwapAbs_termMOD
igSwapInp_termMOD igSwapBinp_termMOD

lemma igSubst_termMOD[simp]: "igSubst termMOD = subst"
unfolding termMOD_def by simp

lemma igSubstAbs_termMOD[simp]: "igSubstAbs termMOD = substAbs"
unfolding termMOD_def by simp

lemma igSubstInp_termMOD[simp]: "igSubstInp termMOD = substInp"
by (simp add: igSubstInp_def[abs_def] substInp_def[abs_def]  
psubstInp_def[abs_def] subst_def)

lemma igSubstBinp_termMOD[simp]: "igSubstBinp termMOD = substBinp"
by (simp add: igSubstBinp_def[abs_def] substBinp_def[abs_def]  
psubstBinp_def[abs_def] substAbs_def)

lemmas igSubstAll_termMOD_simps =
igSubst_termMOD igSubstAbs_termMOD
igSubstInp_termMOD igSubstBinp_termMOD

lemmas structure_termMOD_simps =
igWlsAll_termMOD_simps
igFreshAll_termMOD_simps
igSwapAll_termMOD_simps
igSubstAll_termMOD_simps

subsubsection {*  Well-sortedness of the term model *}

text{* Domains are disjoint: *}

lemma termMOD_igWlsDisj: "igWlsDisj termMOD"
unfolding igWlsDisj_def using wls_disjoint by auto

lemma termMOD_igWlsAbsDisj: "igWlsAbsDisj termMOD"
unfolding igWlsAbsDisj_def using wlsAbs_disjoint by auto

lemma termMOD_igWlsAllDisj: "igWlsAllDisj termMOD"
unfolding igWlsAllDisj_def
using termMOD_igWlsDisj termMOD_igWlsAbsDisj by simp

text {* Abstraction domains inhabited only within bound arities: *}

lemma termMOD_igWlsAbsIsInBar: "igWlsAbsIsInBar termMOD"
unfolding igWlsAbsIsInBar_def using wlsAbs_nchotomy by simp

text{* The syntactic constructs preserve the domains: *}

lemma termMOD_igVarIPresIGWls: "igVarIPresIGWls termMOD"
unfolding igVarIPresIGWls_def by simp

lemma termMOD_igAbsIPresIGWls: "igAbsIPresIGWls termMOD"
unfolding igAbsIPresIGWls_def by simp

lemma termMOD_igOpIPresIGWls: "igOpIPresIGWls termMOD"
unfolding igOpIPresIGWls_def by simp

lemma termMOD_igConsIPresIGWls: "igConsIPresIGWls termMOD"
unfolding igConsIPresIGWls_def
using termMOD_igVarIPresIGWls termMOD_igAbsIPresIGWls termMOD_igOpIPresIGWls
by auto

text{* Swap preserves the domains: *}

lemma termMOD_igSwapIPresIGWls: "igSwapIPresIGWls termMOD"
unfolding igSwapIPresIGWls_def by simp

lemma termMOD_igSwapAbsIPresIGWlsAbs: "igSwapAbsIPresIGWlsAbs termMOD"
unfolding igSwapAbsIPresIGWlsAbs_def by simp

lemma termMOD_igSwapAllIPresIGWlsAll: "igSwapAllIPresIGWlsAll termMOD"
unfolding igSwapAllIPresIGWlsAll_def
using termMOD_igSwapIPresIGWls termMOD_igSwapAbsIPresIGWlsAbs by auto

text{* ``Subst" preserves the domains: *}

lemma termMOD_igSubstIPresIGWls: "igSubstIPresIGWls termMOD"
unfolding igSubstIPresIGWls_def by simp

lemma termMOD_igSubstAbsIPresIGWlsAbs: "igSubstAbsIPresIGWlsAbs termMOD"
unfolding igSubstAbsIPresIGWlsAbs_def by simp

lemma termMOD_igSubstAllIPresIGWlsAll: "igSubstAllIPresIGWlsAll termMOD"
unfolding igSubstAllIPresIGWlsAll_def
using termMOD_igSubstIPresIGWls termMOD_igSubstAbsIPresIGWlsAbs by auto

text{* The ``fresh" clauses hold: *}

lemma termMOD_igFreshIGVar: "igFreshIGVar termMOD"
unfolding igFreshIGVar_def by simp

lemma termMOD_igFreshIGAbs1: "igFreshIGAbs1 termMOD"
unfolding igFreshIGAbs1_def by auto

lemma termMOD_igFreshIGAbs2: "igFreshIGAbs2 termMOD"
unfolding igFreshIGAbs2_def by auto

lemma termMOD_igFreshIGOp: "igFreshIGOp termMOD"
unfolding igFreshIGOp_def by simp

lemma termMOD_igFreshCls: "igFreshCls termMOD"
unfolding igFreshCls_def
using termMOD_igFreshIGVar termMOD_igFreshIGAbs1 termMOD_igFreshIGAbs2 termMOD_igFreshIGOp
by simp

text{* The ``swap" clauses hold: *}

lemma termMOD_igSwapIGVar: "igSwapIGVar termMOD"
unfolding igSwapIGVar_def by simp

lemma termMOD_igSwapIGAbs: "igSwapIGAbs termMOD"
unfolding igSwapIGAbs_def by auto

lemma termMOD_igSwapIGOp: "igSwapIGOp termMOD"
unfolding igSwapIGOp_def by simp

lemma termMOD_igSwapCls: "igSwapCls termMOD"
unfolding igSwapCls_def
using termMOD_igSwapIGVar termMOD_igSwapIGAbs termMOD_igSwapIGOp by simp

text{* The ``subst" clauses hold: *}

lemma termMOD_igSubstIGVar1: "igSubstIGVar1 termMOD"
unfolding igSubstIGVar1_def by auto

lemma termMOD_igSubstIGVar2: "igSubstIGVar2 termMOD"
unfolding igSubstIGVar2_def by auto

lemma termMOD_igSubstIGAbs: "igSubstIGAbs termMOD"
unfolding igSubstIGAbs_def by auto

lemma termMOD_igSubstIGOp: "igSubstIGOp termMOD"
unfolding igSubstIGOp_def by simp

lemma termMOD_igSubstCls: "igSubstCls termMOD"
unfolding igSubstCls_def
using termMOD_igSubstIGVar1 termMOD_igSubstIGVar2
termMOD_igSubstIGAbs termMOD_igSubstIGOp by simp

text{* The swap-congruence clause for abstractions holds: *}

lemma termMOD_igAbsCongS: "igAbsCongS termMOD" 
unfolding igAbsCongS_def using wls_Abs_swap_cong 
by (metis igAbs_termMOD igFresh_termMOD igSwap_termMOD igWls_termMOD) 
 

text{* The subst-renaming clause for abstractions holds: *}

lemma termMOD_igAbsRen: "igAbsRen termMOD"
unfolding igAbsRen_def by auto

lemma termMOD_iwlsFSw: "iwlsFSw termMOD"
unfolding iwlsFSw_def
using
termMOD_igWlsAllDisj termMOD_igWlsAbsIsInBar
termMOD_igConsIPresIGWls termMOD_igSwapAllIPresIGWlsAll
termMOD_igFreshCls termMOD_igSwapCls termMOD_igAbsCongS
by auto

lemma termMOD_iwlsFSb: "iwlsFSb termMOD"
unfolding iwlsFSb_def
using
termMOD_igWlsAllDisj termMOD_igWlsAbsIsInBar
termMOD_igConsIPresIGWls termMOD_igSubstAllIPresIGWlsAll
termMOD_igFreshCls termMOD_igSubstCls termMOD_igAbsRen
by auto

lemma termMOD_iwlsFSwSb: "iwlsFSwSb termMOD"
unfolding iwlsFSwSb_def
using termMOD_iwlsFSw termMOD_igSubstAllIPresIGWlsAll termMOD_igSubstCls
by simp

lemma termMOD_iwlsFSbSw: "iwlsFSbSw termMOD"
unfolding iwlsFSbSw_def
using termMOD_iwlsFSb termMOD_igSwapAllIPresIGWlsAll termMOD_igSwapCls
by simp

subsubsection {* Direct description of morphisms from the term models  *}

(* We merely employ predicates referring directly to terms rather than
mediating through the model structure of terms. *)

definition ipresWls where
"ipresWls h MOD ==
 \<forall> s X. wls s X \<longrightarrow> igWls MOD s (h X)"

lemma ipresIGWls_termMOD[simp]:
"ipresIGWls h termMOD MOD = ipresWls h MOD"
unfolding ipresIGWls_def ipresWls_def by simp

definition ipresWlsAbs where
"ipresWlsAbs hA MOD ==
 \<forall> us s A. wlsAbs (us,s) A \<longrightarrow> igWlsAbs MOD (us,s) (hA A)"

lemma ipresIGWlsAbs_termMOD[simp]:
"ipresIGWlsAbs hA termMOD MOD = ipresWlsAbs hA MOD"
unfolding ipresIGWlsAbs_def ipresWlsAbs_def by simp

definition ipresWlsAll where
"ipresWlsAll h hA MOD ==
 ipresWls h MOD \<and> ipresWlsAbs hA MOD"

lemmas ipresWlsAll_defs = ipresWlsAll_def
ipresWls_def ipresWlsAbs_def

lemma ipresIGWlsAll_termMOD[simp]:
"ipresIGWlsAll h hA termMOD MOD = ipresWlsAll h hA MOD"
unfolding ipresIGWlsAll_def ipresWlsAll_def by simp

lemmas ipresIGWlsAll_termMOD_simps =
ipresIGWls_termMOD ipresIGWlsAbs_termMOD ipresIGWlsAll_termMOD

definition ipresVar where
"ipresVar h MOD ==
 \<forall> xs x. h (Var xs x) = igVar MOD xs x"

lemma ipresIGVar_termMOD[simp]:
"ipresIGVar h termMOD MOD = ipresVar h MOD"
unfolding ipresIGVar_def ipresVar_def by simp

definition ipresAbs where
"ipresAbs h hA MOD ==
 \<forall> xs x s X. isInBar (xs,s) \<and> wls s X \<longrightarrow> hA (Abs xs x X) = igAbs MOD xs x (h X)"

lemma ipresIGAbs_termMOD[simp]:
"ipresIGAbs h hA termMOD MOD = ipresAbs h hA MOD"
unfolding ipresIGAbs_def ipresAbs_def by simp

definition ipresOp where
"ipresOp h hA MOD ==
 \<forall> delta inp binp.
    wlsInp delta inp \<and> wlsBinp delta binp \<longrightarrow>
    h (Op delta inp binp) =
    igOp MOD delta (lift h inp) (lift hA binp)"

lemma ipresIGOp_termMOD[simp]:
"ipresIGOp h hA termMOD MOD = ipresOp h hA MOD"
unfolding ipresIGOp_def ipresOp_def by simp

definition ipresCons where
"ipresCons h hA MOD ==
 ipresVar h MOD \<and>
 ipresAbs h hA MOD \<and>
 ipresOp h hA MOD"

lemmas ipresCons_defs = ipresCons_def
ipresVar_def
ipresAbs_def
ipresOp_def

lemma ipresIGCons_termMOD[simp]:
"ipresIGCons h hA termMOD MOD = ipresCons h hA MOD"
unfolding ipresIGCons_def ipresCons_def by simp

lemmas ipresIGCons_termMOD_simps =
ipresIGVar_termMOD ipresIGAbs_termMOD ipresIGOp_termMOD
ipresIGCons_termMOD

definition ipresFresh where
"ipresFresh h MOD ==
 \<forall> ys y s X.
    wls s X \<longrightarrow>
    fresh ys y X \<longrightarrow> igFresh MOD ys y (h X)"

lemma ipresIGFresh_termMOD[simp]:
"ipresIGFresh h termMOD MOD = ipresFresh h MOD"
unfolding ipresIGFresh_def ipresFresh_def by simp

definition ipresFreshAbs where
"ipresFreshAbs hA MOD ==
 \<forall> ys y us s A.
    wlsAbs (us,s) A \<longrightarrow>
    freshAbs ys y A \<longrightarrow> igFreshAbs MOD ys y (hA A)"

lemma ipresIGFreshAbs_termMOD[simp]:
"ipresIGFreshAbs hA termMOD MOD = ipresFreshAbs hA MOD"
unfolding ipresIGFreshAbs_def ipresFreshAbs_def by simp

definition ipresFreshAll where
"ipresFreshAll h hA MOD ==
 ipresFresh h MOD \<and> ipresFreshAbs hA MOD"

lemmas ipresFreshAll_defs = ipresFreshAll_def
ipresFresh_def ipresFreshAbs_def

lemma ipresIGFreshAll_termMOD[simp]:
"ipresIGFreshAll h hA termMOD MOD = ipresFreshAll h hA MOD"
unfolding ipresIGFreshAll_def ipresFreshAll_def by simp

lemmas ipresIGFreshAll_termMOD_simps =
ipresIGFresh_termMOD ipresIGFreshAbs_termMOD ipresIGFreshAll_termMOD

definition ipresSwap where
"ipresSwap h MOD ==
 \<forall> zs z1 z2 s X.
    wls s X \<longrightarrow>
    h (X #[z1 \<and> z2]_zs) = igSwap MOD zs z1 z2 (h X)"

lemma ipresIGSwap_termMOD[simp]:
"ipresIGSwap h termMOD MOD = ipresSwap h MOD"
unfolding ipresIGSwap_def ipresSwap_def by simp

definition ipresSwapAbs where
"ipresSwapAbs hA MOD ==
 \<forall> zs z1 z2 us s A.
    wlsAbs (us,s) A \<longrightarrow>
    hA (A $[z1 \<and> z2]_zs) = igSwapAbs MOD zs z1 z2 (hA A)"

lemma ipresIGSwapAbs_termMOD[simp]:
"ipresIGSwapAbs hA termMOD MOD = ipresSwapAbs hA MOD"
unfolding ipresIGSwapAbs_def ipresSwapAbs_def by simp

definition ipresSwapAll where
"ipresSwapAll h hA MOD ==
 ipresSwap h MOD \<and> ipresSwapAbs hA MOD"

lemmas ipresSwapAll_defs = ipresSwapAll_def
ipresSwap_def ipresSwapAbs_def

lemma ipresIGSwapAll_termMOD[simp]:
"ipresIGSwapAll h hA termMOD MOD = ipresSwapAll h hA MOD"
unfolding ipresIGSwapAll_def ipresSwapAll_def by simp

lemmas ipresIGSwapAll_termMOD_simps =
ipresIGSwap_termMOD ipresIGSwapAbs_termMOD ipresIGSwapAll_termMOD

definition ipresSubst where
"ipresSubst h MOD ==
 \<forall> ys Y y s X.
    wls (asSort ys) Y \<and> wls s X \<longrightarrow>
    h (subst ys Y y X) = igSubst MOD ys (h Y) y (h X)"

lemma ipresIGSubst_termMOD[simp]:
"ipresIGSubst h termMOD MOD = ipresSubst h MOD"
unfolding ipresIGSubst_def ipresSubst_def by simp

definition ipresSubstAbs where
"ipresSubstAbs h hA MOD ==
 \<forall> ys Y y us s A.
    wls (asSort ys) Y \<and> wlsAbs (us,s) A \<longrightarrow>
    hA (A $[Y / y]_ys) = igSubstAbs MOD ys (h Y) y (hA A)"

lemma ipresIGSubstAbs_termMOD[simp]:
"ipresIGSubstAbs h hA termMOD MOD = ipresSubstAbs h hA MOD"
unfolding ipresIGSubstAbs_def ipresSubstAbs_def by simp

definition ipresSubstAll where
"ipresSubstAll h hA MOD ==
 ipresSubst h MOD \<and> ipresSubstAbs h hA MOD"

lemmas ipresSubstAll_defs = ipresSubstAll_def
ipresSubst_def ipresSubstAbs_def

lemma ipresIGSubstAll_termMOD[simp]:
"ipresIGSubstAll h hA termMOD MOD = ipresSubstAll h hA MOD"
unfolding ipresIGSubstAll_def ipresSubstAll_def by simp

lemmas ipresIGSubstAll_termMOD_simps =
ipresIGSubst_termMOD ipresIGSubstAbs_termMOD ipresIGSubstAll_termMOD

definition termFSwImorph where
"termFSwImorph h hA MOD ==
 ipresWlsAll h hA MOD \<and> ipresCons h hA MOD \<and>
 ipresFreshAll h hA MOD \<and> ipresSwapAll h hA MOD"

lemmas termFSwImorph_defs1 = termFSwImorph_def
ipresWlsAll_def ipresCons_def
ipresFreshAll_def ipresSwapAll_def

lemmas termFSwImorph_defs = termFSwImorph_def
ipresWlsAll_defs ipresCons_defs
ipresFreshAll_defs ipresSwapAll_defs

lemma FSwImorph_termMOD[simp]:
"FSwImorph h hA termMOD MOD = termFSwImorph h hA MOD"
unfolding FSwImorph_def termFSwImorph_def by simp

definition termFSbImorph where
"termFSbImorph h hA MOD ==
 ipresWlsAll h hA MOD \<and> ipresCons h hA MOD \<and>
 ipresFreshAll h hA MOD \<and> ipresSubstAll h hA MOD"

lemmas termFSbImorph_defs1 = termFSbImorph_def
ipresWlsAll_def ipresCons_def
ipresFreshAll_def ipresSubstAll_def

lemmas termFSbImorph_defs = termFSbImorph_def
ipresWlsAll_defs ipresCons_defs
ipresFreshAll_defs ipresSubstAll_defs

lemma FSbImorph_termMOD[simp]:
"FSbImorph h hA termMOD MOD = termFSbImorph h hA MOD"
unfolding FSbImorph_def termFSbImorph_def by simp

definition termFSwSbImorph where
"termFSwSbImorph h hA MOD ==
 termFSwImorph h hA MOD \<and> ipresSubstAll h hA MOD"

lemmas termFSwSbImorph_defs1 = termFSwSbImorph_def
termFSwImorph_def ipresSubstAll_def

lemmas termFSwSbImorph_defs = termFSwSbImorph_def
termFSwImorph_defs ipresSubstAll_defs

text {* Term FSwSb morphisms are the same as FSbSw morphisms: *}

lemma termFSwSbImorph_iff:
"termFSwSbImorph h hA MOD =
 (termFSbImorph h hA MOD \<and> ipresSwapAll h hA MOD)"
unfolding termFSwSbImorph_def termFSwImorph_def termFSbImorph_def ipresSubstAll_def
unfolding FSwSbImorph_def FSbImorph_def FSwImorph_def by auto

lemma FSwSbImorph_termMOD[simp]:
"FSwSbImorph h hA termMOD MOD = termFSwSbImorph h hA MOD"
unfolding FSwSbImorph_def termFSwSbImorph_def by simp

lemma ipresWls_wlsInp:
assumes "wlsInp delta inp" and "ipresWls h MOD"
shows "igWlsInp MOD delta (lift h inp)"
using assms imp_igWlsInp[of termMOD delta inp h MOD] by auto

lemma termFSwImorph_wlsInp:
assumes "wlsInp delta inp" and "termFSwImorph h hA MOD"
shows "igWlsInp MOD delta (lift h inp)"
using assms FSwImorph_igWlsInp[of termMOD delta inp h hA MOD] by auto

lemma termFSwSbImorph_wlsInp:
assumes "wlsInp delta inp" and "termFSwSbImorph h hA MOD"
shows "igWlsInp MOD delta (lift h inp)"
using assms FSwSbImorph_igWlsInp[of termMOD delta inp h hA MOD] by auto

lemma ipresWls_wlsBinp:
assumes "wlsBinp delta binp" and "ipresWlsAbs hA MOD"
shows "igWlsBinp MOD delta (lift hA binp)"
using assms imp_igWlsBinp[of termMOD delta binp hA MOD] by auto

lemma termFSwImorph_wlsBinp:
assumes "wlsBinp delta binp" and "termFSwImorph h hA MOD"
shows "igWlsBinp MOD delta (lift hA binp)"
using assms FSwImorph_igWlsBinp[of termMOD delta binp h hA MOD] by auto

lemma termFSwSbImorph_wlsBinp:
assumes "wlsBinp delta binp" and "termFSwSbImorph h hA MOD"
shows "igWlsBinp MOD delta (lift hA binp)"
using assms FSwSbImorph_igWlsBinp[of termMOD delta binp h hA MOD] by auto

lemma id_termFSwImorph: "termFSwImorph id id termMOD"
using id_FSwImorph[of termMOD] by simp

lemma id_termFSbImorph: "termFSbImorph id id termMOD"
using id_FSbImorph[of termMOD] by simp

lemma id_termFSwSbImorph: "termFSwSbImorph id id termMOD"
using id_FSwSbImorph[of termMOD] by simp

lemma comp_termFSwImorph:
assumes *: "termFSwImorph h hA MOD" and **: "FSwImorph h' hA' MOD MOD'"
shows "termFSwImorph (h' o h) (hA' o hA) MOD'"
using assms comp_FSwImorph[of h hA termMOD MOD h' hA' MOD'] by auto

lemma comp_termFSbImorph:
assumes *: "termFSbImorph h hA MOD" and **: "FSbImorph h' hA' MOD MOD'"
shows "termFSbImorph (h' o h) (hA' o hA) MOD'"
using assms comp_FSbImorph[of termMOD h hA MOD h' hA' MOD']
      termMOD_igWlsAbsIsInBar by auto

lemma comp_termFSwSbImorph:
assumes *: "termFSwSbImorph h hA MOD" and **: "FSwSbImorph h' hA' MOD MOD'"
shows "termFSwSbImorph (h' o h) (hA' o hA) MOD'"
using assms comp_FSwSbImorph[of termMOD h hA MOD h' hA' MOD']
      termMOD_igWlsAbsIsInBar by auto

lemmas mapFrom_termMOD_simps =
ipresIGWlsAll_termMOD_simps
ipresIGCons_termMOD_simps
ipresIGFreshAll_termMOD_simps
ipresIGSwapAll_termMOD_simps
ipresIGSubstAll_termMOD_simps
FSwImorph_termMOD FSbImorph_termMOD FSwSbImorph_termMOD

lemmas termMOD_simps =
structure_termMOD_simps mapFrom_termMOD_simps

subsubsection
{* Sufficient criteria for being a morphism
   to a well-sorted model (of various kinds) *}

text{* In a nutshell: in these cases, we only need to check preservation of the
  syntactic constructs, ``ipresCons".  *}

lemma ipresCons_imp_ipresWlsAll:
assumes *: "ipresCons h hA MOD" and **: "igConsIPresIGWls MOD"
shows "ipresWlsAll h hA MOD"
proof-
  {fix s X us s' A
   have "(wls s X \<longrightarrow> igWls MOD s (h X)) \<and>
         (wlsAbs (us,s') A \<longrightarrow> igWlsAbs MOD (us,s') (hA A))"
   proof(induction rule: wls_rawInduct)
     case (Var xs x)
     then show ?case 
     by (metis assms igConsIPresIGWls_def igVarIPresIGWls_def ipresCons_def ipresVar_def)
   next
     case (Op delta inp binp)
     have "igWlsInp MOD delta (lift h inp) \<and> igWlsBinp MOD delta (lift hA binp)"
     using Op unfolding igWlsInp_def igWlsBinp_def wlsInp_iff wlsBinp_iff  
     by simp (simp add: liftAll2_def lift_def split: option.splits)
     hence "igWls MOD (stOf delta) (igOp MOD delta (lift h inp) (lift hA binp))"
     using ** unfolding igConsIPresIGWls_def igOpIPresIGWls_def by simp
     thus ?case using Op * unfolding ipresCons_def ipresOp_def by simp
   next
     case (Abs s xs x X)
     then show ?case  
     by (metis assms igAbsIPresIGWls_def igConsIPresIGWls_def ipresAbs_def ipresCons_def)
   qed 
  }
  thus ?thesis unfolding ipresWlsAll_defs by simp
qed

lemma ipresCons_imp_ipresFreshAll:
assumes *: "ipresCons h hA MOD" and **: "igFreshCls MOD"
and "igConsIPresIGWls MOD"
shows "ipresFreshAll h hA MOD"
proof-
  have ***: "ipresWlsAll h hA MOD"
  using assms ipresCons_imp_ipresWlsAll by auto
  hence ****:
  "\<And> delta inp. wlsInp delta inp \<Longrightarrow> igWlsInp MOD delta (lift h inp)"
  "\<And> delta binp. wlsBinp delta binp \<Longrightarrow> igWlsBinp MOD delta (lift hA binp)"
  unfolding ipresWlsAll_def using ipresWls_wlsInp ipresWls_wlsBinp by auto
  (*  *)
  {fix s X us s' A ys y
   have "(wls s X \<longrightarrow> fresh ys y X \<longrightarrow> igFresh MOD ys y (h X)) \<and>
         (wlsAbs (us,s') A \<longrightarrow> freshAbs ys y A \<longrightarrow> igFreshAbs MOD ys y (hA A))"
   proof(induction rule: wls_rawInduct)
     case (Var xs x)
     then show ?case 
     by (metis * ** fresh_Var_simp igFreshCls_def igFreshIGVar_def ipresCons_def ipresVar_def)
   next
     case (Op delta inp binp) 
     show ?case proof safe
       assume y_fresh: "fresh ys y (Op delta inp binp)"
       {fix i X assume inp: "inp i = Some X"
        then obtain s where "arOf delta i = Some s" 
        using Op unfolding wlsInp_iff sameDom_def by fastforce
        hence "igFresh MOD ys y (h X)"
        using Op.IH y_fresh inp unfolding freshInp_def liftAll_def liftAll2_def 
        by (metis freshInp_def liftAll_def wls_fresh_Op_simp)
       }
       moreover
       {fix i A assume binp: "binp i = Some A"
        then obtain us_s where "barOf delta i = Some us_s"
        using Op unfolding wlsBinp_iff sameDom_def by force
        hence "igFreshAbs MOD ys y (hA A)"
        using Op.IH y_fresh binp unfolding freshBinp_def liftAll_def liftAll2_def 
        by simp (metis (no_types, hide_lams) freshBinp_def liftAll_def old.prod.exhaust)
       }
       ultimately have "igFreshInp MOD ys y (lift h inp) \<and> igFreshBinp MOD ys y (lift hA binp)"
       unfolding igFreshInp_def igFreshBinp_def liftAll_lift_comp unfolding liftAll_def by auto        
       moreover have "igWlsInp MOD delta (lift h inp) \<and> igWlsBinp MOD delta (lift hA binp)"
       using Op **** by simp
       ultimately have "igFresh MOD ys y (igOp MOD delta (lift h inp) (lift hA binp))"
       using ** unfolding igFreshCls_def igFreshIGOp_def by simp
       thus "igFresh MOD ys y (h (Op delta inp binp))"
       using Op * unfolding ipresCons_def ipresOp_def by simp
     qed
   next
     case (Abs s xs x X) 
     hence hX_wls: "igWls MOD s (h X)"
     using *** unfolding ipresWlsAll_def ipresWls_def by simp
     thus ?case  
     using Abs assms by (cases "ys = xs \<and> y = x")
     (simp_all add: igFreshCls_def igFreshIGAbs1_def igFreshIGAbs2_def ipresAbs_def ipresCons_def)
   qed 
  }
  thus ?thesis unfolding ipresFreshAll_defs by auto
qed

lemma ipresCons_imp_ipresSwapAll:
assumes *: "ipresCons h hA MOD" and **: "igSwapCls MOD"
and "igConsIPresIGWls MOD"
shows "ipresSwapAll h hA MOD"
proof-
  have ***: "ipresWlsAll h hA MOD"
  using assms ipresCons_imp_ipresWlsAll by auto
  hence ****:
  "\<And> delta inp. wlsInp delta inp \<Longrightarrow> igWlsInp MOD delta (lift h inp)"
  "\<And> delta binp. wlsBinp delta binp \<Longrightarrow> igWlsBinp MOD delta (lift hA binp)"
  unfolding ipresWlsAll_def using ipresWls_wlsInp ipresWls_wlsBinp by auto
  (*  *)
  {fix s X us s' A zs z1 z2
   have "(wls s X \<longrightarrow> h (swap zs z1 z2 X) = igSwap MOD zs z1 z2 (h X)) \<and>
         (wlsAbs (us,s') A \<longrightarrow> hA (swapAbs zs z1 z2 A) = igSwapAbs MOD zs z1 z2 (hA A))"
   proof(induction rule: wls_rawInduct)
     case (Var xs x)
     then show ?case  
     by (metis "*" "**" igSwapCls_def igSwapIGVar_def ipresCons_def ipresVar_def swap_Var_simp)
   next
     case (Op delta inp binp)
     let ?inpsw = "swapInp zs z1 z2 inp"   let ?binpsw = "swapBinp zs z1 z2 binp"
     let ?Left = "h (Op delta ?inpsw ?binpsw)"
     let ?Right = "igSwap MOD zs z1 z2 (h (Op delta inp binp))" 
     have wlsLiftInp:
     "igWlsInp MOD delta (lift h inp) \<and> igWlsBinp MOD delta (lift hA binp)"
     using Op **** by simp
     have "wlsInp delta ?inpsw \<and> wlsBinp delta ?binpsw"
     using Op by simp
     hence "?Left = igOp MOD delta (lift h ?inpsw) (lift hA ?binpsw)"
     using * unfolding ipresCons_def ipresOp_def by simp
     moreover
     have "lift h ?inpsw = igSwapInp MOD zs z1 z2 (lift h inp) \<and>
           lift hA ?binpsw = igSwapBinp MOD zs z1 z2 (lift hA binp)"
     using Op * not_None_eq
     by (simp add:  igSwapCls_def igSwapIGOp_def wlsInp_iff wlsBinp_iff
     swapInp_def swapBinp_def igSwapInp_def igSwapBinp_def 
     lift_comp fun_eq_iff liftAll2_def lift_def sameDom_def split: option.splits)
     (metis not_None_eq old.prod.exhaust) 
     moreover
     have "igOp MOD delta (igSwapInp MOD zs z1 z2 (lift h inp))
                         (igSwapBinp MOD zs z1 z2 (lift hA binp)) =
           igSwap MOD zs z1 z2 (igOp MOD delta (lift h inp) (lift hA binp))"
     using wlsLiftInp ** unfolding igSwapCls_def igSwapIGOp_def by simp
     moreover
     have "igSwap MOD zs z1 z2 (igOp MOD delta (lift h inp) (lift hA binp)) = ?Right"
     using Op * unfolding ipresCons_def ipresOp_def by simp
     ultimately have "?Left = ?Right" by simp
     then show ?case by (simp add: Op)
   next
     case (Abs s xs x X)
     let ?Xsw = "swap zs z1 z2 X"  let ?xsw = "x @xs[z1 \<and> z2]_zs"
     have hX: "igWls MOD s (h X)" using Abs.IH *** unfolding ipresWlsAll_def ipresWls_def by simp
     let ?Left = "hA (Abs xs ?xsw ?Xsw)"
     let ?Right = "igSwapAbs MOD zs z1 z2 (hA (Abs xs x X))"
     have "wls s (swap zs z1 z2 X)" using Abs by simp
     hence "?Left = igAbs MOD xs ?xsw (h ?Xsw)"
     using Abs * unfolding ipresCons_def ipresAbs_def by blast
     also note Abs(3)
     also have "igAbs MOD xs ?xsw (igSwap MOD zs z1 z2 (h X)) =
                igSwapAbs MOD zs z1 z2 (igAbs MOD xs x (h X))"
     using Abs hX ** by (auto simp: igSwapCls_def igSwapIGAbs_def) 
     also have "\<dots> = ?Right" using Abs * by (auto simp: ipresCons_def ipresAbs_def)
     finally have "?Left = ?Right" .
     then show ?case using Abs(2) by auto
   qed
  }
  thus ?thesis unfolding ipresSwapAll_defs by auto
qed 

lemma ipresCons_imp_ipresSubstAll_aux:
assumes *: "ipresCons h hA MOD" and **: "igSubstCls MOD"
and "igConsIPresIGWls MOD" and "igFreshCls MOD"
assumes P: "wlsPar P"
shows
"(wls s X \<longrightarrow>
  (\<forall> ys y Y. y \<in> varsOfS P ys \<and> Y \<in> termsOfS P (asSort ys) \<longrightarrow>
             h (X #[Y / y]_ys) = igSubst MOD ys (h Y) y (h X)))
\<and>
 (wlsAbs (us,s') A \<longrightarrow>
  (\<forall> ys y Y. y \<in> varsOfS P ys \<and> Y \<in> termsOfS P (asSort ys) \<longrightarrow>
             hA (A $[Y / y]_ys) = igSubstAbs MOD ys (h Y) y (hA A)))"
proof-
  have ***: "ipresWlsAll h hA MOD"
  using assms ipresCons_imp_ipresWlsAll by auto
  hence ****:
  "\<And> delta inp. wlsInp delta inp \<Longrightarrow> igWlsInp MOD delta (lift h inp)"
  "\<And> delta binp. wlsBinp delta binp \<Longrightarrow> igWlsBinp MOD delta (lift hA binp)"
  unfolding ipresWlsAll_def using ipresWls_wlsInp ipresWls_wlsBinp by auto
  have *****: "ipresFreshAll h hA MOD"
  using assms ipresCons_imp_ipresFreshAll by auto
  (*  *)
  show ?thesis
  proof(induction rule: wls_induct_fresh[of P])
    case Par
    then show ?case using P by auto
  next
    case (Var xs x)
    then show ?case using assms
    by (simp add: ipresWlsAll_def ipresWls_def igSubstCls_def igSubstIGVar2_def 
       ipresCons_def ipresVar_def)  
    (metis "***" FixSyn.ipresWlsAll_defs(1) FixSyn.ipresWlsAll_defs(2) FixSyn_axioms 
      igSubstIGVar1_def wlsPar_def wls_subst_Var_simp1 wls_subst_Var_simp2)
  next
    case (Op delta inp binp)
    show ?case proof safe
      fix ys y Y
      assume yP: "y \<in> varsOfS P ys" and YP: "Y \<in> termsOfS P (asSort ys)"
      hence Y: "wls (asSort ys) Y" using P by auto
      hence hY: "igWls MOD (asSort ys) (h Y)"
      using *** unfolding ipresWlsAll_def ipresWls_def by simp
      have sinp: "wlsInp delta (substInp ys Y y inp) \<and>
                wlsBinp delta (substBinp ys Y y binp)" using Y Op by simp
      have liftInp: "igWlsInp MOD delta (lift h inp) \<and>
                     igWlsBinp MOD delta (lift hA binp)"
      using Op **** by simp
      let ?Left = "h ((Op delta inp binp) #[Y / y]_ys)"
      let ?Right = "igSubst MOD ys (h Y) y (h (Op delta inp binp))"
      have "?Left = igOp MOD delta (lift h (substInp ys Y y inp))
                                   (lift hA (substBinp ys Y y binp))"
      using sinp * unfolding ipresCons_def ipresOp_def  
      by (simp add: Op.IH(1) Op.IH(2) Y)
      moreover
      have "lift h (substInp ys Y y inp) = igSubstInp MOD ys (h Y) y (lift h inp) \<and>
            lift hA (substBinp ys Y y binp) = igSubstBinp MOD ys (h Y) y (lift hA binp)"
      using Op YP yP by (simp add: substInp_def2 igSubstInp_def substBinp_def2 igSubstBinp_def lift_comp 
      lift_def liftAll2_def fun_eq_iff wlsInp_iff wlsBinp_iff sameDom_def split: option.splits) 
      (metis (no_types, hide_lams) not_Some_eq option.distinct(1) sinp wlsBinp.simps) 
      moreover
      have "igOp MOD delta (igSubstInp MOD ys (h Y) y (lift h inp))
                        (igSubstBinp MOD ys (h Y) y (lift hA binp)) =
            igSubst MOD ys (h Y) y (igOp MOD delta (lift h inp) (lift hA binp))"
      using hY liftInp ** unfolding igSubstCls_def igSubstIGOp_def by simp
      moreover have "\<dots> = ?Right" using Op * unfolding ipresCons_def ipresOp_def by simp
      ultimately show "?Left = ?Right" by simp
    qed
    next
      case (Abs s xs x X)
      show ?case proof safe
      fix ys y Y 
      assume yP: "y \<in> varsOfS P ys" and YP: "Y \<in>  termsOfS P (asSort ys)" 
      hence x_diff: "ys \<noteq> xs \<or> y \<noteq> x"
      and Y: "wls (asSort ys) Y" and x_fresh: "fresh xs x Y" using P Abs by auto
      hence hY: "igWls MOD (asSort ys) (h Y)"
      using *** unfolding ipresWlsAll_def ipresWls_def by simp
      have hX: "igWls MOD s (h X)"
      using Abs *** unfolding ipresWlsAll_def ipresWls_def by simp
      let ?Xsb = "subst ys Y y X"
      have Xsb: "wls s ?Xsb" using Y Abs by simp
      have x_igFresh: "igFresh MOD xs x (h Y)"
      using Y x_fresh ***** unfolding ipresFreshAll_def ipresFresh_def by simp
      let ?Left = "hA (Abs xs x X $[Y / y]_ys)"
      let ?Right = "igSubstAbs MOD ys (h Y) y (hA (Abs xs x X))"
      have "?Left = hA (Abs xs x ?Xsb)" using Y Abs x_diff x_fresh by auto
      also have "\<dots> = igAbs MOD xs x (h ?Xsb)"
      using Abs Xsb * unfolding ipresCons_def ipresAbs_def by fastforce
      also have "\<dots> = igAbs MOD xs x (igSubst MOD ys (h Y) y (h X))"
      using yP YP Abs.IH by simp
      also have "\<dots> = igSubstAbs MOD ys (h Y) y (igAbs MOD xs x (h X))"
      using Abs hY hX x_diff x_igFresh ** 
      by (auto simp: igSubstCls_def igSubstIGAbs_def) 
      also have "\<dots> = ?Right" using Abs * by (auto simp: ipresCons_def ipresAbs_def) 
      finally show "?Left = ?Right" .
    qed 
  qed
qed 

lemma ipresCons_imp_ipresSubst:
assumes *: "ipresCons h hA MOD" and **: "igSubstCls MOD"
and "igConsIPresIGWls MOD" and "igFreshCls MOD"
shows "ipresSubst h MOD"
unfolding ipresSubst_def apply clarify 
subgoal for ys Y y s X 
using assms ipresCons_imp_ipresSubstAll_aux
  [of h hA MOD
      "ParS (\<lambda>zs. if zs = ys then [y] else [])
            (\<lambda>s'. if s' = asSort ys then [Y] else [])
            (\<lambda>_. [])
            []"]
unfolding wlsPar_def by auto .

lemma ipresCons_imp_ipresSubstAbs:
assumes *: "ipresCons h hA MOD" and **: "igSubstCls MOD"
and "igConsIPresIGWls MOD" and "igFreshCls MOD"
shows "ipresSubstAbs h hA MOD"
unfolding ipresSubstAbs_def apply clarify
subgoal for ys Y y us s A 
using assms ipresCons_imp_ipresSubstAll_aux
  [of h hA MOD
      "ParS (\<lambda>zs. if zs = ys then [y] else [])
            (\<lambda>s'. if s' = asSort ys then [Y] else [])
            (\<lambda>_. [])
            []"]
unfolding wlsPar_def by auto .

lemma ipresCons_imp_ipresSubstAll:
assumes *: "ipresCons h hA MOD" and **: "igSubstCls MOD"
and "igConsIPresIGWls MOD" and "igFreshCls MOD"
shows "ipresSubstAll h hA MOD"
unfolding ipresSubstAll_def using assms
ipresCons_imp_ipresSubst ipresCons_imp_ipresSubstAbs by auto

lemma iwlsFSw_termFSwImorph_iff:
"iwlsFSw MOD \<Longrightarrow> termFSwImorph h hA MOD = ipresCons h hA MOD"
unfolding iwlsFSw_def termFSwImorph_def
using ipresCons_imp_ipresWlsAll
ipresCons_imp_ipresFreshAll ipresCons_imp_ipresSwapAll by auto

corollary iwlsFSwSTR_termFSwImorph_iff:
"iwlsFSwSTR MOD \<Longrightarrow> termFSwImorph h hA MOD = ipresCons h hA MOD"
using iwlsFSwSTR_imp_iwlsFSw iwlsFSw_termFSwImorph_iff by fastforce

lemma iwlsFSb_termFSbImorph_iff:
"iwlsFSb MOD \<Longrightarrow> termFSbImorph h hA MOD = ipresCons h hA MOD"
unfolding iwlsFSb_def termFSbImorph_def
using ipresCons_imp_ipresWlsAll
ipresCons_imp_ipresFreshAll ipresCons_imp_ipresSubstAll
unfolding igSubstCls_def by fastforce+

corollary iwlsFSbSwTR_termFSbImorph_iff:
"iwlsFSbSwTR MOD \<Longrightarrow> termFSbImorph h hA MOD = ipresCons h hA MOD"
using iwlsFSbSwTR_imp_iwlsFSb iwlsFSb_termFSbImorph_iff by fastforce

lemma iwlsFSwSb_termFSwSbImorph_iff:
"iwlsFSwSb MOD \<Longrightarrow> termFSwSbImorph h hA MOD = ipresCons h hA MOD"
unfolding termFSwSbImorph_def iwlsFSwSb_def
apply(simp add: iwlsFSw_termFSwImorph_iff)
unfolding iwlsFSw_def using ipresCons_imp_ipresSubstAll by auto

lemma iwlsFSbSw_termFSwSbImorph_iff:
"iwlsFSbSw MOD \<Longrightarrow> termFSwSbImorph h hA MOD = ipresCons h hA MOD"
unfolding termFSwSbImorph_iff iwlsFSbSw_def
apply(simp add: iwlsFSb_termFSbImorph_iff)
unfolding iwlsFSb_def using ipresCons_imp_ipresSwapAll by auto

end (* context FixSyn *)

subsection{* The ``error" model of associated to a model  *}

text{* The error model will have the operators act like the original ones
on well-formed terms, except that will return ``ERR" (error) or ``True" (in the case of fresh)
whenever one of the inputs (variables, terms or abstractions) is ``ERR" or
is not well-formed.

The error model is more convenient than the original one, since
one can define more easily a map from the model of terms to the former. This map shall be defined
by the universal property of quotients, via a map from quasi-terms whose kernel
includes the alpha-equivalence relation. The latter property (of including
the alpha-equivalence would not be achievable with the original model as tariget, since
alpha is defined unsortedly and the model clauses hold sortedly.

We shall only need error models associated to fresh-swap and to fresh-subst models. *}

subsubsection {* Preliminaries *}

(* I prefer defining a new type to using the option type, since
I already use options for inputs: *)

datatype 'a withERR = ERR | OK 'a

(* *************************************************** *)
context FixSyn   (* scope all throuighout the file *)
begin

definition OKI where
"OKI inp = lift OK inp"

definition check where
"check eX == THE X. eX = OK X"

definition checkI where
"checkI einp == lift check einp"

lemma check_ex_unique:
"eX \<noteq> ERR \<Longrightarrow> (EX! X. eX = OK X)"
by(cases eX, auto)

lemma check_OK[simp]:
"check (OK X) = X"
unfolding check_def using check_ex_unique theI' by auto

lemma OK_check[simp]:
"eX \<noteq> ERR \<Longrightarrow> OK (check eX) = eX"
unfolding check_def using check_ex_unique theI' by auto

lemma checkI_OKI[simp]:
"checkI (OKI inp) = inp"
unfolding OKI_def checkI_def lift_def apply(rule ext)
by(case_tac "inp i", auto)

lemma OKI_checkI[simp]:
assumes "liftAll (\<lambda> X. X \<noteq> ERR) einp"
shows "OKI (checkI einp) = einp"
unfolding OKI_def checkI_def lift_def apply(rule ext)
using assms unfolding liftAll_def by (case_tac "einp i", auto)

lemma OKI_inj[simp]:
fixes inp inp' :: "('index,'gTerm)input"
shows "(OKI inp = OKI inp') = (inp = inp')"
apply(auto) unfolding OKI_def
using lift_preserves_inj[of OK]
unfolding inj_on_def by auto

lemmas OK_OKI_simps =
check_OK OK_check checkI_OKI OKI_checkI OKI_inj

subsubsection {* Definitions and notations *}

definition errMOD ::
"('index,'bindex,'varSort,'sort,'opSym,'var,'gTerm,'gAbs)model \<Rightarrow>
 ('index,'bindex,'varSort,'sort,'opSym,'var,'gTerm withERR,'gAbs withERR)model"
where
"errMOD MOD ==
 \<lparr>igWls = \<lambda> s eX. case eX of ERR \<Rightarrow> False | OK X \<Rightarrow> igWls MOD s X,
  igWlsAbs = \<lambda> (us,s) eA. case eA of ERR \<Rightarrow> False | OK A \<Rightarrow> igWlsAbs MOD (us,s) A,

  igVar = \<lambda> xs x. OK (igVar MOD xs x),
  igAbs = \<lambda>xs x eX.
           if (eX \<noteq> ERR \<and> (\<exists> s. isInBar (xs,s) \<and> igWls MOD s (check eX)))
             then OK (igAbs MOD xs x (check eX))
             else ERR,
  igOp = \<lambda>delta einp ebinp.
          if liftAll (\<lambda> X. X \<noteq> ERR) einp \<and> liftAll (\<lambda> A. A \<noteq> ERR) ebinp
             \<and> igWlsInp MOD delta (checkI einp) \<and> igWlsBinp MOD delta (checkI ebinp)
            then OK (igOp MOD delta (checkI einp) (checkI ebinp))
            else ERR,
  igFresh = \<lambda>ys y eX.
             if eX \<noteq> ERR \<and> (\<exists> s. igWls MOD s (check eX))
               then igFresh MOD ys y (check eX)
               else True,
  igFreshAbs = \<lambda>ys y eA.
                if eA \<noteq> ERR \<and> (\<exists> us s. igWlsAbs MOD (us,s) (check eA))
                  then igFreshAbs MOD ys y (check eA)
                  else True,
  igSwap = \<lambda>zs z1 z2 eX.
            if eX \<noteq> ERR \<and> (\<exists> s. igWls MOD s (check eX))
              then OK (igSwap MOD zs z1 z2 (check eX))
              else ERR,
  igSwapAbs = \<lambda>zs z1 z2 eA.
               if eA \<noteq> ERR \<and> (\<exists> us s. igWlsAbs MOD (us,s) (check eA))
                 then OK (igSwapAbs MOD zs z1 z2 (check eA))
                 else ERR,
  igSubst = \<lambda>ys eY y eX.
              if eY \<noteq> ERR \<and> igWls MOD (asSort ys) (check eY)
                 \<and> eX \<noteq> ERR \<and> (\<exists> s. igWls MOD s (check eX))
                then OK (igSubst MOD ys (check eY) y (check eX))
                else ERR,
  igSubstAbs = \<lambda>ys eY y eA.
                 if eY \<noteq> ERR \<and> igWls MOD (asSort ys) (check eY)
                    \<and> eA \<noteq> ERR \<and> (\<exists> us s. igWlsAbs MOD (us,s) (check eA))
                   then OK (igSubstAbs MOD ys (check eY) y (check eA))
                   else ERR
 \<rparr>"

abbreviation eWls where "eWls MOD == igWls (errMOD MOD)"
abbreviation eWlsAbs where "eWlsAbs MOD == igWlsAbs (errMOD MOD)"
abbreviation eWlsInp where "eWlsInp MOD == igWlsInp (errMOD MOD)"
abbreviation eWlsBinp where "eWlsBinp MOD == igWlsBinp (errMOD MOD)"
abbreviation eVar where "eVar MOD == igVar (errMOD MOD)"
abbreviation eAbs where "eAbs MOD == igAbs (errMOD MOD)"
abbreviation eOp where "eOp MOD == igOp (errMOD MOD)"
abbreviation eFresh where "eFresh MOD == igFresh (errMOD MOD)"
abbreviation eFreshAbs where "eFreshAbs MOD == igFreshAbs (errMOD MOD)"
abbreviation eFreshInp where "eFreshInp MOD == igFreshInp (errMOD MOD)"
abbreviation eFreshBinp where "eFreshBinp MOD == igFreshBinp (errMOD MOD)"
abbreviation eSwap where "eSwap MOD == igSwap (errMOD MOD)"
abbreviation eSwapAbs where "eSwapAbs MOD == igSwapAbs (errMOD MOD)"
abbreviation eSwapInp where "eSwapInp MOD == igSwapInp (errMOD MOD)"
abbreviation eSwapBinp where "eSwapBinp MOD == igSwapBinp (errMOD MOD)"
abbreviation eSubst where "eSubst MOD == igSubst (errMOD MOD)"
abbreviation eSubstAbs where "eSubstAbs MOD == igSubstAbs (errMOD MOD)"
abbreviation eSubstInp where "eSubstInp MOD == igSubstInp (errMOD MOD)"
abbreviation eSubstBinp where "eSubstBinp MOD == igSubstBinp (errMOD MOD)"

subsubsection {*  Simplification rules *}

lemma eWls_simp1[simp]:
"eWls MOD s (OK X) = igWls MOD s X"
unfolding errMOD_def by simp

lemma eWls_simp2[simp]:
"eWls MOD s ERR = False"
unfolding errMOD_def by simp

lemma eWlsAbs_simp1[simp]:
"eWlsAbs MOD (us,s) (OK A) = igWlsAbs MOD (us,s) A"
unfolding errMOD_def by simp

lemma eWlsAbs_simp2[simp]:
"eWlsAbs MOD (us,s) ERR = False"
unfolding errMOD_def by simp

lemma eWlsInp_simp1[simp]:
"eWlsInp MOD delta (OKI inp) = igWlsInp MOD delta inp"
by (fastforce simp: OKI_def sameDom_def liftAll2_def lift_def igWlsInp_def 
  split: option.splits) 

lemma eWlsInp_simp2[simp]:
"\<not> liftAll (\<lambda> eX. eX \<noteq> ERR) einp \<Longrightarrow> \<not> eWlsInp MOD delta einp"
by (force simp: sameDom_def liftAll_def liftAll2_def lift_def igWlsInp_def)  
 
corollary eWlsInp_simp3[simp]:
"\<not> eWlsInp MOD delta (\<lambda>i. Some ERR)"
by (auto simp: liftAll_def)
 
lemma eWlsBinp_simp1[simp]:
"eWlsBinp MOD delta (OKI binp) = igWlsBinp MOD delta binp"
by (fastforce simp: OKI_def sameDom_def liftAll2_def lift_def igWlsBinp_def 
  split: option.splits) 

lemma eWlsBinp_simp2[simp]:
"\<not> liftAll (\<lambda> eA. eA \<noteq> ERR) ebinp \<Longrightarrow> \<not> eWlsBinp MOD delta ebinp"
by (force simp: sameDom_def liftAll_def liftAll2_def lift_def igWlsBinp_def)
 
corollary eWlsBinp_simp3[simp]:
"\<not> eWlsBinp MOD delta (\<lambda>i. Some ERR)"
by (auto simp: liftAll_def)
 
lemmas eWlsAll_simps =
eWls_simp1 eWls_simp2
eWlsAbs_simp1 eWlsAbs_simp2
eWlsInp_simp1 eWlsInp_simp2 eWlsInp_simp3
eWlsBinp_simp1 eWlsBinp_simp2 eWlsBinp_simp3

lemma eVar_simp[simp]:
"eVar MOD xs x = OK (igVar MOD xs x)"
unfolding errMOD_def by simp

lemma eAbs_simp1[simp]:
"\<lbrakk>isInBar (xs,s); igWls MOD s X\<rbrakk> \<Longrightarrow> eAbs MOD xs x (OK X) = OK (igAbs MOD xs x X)"
unfolding errMOD_def by auto

lemma eAbs_simp2[simp]:
"\<forall> s. \<not> (isInBar (xs,s) \<and> igWls MOD s X) \<Longrightarrow> eAbs MOD xs x (OK X) = ERR"
unfolding errMOD_def by auto

lemma eAbs_simp3[simp]:
"eAbs MOD xs x ERR = ERR"
unfolding errMOD_def by auto

lemma eOp_simp1[simp]:
assumes "igWlsInp MOD delta inp" and "igWlsBinp MOD delta binp"
shows "eOp MOD delta (OKI inp) (OKI binp) = OK (igOp MOD delta inp binp)"
unfolding errMOD_def apply simp
unfolding liftAll_def OKI_def lift_def  
using assms by (auto split: option.splits)

lemma eOp_simp2[simp]:
assumes "\<not> igWlsInp MOD delta inp"
shows "eOp MOD delta (OKI inp) ebinp = ERR"
using assms unfolding errMOD_def by auto

lemma eOp_simp3[simp]:
assumes "\<not> igWlsBinp MOD delta binp"
shows "eOp MOD delta einp (OKI binp) = ERR"
using assms unfolding errMOD_def by auto

lemma eOp_simp4[simp]:
assumes "\<not> liftAll (\<lambda> eX. eX \<noteq> ERR) einp"
shows "eOp MOD delta einp ebinp = ERR"
using assms unfolding errMOD_def by auto

corollary eOp_simp5[simp]:
"eOp MOD delta (\<lambda>i. Some ERR) ebinp = ERR"
by (auto simp: liftAll_def)
 
lemma eOp_simp6[simp]:
assumes "\<not> liftAll (\<lambda> eA. eA \<noteq> ERR) ebinp"
shows "eOp MOD delta einp ebinp = ERR"
using assms unfolding errMOD_def by auto

corollary eOp_simp7[simp]:
"eOp MOD delta einp (\<lambda>i. Some ERR) = ERR"
by (auto simp: liftAll_def)
 
lemmas eCons_simps =
eVar_simp
eAbs_simp1 eAbs_simp2 eAbs_simp3
eOp_simp1 eOp_simp2 eOp_simp3 eOp_simp4 eOp_simp5 eOp_simp6 eOp_simp7

lemma eFresh_simp1[simp]:
"igWls MOD s X \<Longrightarrow> eFresh MOD ys y (OK X) = igFresh MOD ys y X"
unfolding errMOD_def by auto

lemma eFresh_simp2[simp]:
"\<forall> s. \<not> igWls MOD s X \<Longrightarrow> eFresh MOD ys y (OK X)"
unfolding errMOD_def by auto

lemma eFresh_simp3[simp]:
"eFresh MOD ys y ERR"
unfolding errMOD_def by auto

lemma eFreshAbs_simp1[simp]:
"igWlsAbs MOD (us,s) A \<Longrightarrow> eFreshAbs MOD ys y (OK A) = igFreshAbs MOD ys y A"
unfolding errMOD_def by auto

lemma eFreshAbs_simp2[simp]:
"\<forall> us s. \<not> igWlsAbs MOD (us,s) A \<Longrightarrow> eFreshAbs MOD ys y (OK A)"
unfolding errMOD_def by auto

lemma eFreshAbs_simp3[simp]:
"eFreshAbs MOD ys y ERR"
unfolding errMOD_def by auto

lemma eFreshInp_simp[simp]:
"igWlsInp MOD delta inp
 \<Longrightarrow> eFreshInp MOD ys y (OKI inp) = igFreshInp MOD ys y inp"
by (force simp: igFreshInp_def OKI_def liftAll_lift_comp igWlsInp_defs intro!: liftAll_cong)
 
lemma eFreshBinp_simp[simp]:
"igWlsBinp MOD delta binp
 \<Longrightarrow> eFreshBinp MOD ys y (OKI binp) = igFreshBinp MOD ys y binp"
by (force simp: igFreshBinp_def OKI_def liftAll_lift_comp igWlsBinp_defs intro!: liftAll_cong)
 
lemmas eFreshAll_simps =
eFresh_simp1 eFresh_simp2 eFresh_simp3
eFreshAbs_simp1 eFreshAbs_simp2 eFreshAbs_simp3
eFreshInp_simp
eFreshBinp_simp

lemma eSwap_simp1[simp]:
"igWls MOD s X
 \<Longrightarrow> eSwap MOD zs z1 z2 (OK X) = OK (igSwap MOD zs z1 z2 X)"
unfolding errMOD_def by auto

lemma eSwap_simp2[simp]:
"\<forall> s. \<not> igWls MOD s X \<Longrightarrow> eSwap MOD zs z1 z2 (OK X) = ERR"
unfolding errMOD_def by auto

lemma eSwap_simp3[simp]:
"eSwap MOD zs z1 z2 ERR = ERR"
unfolding errMOD_def by auto

lemma eSwapAbs_simp1[simp]:
"igWlsAbs MOD (us,s) A
 \<Longrightarrow> eSwapAbs MOD zs z1 z2 (OK A) = OK (igSwapAbs MOD zs z1 z2 A)"
unfolding errMOD_def by auto

lemma eSwapAbs_simp2[simp]:
"\<forall> us s. \<not> igWlsAbs MOD (us,s) A \<Longrightarrow> eSwapAbs MOD zs z1 z2 (OK A) = ERR"
unfolding errMOD_def by auto

lemma eSwapAbs_simp3[simp]:
"eSwapAbs MOD zs z1 z2 ERR = ERR"
unfolding errMOD_def by auto

lemma eSwapInp_simp1[simp]:
"igWlsInp MOD delta inp
 \<Longrightarrow> eSwapInp MOD zs z1 z2 (OKI inp) = OKI (igSwapInp MOD zs z1 z2 inp)"
by (force simp: igSwapInp_def OKI_def lift_comp igWlsInp_defs intro!: lift_cong)

lemma eSwapInp_simp2[simp]:
assumes "\<not> liftAll (\<lambda> eX. eX \<noteq> ERR) einp"
shows "\<not> liftAll (\<lambda> eX. eX \<noteq> ERR) (eSwapInp MOD zs z1 z2 einp)"
using assms unfolding liftAll_def igSwapInp_def lift_def by (auto split: option.splits)

lemma eSwapBinp_simp1[simp]:
"igWlsBinp MOD delta binp
 \<Longrightarrow> eSwapBinp MOD zs z1 z2 (OKI binp) = OKI (igSwapBinp MOD zs z1 z2 binp)"
by (force simp: igSwapBinp_def OKI_def lift_comp igWlsBinp_defs intro!: lift_cong)

lemma eSwapBinp_simp2[simp]:
assumes "\<not> liftAll (\<lambda> eA. eA \<noteq> ERR) ebinp"
shows "\<not> liftAll (\<lambda> eA. eA \<noteq> ERR) (eSwapBinp MOD zs z1 z2 ebinp)"
using assms unfolding liftAll_def igSwapBinp_def lift_def by (auto split: option.splits)
 
lemmas eSwapAll_simps =
eSwap_simp1 eSwap_simp2 eSwap_simp3
eSwapAbs_simp1 eSwapAbs_simp2 eSwapAbs_simp3
eSwapInp_simp1 eSwapInp_simp2
eSwapBinp_simp1 eSwapBinp_simp2

lemma eSubst_simp1[simp]:
"\<lbrakk>igWls MOD (asSort ys) Y; igWls MOD s X\<rbrakk>
 \<Longrightarrow> eSubst MOD ys (OK Y) y (OK X) = OK (igSubst MOD ys Y y X)"
unfolding errMOD_def by auto

lemma eSubst_simp2[simp]:
"\<not> igWls MOD (asSort ys) Y \<Longrightarrow> eSubst MOD ys (OK Y) y eX = ERR"
unfolding errMOD_def by auto

lemma eSubst_simp3[simp]:
"\<forall> s. \<not> igWls MOD s X \<Longrightarrow> eSubst MOD ys eY y (OK X) = ERR"
unfolding errMOD_def by auto

lemma eSubst_simp4[simp]:
"eSubst MOD ys eY y ERR = ERR"
unfolding errMOD_def by auto

lemma eSubst_simp5[simp]:
"eSubst MOD ys ERR y eX = ERR"
unfolding errMOD_def by auto

lemma eSubstAbs_simp1[simp]:
"\<lbrakk>igWls MOD (asSort ys) Y; igWlsAbs MOD (us,s) A\<rbrakk>
 \<Longrightarrow> eSubstAbs MOD ys (OK Y) y (OK A) = OK (igSubstAbs MOD ys Y y A)"
unfolding errMOD_def by auto

lemma eSubstAbs_simp2[simp]:
"\<not> igWls MOD (asSort ys) Y \<Longrightarrow> eSubstAbs MOD ys (OK Y) y eA = ERR"
unfolding errMOD_def by auto

lemma eSubstAbs_simp3[simp]:
"\<forall> us s. \<not> igWlsAbs MOD (us,s) A \<Longrightarrow> eSubstAbs MOD ys eY y (OK A) = ERR"
unfolding errMOD_def by auto

lemma eSubstAbs_simp4[simp]:
"eSubstAbs MOD ys eY y ERR = ERR"
unfolding errMOD_def by auto

lemma eSubstAbs_simp5[simp]:
"eSubstAbs MOD ys ERR y eA = ERR"
unfolding errMOD_def by auto

lemma eSubstInp_simp1[simp]:
"\<lbrakk>igWls MOD (asSort ys) Y; igWlsInp MOD delta inp\<rbrakk>
 \<Longrightarrow> eSubstInp MOD ys (OK Y) y (OKI inp) = OKI (igSubstInp MOD ys Y y inp)"
by (force simp: igSubstInp_def OKI_def lift_comp igWlsInp_defs intro!: lift_cong)

lemma eSubstInp_simp2[simp]:
assumes "\<not> liftAll (\<lambda>eX. eX \<noteq> ERR) einp"
shows "\<not> liftAll (\<lambda>eX. eX \<noteq> ERR) (eSubstInp MOD ys eY y einp)"
using assms unfolding lift_def igSubstInp_def liftAll_def by (auto split: option.splits)
 
lemma eSubstInp_simp3[simp]:
assumes *: "\<not> igWls MOD (asSort ys) Y" and **: "\<not> einp = (\<lambda> i. None)"
shows "\<not> liftAll (\<lambda>eX. eX \<noteq> ERR) (eSubstInp MOD ys (OK Y) y einp)"
using assms by (auto simp: igSubstInp_def liftAll_lift_comp lift_def liftAll_def 
split: option.splits) 

lemma eSubstInp_simp4[simp]:
assumes "\<not> einp = (\<lambda> i. None)"
shows "\<not> liftAll (\<lambda>eX. eX \<noteq> ERR) (eSubstInp MOD ys ERR y einp)"
using assms by (auto simp: igSubstInp_def liftAll_lift_comp lift_def liftAll_def 
split: option.splits)  

lemma eSubstBinp_simp1[simp]:
"\<lbrakk>igWls MOD (asSort ys) Y; igWlsBinp MOD delta binp\<rbrakk>
 \<Longrightarrow> eSubstBinp MOD ys (OK Y) y (OKI binp) = OKI (igSubstBinp MOD ys Y y binp)"
by (force simp: igSubstBinp_def OKI_def lift_comp igWlsBinp_defs intro!: lift_cong)
 
lemma eSubstBinp_simp2[simp]:
assumes "\<not> liftAll (\<lambda>eA. eA \<noteq> ERR) ebinp"
shows "\<not> liftAll (\<lambda>eA. eA \<noteq> ERR) (eSubstBinp MOD ys eY y ebinp)"
using assms by (auto simp: igSubstBinp_def liftAll_lift_comp lift_def liftAll_def 
split: option.splits)  
 
lemma eSubstBinp_simp3[simp]:
assumes *: "\<not> igWls MOD (asSort ys) Y" and **: "\<not> ebinp = (\<lambda> i. None)"
shows "\<not> liftAll (\<lambda>eA. eA \<noteq> ERR) (eSubstBinp MOD ys (OK Y) y ebinp)"
using assms by (auto simp: igSubstBinp_def liftAll_lift_comp lift_def liftAll_def 
split: option.splits)  

lemma eSubstBinp_simp4[simp]:
assumes "\<not> ebinp = (\<lambda> i. None)"
shows "\<not> liftAll (\<lambda>eA. eA \<noteq> ERR) (eSubstBinp MOD ys ERR y ebinp)"
using assms by (auto simp: igSubstBinp_def liftAll_lift_comp lift_def liftAll_def 
split: option.splits) 

lemmas eSubstAll_simps =
eSubst_simp1 eSubst_simp2 eSubst_simp3 eSubst_simp4 eSubst_simp5
eSubstAbs_simp1 eSubstAbs_simp2 eSubstAbs_simp3 eSubstAbs_simp4 eSubstAbs_simp5
eSubstInp_simp1 eSubstInp_simp2 eSubstInp_simp3 eSubstInp_simp4
eSubstBinp_simp1 eSubstBinp_simp2 eSubstBinp_simp3 eSubstBinp_simp4

lemmas error_model_simps =
OK_OKI_simps
eWlsAll_simps
eCons_simps
eFreshAll_simps
eSwapAll_simps
eSubstAll_simps

subsubsection {* Nchotomies *}

lemma eWls_nchotomy:
"(\<exists> X. eX = OK X \<and> igWls MOD s X) \<or> \<not> eWls MOD s eX"
unfolding errMOD_def by(cases eX) auto

lemma eWlsAbs_nchotomy:
"(\<exists> A. eA = OK A \<and> igWlsAbs MOD (us,s) A) \<or> \<not> eWlsAbs MOD (us,s) eA"
unfolding errMOD_def by(cases eA) auto

lemma eAbs_nchotomy:
"((\<exists> s X. eX = OK X \<and> isInBar (xs,s) \<and> igWls MOD s X)) \<or> (eAbs MOD xs x eX = ERR)"
unfolding errMOD_def apply simp using OK_check by fastforce

lemma eOp_nchotomy:
"(\<exists> inp binp. einp = OKI inp \<and> igWlsInp MOD delta inp \<and>
              ebinp = OKI binp \<and> igWlsBinp MOD delta binp)
  \<or>
 (eOp MOD delta einp ebinp = ERR)"
unfolding errMOD_def apply simp using OKI_checkI by force

lemma eFresh_nchotomy:
"(\<exists> s X. eX = OK X \<and> igWls MOD s X) \<or> eFresh MOD ys y eX"
unfolding errMOD_def apply simp using OK_check by fastforce

lemma eFreshAbs_nchotomy:
"(\<exists> us s A. eA = OK A \<and> igWlsAbs MOD (us,s) A)
 \<or> eFreshAbs MOD ys y eA"
unfolding errMOD_def apply simp using OK_check by fastforce

lemma eSwap_nchotomy:
"(\<exists> s X. eX = OK X \<and> igWls MOD s X) \<or>
 (eSwap MOD zs z1 z2 eX = ERR)"
unfolding errMOD_def apply simp using OK_check by fastforce

lemma eSwapAbs_nchotomy:
"(\<exists> us s A. eA = OK A \<and> igWlsAbs MOD (us,s) A) \<or>
 (eSwapAbs MOD zs z1 z2 eA = ERR)"
unfolding errMOD_def apply simp using OK_check by fastforce

lemma eSubst_nchotomy:
"(\<exists> Y. eY = OK Y \<and>
  igWls MOD (asSort ys) Y) \<and> (\<exists> s X. eX = OK X \<and> igWls MOD s X)
 \<or>
 (eSubst MOD ys eY y eX = ERR)"
unfolding errMOD_def apply simp using OK_check by fastforce 

lemma eSubstAbs_nchotomy:
"(\<exists> Y. eY = OK Y \<and> igWls MOD (asSort ys) Y) \<and>
 (\<exists> us s A. eA = OK A \<and> igWlsAbs MOD (us,s) A)
 \<or>
 (eSubstAbs MOD ys eY y eA = ERR)"
unfolding errMOD_def apply simp using OK_check by fastforce


subsubsection {* Inversion rules *}

lemma eWls_invert:
assumes "eWls MOD s eX"
shows "\<exists> X. eX = OK X \<and> igWls MOD s X"
using assms eWls_nchotomy by blast

lemma eWlsAbs_invert:
assumes "eWlsAbs MOD (us,s) eA"
shows "\<exists> A. eA = OK A \<and> igWlsAbs MOD (us,s) A"
using assms eWlsAbs_nchotomy by blast

lemma eWlsInp_invert:
assumes "eWlsInp MOD delta einp"
shows "\<exists> inp. igWlsInp MOD delta inp \<and> einp = OKI inp"
proof
  let ?inp = "checkI einp"
  have "wlsOpS delta" using assms unfolding igWlsInp_def by simp
  moreover have "sameDom (arOf delta) ?inp"
  using assms unfolding igWlsInp_def  checkI_def by simp
  moreover have "liftAll2 (igWls MOD) (arOf delta) ?inp"
  using assms eWls_invert
  by (fastforce simp: igWlsInp_def checkI_def liftAll2_def lift_def sameDom_def 
  split: option.splits) 
  ultimately have "igWlsInp MOD delta ?inp" unfolding igWlsInp_def by simp
  moreover
  {have "liftAll (\<lambda>eX. eX \<noteq> ERR) einp"
   using assms using eWlsInp_simp2 by blast
   hence "einp = OKI ?inp" by simp
  }
  ultimately show "igWlsInp MOD delta ?inp \<and> einp = OKI ?inp" by simp
qed

lemma eWlsBinp_invert:
assumes "eWlsBinp MOD delta ebinp"
shows "\<exists> binp. igWlsBinp MOD delta binp \<and> ebinp = OKI binp"
proof
  let ?binp = "checkI ebinp"
  have "wlsOpS delta" using assms unfolding igWlsBinp_def by simp
  moreover have "sameDom (barOf delta) ?binp"
  using assms unfolding igWlsBinp_def  checkI_def by simp
  moreover have "liftAll2 (igWlsAbs MOD) (barOf delta) ?binp"
  using assms eWlsAbs_invert
  by (fastforce simp: igWlsBinp_def checkI_def liftAll2_def lift_def sameDom_def 
  split: option.splits)
  ultimately have "igWlsBinp MOD delta ?binp" unfolding igWlsBinp_def by simp
  moreover
  {have "liftAll (\<lambda>eA. eA \<noteq> ERR) ebinp"
   using assms using eWlsBinp_simp2 by blast
   hence "ebinp = OKI ?binp" by simp
  }
  ultimately show "igWlsBinp MOD delta ?binp \<and> ebinp = OKI ?binp" by simp
qed

lemma eAbs_invert:
assumes "eAbs MOD xs x eX = OK A"
shows "\<exists> s X. eX = OK X \<and> isInBar (xs,s) \<and> A = igAbs MOD xs x X \<and> igWls MOD s X"
proof-
  have 1: "eAbs MOD xs x eX \<noteq> ERR" using assms by auto
  then obtain s X where *: "eX = OK X"
  and **: "isInBar (xs,s)" and ***: "igWls MOD s X"
  using eAbs_nchotomy[of eX] by fastforce
  hence "eAbs MOD xs x eX = OK (igAbs MOD xs x X)" by simp
  thus ?thesis using assms * ** *** by auto
qed

lemma eOp_invert:
assumes "eOp MOD delta einp ebinp = OK X"
shows
"\<exists> inp binp. einp = OKI inp \<and> ebinp = OKI binp \<and>
             X = igOp MOD delta inp binp \<and>
             igWlsInp MOD delta inp \<and> igWlsBinp MOD delta binp"
proof-
  have "eOp MOD delta einp ebinp \<noteq> ERR" using assms by auto
  then obtain inp binp where *: "einp = OKI inp"   "ebinp = OKI binp"
  "igWlsInp MOD delta inp"   "igWlsBinp MOD delta binp"
  using eOp_nchotomy by blast
  hence "eOp MOD delta einp ebinp = OK (igOp MOD delta inp binp)" by simp
  thus ?thesis using assms * by auto
qed

lemma eFresh_invert:
assumes "\<not> eFresh MOD ys y eX"
shows "\<exists> s X. eX = OK X \<and> \<not> igFresh MOD ys y X \<and> igWls MOD s X"
proof-
  obtain s X where *: "eX = OK X" and **: "igWls MOD s X"
  using assms eFresh_nchotomy[of eX] by fastforce
  hence "eFresh MOD ys y eX = igFresh MOD ys y X" by simp
  thus ?thesis using assms * ** by auto
qed

lemma eFreshAbs_invert:
assumes "\<not> eFreshAbs MOD ys y eA"
shows "\<exists> us s A. eA = OK A \<and> \<not> igFreshAbs MOD ys y A \<and> igWlsAbs MOD (us,s) A"
proof-
  obtain us s A where *: "eA = OK A" and **: "igWlsAbs MOD (us,s) A"
  using assms eFreshAbs_nchotomy[of eA] by fastforce
  hence "eFreshAbs MOD ys y eA = igFreshAbs MOD ys y A" by simp
  thus ?thesis using assms * ** by auto
qed

lemma eSwap_invert:
assumes "eSwap MOD zs z1 z2 eX = OK Y"
shows "\<exists> s X. eX = OK X \<and> Y = igSwap MOD zs z1 z2 X \<and> igWls MOD s X"
proof-
  have 1: "eSwap MOD zs z1 z2 eX \<noteq> ERR" using assms by auto
  then obtain s X where *: "eX = OK X" and **: "igWls MOD s X"
  using eSwap_nchotomy[of eX] by fastforce
  hence "eSwap MOD zs z1 z2 eX = OK (igSwap MOD zs z1 z2 X)" by simp
  thus ?thesis using assms * ** by auto
qed

lemma eSwapAbs_invert:
assumes "eSwapAbs MOD zs z1 z2 eA = OK B"
shows "\<exists> us s A. eA = OK A \<and> B = igSwapAbs MOD zs z1 z2 A \<and> igWlsAbs MOD (us,s) A"
proof-
  have 1: "eSwapAbs MOD zs z1 z2 eA \<noteq> ERR" using assms by auto
  then obtain us s A where *: "eA = OK A" and **: "igWlsAbs MOD (us,s) A"
  using eSwapAbs_nchotomy[of eA] by fastforce
  hence "eSwapAbs MOD zs z1 z2 eA = OK (igSwapAbs MOD zs z1 z2 A)" by simp
  thus ?thesis using assms * ** by auto
qed

lemma eSubst_invert:
assumes "eSubst MOD ys eY y eX = OK Z"
shows
"\<exists> s X Y. eY = OK Y \<and> eX = OK X \<and> igWls MOD s X \<and> igWls MOD (asSort ys) Y \<and>
          Z = igSubst MOD ys Y y X"
proof-
  have 1: "eSubst MOD ys eY y eX \<noteq> ERR" using assms by auto
  then obtain s X Y where *: "eX = OK X"   "eY = OK Y"
  "igWls MOD s X"  "igWls MOD (asSort ys) Y"
  using eSubst_nchotomy[of eY _ _ eX] by fastforce
  hence "eSubst MOD ys eY y eX = OK (igSubst MOD ys Y y X)" by simp
  thus ?thesis using assms * by auto
qed

lemma eSubstAbs_invert:
assumes "eSubstAbs MOD ys eY y eA = OK Z"
shows
"\<exists> us s A Y. eY = OK Y \<and> eA = OK A \<and> igWlsAbs MOD (us,s) A \<and> igWls MOD (asSort ys) Y \<and>
             Z = igSubstAbs MOD ys Y y A"
proof-
  have 1: "eSubstAbs MOD ys eY y eA \<noteq> ERR" using assms by auto
  then obtain us s A Y where *: "eA = OK A"   "eY = OK Y"
  "igWlsAbs MOD (us,s) A"  "igWls MOD (asSort ys) Y"
  using eSubstAbs_nchotomy[of eY _ _ eA] by fastforce
  hence "eSubstAbs MOD ys eY y eA = OK (igSubstAbs MOD ys Y y A)" by simp
  thus ?thesis using assms * by auto
qed

subsubsection {* The error model is strongly well-sorted
as a fresh-swap-subst and as a fresh-subst-swap model *}

text{* That is, provided the original model is a well-sorted fresh-swap model. *}

text{* The domains are disjoint: *}

lemma errMOD_igWlsDisj:
assumes "igWlsDisj MOD"
shows "igWlsDisj (errMOD MOD)"
using assms unfolding errMOD_def igWlsDisj_def  
apply clarify subgoal for _ _ X by(cases X) auto . 

lemma errMOD_igWlsAbsDisj:
assumes "igWlsAbsDisj MOD"
shows "igWlsAbsDisj (errMOD MOD)"
using assms unfolding errMOD_def igWlsAbsDisj_def
apply clarify subgoal for _ _ _ _ A by(cases A) fastforce+ . 

lemma errMOD_igWlsAllDisj:
assumes "igWlsAllDisj MOD"
shows "igWlsAllDisj (errMOD MOD)"
using assms unfolding igWlsAllDisj_def
using errMOD_igWlsDisj errMOD_igWlsAbsDisj by auto

text{* Only ``bound arity" abstraction domains are inhabited:  *}

lemma errMOD_igWlsAbsIsInBar:
assumes "igWlsAbsIsInBar MOD"
shows "igWlsAbsIsInBar (errMOD MOD)"
using assms eWlsAbs_invert unfolding igWlsAbsIsInBar_def by blast
 

text{* The operators preserve the domains strongly: *}

lemma errMOD_igVarIPresIGWlsSTR:
assumes "igVarIPresIGWls MOD"
shows "igVarIPresIGWls (errMOD MOD)"
using assms unfolding errMOD_def igVarIPresIGWls_def by simp

lemma errMOD_igAbsIPresIGWlsSTR:
assumes *: "igAbsIPresIGWls MOD" and **: "igWlsAbsDisj MOD"
and ***: "igWlsAbsIsInBar MOD"
shows "igAbsIPresIGWlsSTR (errMOD MOD)"
using assms by (fastforce simp: errMOD_def igAbsIPresIGWls_def igAbsIPresIGWlsSTR_def 
igWlsAbsIsInBar_def igWlsAbsDisj_def split: withERR.splits) 
  
lemma errMOD_igOpIPresIGWlsSTR:
fixes MOD :: "('index,'bindex,'varSort,'sort,'opSym,'var,'gTerm,'gAbs)model"
assumes "igOpIPresIGWls MOD"
shows "igOpIPresIGWlsSTR (errMOD MOD)"
by (simp add: igOpIPresIGWlsSTR_def igOpIPresIGWls_def) 
  (smt assms eOp_nchotomy eOp_simp1 eWlsBinp_invert 
eWlsBinp_simp1 eWlsInp_invert eWlsInp_simp1 eWls_simp1 eWls_simp2 igOpIPresIGWls_def) 

lemma errMOD_igConsIPresIGWlsSTR:
assumes "igConsIPresIGWls MOD" and "igWlsAllDisj MOD"
and "igWlsAbsIsInBar MOD"
shows "igConsIPresIGWlsSTR (errMOD MOD)"
using assms unfolding igConsIPresIGWls_def igConsIPresIGWlsSTR_def igWlsAllDisj_def
using
errMOD_igVarIPresIGWlsSTR[of MOD]
errMOD_igAbsIPresIGWlsSTR[of MOD]
errMOD_igOpIPresIGWlsSTR[of MOD]
by auto

lemma errMOD_igSwapIPresIGWlsSTR:
assumes "igSwapIPresIGWls MOD" and "igWlsDisj MOD"
shows "igSwapIPresIGWlsSTR (errMOD MOD)"
using `igSwapIPresIGWls MOD` 
using assms by (fastforce simp: errMOD_def igSwapIPresIGWls_def igSwapIPresIGWlsSTR_def 
igWlsDisj_def split: withERR.splits) 

lemma errMOD_igSwapAbsIPresIGWlsAbsSTR:
assumes *: "igSwapAbsIPresIGWlsAbs MOD" and **: "igWlsAbsDisj MOD"
and ***: "igWlsAbsIsInBar MOD"
shows "igSwapAbsIPresIGWlsAbsSTR (errMOD MOD)"
using assms by (simp add: errMOD_def igSwapAbsIPresIGWlsAbs_def igSwapAbsIPresIGWlsAbsSTR_def 
igWlsAbsIsInBar_def igWlsAbsDisj_def split: withERR.splits) blast

lemma errMOD_igSwapAllIPresIGWlsAllSTR:
assumes "igSwapAllIPresIGWlsAll MOD" and "igWlsAllDisj MOD"
and "igWlsAbsIsInBar MOD"
shows "igSwapAllIPresIGWlsAllSTR (errMOD MOD)"
using assms
unfolding igSwapAllIPresIGWlsAll_def igSwapAllIPresIGWlsAllSTR_def igWlsAllDisj_def
using errMOD_igSwapIPresIGWlsSTR[of MOD] errMOD_igSwapIPresIGWlsSTR[of MOD]
errMOD_igSwapAbsIPresIGWlsAbsSTR[of MOD]
by auto

lemma errMOD_igSubstIPresIGWlsSTR:
assumes "igSubstIPresIGWls MOD" and "igWlsDisj MOD"
shows "igSubstIPresIGWlsSTR (errMOD MOD)"
using `igSubstIPresIGWls MOD`
using assms by (fastforce simp: errMOD_def igSubstIPresIGWls_def igSubstIPresIGWlsSTR_def 
igWlsDisj_def split: withERR.splits)
 
lemma errMOD_igSubstAbsIPresIGWlsAbsSTR:
assumes *: "igSubstAbsIPresIGWlsAbs MOD" and **: "igWlsAbsDisj MOD"
and ***: "igWlsAbsIsInBar MOD"
shows "igSubstAbsIPresIGWlsAbsSTR (errMOD MOD)"
using assms by (simp add: errMOD_def igSubstAbsIPresIGWlsAbs_def igSubstAbsIPresIGWlsAbsSTR_def 
igWlsAbsIsInBar_def igWlsAbsDisj_def split: withERR.splits) blast

lemma errMOD_igSubstAllIPresIGWlsAllSTR:
assumes "igSubstAllIPresIGWlsAll MOD" and "igWlsAllDisj MOD"
and "igWlsAbsIsInBar MOD"
shows "igSubstAllIPresIGWlsAllSTR (errMOD MOD)"
using assms
unfolding igSubstAllIPresIGWlsAll_def igSubstAllIPresIGWlsAllSTR_def igWlsAllDisj_def
using errMOD_igSubstIPresIGWlsSTR[of MOD] errMOD_igSubstIPresIGWlsSTR[of MOD]
errMOD_igSubstAbsIPresIGWlsAbsSTR[of MOD]
by auto

text{* The strong ``fresh" clauses are satisfied: *}

lemma errMOD_igFreshIGVarSTR:
assumes "igVarIPresIGWls MOD" and "igFreshIGVar MOD"
shows "igFreshIGVar (errMOD MOD)"
using assms eFresh_simp1 
by(fastforce simp: igVarIPresIGWls_def igFreshIGVar_def)

lemma errMOD_igFreshIGAbs1STR:
assumes *: "igAbsIPresIGWls MOD" and **: "igFreshIGAbs1 MOD"
shows "igFreshIGAbs1STR (errMOD MOD)"
unfolding igFreshIGAbs1STR_def proof(clarify)
  fix ys y eX
  show "eFreshAbs MOD ys y (eAbs MOD ys y eX)"
  proof(cases "eX \<noteq> ERR")
    define X where "X \<equiv> check eX"
    case True 
    hence eX: "eX = OK X" unfolding X_def using OK_check by auto
    show ?thesis using assms eFreshAbs_simp1 unfolding eX 
    by (cases "\<exists> s. isInBar (ys,s) \<and> igWls MOD s X")
    (fastforce simp: igAbsIPresIGWls_def igFreshIGAbs1_def)+
  qed auto
qed

lemma errMOD_igFreshIGAbs2STR:
assumes "igAbsIPresIGWls MOD" and "igFreshIGAbs2 MOD"
shows "igFreshIGAbs2STR (errMOD MOD)"
unfolding igFreshIGAbs2STR_def proof(clarify)
  fix ys y xs x eX
  assume *: "eFresh MOD ys y eX"
  define X where "X \<equiv> check eX"
  show "eFreshAbs MOD ys y (eAbs MOD xs x eX)"
  proof(cases "eX \<noteq> ERR") 
    case True
    hence eX: "eX = OK X" unfolding X_def using OK_check by auto
    show ?thesis unfolding eX
    using assms * eFreshAbs_invert eX  
    by (cases "\<exists> s. isInBar (xs,s) \<and> igWls MOD s X")
    (fastforce simp: igAbsIPresIGWls_def igFreshIGAbs2_def)+  
  qed auto
qed

(* HERE *)

lemma errMOD_igFreshIGOpSTR:
fixes MOD :: "('index,'bindex,'varSort,'sort,'opSym,'var,'gTerm,'gAbs)model"
assumes "igOpIPresIGWls MOD" and "igFreshIGOp MOD"
shows "igFreshIGOpSTR (errMOD MOD)"
unfolding igFreshIGOpSTR_def apply clarify
subgoal for ys y delta einp ebinp
apply(cases "liftAll (\<lambda>eX. eX \<noteq> ERR) einp \<and>
               liftAll (\<lambda>eA. eA \<noteq> ERR) ebinp")
using assms by (simp_all add: igOpIPresIGWls_def  igFreshIGOp_def)
(metis eFreshBinp_simp eFreshInp_simp eFresh_invert eOp_invert)+ .

lemma errMOD_igFreshClsSTR:
assumes "igConsIPresIGWls MOD" and "igFreshCls MOD"
shows "igFreshClsSTR (errMOD MOD)"
using assms unfolding igConsIPresIGWls_def igFreshCls_def igFreshClsSTR_def
using
errMOD_igFreshIGVarSTR
errMOD_igFreshIGAbs1STR errMOD_igFreshIGAbs2STR
errMOD_igFreshIGOpSTR
by auto

text{* The strong ``swap" clauses are satisfied: *}

lemma errMOD_igSwapIGVarSTR:
fixes MOD :: "('index,'bindex,'varSort,'sort,'opSym,'var,'gTerm,'gAbs)model"
assumes "igVarIPresIGWls MOD" and "igSwapIGVar MOD"
shows "igSwapIGVar (errMOD MOD)"
using assms by (simp add: igVarIPresIGWls_def igSwapIGVar_def) (metis eSwap_simp1)

lemma errMOD_igSwapIGAbsSTR:
assumes *: "igAbsIPresIGWls MOD" and **: "igWlsDisj MOD"
and ***: "igSwapIPresIGWls MOD" and ****: "igSwapIGAbs MOD"
shows "igSwapIGAbsSTR (errMOD MOD)"
unfolding igSwapIGAbsSTR_def apply(clarify)
subgoal for zs z1 z2 xs x eX
apply (cases eX)
 subgoal by auto
 subgoal for X
 apply(cases "\<exists> s. isInBar (xs,s) \<and> igWls MOD s X") 
  subgoal using assms 
  using assms OK_check 
  by (simp_all add: igAbsIPresIGWls_def igSwapIPresIGWls_def igSwapIGAbs_def igWlsDisj_def)  
     (smt eAbs_simp1 eSwapAbs_simp1 eSwap_simp1 withERR.inject)
  subgoal using assms 
  by(simp_all add: igAbsIPresIGWls_def igSwapIPresIGWls_def igSwapIGAbs_def igWlsDisj_def)  
    (metis check_OK eAbs_nchotomy eSwap_invert) . . .
 
lemma errMOD_igSwapIGOpSTR:
assumes "igWlsAbsIsInBar MOD" and "igOpIPresIGWls MOD"
and "igSwapIPresIGWls MOD" and "igSwapAbsIPresIGWlsAbs MOD"
and "igWlsDisj MOD" and "igWlsAbsDisj MOD"
and "igSwapIGOp MOD"
shows "igSwapIGOpSTR (errMOD MOD)"
unfolding igSwapIGOpSTR_def proof(clarify)
  have 0: "igSwapInpIPresIGWlsInp MOD \<and> igSwapBinpIPresIGWlsBinp MOD"
  using `igSwapIPresIGWls MOD`  `igSwapAbsIPresIGWlsAbs MOD`
  imp_igSwapInpIPresIGWlsInp imp_igSwapBinpIPresIGWlsBinp by auto
  have "igSwapIPresIGWlsSTR (errMOD MOD) \<and>
        igSwapAbsIPresIGWlsAbsSTR (errMOD MOD)"
  using assms errMOD_igSwapIPresIGWlsSTR
        errMOD_igSwapAbsIPresIGWlsAbsSTR by auto
  hence 1: "igSwapInpIPresIGWlsInpSTR (errMOD MOD) \<and>
            igSwapBinpIPresIGWlsBinpSTR (errMOD MOD)"
  using imp_igSwapInpIPresIGWlsInpSTR
        imp_igSwapBinpIPresIGWlsBinpSTR by auto
  fix zs::'varSort and z1 z2 ::'var and delta einp ebinp
  let ?Left = "eSwap MOD zs z1 z2 (eOp MOD delta einp ebinp)"
  let ?einpsw = "eSwapInp MOD zs z1 z2 einp"
  let ?ebinpsw = "eSwapBinp MOD zs z1 z2 ebinp"
  let ?Right = "eOp MOD delta ?einpsw ?ebinpsw"
  show "?Left = ?Right"
  proof(cases "liftAll (\<lambda>eX. eX \<noteq> ERR) einp \<and>
               liftAll (\<lambda>eA. eA \<noteq> ERR) ebinp")
    case True note t = True
    moreover obtain inp and binp where
    "inp = checkI einp" and  "binp = checkI ebinp" by blast
    ultimately have einp: "einp = OKI inp"   "ebinp = OKI binp" by auto
    show ?thesis
    proof(cases "igWlsInp MOD delta inp \<and> igWlsBinp MOD delta binp")
      case False
      hence "?Left = ERR" unfolding einp by auto
      have "\<not> (eWlsInp MOD delta einp \<and> eWlsBinp MOD delta ebinp)"
      unfolding einp using False by auto
      hence 2: "\<not> (eWlsInp MOD delta ?einpsw \<and> eWlsBinp MOD delta ?ebinpsw)"
      using 1 unfolding igSwapInpIPresIGWlsInpSTR_def
                             igSwapBinpIPresIGWlsBinpSTR_def by auto
      {fix X assume "?Right = OK X"
       then obtain inpsw and binpsw
       where "?einpsw = OKI inpsw" and "?ebinpsw = OKI binpsw"
       and "igWlsInp MOD delta inpsw" and "igWlsBinp MOD delta binpsw"
       and "X = igOp MOD delta inpsw binpsw"
       using eOp_invert[of MOD delta ?einpsw ?ebinpsw X] by auto
       hence False using 2 by auto
      } 
      with `?Left = ERR` show ?thesis by (cases ?Right) auto
    next
      case True  
      moreover have "igWls MOD (stOf delta) (igOp MOD delta inp binp)"
      using True `igOpIPresIGWls MOD` unfolding igOpIPresIGWls_def by simp
      moreover have "igWlsInp MOD delta (igSwapInp MOD zs z1 z2 inp) \<and>
                     igWlsBinp MOD delta (igSwapBinp MOD zs z1 z2 binp)"
      using 0 unfolding igSwapInpIPresIGWlsInp_def igSwapBinpIPresIGWlsBinp_def
      using True by simp
      ultimately show ?thesis using `igSwapIGOp MOD` unfolding einp igSwapIGOp_def by auto
    qed
  qed auto
qed

lemma errMOD_igSwapClsSTR:
assumes "igWlsAllDisj MOD" and "igWlsDisj MOD"
and "igWlsAbsIsInBar MOD" and "igConsIPresIGWls MOD"
and "igSwapAllIPresIGWlsAll MOD" and "igSwapCls MOD"
shows "igSwapClsSTR (errMOD MOD)"
using assms
unfolding igWlsAllDisj_def igConsIPresIGWls_def igSwapCls_def
igSwapAllIPresIGWlsAll_def igSwapClsSTR_def
using
errMOD_igSwapIGVarSTR[of MOD]
errMOD_igSwapIGAbsSTR[of MOD]
errMOD_igSwapIGOpSTR[of MOD]
by simp

text{* The strong ``subst" clauses are satisfied: *}

lemma errMOD_igSubstIGVar1STR:
assumes "igVarIPresIGWls MOD" and "igSubstIGVar1 MOD"
shows "igSubstIGVar1STR (errMOD MOD)"
using assms  
by (simp add: igSubstIGVar1STR_def igVarIPresIGWls_def igSubstIGVar1_def)
   (metis eSubst_simp1 eWls_invert)

lemma errMOD_igSubstIGVar2STR:
assumes "igVarIPresIGWls MOD" and "igSubstIGVar2 MOD"
shows "igSubstIGVar2STR (errMOD MOD)"
using assms  
by (simp add: igSubstIGVar2STR_def igVarIPresIGWls_def igSubstIGVar2_def) 
   (metis eSubst_simp1 eWls_invert)

lemma errMOD_igSubstIGAbsSTR:
fixes MOD :: "('index,'bindex,'varSort,'sort,'opSym,'var,'gTerm,'gAbs)model"
assumes *: "igAbsIPresIGWls MOD" and **: "igWlsDisj MOD"
and ***: "igSubstIPresIGWls MOD" and ****: "igSubstIGAbs MOD"
shows "igSubstIGAbsSTR (errMOD MOD)"
unfolding igSubstIGAbsSTR_def proof(clarify)
  fix ys xs ::'varSort and y x ::'var and eX eY
  assume diff: "xs \<noteq> ys \<or> x \<noteq> y"
  and x_fresh_Y: "eFresh MOD xs x eY"
  show "eSubstAbs MOD ys eY y (eAbs MOD xs x eX) =
        eAbs MOD xs x (eSubst MOD ys eY y eX)"
  proof(cases "eX \<noteq> ERR \<and> eY \<noteq> ERR")
    case True
    define X and Y where "X \<equiv> check eX" and "Y \<equiv> check eY"
    hence eX: "eX = OK X" and eY: "eY = OK Y" unfolding X_def Y_def
    using True OK_check by auto
    show ?thesis 
    proof(cases "(\<exists> s. isInBar (xs,s) \<and> igWls MOD s X) \<and> igWls MOD (asSort ys) Y")
      case True 
      then obtain s where xs_s: "isInBar (xs, s)" and X: "igWls MOD s X" 
      and Y: "igWls MOD (asSort ys) Y" by auto
      hence "igWlsAbs MOD (xs,s) (igAbs MOD xs x X)"
      using * unfolding igAbsIPresIGWls_def by simp
      moreover have "igWls MOD s (igSubst MOD ys Y y X)"
      using X Y *** unfolding igSubstIPresIGWls_def by simp
      moreover have "igFresh MOD xs x Y"
      using x_fresh_Y Y unfolding eY by simp
      ultimately show ?thesis unfolding eX eY
      using xs_s X Y apply simp
      using x_fresh_Y diff **** unfolding igSubstIGAbs_def by fastforce
    next
      case False 
      show ?thesis 
      proof(cases "(EX s. igWls MOD s X) \<and> igWls MOD (asSort ys) Y")
        case True
        then obtain s where X: "igWls MOD s X" and Y: "igWls MOD (asSort ys) Y" by auto
        hence 2: "~ isInBar (xs,s)" using False by (auto simp: eX eY)
        let ?Xsb = "igSubst MOD ys Y y X"
        have Xsb: "igWls MOD s ?Xsb"
        using Y X *** unfolding igSubstIPresIGWls_def by auto
        {fix s' assume 3: "isInBar (xs,s')" and "igWls MOD s' ?Xsb"
         hence "s = s'" using Xsb ** unfolding igWlsDisj_def by auto
         hence False using 2 3 by (simp add: eX eY)
        }
        thus ?thesis using False Y eAbs_simp2 X eX eY by fastforce
      qed(auto simp add: eX eY)
    qed
  qed auto
qed

lemma errMOD_igSubstIGOpSTR:
assumes "igWlsAbsIsInBar MOD"
and "igVarIPresIGWls MOD" and "igOpIPresIGWls MOD"
and "igSubstIPresIGWls MOD" and "igSubstAbsIPresIGWlsAbs MOD"
and "igWlsDisj MOD" and "igWlsAbsDisj MOD"
and "igSubstIGOp MOD"
shows "igSubstIGOpSTR (errMOD MOD)"
proof-
  have 0: "igSubstInpIPresIGWlsInp MOD \<and> igSubstBinpIPresIGWlsBinp MOD"
  using `igSubstIPresIGWls MOD` `igSubstAbsIPresIGWlsAbs MOD`
  imp_igSubstInpIPresIGWlsInp imp_igSubstBinpIPresIGWlsBinp by auto
  have "igSubstIPresIGWlsSTR (errMOD MOD) \<and> igSubstAbsIPresIGWlsAbsSTR (errMOD MOD)"
  using assms errMOD_igSubstIPresIGWlsSTR errMOD_igSubstAbsIPresIGWlsAbsSTR by auto
  hence 1: "igSubstInpIPresIGWlsInpSTR (errMOD MOD) \<and>
            igSubstBinpIPresIGWlsBinpSTR (errMOD MOD)"
  using imp_igSubstInpIPresIGWlsInpSTR imp_igSubstBinpIPresIGWlsBinpSTR by auto
  show ?thesis
  unfolding igSubstIGOpSTR_def proof safe
    fix ys::'varSort and y y1 ::'var and delta einp ebinp
    let ?Left = "eSubst MOD ys (eVar MOD ys y1) y (eOp MOD delta einp ebinp)"
    let ?einpsb = "eSubstInp MOD ys (eVar MOD ys y1) y einp"
    let ?ebinpsb = "eSubstBinp MOD ys (eVar MOD ys y1) y ebinp"
    let ?Right = "eOp MOD delta ?einpsb ?ebinpsb"
    show "?Left = ?Right"
    proof(cases "liftAll (\<lambda>eX. eX \<noteq> ERR) einp \<and> liftAll (\<lambda>eA. eA \<noteq> ERR) ebinp")
      case True 
      moreover obtain inp binp where
      "inp = checkI einp" and "binp = checkI ebinp" by blast
      ultimately have einp: "einp = OKI inp"  "ebinp = OKI binp"  by auto
      have igWls_y1: "igWls MOD (asSort ys) (igVar MOD ys y1)"
      using `igVarIPresIGWls MOD` unfolding igVarIPresIGWls_def by simp
      show ?thesis
      proof(cases "igWlsInp MOD delta inp \<and> igWlsBinp MOD delta binp")
        case False
        hence "?Left = ERR" unfolding einp by auto
        have "\<not> (eWlsInp MOD delta einp \<and> eWlsBinp MOD delta ebinp)"
        unfolding einp using False by simp
        hence 2: "\<not> (eWlsInp MOD delta ?einpsb \<and> eWlsBinp MOD delta ?ebinpsb)"
        using igWls_y1 1
        unfolding igSubstInpIPresIGWlsInpSTR_def igSubstBinpIPresIGWlsBinpSTR_def by simp
        {fix X assume "?Right = OK X"
         then obtain inpsb binpsb where
         "?einpsb = OKI inpsb" and "?ebinpsb = OKI binpsb"
         and "igWlsInp MOD delta inpsb" and "igWlsBinp MOD delta binpsb"
         and "X = igOp MOD delta inpsb binpsb"
         using eOp_invert[of MOD delta ?einpsb ?ebinpsb X] by auto
         hence False using 2 by auto
        }
        hence "?Right = ERR" by (cases ?Right, auto)
        with `?Left = ERR` show ?thesis by simp
      next
        case True
        moreover have "igWls MOD (stOf delta) (igOp MOD delta inp binp)"
        using True `igOpIPresIGWls MOD` unfolding igOpIPresIGWls_def by simp
        moreover
        have "igWlsInp MOD delta (igSubstInp MOD ys (igVar MOD ys y1) y inp) \<and>
              igWlsBinp MOD delta (igSubstBinp MOD ys (igVar MOD ys y1) y binp)"
        using 0 unfolding igSubstInpIPresIGWlsInp_def igSubstBinpIPresIGWlsBinp_def
        using True igWls_y1 by simp
        ultimately show ?thesis
        using `igSubstIGOp MOD` igWls_y1 unfolding einp igSubstIGOp_def by auto
      qed
    qed auto
  next
    fix ys::'varSort and y ::'var and eY delta einp ebinp
    assume eY: "eWls MOD (asSort ys) eY"
    let ?Left = "eSubst MOD ys eY y (eOp MOD delta einp ebinp)"
    let ?einpsb = "eSubstInp MOD ys eY y einp"
    let ?ebinpsb = "eSubstBinp MOD ys eY y ebinp"
    let ?Right = "eOp MOD delta ?einpsb ?ebinpsb"
    from eY obtain Y where eY_def: "eY = OK Y"
    and Y: "igWls MOD (asSort ys) Y" using eWls_invert[of MOD "asSort ys" eY] by auto
    show "?Left = ?Right"
    proof(cases "liftAll (\<lambda>eX. eX \<noteq> ERR) einp \<and> liftAll (\<lambda>eA. eA \<noteq> ERR) ebinp")
      case True
      moreover obtain inp binp where
      "inp = checkI einp" and "binp = checkI ebinp" by blast
      ultimately have einp: "einp = OKI inp"  "ebinp = OKI binp" by auto
      show ?thesis
      proof(cases "igWlsInp MOD delta inp \<and> igWlsBinp MOD delta binp")
        case False
        hence "?Left = ERR" unfolding einp by auto
        have "\<not> (eWlsInp MOD delta einp \<and> eWlsBinp MOD delta ebinp)"
        unfolding einp using False by simp
        hence 2: "\<not> (eWlsInp MOD delta ?einpsb \<and> eWlsBinp MOD delta ?ebinpsb)"
        unfolding eY_def using Y 1
        unfolding igSubstInpIPresIGWlsInpSTR_def igSubstBinpIPresIGWlsBinpSTR_def by simp
        {fix X assume "?Right = OK X"
         then obtain inpsb binpsb
         where "?einpsb = OKI inpsb" and "?ebinpsb = OKI binpsb"
         and "igWlsInp MOD delta inpsb" and "igWlsBinp MOD delta binpsb"
         and "X = igOp MOD delta inpsb binpsb"
         using eOp_invert[of MOD delta ?einpsb ?ebinpsb X] by auto
         hence False using 2 by auto
        }
        hence "?Right = ERR" by (cases ?Right, auto)
        with `?Left = ERR` show ?thesis by simp
      next
        case True
        moreover have "igWls MOD (stOf delta) (igOp MOD delta inp binp)"
        using True `igOpIPresIGWls MOD` unfolding igOpIPresIGWls_def by simp
        moreover
        have "igWlsInp MOD delta (igSubstInp MOD ys Y y inp) \<and>
              igWlsBinp MOD delta (igSubstBinp MOD ys Y y binp)"
        using 0 unfolding igSubstInpIPresIGWlsInp_def igSubstBinpIPresIGWlsBinp_def
        using True Y by simp
        ultimately show ?thesis unfolding einp eY_def 
        using `igSubstIGOp MOD` Y unfolding igSubstIGOp_def by auto
      qed
    qed auto
  qed
qed

lemma errMOD_igSubstClsSTR:
assumes "igWlsAllDisj MOD" and "igConsIPresIGWls MOD"
and "igWlsAbsIsInBar MOD"
and "igSubstAllIPresIGWlsAll MOD" and "igSubstCls MOD"
shows "igSubstClsSTR (errMOD MOD)"
using assms
unfolding igWlsAllDisj_def igConsIPresIGWls_def igSubstCls_def
igSubstAllIPresIGWlsAll_def igSubstClsSTR_def
using
errMOD_igSubstIGVar1STR[of MOD] errMOD_igSubstIGVar2STR[of MOD]
errMOD_igSubstIGAbsSTR[of MOD]
errMOD_igSubstIGOpSTR[of MOD]
by simp

text{* Strong swap-based congruence for abstractions holds: *}

lemma errMOD_igAbsCongSSTR:
assumes "igSwapIPresIGWls MOD" and "igWlsDisj MOD" and "igAbsCongS MOD"
shows "igAbsCongSSTR (errMOD MOD)"
unfolding igAbsCongSSTR_def proof(clarify)
  fix xs ::'varSort and x x' y ::'var and eX eX'
  assume *: "eFresh MOD xs y eX" and **: "eFresh MOD xs y eX'"
  and ***: "eSwap MOD xs y x eX = eSwap MOD xs y x' eX'"
  let ?phi = "\<lambda>eX. eX = ERR \<or> (\<exists> X. eX = OK X \<and> (\<forall> s. \<not> igWls MOD s X))"
  have 1: "?phi eX = ?phi eX'"
  proof
    assume "?phi eX"
    {fix X' s' assume "eX' = OK X' \<and> (\<exists> s. igWls MOD s X')"
     hence "ERR = OK (igSwap MOD xs y x' X')" using `?phi eX` *** by auto
    }
    thus "?phi eX'" by(cases eX', auto)
  next
    assume "?phi eX'"
    {fix X assume "eX = OK X \<and> (\<exists> s. igWls MOD s X)"
     hence "ERR = OK (igSwap MOD xs y x X)" using `?phi eX'` *** by auto
    }
    thus "?phi eX" by(cases eX, auto)
  qed
  show "eAbs MOD xs x eX = eAbs MOD xs x' eX'"
  proof(cases "?phi eX")
    case True
    thus ?thesis using 1 by auto
  next
    case False
    then obtain s X where eX: "eX = OK X" and X_wls: "igWls MOD s X" by(cases eX, auto)
    obtain s' X' where eX': "eX' = OK X'" and X'_wls: "igWls MOD s' X'"
    using `\<not> ?phi eX` 1 by(cases eX') auto
    hence "igSwap MOD xs y x X = igSwap MOD xs y x' X'"
    using eX X_wls *** by auto
    moreover have "igWls MOD s (igSwap MOD xs y x X)"
    using X_wls `igSwapIPresIGWls MOD` unfolding igSwapIPresIGWls_def by simp
    moreover have "igWls MOD s' (igSwap MOD xs y x' X')"
    using X'_wls `igSwapIPresIGWls MOD` unfolding igSwapIPresIGWls_def by simp
    ultimately have "s' = s" using `igWlsDisj MOD` unfolding igWlsDisj_def by auto
    show ?thesis
    proof (cases "isInBar (xs,s)")
      case True
      have "igFresh MOD xs y X" using * X_wls unfolding eX by simp
      moreover have "igFresh MOD xs y X'" using ** X'_wls unfolding eX' by simp
      moreover have "igSwap MOD xs y x X = igSwap MOD xs y x' X'"
      using *** X_wls X'_wls unfolding eX eX' by simp
      ultimately show ?thesis  
      unfolding eX eX' 
      using X_wls X'_wls unfolding `s' = s`
      using `igAbsCongS MOD` True unfolding igAbsCongS_def 
      by (metis FixSyn.eCons_simps(2) FixSyn_axioms)
    next
      case False
      {fix s'' assume xs_s'': "isInBar (xs,s'')" and "igWls MOD s'' X"
       hence "s = s''" using X_wls `igWlsDisj MOD` unfolding igWlsDisj_def by auto
       hence False using False xs_s'' by simp
      }
      moreover
      {fix s'' assume xs_s'': "isInBar (xs,s'')" and "igWls MOD s'' X'"
       hence "s = s''" using X'_wls `igWlsDisj MOD` unfolding igWlsDisj_def `s' = s` by auto
       hence False using False xs_s'' by simp
      }
      ultimately show ?thesis 
      using eX eX' X_wls X'_wls unfolding `s' = s` by fastforce
    qed
  qed
qed

text{* The renaming clause for abstractions holds: *}

lemma errMOD_igAbsRenSTR:
assumes "igVarIPresIGWls MOD" and "igSubstIPresIGWls MOD"
and "igWlsDisj MOD" and "igAbsRen MOD"
shows "igAbsRenSTR (errMOD MOD)"
using assms unfolding igAbsRenSTR_def apply clarify
subgoal for xs y x eX
apply(cases eX)
 subgoal by auto
 subgoal for X
 apply(cases "EX s. isInBar (xs,s) \<and> igWls MOD s X")
   subgoal by (auto simp: igVarIPresIGWls_def igSubstIPresIGWls_def igAbsRen_def) 
   subgoal using assms by (simp add: igVarIPresIGWls_def igSubstIPresIGWls_def igAbsRen_def igWlsDisj_def)   
     (metis eAbs_simp2 eAbs_simp3  eSubst_simp1 eSubst_simp3) . . .

text{* Strong subst-based congruence for abstractions holds: *}

corollary errMOD_igAbsCongUSTR:
assumes "igVarIPresIGWls MOD" and "igSubstIPresIGWls MOD"
and "igWlsDisj MOD" and "igAbsRen MOD"
shows "igAbsCongUSTR (errMOD MOD)"
using assms errMOD_igAbsRenSTR igAbsRenSTR_imp_igAbsCongUSTR by auto

text{* The error model is a strongly well-sorted fresh-swap model: *}

lemma errMOD_iwlsFSwSTR:
fixes MOD :: "('index,'bindex,'varSort,'sort,'opSym,'var,'gTerm,'gAbs) model"
assumes "iwlsFSw MOD"
shows "iwlsFSwSTR (errMOD MOD)"
using assms unfolding iwlsFSw_def iwlsFSwSTR_def
using errMOD_igWlsAllDisj[of MOD]
errMOD_igWlsAbsIsInBar[of MOD]
errMOD_igConsIPresIGWlsSTR[of MOD]
errMOD_igSwapAllIPresIGWlsAllSTR[of MOD]
errMOD_igFreshClsSTR[of MOD] errMOD_igSwapClsSTR[of MOD]
errMOD_igAbsCongSSTR[of MOD]
apply simp
unfolding igSwapAllIPresIGWlsAll_def igWlsAllDisj_defs by simp

text{* The error model is a strongly well-sorted fresh-subst model: *}

lemma errMOD_iwlsFSbSwTR:
fixes MOD :: "('index,'bindex,'varSort,'sort,'opSym,'var,'gTerm,'gAbs) model"
assumes "iwlsFSb MOD"
shows "iwlsFSbSwTR (errMOD MOD)"
using assms unfolding iwlsFSb_def iwlsFSbSwTR_def
using errMOD_igWlsAllDisj[of MOD]
errMOD_igWlsAbsIsInBar[of MOD]
errMOD_igConsIPresIGWlsSTR[of MOD]
errMOD_igSubstAllIPresIGWlsAllSTR[of MOD]
errMOD_igFreshClsSTR[of MOD] errMOD_igSubstClsSTR[of MOD]
errMOD_igAbsRenSTR[of MOD]
by (simp add: igConsIPresIGWls_def igSubstAllIPresIGWlsAll_def igWlsAllDisj_defs) 

subsubsection {* The natural morhpism from an error model to its original model  *}

text{* This morphism is igiven by the ``check" functions.  *}

text{* Preservation of the domains: *}

lemma check_ipresIGWls:
"ipresIGWls check (errMOD MOD) MOD"
unfolding ipresIGWls_def apply clarify
subgoal for _ X by(cases X) auto .

lemma check_ipresIGWlsAbs:
"ipresIGWlsAbs check (errMOD MOD) MOD"
unfolding ipresIGWlsAbs_def apply clarify
subgoal for _ _ A by(cases A) auto .

lemma check_ipresIGWlsAll:
"ipresIGWlsAll check check (errMOD MOD) MOD"
unfolding ipresIGWlsAll_def
using check_ipresIGWls check_ipresIGWlsAbs by auto

text{* Preservation of the operations: *}

lemma check_ipresIGVar:
"ipresIGVar check (errMOD MOD) MOD"
unfolding ipresIGVar_def by simp

lemma check_ipresIGAbs:
"ipresIGAbs check check (errMOD MOD) MOD"
unfolding ipresIGAbs_def apply clarify
subgoal for _ _ _ X by(cases X) auto .

lemma check_ipresIGOp:
"ipresIGOp check check (errMOD MOD) MOD"
unfolding ipresIGOp_def proof clarify
  fix delta einp ebinp
  assume "eWlsInp MOD delta einp" and "eWlsBinp MOD delta ebinp"
  then obtain inp binp where
  "igWlsInp MOD delta inp" and "igWlsBinp MOD delta binp"
  and "einp = OKI inp" and "ebinp = OKI binp"
  using eWlsInp_invert eWlsBinp_invert by blast
  hence "check (eOp MOD delta einp ebinp) =
         igOp MOD delta (checkI einp) (checkI ebinp)" by simp
  thus "check (eOp MOD delta einp ebinp) =
        igOp MOD delta (lift check einp) (lift check ebinp)"
  unfolding checkI_def .
qed

lemma check_ipresIGCons:
"ipresIGCons check check (errMOD MOD) MOD"
unfolding ipresIGCons_def
using
check_ipresIGVar
check_ipresIGAbs
check_ipresIGOp
by auto

lemma check_ipresIGFresh:
"ipresIGFresh check (errMOD MOD) MOD"
unfolding ipresIGFresh_def apply clarify
subgoal for _ _ _ X by(cases X) auto .

lemma check_ipresIGFreshAbs:
"ipresIGFreshAbs check (errMOD MOD) MOD"
unfolding ipresIGFreshAbs_def apply clarify
subgoal for _ _ _ _ A by(cases A) auto .

lemma check_ipresIGFreshAll:
"ipresIGFreshAll check check (errMOD MOD) MOD"
unfolding ipresIGFreshAll_def
using check_ipresIGFresh check_ipresIGFreshAbs by auto

lemma check_ipresIGSwap:
"ipresIGSwap check (errMOD MOD) MOD"
unfolding ipresIGSwap_def apply clarify
subgoal for _ _ _ _ X by(cases X) auto .

lemma check_ipresIGSwapAbs:
"ipresIGSwapAbs check (errMOD MOD) MOD"
unfolding ipresIGSwapAbs_def apply clarify
subgoal for _ _ _ _ _ A by(cases A) auto .

lemma check_ipresIGSwapAll:
"ipresIGSwapAll check check (errMOD MOD) MOD"
unfolding ipresIGSwapAll_def
using check_ipresIGSwap check_ipresIGSwapAbs by auto

lemma check_ipresIGSubst:
"ipresIGSubst check (errMOD MOD) MOD"
unfolding ipresIGSubst_def apply clarify
subgoal for _ Y _ _  X by (cases X, simp, cases Y) auto .

lemma check_ipresIGSubstAbs:
"ipresIGSubstAbs check check (errMOD MOD) MOD"
unfolding ipresIGSubstAbs_def apply clarify
subgoal for _ Y _ _ _ A by (cases A, simp, cases Y) auto .

lemma check_ipresIGSubstAll:
"ipresIGSubstAll check check (errMOD MOD) MOD"
unfolding ipresIGSubstAll_def
using check_ipresIGSubst check_ipresIGSubstAbs by auto

text{* ``check" is a fresh-swap morphism: *}

lemma check_FSwImorph:
"FSwImorph check check (errMOD MOD) MOD"
unfolding FSwImorph_def
using check_ipresIGWlsAll check_ipresIGCons
check_ipresIGFreshAll check_ipresIGSwapAll by auto

text{* ``check" is a fresh-subst morphism: *}

lemma check_FSbImorph:
"FSbImorph check check (errMOD MOD) MOD"
unfolding FSbImorph_def
using check_ipresIGWlsAll check_ipresIGCons
check_ipresIGFreshAll check_ipresIGSubstAll by auto

subsection {* Initiality of the models of terms *}

text {* We show that terms form initial models in all the considered kinds.
The desired initial morphism will be the composition of ``check" with the
factorization of the standard (absolute-initial) function from quasi-terms, ``qInit",
to alpha-equivalence.
``qInit" preserving alpha-equivalence (in an unsorted fashion)
was the main reason for introducing error models. *}

(* Here we need to switch back for a while to the quasi-term ``implementation" of terms: *)

declare qItem_simps[simp]
declare qItem_versus_item_simps[simp]
declare good_item_simps[simp]

subsubsection {* The initial map from quasi-terms to a strong model *}

(* The next is needed in the termination arigument for ``qInit": *)

definition
aux_qInit_ignoreFirst ::
"('index,'bindex,'varSort,'sort,'opSym,'var,'gTerm,'gAbs)model *
 ('index,'bindex,'varSort,'var,'opSym)qTerm +
 ('index,'bindex,'varSort,'sort,'opSym,'var,'gTerm,'gAbs)model *
 ('index,'bindex,'varSort,'var,'opSym)qAbs \<Rightarrow>
 ('index,'bindex,'varSort,'var,'opSym)qTermItem"
where
"aux_qInit_ignoreFirst K =
 (case K of Inl (MOD,qX) \<Rightarrow> termIn qX
           |Inr (MOD,qA) \<Rightarrow> absIn qA)"

lemma qTermLess_ingoreFirst_wf:
"wf (inv_image qTermLess aux_qInit_ignoreFirst)"
using qTermLess_wf wf_inv_image by auto

function
qInit :: "('index,'bindex,'varSort,'sort,'opSym,'var,'gTerm,'gAbs)model \<Rightarrow>
          ('index,'bindex,'varSort,'var,'opSym)qTerm \<Rightarrow> 'gTerm"
and
qInitAbs :: "('index,'bindex,'varSort,'sort,'opSym,'var,'gTerm,'gAbs)model \<Rightarrow>
          ('index,'bindex,'varSort,'var,'opSym)qAbs \<Rightarrow> 'gAbs"
where
"qInit MOD (qVar xs x) = igVar MOD xs x"
|
"qInit MOD (qOp delta qinp qbinp) =
 igOp MOD delta (lift (qInit MOD) qinp) (lift (qInitAbs MOD) qbinp)"
|
"qInitAbs MOD (qAbs xs x qX) = igAbs MOD xs x (qInit MOD qX)"
by(pat_completeness) auto
termination
apply(relation "inv_image qTermLess aux_qInit_ignoreFirst")
apply(simp add: qTermLess_ingoreFirst_wf)
by(auto simp: qTermLess_def aux_qInit_ignoreFirst_def)

lemma qFreshAll_igFreshAll_qInitAll:
assumes "igFreshClsSTR MOD"
shows
"(qFresh ys y qX \<longrightarrow> igFresh MOD ys y (qInit MOD qX)) \<and>
 (qFreshAbs ys y qA \<longrightarrow> igFreshAbs MOD ys y (qInitAbs MOD qA))"
apply(induct rule: qTerm_rawInduct)
using assms 
by (auto simp: igFreshClsSTR_def igFreshIGVar_def qFreshInp_def qFreshBinp_def liftAll_lift_comp
  liftAll_def igFreshInp_def igFreshBinp_def lift_def igFreshIGAbs1STR_def igFreshIGAbs2STR_def igFreshIGOpSTR_def
  split: option.splits)

corollary iwlsFSwSTR_qFreshAll_igFreshAll_qInitAll:
assumes "iwlsFSwSTR MOD"
shows
"(qFresh ys y qX \<longrightarrow> igFresh MOD ys y (qInit MOD qX)) \<and>
 (qFreshAbs ys y qA \<longrightarrow> igFreshAbs MOD ys y (qInitAbs MOD qA))"
using assms unfolding iwlsFSwSTR_def by(simp add: qFreshAll_igFreshAll_qInitAll)

corollary iwlsFSbSwTR_qFreshAll_igFreshAll_qInitAll:
assumes "iwlsFSbSwTR MOD"
shows
"(qFresh ys y qX \<longrightarrow> igFresh MOD ys y (qInit MOD qX)) \<and>
 (qFreshAbs ys y qA \<longrightarrow> igFreshAbs MOD ys y (qInitAbs MOD qA))"
using assms unfolding iwlsFSbSwTR_def by(simp add: qFreshAll_igFreshAll_qInitAll)

lemma qSwapAll_igSwapAll_qInitAll:
assumes "igSwapClsSTR MOD"
shows
"qInit MOD (qX #[[ z1 \<and> z2]]_zs) = igSwap MOD zs z1 z2 (qInit MOD qX) \<and>
 qInitAbs MOD (qA $[[z1 \<and> z2]]_zs) = igSwapAbs MOD zs z1 z2 (qInitAbs MOD qA)"
proof(induction rule: qTerm_rawInduct)
  case (Var xs x)
  then show ?case using assms unfolding igSwapClsSTR_def igSwapIGVar_def by simp
next
  case (Op delta qinp qbinp) 
  hence "lift (qInit MOD) (qSwapInp zs z1 z2 qinp) =
        igSwapInp MOD zs z1 z2 (lift (qInit MOD) qinp) \<and>
        lift (qInitAbs MOD) (qSwapBinp zs z1 z2 qbinp) =
        igSwapBinp MOD zs z1 z2 (lift (qInitAbs MOD) qbinp)"
  using Op.IH by (auto simp: qSwapInp_def qSwapBinp_def igSwapInp_def lift_def liftAll_def 
  igSwapBinp_def iwlsFSwSTR_def igSwapClsSTR_def igSwapIGOpSTR_def
  split: option.splits)
  thus ?case 
  using assms unfolding iwlsFSwSTR_def igSwapClsSTR_def igSwapIGOpSTR_def by simp
next
  case (Abs xs x X)
  then show ?case using assms unfolding igSwapClsSTR_def igSwapIGAbsSTR_def by simp
qed 

corollary iwlsFSwSTR_qSwapAll_igSwapAll_qInitAll:
assumes wls: "iwlsFSwSTR MOD"
shows
"qInit MOD (qX #[[ z1 \<and> z2]]_zs) = igSwap MOD zs z1 z2 (qInit MOD qX) \<and>
 qInitAbs MOD (qA $[[z1 \<and> z2]]_zs) = igSwapAbs MOD zs z1 z2 (qInitAbs MOD qA)"
using assms unfolding iwlsFSwSTR_def by(simp add: qSwapAll_igSwapAll_qInitAll)

lemma qSwapAll_igSubstAll_qInitAll:
fixes qX::"('index,'bindex,'varSort,'var,'opSym)qTerm" and
      qA::"('index,'bindex,'varSort,'var,'opSym)qAbs"
assumes *: "igSubstClsSTR MOD"  and "igFreshClsSTR MOD"
and "igAbsRenSTR MOD"
shows
"(qGood qX \<longrightarrow>
  (\<forall> ys y1 y.
     qAFresh ys y1 qX \<longrightarrow>
     qInit MOD (qX #[[y1 \<and> y]]_ys) = igSubst MOD ys (igVar MOD ys y1) y (qInit MOD qX)))
 \<and>
 (qGoodAbs qA \<longrightarrow>
  (\<forall> ys y1 y.
     qAFreshAbs ys y1 qA \<longrightarrow>
     qInitAbs MOD (qA $[[y1 \<and> y]]_ys) = igSubstAbs MOD ys (igVar MOD ys y1) y (qInitAbs MOD qA)))"
proof(induction rule: qGood_qTerm_induct)
  case (Var xs x)
  show ?case apply safe 
  subgoal for ys y1 y using * 
  by (cases "ys = xs \<and> y = x")
     (auto simp:  igSubstClsSTR_defs igSubstIGVar2STR_def igSubstClsSTR_defs igSubstIGVar1STR_def).
next
  let ?h = "qInit MOD"  let ?hA = "qInitAbs MOD"
  case (Op delta qinp qbinp)
  then show ?case proof safe
    fix ys y1 y  
    assume ***: "qAFresh ys y1 (qOp delta qinp qbinp)"
    have "lift ?h (qSwapInp ys y1 y qinp) =
        igSubstInp MOD ys (igVar MOD ys y1) y (lift ?h qinp) \<and>
        lift ?hA (qSwapBinp ys y1 y qbinp) =
        igSubstBinp MOD ys (igVar MOD ys y1) y (lift ?hA qbinp)"
    using Op.IH ***
    by (auto simp: qSwapInp_def igSubstInp_def qSwapBinp_def igSubstBinp_def 
      lift_def liftAll_def split: option.splits)
    thus "qInit MOD (qOp delta qinp qbinp #[[y1 \<and> y]]_ys) =
       igSubst MOD ys (igVar MOD ys y1) y (qInit MOD (qOp delta qinp qbinp))"
    using assms unfolding iwlsFSwSTR_def igSubstClsSTR_defs igSubstIGOpSTR_def by simp
  qed
next
  let ?h = "qInit MOD"  let ?hA = "qInitAbs MOD"
  case (Abs xs x qX)
  show ?case proof safe 
    fix ys y1 y  
    let ?xy1y = "x @xs[y1 \<and> y]_ys"  let ?y1 = "igVar MOD ys y1"
    assume "qAFreshAbs ys y1 (qAbs xs x qX)"
    hence y1_fresh: "ys = xs \<longrightarrow> y1 \<noteq> x"   "qAFresh ys y1 qX" by auto
    hence 1: "qFresh ys y1 qX" using qAFresh_imp_qFresh by auto
    hence y1_fresh_qX: "igFresh MOD ys y1 (?h qX)"
    using assms unfolding igSubstClsSTR_def
    by(simp add: qFreshAll_igFreshAll_qInitAll)
    (* *)
    obtain x1 where x1_fresh: "x1 \<notin> {y,y1}"  "qFresh xs x1 qX"  "qAFresh xs x1 qX"
    using obtain_qFresh[of "{y,y1}" "{qX}"] using Abs by blast
    hence [simp]: "igFresh MOD xs x1 (?h qX)"
    using assms by(simp add: qFreshAll_igFreshAll_qInitAll)
    let ?x1 = "igVar MOD xs x1"   let ?x1y1y = "x1 @xs[y1 \<and> y]_ys"
    let ?qX_x1x = "qX #[[x1 \<and> x]]_xs"  let ?qX_x1x_y1y = "?qX_x1x #[[y1 \<and> y]]_ys"
    let ?qX_y1y = "qX #[[y1 \<and> y]]_ys" let ?qX_y1y_x1_xy1y = "?qX_y1y #[[x1 \<and> ?xy1y]]_xs"
    let ?qX_y1y_x1y1y_xy1y = "?qX_y1y #[[?x1y1y \<and> ?xy1y]]_xs"
    have [simp]: "qAFresh ys y1 ?qX_x1x"
    using y1_fresh x1_fresh by(auto simp add: qSwap_preserves_qAFresh_distinct)
    have [simp]: "qAFresh xs x1 ?qX_y1y"
    using y1_fresh x1_fresh by(auto simp add: qSwap_preserves_qAFresh_distinct)
    hence "qFresh xs x1 ?qX_y1y" by (simp add: qAFresh_imp_qFresh)
    hence [simp]: "igFresh MOD xs x1 (?h ?qX_y1y)"
    using assms by(simp add: qFreshAll_igFreshAll_qInitAll)
    have [simp]: "igFresh MOD xs x1 ?y1"
    using x1_fresh assms  unfolding igFreshClsSTR_def igFreshIGVar_def by simp
    have x1_def: "x1 = ?x1y1y" using x1_fresh by simp
    (*  *)
    have "?hA ((qAbs xs x qX) $[[y1 \<and> y]]_ys) = igAbs MOD xs ?xy1y (?h ?qX_y1y)" by simp
    also have "\<dots> = igAbs MOD xs x1 (igSubst MOD xs ?x1 ?xy1y (?h ?qX_y1y))"
    using assms unfolding igAbsRenSTR_def by simp
    also have "igSubst MOD xs ?x1 ?xy1y (?h ?qX_y1y) = ?h (?qX_y1y_x1_xy1y)"
    using y1_fresh Abs.IH[of "?qX_y1y"] by(simp add: qSwap_qSwapped)
    also have "?qX_y1y_x1_xy1y = ?qX_y1y_x1y1y_xy1y" using x1_def by simp
    also have "\<dots> = ?qX_x1x_y1y" apply(rule sym) by(rule qSwap_compose)
    also have "?h ?qX_x1x_y1y = igSubst MOD ys ?y1 y (?h ?qX_x1x)"
    using Abs.IH[of "?qX_x1x"] by(simp add: qSwap_qSwapped)
    also have
    "igAbs MOD xs x1 (igSubst MOD ys ?y1 y (?h ?qX_x1x)) =
     igSubstAbs MOD ys ?y1 y (igAbs MOD xs x1 (?h (?qX_x1x)))"
    using assms unfolding igSubstClsSTR_def igSubstIGAbsSTR_def
    using x1_fresh y1_fresh by simp
    also have "?h (?qX_x1x) = igSubst MOD xs ?x1 x (?h qX)"
    using Abs.IH[of "qX"] x1_fresh by(simp add: qSwapped.Refl)
    also have
    "igAbs MOD xs x1 (igSubst MOD xs ?x1 x (?h qX)) =
     igAbs MOD xs x (?h qX)"
    using assms unfolding igAbsRenSTR_def by simp
    also have "igAbs MOD xs x (?h qX) = ?hA (qAbs xs x qX)"
    using assms by simp
    finally show "?hA ((qAbs xs x qX) $[[y1 \<and> y]]_ys) =
        igSubstAbs MOD ys ?y1 y (?hA (qAbs xs x qX))" .
  qed
qed

lemma iwlsFSbSwTR_qSwapAll_igSubstAll_qInitAll:
assumes wls: "iwlsFSbSwTR MOD"
shows
"(qGood qX \<longrightarrow>
  qAFresh ys y1 qX \<longrightarrow>
  qInit MOD (qX #[[y1 \<and> y]]_ys) = igSubst MOD ys (igVar MOD ys y1) y (qInit MOD qX))
 \<and>
 (qGoodAbs qA \<longrightarrow>
  qAFreshAbs ys y1 qA \<longrightarrow>
  qInitAbs MOD (qA $[[y1 \<and> y]]_ys) = igSubstAbs MOD ys (igVar MOD ys y1) y (qInitAbs MOD qA))"
using assms unfolding iwlsFSbSwTR_def by(simp add: qSwapAll_igSubstAll_qInitAll)

lemma iwlsFSwSTR_alphaAll_qInitAll:
assumes "iwlsFSwSTR MOD"
shows
"(\<forall> qX'. qX #= qX' \<longrightarrow> qInit MOD qX = qInit MOD qX') \<and>
 (\<forall> qA'. qA $= qA' \<longrightarrow> qInitAbs MOD qA = qInitAbs MOD qA')"
proof(induction rule: qTerm_induct)
  case (Var xs x)
  then show ?case by(simp add: qVar_alpha_iff) 
next
  case (Op delta qinp qbinp)
  show ?case proof safe
    fix qX'
    assume "qOp delta qinp qbinp #= qX'"
    then obtain qinp' qbinp' where qX': "qX' = qOp delta qinp' qbinp'"
    and *: "sameDom qinp qinp' \<and> sameDom qbinp qbinp'"
    and **: "liftAll2 (\<lambda>qX qX'. qX #= qX') qinp qinp' \<and>
             liftAll2 (\<lambda>qA qA'. qA $= qA') qbinp qbinp'"
    using qOp_alpha_iff[of delta qinp qbinp qX'] by auto
    hence "lift (qInit MOD) qinp = lift (qInit MOD) qinp'"
    by (smt Op.IH(1) liftAll2_def liftAll2_lift_ext liftAll_def)
    moreover have "lift (qInitAbs MOD) qbinp = lift (qInitAbs MOD) qbinp'"
    by (smt * ** Op.IH(2) liftAll2_def liftAll2_lift_ext liftAll_def)
    ultimately
    show "qInit MOD (qOp delta qinp qbinp) = qInit MOD qX'" unfolding qX' by simp
  qed
next
  case (Abs xs x qX)
  show ?case proof safe
    fix qA'
    assume "qAbs xs x qX $= qA'"
    then obtain x' y qX' where qA': "qA' = qAbs xs x' qX'"
    and y_not: "y \<notin> {x, x'}" and "qAFresh xs y qX"  "qAFresh xs y qX'"
    and alpha: "(qX #[[y \<and> x]]_xs) #= (qX' #[[y \<and> x']]_xs)"
    using qAbs_alphaAbs_iff[of xs x qX qA'] by auto
    hence y_fresh: "qFresh xs y qX \<and> qFresh xs y qX'" using qAFresh_imp_qFresh by auto
    have "(qX, qX #[[y \<and> x]]_xs) \<in> qSwapped" using qSwap_qSwapped by fastforce
    hence "qInit MOD (qX #[[y \<and> x]]_xs) = qInit MOD (qX' #[[y \<and> x']]_xs)"
    using Abs.IH alpha by simp  
    hence "igSwap MOD xs y x (qInit MOD qX) = igSwap MOD xs y x' (qInit MOD qX')"
    using assms by(auto simp: iwlsFSwSTR_qSwapAll_igSwapAll_qInitAll)
    moreover have "igFresh MOD xs y (qInit MOD qX) \<and> igFresh MOD xs y (qInit MOD qX')"
    using y_fresh assms by(auto simp add: iwlsFSwSTR_qFreshAll_igFreshAll_qInitAll)
    ultimately have "igAbs MOD xs x (qInit MOD qX) = igAbs MOD xs x' (qInit MOD qX')"
    using y_not assms unfolding iwlsFSwSTR_def igAbsCongSSTR_def 
    apply clarify by (erule allE[of _ xs], erule allE[of _ x]) blast
    thus "qInitAbs MOD (qAbs xs x qX) = qInitAbs MOD qA'" unfolding qA' by simp
  qed
qed 

corollary iwlsFSwSTR_qInit_respectsP_alpha:
assumes "iwlsFSwSTR MOD" shows "(qInit MOD) respectsP alpha"
unfolding congruentP_def using assms iwlsFSwSTR_alphaAll_qInitAll by blast

corollary iwlsFSwSTR_qInitAbs_respectsP_alphaAbs:
assumes "iwlsFSwSTR MOD" shows "(qInitAbs MOD) respectsP alphaAbs"
unfolding congruentP_def using assms iwlsFSwSTR_alphaAll_qInitAll by blast

lemma iwlsFSbSwTR_alphaAll_qInitAll:
fixes qX::"('index,'bindex,'varSort,'var,'opSym)qTerm" and
      qA::"('index,'bindex,'varSort,'var,'opSym)qAbs"
assumes "iwlsFSbSwTR MOD"
shows
"(qGood qX \<longrightarrow> (\<forall> qX'. qX #= qX' \<longrightarrow> qInit MOD qX = qInit MOD qX')) \<and>
 (qGoodAbs qA \<longrightarrow> (\<forall> qA'. qA $= qA' \<longrightarrow> qInitAbs MOD qA = qInitAbs MOD qA'))"
proof(induction rule: qGood_qTerm_induct)
  case (Var xs x)
  then show ?case by(simp add: qVar_alpha_iff) 
next
  case (Op delta qinp qbinp)
  show ?case proof safe
    fix qX'
    assume "qOp delta qinp qbinp #= qX'"
    then obtain qinp' qbinp' where qX': "qX' = qOp delta qinp' qbinp'"
    and *: "sameDom qinp qinp' \<and> sameDom qbinp qbinp'"
    and **: "liftAll2 (\<lambda>qX qX'. qX #= qX') qinp qinp' \<and>
           liftAll2 (\<lambda>qA qA'. qA $= qA') qbinp qbinp'"
    using qOp_alpha_iff[of delta qinp qbinp qX'] by auto
    have "lift (qInit MOD) qinp = lift (qInit MOD) qinp'"
    using "*" "**" Op.IH(1) by (simp add: lift_def liftAll2_def liftAll_def
     sameDom_def fun_eq_iff split: option.splits) (metis option.exhaust)
    moreover
    have "lift (qInitAbs MOD) qbinp = lift (qInitAbs MOD) qbinp'"
    using "*" "**" Op.IH(2) by (simp add: lift_def liftAll2_def liftAll_def
     sameDom_def fun_eq_iff split: option.splits) (metis option.exhaust)
    ultimately
    show "qInit MOD (qOp delta qinp qbinp) = qInit MOD qX'"
    unfolding qX' by simp
  qed
next
  case (Abs xs x qX)
  show ?case proof safe
    fix qA'
    assume "qAbs xs x qX $= qA'"  
    then obtain x' y qX' where qA': "qA' = qAbs xs x' qX'"
    and y_not: "y \<notin> {x, x'}" and y_afresh: "qAFresh xs y qX"  "qAFresh xs y qX'"
    and alpha: "(qX #[[y \<and> x]]_xs) #= (qX' #[[y \<and> x']]_xs)"
    using qAbs_alphaAbs_iff[of xs x qX qA'] by auto
    hence y_fresh: "qFresh xs y qX \<and> qFresh xs y qX'" using qAFresh_imp_qFresh by auto
    have qX': "qGood qX'" using alpha Abs by(simp add: alpha_qSwap_preserves_qGood1)
    have "(qX, qX #[[y \<and> x]]_xs) \<in> qSwapped" using qSwap_qSwapped by fastforce
    hence "qInit MOD (qX #[[y \<and> x]]_xs) = qInit MOD (qX' #[[y \<and> x']]_xs)"
    using Abs.IH alpha by simp 
    moreover have "qInit MOD (qX #[[y \<and> x]]_xs) = igSubst MOD xs (igVar MOD xs y) x (qInit MOD qX)"
    using Abs y_afresh assms by(simp add: iwlsFSbSwTR_qSwapAll_igSubstAll_qInitAll)
    moreover have "qInit MOD (qX' #[[y \<and> x']]_xs) = igSubst MOD xs (igVar MOD xs y) x' (qInit MOD qX')"
    using qX' y_afresh assms by(simp add: iwlsFSbSwTR_qSwapAll_igSubstAll_qInitAll)
    ultimately
    have "igSubst MOD xs (igVar MOD xs y) x (qInit MOD qX) =
        igSubst MOD xs (igVar MOD xs y) x' (qInit MOD qX')"
    by simp
    moreover have "igFresh MOD xs y (qInit MOD qX) \<and> igFresh MOD xs y (qInit MOD qX')"
    using y_fresh assms by(auto simp add: iwlsFSbSwTR_qFreshAll_igFreshAll_qInitAll)
    moreover have "igAbsCongUSTR MOD"
    using assms unfolding iwlsFSbSwTR_def using igAbsRenSTR_imp_igAbsCongUSTR by auto
    ultimately have "igAbs MOD xs x (qInit MOD qX) = igAbs MOD xs x' (qInit MOD qX')"
    using y_not unfolding igAbsCongUSTR_def apply clarify
    by (erule allE[of _ xs], erule allE[of _ x]) blast
    thus "qInitAbs MOD (qAbs xs x qX) = qInitAbs MOD qA'" unfolding qA' by simp
  qed
qed

corollary iwlsFSbSwTR_qInit_respectsP_alphaGood:
assumes "iwlsFSbSwTR MOD"
shows "(qInit MOD) respectsP alphaGood"
unfolding congruentP_def alphaGood_def
using assms iwlsFSbSwTR_alphaAll_qInitAll by fastforce

corollary iwlsFSbSwTR_qInitAbs_respectsP_alphaAbsGood:
assumes "iwlsFSbSwTR MOD"
shows "(qInitAbs MOD) respectsP alphaAbsGood"
unfolding congruentP_def alphaAbsGood_def
using assms iwlsFSbSwTR_alphaAll_qInitAll by auto

subsubsection {* The initial morphism (iteration map) from the term model to any strong model *}

text {* This morphism has the same definition for fresh-swap and fresh-subst strong models *}

definition iterSTR where
"iterSTR MOD == univ (qInit MOD)"

definition iterAbsSTR where
"iterAbsSTR MOD == univ (qInitAbs MOD)"

lemma iwlsFSwSTR_iterSTR_ipresVar:
assumes "iwlsFSwSTR MOD"
shows "ipresVar (iterSTR MOD) MOD"
using assms by(simp add: ipresVar_def Var_def iterSTR_def iwlsFSwSTR_qInit_respectsP_alpha)

lemma iwlsFSbSwTR_iterSTR_ipresVar:
assumes "iwlsFSbSwTR MOD"
shows "ipresVar (iterSTR MOD) MOD"
using assms by (simp add: ipresVar_def Var_def iterSTR_def iwlsFSbSwTR_qInit_respectsP_alphaGood)
 
lemma iwlsFSwSTR_iterSTR_ipresAbs:
assumes "iwlsFSwSTR MOD"
shows "ipresAbs (iterSTR MOD) (iterAbsSTR MOD) MOD"
unfolding ipresAbs_def proof clarify
  fix xs x s X assume X: "wls s X"
  hence "qGood (pick X)" by(simp add: good_imp_qGood_pick)
  hence 1: "qGoodAbs (qAbs xs x (pick X))" by simp
  have "iterAbsSTR MOD (Abs xs x X) = univ (qInitAbs MOD) (asAbs (qAbs xs x (pick X)))"
  using X unfolding Abs_def iterAbsSTR_def by simp
  also have "\<dots> = qInitAbs MOD (qAbs xs x (pick X))"
  using assms 1 by(simp add: iwlsFSwSTR_qInitAbs_respectsP_alphaAbs)
  also have "\<dots> = igAbs MOD xs x (qInit MOD (pick X))" by simp
  also have "\<dots> = igAbs MOD xs x (iterSTR MOD X)" unfolding iterSTR_def
  unfolding univ_def pick_def ..
  finally show "iterAbsSTR MOD (Abs xs x X) = igAbs MOD xs x (iterSTR MOD X)" .
qed

lemma iwlsFSbSwTR_iterSTR_ipresAbs:
assumes "iwlsFSbSwTR MOD"
shows "ipresAbs (iterSTR MOD) (iterAbsSTR MOD) MOD"
unfolding ipresAbs_def proof clarify
  fix xs x s X assume X: "wls s X"
  hence "qGood (pick X)" by(simp add: good_imp_qGood_pick)
  hence 1: "qGoodAbs (qAbs xs x (pick X))" by simp
  have "iterAbsSTR MOD (Abs xs x X) = univ (qInitAbs MOD) (asAbs (qAbs xs x (pick X)))"
  using X unfolding Abs_def iterAbsSTR_def by simp
  also have "\<dots> = qInitAbs MOD (qAbs xs x (pick X))"
  using assms 1 by(simp add: iwlsFSbSwTR_qInitAbs_respectsP_alphaAbsGood)
  also have "\<dots> = igAbs MOD xs x (qInit MOD (pick X))" by simp
  also have "\<dots> = igAbs MOD xs x (iterSTR MOD X)" unfolding iterSTR_def univ_def
  unfolding univ_def pick_def ..
  finally show "iterAbsSTR MOD (Abs xs x X) = igAbs MOD xs x (iterSTR MOD X)" .
qed

lemma iwlsFSwSTR_iterSTR_ipresOp:
assumes "iwlsFSwSTR MOD"
shows "ipresOp (iterSTR MOD) (iterAbsSTR MOD) MOD"
unfolding ipresOp_def proof clarify
  fix delta inp binp
  assume inp: "wlsInp delta inp"  "wlsBinp delta binp"
  hence "qGoodInp (pickInp inp) \<and> qGoodBinp (pickBinp binp)"
  by(simp add: goodInp_imp_qGoodInp_pickInp goodBinp_imp_qGoodBinp_pickBinp)
  hence 1: "qGood (qOp delta (pickInp inp) (pickBinp binp))" by simp
  have "iterSTR MOD (Op delta inp binp) =
         univ (qInit MOD) (asTerm (qOp delta (pickInp inp) (pickBinp binp)))"
  using inp unfolding Op_def iterSTR_def by simp
  moreover have "\<dots> = qInit MOD (qOp delta (pickInp inp) (pickBinp binp))"
  using assms 1 by(simp add: iwlsFSwSTR_qInit_respectsP_alpha)
  moreover have "\<dots> = igOp MOD delta (lift (qInit MOD) (pickInp inp))
                               (lift (qInitAbs MOD) (pickBinp binp))" by auto
  moreover
  have "lift (qInit MOD) (pickInp inp) = lift (iterSTR MOD) inp \<and>
        lift (qInitAbs MOD) (pickBinp binp) = lift (iterAbsSTR MOD) binp"
  unfolding pickInp_def pickBinp_def iterSTR_def iterAbsSTR_def
            lift_comp univ_def[abs_def] comp_def
  unfolding univ_def pick_def by simp
  ultimately
  show "iterSTR MOD (Op delta inp binp) =
        igOp MOD delta (lift (iterSTR MOD) inp) (lift (iterAbsSTR MOD) binp)" by simp
qed

lemma iwlsFSbSwTR_iterSTR_ipresOp:
assumes "iwlsFSbSwTR MOD"
shows "ipresOp (iterSTR MOD) (iterAbsSTR MOD) MOD"
unfolding ipresOp_def proof clarify
  fix delta inp binp
  assume inp: "wlsInp delta inp"  "wlsBinp delta binp"
  hence "qGoodInp (pickInp inp) \<and> qGoodBinp (pickBinp binp)"
  by(simp add: goodInp_imp_qGoodInp_pickInp goodBinp_imp_qGoodBinp_pickBinp)
  hence 1: "qGood (qOp delta (pickInp inp) (pickBinp binp))" by simp
  have "iterSTR MOD (Op delta inp binp) =
         univ (qInit MOD) (asTerm (qOp delta (pickInp inp) (pickBinp binp)))"
  using inp unfolding Op_def iterSTR_def by simp
  moreover have "\<dots> = qInit MOD (qOp delta (pickInp inp) (pickBinp binp))"
  using assms 1 by(simp add: iwlsFSbSwTR_qInit_respectsP_alphaGood)
  moreover have "\<dots> = igOp MOD delta (lift (qInit MOD) (pickInp inp))
                                   (lift (qInitAbs MOD) (pickBinp binp))" by simp
  moreover have "lift (qInit MOD) (pickInp inp) = lift (iterSTR MOD) inp \<and>
                 lift (qInitAbs MOD) (pickBinp binp) = lift (iterAbsSTR MOD) binp"
  unfolding pickInp_def pickBinp_def iterSTR_def iterAbsSTR_def
            lift_comp univ_def[abs_def] comp_def
  unfolding univ_def pick_def by simp
  ultimately
  show "iterSTR MOD (Op delta inp binp) =
        igOp MOD delta (lift (iterSTR MOD) inp) (lift (iterAbsSTR MOD) binp)" by simp
qed

lemma iwlsFSwSTR_iterSTR_ipresCons:
assumes "iwlsFSwSTR MOD"
shows "ipresCons (iterSTR MOD) (iterAbsSTR MOD) MOD"
unfolding ipresCons_def using assms
iwlsFSwSTR_iterSTR_ipresVar
iwlsFSwSTR_iterSTR_ipresAbs
iwlsFSwSTR_iterSTR_ipresOp by auto

lemma iwlsFSbSwTR_iterSTR_ipresCons:
assumes "iwlsFSbSwTR MOD"
shows "ipresCons (iterSTR MOD) (iterAbsSTR MOD) MOD"
unfolding ipresCons_def using assms
iwlsFSbSwTR_iterSTR_ipresVar
iwlsFSbSwTR_iterSTR_ipresAbs
iwlsFSbSwTR_iterSTR_ipresOp by auto

lemma iwlsFSwSTR_iterSTR_termFSwImorph:
assumes "iwlsFSwSTR MOD"
shows "termFSwImorph (iterSTR MOD) (iterAbsSTR MOD) MOD"
using assms by (auto simp: iwlsFSwSTR_termFSwImorph_iff intro: iwlsFSwSTR_iterSTR_ipresCons)

corollary iterSTR_termFSwImorph_errMOD:
assumes "iwlsFSw MOD"
shows
"termFSwImorph (iterSTR (errMOD MOD))
             (iterAbsSTR (errMOD MOD))
             (errMOD MOD)"
using assms errMOD_iwlsFSwSTR iwlsFSwSTR_iterSTR_termFSwImorph by auto

lemma iwlsFSbSwTR_iterSTR_termFSbImorph:
assumes "iwlsFSbSwTR MOD"
shows "termFSbImorph (iterSTR MOD) (iterAbsSTR MOD) MOD"
using assms by (auto simp: iwlsFSbSwTR_termFSbImorph_iff intro: iwlsFSbSwTR_iterSTR_ipresCons)

corollary iterSTR_termFSbImorph_errMOD:
assumes "iwlsFSb MOD"
shows
"termFSbImorph (iterSTR (errMOD MOD))
             (iterAbsSTR (errMOD MOD))
             (errMOD MOD)"
using assms errMOD_iwlsFSbSwTR iwlsFSbSwTR_iterSTR_termFSbImorph by auto

(* We are done with the use of quesi-term ``implementations". *)

declare qItem_simps[simp del]
declare qItem_versus_item_simps[simp del]
declare good_item_simps[simp del]

subsubsection {* The initial morhpism (iteration map) from the term model to any model *}

text {* Again, this morphism has the same definition for fresh-swap and fresh-subst models,
as well as (of course) for fresh-swap-subst and fresh-subst-swap models. (Remember that
there is no such thing as ``fresh-subst-swap" morhpism -- we use the notion of
``fresh-swap-subst" morphism.) *}

text {* Existence of the morphism: *}

definition iter where
"iter MOD == check o (iterSTR (errMOD MOD))"

definition iterAbs where
"iterAbs MOD == check o (iterAbsSTR (errMOD MOD))"

theorem iwlsFSw_iterAll_termFSwImorph:
"iwlsFSw MOD \<Longrightarrow> termFSwImorph (iter MOD) (iterAbs MOD) MOD"
using iterSTR_termFSwImorph_errMOD check_FSwImorph
by (auto simp: iter_def iterAbs_def intro: comp_termFSwImorph)
 
theorem iwlsFSb_iterAll_termFSbImorph:
"iwlsFSb MOD \<Longrightarrow> termFSbImorph (iter MOD) (iterAbs MOD) MOD"
using iterSTR_termFSbImorph_errMOD check_FSbImorph
by (auto simp: iter_def iterAbs_def intro: comp_termFSbImorph)
 
theorem iwlsFSwSb_iterAll_termFSwSbImorph:
"iwlsFSwSb MOD \<Longrightarrow> termFSwSbImorph (iter MOD) (iterAbs MOD) MOD"
using iwlsFSw_iterAll_termFSwImorph
by (auto simp: iwlsFSwSb_termFSwSbImorph_iff iwlsFSwSb_def termFSwImorph_def)

theorem iwlsFSbSw_iterAll_termFSwSbImorph:
"iwlsFSbSw MOD \<Longrightarrow> termFSwSbImorph (iter MOD) (iterAbs MOD) MOD"
using iwlsFSb_iterAll_termFSbImorph 
by (auto simp: iwlsFSbSw_termFSwSbImorph_iff iwlsFSbSw_def  termFSbImorph_def)


text {* Uniqueness of the morphism *}

text {* In fact, already a presumptive construct-preserving map has to be unique:  *}

lemma ipresCons_unique:
assumes "ipresCons f fA MOD" and "ipresCons ig igA MOD"
shows
"(wls s X \<longrightarrow> f X = ig X) \<and>
 (wlsAbs (us,s') A \<longrightarrow> fA A = igA A)"
proof(induction rule: wls_rawInduct)
  case (Var xs x)
  then show ?case using assms unfolding ipresCons_def ipresVar_def by simp
next
  case (Op delta inp binp) 
  hence "lift f inp = lift ig inp \<and> lift fA binp = lift igA binp" 
  using assms  
  apply(simp add: lift_def liftAll2_def sameDom_def fun_eq_iff wlsInp_iff wlsBinp_iff split: option.splits) 
  using not_None_eq by (metis surj_pair)
  thus "f (Op delta inp binp) = ig (Op delta inp binp)"
  using assms unfolding ipresCons_def ipresOp_def by (simp add: Op.IH)
next
  case (Abs s xs x X)
  then show ?case using assms unfolding ipresCons_def ipresAbs_def apply clarify
  by (erule allE[of _ xs], erule allE[of _ x]) fastforce
qed 

theorem iwlsFSw_iterAll_unique_ipresCons:
assumes "iwlsFSw MOD" and "ipresCons h hA MOD"
shows
"(wls s X \<longrightarrow> h X = iter MOD X) \<and>
 (wlsAbs (us,s') A \<longrightarrow> hA A = iterAbs MOD A)"
using assms iwlsFSw_iterAll_termFSwImorph 
by (auto simp: termFSwImorph_def intro!: ipresCons_unique) 

theorem iwlsFSb_iterAll_unique_ipresCons:
assumes "iwlsFSb MOD" and "ipresCons h hA MOD"
shows
"(wls s X \<longrightarrow> h X = iter MOD X) \<and>
 (wlsAbs (us,s') A \<longrightarrow> hA A = iterAbs MOD A)"
using assms iwlsFSb_iterAll_termFSbImorph
by (auto simp: termFSbImorph_def intro!: ipresCons_unique)  

theorem iwlsFSwSb_iterAll_unique_ipresCons:
assumes "iwlsFSwSb MOD" and "ipresCons h hA MOD"
shows
"(wls s X \<longrightarrow> h X = iter MOD X) \<and>
 (wlsAbs (us,s') A \<longrightarrow> hA A = iterAbs MOD A)"
using assms unfolding iwlsFSwSb_def
using iwlsFSw_iterAll_unique_ipresCons by blast

theorem iwlsFSbSw_iterAll_unique_ipresCons:
assumes *: "iwlsFSbSw MOD" and **: "ipresCons h hA MOD"
shows
"(wls s X \<longrightarrow> h X = iter MOD X) \<and>
 (wlsAbs (us,s') A \<longrightarrow> hA A = iterAbs MOD A)"
using assms unfolding iwlsFSbSw_def
using iwlsFSb_iterAll_unique_ipresCons by blast

(**************************************)
lemmas iteration_simps =
input_igSwap_igSubst_None
termMOD_simps
error_model_simps

declare iteration_simps [simp del]

end (* context FixSyn *)
(************************************************)

end
