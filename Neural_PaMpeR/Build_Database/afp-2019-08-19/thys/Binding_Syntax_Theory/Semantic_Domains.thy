section {* Interpretation of syntax in semantic domains *}

theory Semantic_Domains imports Iteration  
begin

text {* In this section, we employ our iteration principle
to obtain interpretation of syntax in semantic domains via valuations.
A bonus from our Horn-theoretic approach is the built-in
commutation of the interpretation with substitution versus valuation update,
a property known in the literature as the ``substitution lemma". *}

subsection {* Semantic domains and valuations *}

text{*
Semantic domains are for binding signatures
what algebras are for standard algebraic signatures. They fix carrier sets for each sort,
and interpret each operation symbol as an operation on these sets
%
\footnote{
To match the Isabelle type system, we model (as usual) the family of carrier sets as a
``well-sortedness" predicate taking sorts and semantic items from a given
(initially unsorted) universe into booleans,
and require the operations, considered on the unsorted universe, to preserve well-sortedness.
}
%
of corresponding arity, where:
%
\\- non-binding arguments
are treated as usual (first-order) arguments;
%
\\- binding arguments are treated as second-order (functional) arguments.
%
\footnote{
In other words, syntactic bindings are captured semantically as functional bindings.}
%

In particular, for the untyped and simply-typed $\lambda$-calculi,
the semantic domains become the well-known (set-theoretic) Henkin models.

We use terminology and notation according to our general methodology employed so far:
the inhabitants of semantic domains are referred to as ``semantic items";
we prefix the reference to semantic items with an ``s": sX, sA, etc.
This convention also applies to the operations on semantic domains: ``sAbs", ``sOp", etc.

We eventually show that the function spaces consisting of maps
from valuations to semantic items form models;
in other words,
these maps can be viewed as ``generalized items"; we use for them
term-like notations ``X", ``A", etc.
(as we did in the theory that dealt with iteration).
*}

subsubsection {* Definitions: *}

datatype ('varSort,'sTerm)sAbs = sAbs 'varSort "'sTerm \<Rightarrow> 'sTerm"

record ('index,'bindex,'varSort,'sort,'opSym,'sTerm)semDom =
  sWls :: "'sort \<Rightarrow> 'sTerm \<Rightarrow> bool"
  sDummy :: "'sort \<Rightarrow> 'sTerm"
  sOp :: "'opSym \<Rightarrow> ('index,'sTerm)input \<Rightarrow> ('bindex,('varSort,'sTerm)sAbs)input \<Rightarrow>'sTerm"

text{* The type of valuations: *}

type_synonym ('varSort,'var,'sTerm)val = "'varSort \<Rightarrow> 'var \<Rightarrow> 'sTerm"

(* *************************************************** *)
context FixSyn
begin

(* A new type variable, corresponding to 'sTerm, is introduced in the context by 
the following definitions and facts. *)

fun sWlsAbs where
"sWlsAbs SEM (xs,s) (sAbs xs' sF) =
 (isInBar (xs,s) \<and> xs = xs' \<and>
  (\<forall> sX. if sWls SEM (asSort xs) sX
           then sWls SEM s (sF sX)
           else sF sX = sDummy SEM s))"

definition sWlsInp where
"sWlsInp SEM delta sinp \<equiv>
 wlsOpS delta \<and> sameDom (arOf delta) sinp \<and> liftAll2 (sWls SEM) (arOf delta) sinp"

definition sWlsBinp where
"sWlsBinp SEM delta sbinp \<equiv>
 wlsOpS delta \<and> sameDom (barOf delta) sbinp \<and> liftAll2 (sWlsAbs SEM) (barOf delta) sbinp"

definition sWlsNE where
"sWlsNE SEM \<equiv>
 \<forall> s. \<exists> sX. sWls SEM s sX"

definition sWlsDisj where
"sWlsDisj SEM \<equiv>
 \<forall> s s' sX. sWls SEM s sX \<and> sWls SEM s' sX \<longrightarrow> s = s'"

definition sOpPrSWls where
"sOpPrSWls SEM \<equiv>
 \<forall> delta sinp sbinp.
   sWlsInp SEM delta sinp \<and> sWlsBinp SEM delta sbinp
   \<longrightarrow> sWls SEM (stOf delta) (sOp SEM delta sinp sbinp)"

text{* The notion of a ``well-sorted" (better read as ``well-structured")
semantic domain: 
%
\footnote{
As usual in Isabelle, we first define the ``raw" version,
and then ``fix" it with a well-structuredness predicate.
}
%
*}
definition wlsSEM where
"wlsSEM SEM \<equiv>
 sWlsNE SEM \<and> sWlsDisj SEM \<and> sOpPrSWls SEM"

text{* The preperties described  in the next 4 definitions turn out to be
consequences of the well-structuredness of the semantic domain: *}

definition sWlsAbsNE where
"sWlsAbsNE SEM \<equiv>
 \<forall> us s. isInBar (us,s) \<longrightarrow> (\<exists> sA. sWlsAbs SEM (us,s) sA)"

definition sWlsAbsDisj where
"sWlsAbsDisj SEM \<equiv>
 \<forall> us s us' s' sA.
   isInBar (us,s) \<and> isInBar (us',s') \<and> sWlsAbs SEM (us,s) sA \<and> sWlsAbs SEM (us',s') sA
   \<longrightarrow> us = us' \<and> s = s'"

text{* The notion of two valuations being equal everywhere but on a given variable: *}

definition eqBut where
"eqBut val val' xs x \<equiv>
 \<forall> ys y. (ys = xs \<and> y = x) \<or> val ys y = val' ys y"

definition updVal ::
"('varSort,'var,'sTerm)val \<Rightarrow>
 'var \<Rightarrow> 'sTerm \<Rightarrow> 'varSort \<Rightarrow>
 ('varSort,'var,'sTerm)val" ("_ '(_ := _')'__" 200)
where
"(val (x := sX)_xs) \<equiv>
 \<lambda> ys y. (if ys = xs \<and> y = x then sX else val ys y)"

definition swapVal ::
"'varSort \<Rightarrow> 'var \<Rightarrow> 'var \<Rightarrow> ('varSort,'var,'sTerm)val \<Rightarrow>
 ('varSort,'var,'sTerm)val"
where
"swapVal zs z1 z2 val \<equiv> \<lambda>xs x. val xs (x @xs[z1 \<and> z2]_zs) "

abbreviation swapVal_abbrev ("_ ^[_ \<and> _]'__" 200) where
"val ^[z1 \<and> z2]_zs \<equiv> swapVal zs z1 z2 val"

definition sWlsVal where
"sWlsVal SEM val \<equiv>
 \<forall> ys y. sWls SEM (asSort ys) (val ys y)"

(* The last argument is a dummy argument identifying the type 'var --
it may be regarded as a type argument:  *)

definition sWlsValNE ::
"('index,'bindex,'varSort,'sort,'opSym,'sTerm)semDom \<Rightarrow> 'var \<Rightarrow> bool"
where
"sWlsValNE SEM x \<equiv> \<exists> (val :: ('varSort,'var,'sTerm)val). sWlsVal SEM val"

subsubsection {* Basic facts *}

lemma sWlsNE_imp_sWlsAbsNE:
assumes "sWlsNE SEM"
shows "sWlsAbsNE SEM"
unfolding sWlsAbsNE_def proof clarify
  fix xs s
  obtain sY where "sWls SEM s sY"
  using assms unfolding sWlsNE_def by auto
  moreover assume "isInBar (xs,s)"
  ultimately
  have "sWlsAbs SEM (xs,s) (sAbs xs (\<lambda>sX. if sWls SEM (asSort xs) sX
                                           then sY
                                           else sDummy SEM s))" by simp
  thus "\<exists>sA. sWlsAbs SEM (xs,s) sA" by blast
qed

lemma sWlsDisj_imp_sWlsAbsDisj:
"sWlsDisj SEM \<Longrightarrow> sWlsNE SEM \<Longrightarrow> sWlsAbsDisj SEM"
by (simp add: sWlsAbsDisj_def sWlsNE_def sWlsDisj_def) 
   (smt prod.inject sAbs.inject sWlsAbs.elims(2))

lemma sWlsNE_imp_sWlsValNE:
"sWlsNE SEM \<Longrightarrow> sWlsValNE SEM x"  
by (auto simp: sWlsNE_def  sWlsValNE_def sWlsVal_def 
 intro!: exI someI_ex[of "(\<lambda> sY. sWls SEM (asSort _) sY)"])
 
theorem updVal_simp[simp]:
"(val (x := sX)_xs) ys y = (if ys = xs \<and> y = x then sX else val ys y)"
unfolding updVal_def by simp

theorem updVal_over[simp]:
"((val (x := sX)_xs) (x := sX')_xs) = (val (x := sX')_xs)"
unfolding updVal_def by fastforce

theorem updVal_commute:
assumes "xs \<noteq> ys \<or> x \<noteq> y"
shows "((val (x := sX)_xs) (y := sY)_ys) = ((val (y := sY)_ys) (x := sX)_xs)"
using assms unfolding updVal_def by fastforce

theorem updVal_preserves_sWls[simp]:
assumes "sWls SEM (asSort xs) sX" and "sWlsVal SEM val"
shows "sWlsVal SEM (val (x := sX)_xs)"
using assms unfolding sWlsVal_def by auto

lemmas updVal_simps = updVal_simp updVal_over updVal_preserves_sWls

theorem swapVal_ident[simp]: "(val ^[x \<and> x]_xs) = val"
unfolding swapVal_def by auto

theorem swapVal_compose:
"((val ^[x \<and> y]_zs) ^[x' \<and> y']_zs') =
 ((val ^[x' @zs'[x \<and> y]_zs \<and> y' @zs'[x \<and> y]_zs]_zs') ^[x \<and> y]_zs)"
unfolding swapVal_def by (metis sw_compose) 
 
theorem swapVal_commute:
"zs \<noteq> zs' \<or> {x,y} \<inter> {x',y'} = {} \<Longrightarrow>
 ((val ^[x \<and> y]_zs) ^[x' \<and> y']_zs') = ((val ^[x' \<and> y']_zs') ^[x \<and> y]_zs)"
using swapVal_compose[of zs' x' y' zs x y val] by(simp add: sw_def)

lemma swapVal_involutive[simp]: "((val ^[x \<and> y]_zs) ^[x \<and> y]_zs) = val"
unfolding swapVal_def by auto

lemma swapVal_sym: "(val ^[x \<and> y]_zs) = (val ^[y \<and> x]_zs)"
unfolding swapVal_def by(auto simp add: sw_sym)

lemma swapVal_preserves_sWls1:
assumes "sWlsVal SEM val"
shows "sWlsVal SEM (val ^[z1 \<and> z2]_zs)"
using assms unfolding sWlsVal_def swapVal_def by simp

theorem swapVal_preserves_sWls[simp]:
"sWlsVal SEM (val ^[z1 \<and> z2]_zs) = sWlsVal SEM val"
using swapVal_preserves_sWls1[of _ _ zs z1 z2] by fastforce
 
lemmas swapVal_simps = swapVal_ident swapVal_involutive swapVal_preserves_sWls

lemma updVal_swapVal:
"((val (x := sX)_xs) ^[y1 \<and> y2]_ys) =
 ((val ^[y1 \<and> y2]_ys) ((x @xs[y1 \<and> y2]_ys) := sX)_xs)"
unfolding swapVal_def by fastforce

lemma updVal_preserves_eqBut:
assumes "eqBut val val' ys y"
shows "eqBut (val (x := sX)_xs) (val' (x := sX)_xs) ys y"
using assms unfolding eqBut_def updVal_def by auto

lemma updVal_eqBut_eq:
assumes "eqBut val val' ys y"
shows "(val (y := sY)_ys) = (val' (y := sY)_ys)"
using assms unfolding eqBut_def by fastforce 
   
lemma swapVal_preserves_eqBut:
assumes "eqBut val val' xs x"
shows "eqBut (val ^[z1 \<and> z2]_zs) (val' ^[z1 \<and> z2]_zs) xs (x @xs[z1 \<and> z2]_zs)"
using assms unfolding eqBut_def swapVal_def by force

subsection {* Interpretation maps *}

text{* An interpretation map, of syntax in a semantic domain,
is the usual one w.r.t. valuations.  Here we state its compostionality conditions
(including the ``substitution lemma"), and later we prove the existence of a map
satisfying these conditions.  *}

subsubsection {* Definitions *}

text {* Below, prefix ``pr" means ``preserves". *}

definition prWls where
"prWls g SEM \<equiv> \<forall> s X val.
    wls s X \<and> sWlsVal SEM val
    \<longrightarrow> sWls SEM s (g X val)"

definition prWlsAbs where
"prWlsAbs gA SEM \<equiv> \<forall> us s A val.
    wlsAbs (us,s) A \<and> sWlsVal SEM val
    \<longrightarrow> sWlsAbs SEM (us,s) (gA A val)"

definition prWlsAll where
"prWlsAll g gA SEM \<equiv> prWls g SEM \<and> prWlsAbs gA SEM"

definition prVar where
"prVar g SEM \<equiv> \<forall> xs x val.
    sWlsVal SEM val \<longrightarrow> g (Var xs x) val = val xs x"

definition prAbs where
"prAbs g gA SEM \<equiv> \<forall> xs s x X val.
    isInBar (xs,s) \<and> wls s X \<and> sWlsVal SEM val
    \<longrightarrow>
    gA (Abs xs x X) val =
    sAbs xs (\<lambda>sX. if sWls SEM (asSort xs) sX then g X (val (x := sX)_xs)
                                             else sDummy SEM s)"

definition prOp where
"prOp g gA SEM \<equiv> \<forall> delta inp binp val.
    wlsInp delta inp \<and> wlsBinp delta binp \<and> sWlsVal SEM val
    \<longrightarrow>
    g (Op delta inp binp) val =
    sOp SEM delta (lift (\<lambda>X. g X val) inp)
                  (lift (\<lambda>A. gA A val) binp)"

definition prCons where
"prCons g gA SEM \<equiv> prVar g SEM \<and> prAbs g gA SEM \<and> prOp g gA SEM"

definition prFresh where
"prFresh g SEM \<equiv> \<forall> ys y s X val val'.
   wls s X \<and> fresh ys y X \<and>
   sWlsVal SEM val \<and> sWlsVal SEM val' \<and> eqBut val val' ys y
   \<longrightarrow> g X val = g X val'"

definition prFreshAbs where
"prFreshAbs gA SEM \<equiv> \<forall> ys y us s A val val'.
   wlsAbs (us,s) A \<and> freshAbs ys y A \<and>
   sWlsVal SEM val \<and> sWlsVal SEM val' \<and> eqBut val val' ys y
   \<longrightarrow> gA A val = gA A val'"

definition prFreshAll where
"prFreshAll g gA SEM \<equiv> prFresh g SEM \<and> prFreshAbs gA SEM"

definition prSwap where
"prSwap g SEM \<equiv> \<forall> zs z1 z2 s X val.
   wls s X \<and> sWlsVal SEM val
   \<longrightarrow>
   g (X #[z1 \<and> z2]_zs) val =
   g X (val ^[z1 \<and> z2]_zs)"

definition prSwapAbs where
"prSwapAbs gA SEM \<equiv> \<forall> zs z1 z2 us s A val.
   wlsAbs (us,s) A \<and> sWlsVal SEM val
   \<longrightarrow>
   gA (A $[z1 \<and> z2]_zs) val =
   gA A (val ^[z1 \<and> z2]_zs)"

definition prSwapAll where
"prSwapAll g gA SEM \<equiv> prSwap g SEM \<and> prSwapAbs gA SEM"

definition prSubst where
"prSubst g SEM \<equiv> \<forall> ys Y y s X val.
    wls (asSort ys) Y \<and> wls s X
    \<and> sWlsVal SEM val
    \<longrightarrow>
    g (X #[Y / y]_ys) val =
    g X (val (y := g Y val)_ys)"

definition prSubstAbs where
"prSubstAbs g gA SEM \<equiv> \<forall> ys Y y us s A val.
    wls (asSort ys) Y \<and> wlsAbs (us,s) A
    \<and> sWlsVal SEM val
    \<longrightarrow>
    gA (A $[Y / y]_ys) val =
    gA A (val (y := g Y val)_ys)"

definition prSubstAll where
"prSubstAll g gA SEM \<equiv> prSubst g SEM \<and> prSubstAbs g gA SEM"

definition compInt where
"compInt g gA SEM \<equiv> prWlsAll g gA SEM \<and> prCons g gA SEM \<and>
 prFreshAll g gA SEM \<and> prSwapAll g gA SEM \<and> prSubstAll g gA SEM"

subsubsection {* Extension of domain preservation to inputs *}

lemma prWls_wlsInp:
assumes "wlsInp delta inp" and "prWls g SEM" and "sWlsVal SEM val"
shows "sWlsInp SEM delta (lift (\<lambda> X. g X val) inp)"
using assms unfolding sWlsInp_def wlsInp_iff liftAll2_def lift_def prWls_def  
by (auto simp add: option.case_eq_if sameDom_def)

lemma prWlsAbs_wlsBinp:
assumes "wlsBinp delta binp" and "prWlsAbs gA SEM" and "sWlsVal SEM val"
shows "sWlsBinp SEM delta (lift (\<lambda> A. gA A val) binp)"
using assms unfolding sWlsBinp_def wlsBinp_iff liftAll2_def lift_def prWlsAbs_def
by (auto simp add: option.case_eq_if sameDom_def)

end (* context FixSyn *)
(***************************************)

subsection {* The iterative model associated to a semantic domain *}

text{*
``asIMOD SEM" stands for ``SEM (regarded) as a model".
%
\footnote{
We use the word ``model" as introduced in the theory ``Models-and-Recursion".
}
%
The associated model is built essentially as follows:
%
\\- Its carrier sets consist of functions from valuations to semantic items.
%
\\- The construct operations (i.e., those corresponding to the syntactic constructs
indicated in the given binding signature) are lifted componentwise from those of the semantic domain
``SEM" (also taking into account the higher-order nature of of the semantic counterparts of abstractions).
%
\\- For a map from valuations to items (terms or abstractions), freshness of a variable ``x"
is defined as being oblivious what the argument valuation returns for ``x".
%
\\- Swapping is defined componentwise, by two iterations of the notion of swapping the
returned value of a function.
%
\\- Substitution of a semantic term ``Y" for a variable ``y" is a semantic term ``X"
is defined to map each valuation ``val" to the application of ``X" to
[``val" updated at ``y" with whatever ``Y" returns for ``val"].

Note that:
%
\\- The construct operations definitions are determined by the desired clauses of the standard
notion of interpreting syntax in a semantic domains.
%
\\- Substitution and freshness are defined having in mind the (again standard) facts of
the interpretation commuting with substitution versus valuation update and the interpretation
being oblivious to the valuation of fresh variables.
*}

subsubsection {* Definition and basic facts  *}

text{*
The next two types of ``generalized items" are used to build models from semantic domains:
%
\footnote{
Recall that ``generalized items" inhabit models.
}
%
*}

type_synonym ('varSort,'var,'sTerm) gTerm = "('varSort,'var,'sTerm)val \<Rightarrow> 'sTerm"

type_synonym ('varSort,'var,'sTerm) gAbs = "('varSort,'var,'sTerm)val \<Rightarrow> ('varSort,'sTerm)sAbs"

(* *************************************************** *)
context FixSyn
begin

definition asIMOD ::
"('index,'bindex,'varSort,'sort,'opSym,'sTerm)semDom \<Rightarrow>
 ('index,'bindex,'varSort,'sort,'opSym,'var,
  ('varSort,'var,'sTerm)gTerm,
  ('varSort,'var,'sTerm)gAbs)model"
where
"asIMOD SEM \<equiv>
 \<lparr>igWls = \<lambda>s X. \<forall> val. (sWlsVal SEM val \<or> X val = undefined) \<and>
                      (sWlsVal SEM val \<longrightarrow> sWls SEM s (X val)),
  igWlsAbs = \<lambda>(xs,s) A. \<forall> val. (sWlsVal SEM val \<or> A val = undefined) \<and>
                              (sWlsVal SEM val \<longrightarrow> sWlsAbs SEM (xs,s) (A val)),
  igVar = \<lambda>ys y. \<lambda>val. if sWlsVal SEM val then val ys y else undefined,
  igAbs =
  \<lambda>xs x X. \<lambda>val. if sWlsVal SEM val
                   then sAbs xs (\<lambda>sX. if sWls SEM (asSort xs) sX
                                         then X (val (x := sX)_xs)
                                         else sDummy SEM (SOME s. sWls SEM s (X val)))
                   else undefined,
  igOp = \<lambda>delta inp binp. \<lambda>val.
          if sWlsVal SEM val then sOp SEM delta (lift (\<lambda>X. X val) inp)
                                                (lift (\<lambda>A. A val) binp)
                             else undefined,
  igFresh =
  \<lambda>ys y X. \<forall> val val'. sWlsVal SEM val \<and> sWlsVal SEM val' \<and> eqBut val val' ys y
                       \<longrightarrow> X val = X val',
  igFreshAbs =
  \<lambda>ys y A. \<forall> val val'. sWlsVal SEM val \<and> sWlsVal SEM val' \<and> eqBut val val' ys y
                       \<longrightarrow> A val = A val',
  igSwap = \<lambda>zs z1 z2 X. \<lambda>val. if sWlsVal SEM val then X (val ^[z1 \<and> z2]_zs)
                                                else undefined,
  igSwapAbs = \<lambda>zs z1 z2 A. \<lambda>val. if sWlsVal SEM val then A (val ^[z1 \<and> z2]_zs)
                                                   else undefined,
  igSubst = \<lambda>ys Y y X. \<lambda>val. if sWlsVal SEM val then X (val (y := Y val)_ys)
                                                else undefined,
  igSubstAbs = \<lambda>ys Y y A. \<lambda>val. if sWlsVal SEM val then A (val (y := Y val)_ys)
                                                   else undefined\<rparr>"

text{* Next we state, as usual, the direct definitions of the operators and relations
of associated model, freeing ourselves from
having to go through the ``asIMOD" definition each time we reason about them.  *}

lemma asIMOD_igWls:
"igWls (asIMOD SEM) s X \<longleftrightarrow> 
 (\<forall> val. (sWlsVal SEM val \<or> X val = undefined) \<and>
         (sWlsVal SEM val \<longrightarrow> sWls SEM s (X val)))"
unfolding asIMOD_def by simp

lemma asIMOD_igWlsAbs:
"igWlsAbs (asIMOD SEM) (us,s) A \<longleftrightarrow> 
 (\<forall> val. (sWlsVal SEM val \<or> A val = undefined) \<and>
         (sWlsVal SEM val \<longrightarrow> sWlsAbs SEM (us,s) (A val)))"
unfolding asIMOD_def by simp

lemma asIMOD_igOp:
"igOp (asIMOD SEM) delta inp binp =
(\<lambda>val. if sWlsVal SEM val then sOp SEM delta (lift (\<lambda>X. X val) inp)
                                             (lift (\<lambda>A. A val) binp)
                          else undefined)"
unfolding asIMOD_def by simp

lemma asIMOD_igVar:
"igVar (asIMOD SEM) ys y = (\<lambda>val. if sWlsVal SEM val then val ys y else undefined)"
unfolding asIMOD_def by simp

lemma asIMOD_igAbs:
"igAbs (asIMOD SEM) xs x X =
(\<lambda>val. if sWlsVal SEM val then sAbs xs (\<lambda>sX. if sWls SEM (asSort xs) sX
                                                then X (val (x := sX)_xs)
                                                else sDummy SEM (SOME s. sWls SEM s (X val)))
                          else undefined)"
unfolding asIMOD_def by simp

lemma asIMOD_igAbs2:
fixes SEM :: "('index,'bindex,'varSort,'sort,'opSym,'sTerm)semDom"
assumes *: "sWlsDisj SEM" and **: "igWls (asIMOD SEM) s X"
shows "igAbs (asIMOD SEM) xs x X =
(\<lambda>val. if sWlsVal SEM val then sAbs xs (\<lambda>sX. if sWls SEM (asSort xs) sX
                                                then X (val (x := sX)_xs)
                                                else sDummy SEM s)
                          else undefined)"
proof-
  {fix val :: "('varSort,'var,'sTerm)val" assume val: "sWlsVal SEM val"
   hence Xval: "sWls SEM s (X val)"
   using ** unfolding asIMOD_igWls by simp
   hence "(SOME s. sWls SEM s (X val)) = s"
   using Xval * unfolding sWlsDisj_def by auto
  }
  thus ?thesis unfolding asIMOD_igAbs by fastforce
qed

lemma asIMOD_igFresh:
"igFresh (asIMOD SEM) ys y X =
(\<forall> val val'. sWlsVal SEM val \<and> sWlsVal SEM val' \<and> eqBut val val' ys y
             \<longrightarrow> X val = X val')"
unfolding asIMOD_def by simp

lemma asIMOD_igFreshAbs:
"igFreshAbs (asIMOD SEM) ys y A =
(\<forall> val val'. sWlsVal SEM val \<and> sWlsVal SEM val' \<and> eqBut val val' ys y
             \<longrightarrow> A val = A val')"
unfolding asIMOD_def by simp

lemma asIMOD_igSwap:
"igSwap (asIMOD SEM) zs z1 z2 X =
(\<lambda>val. if sWlsVal SEM val then X (val ^[z1 \<and> z2]_zs) else undefined)"
unfolding asIMOD_def by simp

lemma asIMOD_igSwapAbs:
"igSwapAbs (asIMOD SEM) zs z1 z2 A =
(\<lambda>val. if sWlsVal SEM val then A (val ^[z1 \<and> z2]_zs) else undefined)"
unfolding asIMOD_def by simp

lemma asIMOD_igSubst:
"igSubst (asIMOD SEM) ys Y y X =
(\<lambda>val. if sWlsVal SEM val then X (val (y := Y val)_ys) else undefined)"
unfolding asIMOD_def by simp

lemma asIMOD_igSubstAbs:
"igSubstAbs (asIMOD SEM) ys Y y A =
(\<lambda>val. if sWlsVal SEM val then A (val (y := Y val)_ys) else undefined)"
unfolding asIMOD_def by simp

lemma asIMOD_igWlsInp: 
assumes "sWlsNE SEM"
shows
"igWlsInp (asIMOD SEM) delta inp \<longleftrightarrow> 
 ((\<forall> val. liftAll (\<lambda>X. sWlsVal SEM val \<or> X val = undefined) inp) \<and>
  (\<forall> val. sWlsVal SEM val \<longrightarrow> sWlsInp SEM delta (lift (\<lambda>X. X val) inp)))"
using assms apply safe
 subgoal by (simp add: asIMOD_igWls liftAll_def liftAll2_def igWlsInp_def 
  sameDom_def split: option.splits) (metis option.distinct(1) option.exhaust)
 subgoal by (simp add: igWlsInp_def asIMOD_igWls liftAll_def liftAll2_def 
  lift_def sWlsInp_def sameDom_def split: option.splits) 
 subgoal by (simp add:igWlsInp_def asIMOD_igWls liftAll_def liftAll2_def 
  lift_def sWlsInp_def sameDom_def split: option.splits) 
  (metis (no_types) option.distinct(1) sWlsNE_imp_sWlsValNE sWlsValNE_def) .

lemma asIMOD_igSwapInp:
"sWlsVal SEM val \<Longrightarrow> 
 lift (\<lambda>X. X val) (igSwapInp (asIMOD SEM) zs z1 z2 inp) =
 lift (\<lambda>X. X (swapVal zs z1 z2 val)) inp"
by (auto simp: igSwapInp_def asIMOD_igSwap lift_def split: option.splits)

lemma asIMOD_igSubstInp:
"sWlsVal SEM val \<Longrightarrow> 
 lift (\<lambda>X. X val) (igSubstInp (asIMOD SEM) ys Y y inp) =
 lift (\<lambda>X. X (val (y := Y val)_ys)) inp"
by (auto simp: igSubstInp_def asIMOD_igSubst lift_def split: option.splits)

lemma asIMOD_igWlsBinp: 
assumes "sWlsNE SEM"
shows
"igWlsBinp (asIMOD SEM) delta binp =
 ((\<forall> val. liftAll (\<lambda>X. sWlsVal SEM val \<or> X val = undefined) binp) \<and>
  (\<forall> val. sWlsVal SEM val \<longrightarrow> sWlsBinp SEM delta (lift (\<lambda>X. X val) binp)))"
using assms apply safe
 subgoal by (simp add: asIMOD_igWlsAbs liftAll_def liftAll2_def igWlsBinp_def 
  sameDom_def split: option.splits)
 (metis option.distinct(1) option.exhaust surj_pair)
 subgoal by (simp add: igWlsBinp_def asIMOD_igWlsAbs liftAll_def liftAll2_def 
  lift_def sWlsBinp_def sameDom_def split: option.splits) 
 subgoal by (simp add:igWlsBinp_def asIMOD_igWlsAbs liftAll_def liftAll2_def 
  lift_def sWlsBinp_def sameDom_def split: option.splits) 
  (metis (no_types) old.prod.exhaust option.distinct(1) option.exhaust 
   sWlsNE_imp_sWlsValNE sWlsValNE_def) .

lemma asIMOD_igSwapBinp:
"sWlsVal SEM val \<Longrightarrow> 
 lift (\<lambda>A. A val) (igSwapBinp (asIMOD SEM) zs z1 z2 binp) =
 lift (\<lambda>A. A (swapVal zs z1 z2 val)) binp"
by (auto simp: igSwapBinp_def asIMOD_igSwapAbs lift_def split: option.splits)

lemma asIMOD_igSubstBinp:
"sWlsVal SEM val \<Longrightarrow> 
 lift (\<lambda>A. A val) (igSubstBinp (asIMOD SEM) ys Y y binp) =
 lift (\<lambda>A. A (val (y := Y val)_ys)) binp"
by (auto simp: igSubstBinp_def asIMOD_igSubstAbs lift_def split: option.splits)

subsubsection {* The associated model is well-structured *}

text{* That is to say: it is a fresh-swap-subst
and fresh-subst-swap model (hence of course also a fresh-swap and fresh-subst) model. *}

text{* Domain disjointness: *}

lemma asIMOD_igWlsDisj:
"sWlsNE SEM \<Longrightarrow> sWlsDisj SEM \<Longrightarrow> igWlsDisj (asIMOD SEM)"
using sWlsNE_imp_sWlsValNE 
by (fastforce simp: igWlsDisj_def asIMOD_igWls sWlsValNE_def sWlsDisj_def)

lemma asIMOD_igWlsAbsDisj:
"sWlsNE SEM \<Longrightarrow> sWlsDisj SEM \<Longrightarrow> igWlsAbsDisj (asIMOD SEM)"
using sWlsNE_imp_sWlsValNE sWlsDisj_imp_sWlsAbsDisj
by (fastforce simp: igWlsAbsDisj_def asIMOD_igWlsAbs sWlsAbsDisj_def sWlsValNE_def)

lemma asIMOD_igWlsAllDisj: 
"sWlsNE SEM \<Longrightarrow> sWlsDisj SEM \<Longrightarrow> igWlsAllDisj (asIMOD SEM)"
unfolding igWlsAllDisj_def using asIMOD_igWlsDisj asIMOD_igWlsAbsDisj by auto

text {* Only ``bound arit" abstraction domains are inhabited: *}

lemma asIMOD_igWlsAbsIsInBar:
"sWlsNE SEM \<Longrightarrow> igWlsAbsIsInBar (asIMOD SEM)"
using sWlsNE_imp_sWlsValNE 
by (auto simp: sWlsValNE_def igWlsAbsIsInBar_def asIMOD_igWlsAbs 
         split: option.splits elim: sWlsAbs.elims(2))  

text{* Domain preservation by the operators *}

text{* The constructs preserve the domains: *}

lemma asIMOD_igVarIPresIGWls: "igVarIPresIGWls (asIMOD SEM)"
unfolding igVarIPresIGWls_def asIMOD_igWls asIMOD_igVar sWlsVal_def by simp

lemma asIMOD_igAbsIPresIGWls:
"sWlsDisj SEM \<Longrightarrow> igAbsIPresIGWls (asIMOD SEM)"
unfolding igAbsIPresIGWls_def asIMOD_igWlsAbs apply clarify
subgoal for _ _ _ _ val
unfolding asIMOD_igAbs2 by (cases "sWlsVal SEM val") (auto simp: asIMOD_igWls) .

lemma asIMOD_igOpIPresIGWls: 
"sOpPrSWls SEM \<Longrightarrow> sWlsNE SEM \<Longrightarrow> igOpIPresIGWls (asIMOD SEM)"
using asIMOD_igWlsInp asIMOD_igWlsBinp 
by (fastforce simp: igOpIPresIGWls_def asIMOD_igWls asIMOD_igOp sOpPrSWls_def)

lemma asIMOD_igConsIPresIGWls: 
"wlsSEM SEM \<Longrightarrow> igConsIPresIGWls (asIMOD SEM)"
unfolding igConsIPresIGWls_def wlsSEM_def
using asIMOD_igVarIPresIGWls asIMOD_igAbsIPresIGWls asIMOD_igOpIPresIGWls by auto

text{* Swap preserves the domains: *}

lemma asIMOD_igSwapIPresIGWls: "igSwapIPresIGWls (asIMOD SEM)"
unfolding igSwapIPresIGWls_def asIMOD_igSwap asIMOD_igWls by auto

lemma asIMOD_igSwapAbsIPresIGWlsAbs: "igSwapAbsIPresIGWlsAbs (asIMOD SEM)"
unfolding igSwapAbsIPresIGWlsAbs_def asIMOD_igSwapAbs asIMOD_igWlsAbs by auto

lemma asIMOD_igSwapAllIPresIGWlsAll: "igSwapAllIPresIGWlsAll (asIMOD SEM)"
unfolding igSwapAllIPresIGWlsAll_def
using asIMOD_igSwapIPresIGWls asIMOD_igSwapAbsIPresIGWlsAbs by auto

text {* Subst preserves the domains:  *}

lemma asIMOD_igSubstIPresIGWls: "igSubstIPresIGWls (asIMOD SEM)"
unfolding igSubstIPresIGWls_def asIMOD_igSubst asIMOD_igWls by simp

lemma asIMOD_igSubstAbsIPresIGWlsAbs: "igSubstAbsIPresIGWlsAbs (asIMOD SEM)"
unfolding igSubstAbsIPresIGWlsAbs_def asIMOD_igSubstAbs asIMOD_igWls asIMOD_igWlsAbs by simp

lemma asIMOD_igSubstAllIPresIGWlsAll: "igSubstAllIPresIGWlsAll (asIMOD SEM)"
unfolding igSubstAllIPresIGWlsAll_def
using asIMOD_igSubstIPresIGWls asIMOD_igSubstAbsIPresIGWlsAbs by auto

text {* The clauses for fresh hold:  *}

lemma asIMOD_igFreshIGVar: "igFreshIGVar (asIMOD SEM)"
unfolding igFreshIGVar_def asIMOD_igFresh asIMOD_igVar eqBut_def by force

lemma asIMOD_igFreshIGAbs1:
"sWlsDisj SEM \<Longrightarrow> igFreshIGAbs1 (asIMOD SEM)"
by(fastforce simp: igFreshIGAbs1_def asIMOD_igFresh asIMOD_igFreshAbs asIMOD_igAbs2 updVal_eqBut_eq)
 
lemma asIMOD_igFreshIGAbs2:
"sWlsDisj SEM \<Longrightarrow> igFreshIGAbs2 (asIMOD SEM)"
by(fastforce simp: igFreshIGAbs2_def asIMOD_igFresh asIMOD_igFreshAbs asIMOD_igAbs2  updVal_preserves_eqBut)

lemma asIMOD_igFreshIGOp:
fixes SEM :: "('index,'bindex,'varSort,'sort,'opSym,'sTerm)semDom"
shows "igFreshIGOp (asIMOD SEM)"
unfolding igFreshIGOp_def proof clarify
  fix ys y delta and inp :: "('index, ('varSort,'var,'sTerm)gTerm)input"
  and binp :: "('bindex, ('varSort,'var,'sTerm)gAbs)input"
  assume inp_fresh: "igFreshInp (asIMOD SEM) ys y inp"
                    "igFreshBinp (asIMOD SEM) ys y binp"
  show "igFresh (asIMOD SEM) ys y (igOp (asIMOD SEM) delta inp binp)"
  unfolding asIMOD_igFresh asIMOD_igOp proof safe
    fix val val'
    let ?sinp = "lift (\<lambda>X. X val) inp" let ?sinp' = "lift (\<lambda>X. X val') inp"
    let ?sbinp = "lift (\<lambda>A. A val) binp" let ?sbinp' = "lift (\<lambda>A. A val') binp"
    assume wls: "sWlsVal SEM val" "sWlsVal SEM val'" and "eqBut val val' ys y"
    hence "?sinp = ?sinp' \<and> ?sbinp = ?sbinp'"
    using inp_fresh
    by (auto simp: lift_def igFreshInp_def igFreshBinp_def errMOD_def liftAll_def 
    asIMOD_igFresh asIMOD_igFreshAbs split: option.splits) 
    then show "(if sWlsVal SEM val then sOp SEM delta (lift (\<lambda>X. X val) inp) (lift (\<lambda>A. A val) binp)
           else undefined) =
          (if sWlsVal SEM val' then sOp SEM delta (lift (\<lambda>X. X val') inp) (lift (\<lambda>A. A val') binp)
           else undefined)" using wls by auto 
  qed
qed 

lemma asIMOD_igFreshCls:
assumes "sWlsDisj SEM"
shows "igFreshCls (asIMOD SEM)"
using assms unfolding igFreshCls_def
using asIMOD_igFreshIGVar asIMOD_igFreshIGAbs1 asIMOD_igFreshIGAbs2 asIMOD_igFreshIGOp by auto

text {* The clauses for swap hold:  *}

lemma asIMOD_igSwapIGVar: "igSwapIGVar (asIMOD SEM)"
unfolding igSwapIGVar_def apply clarsimp apply(rule ext)
unfolding asIMOD_igSwap asIMOD_igVar apply clarsimp
unfolding swapVal_def by simp

lemma asIMOD_igSwapIGAbs: "igSwapIGAbs (asIMOD SEM)"
by (fastforce simp: igSwapIGAbs_def asIMOD_igSwap asIMOD_igSwapAbs asIMOD_igAbs updVal_swapVal)
 
lemma asIMOD_igSwapIGOp: "igSwapIGOp (asIMOD SEM)"
by (auto simp: igSwapIGOp_def asIMOD_igSwap asIMOD_igOp asIMOD_igSwapInp asIMOD_igSwapBinp)
 
lemma asIMOD_igSwapCls: "igSwapCls (asIMOD SEM)"
unfolding igSwapCls_def using asIMOD_igSwapIGVar asIMOD_igSwapIGAbs asIMOD_igSwapIGOp by auto

text{* The clauses for subst hold: *}

lemma asIMOD_igSubstIGVar1: "igSubstIGVar1 (asIMOD SEM)"
by (auto simp: igSubstIGVar1_def asIMOD_igSubst asIMOD_igVar asIMOD_igWls)

lemma asIMOD_igSubstIGVar2: "igSubstIGVar2 (asIMOD SEM)"
by (fastforce simp: igSubstIGVar2_def asIMOD_igSubst asIMOD_igVar asIMOD_igWls)

lemma asIMOD_igSubstIGAbs: "igSubstIGAbs (asIMOD SEM)"
unfolding igSubstIGAbs_def proof(clarify, rule ext)
  fix ys y Y xs x s X val
  assume Y: "igWls (asIMOD SEM) (asSort ys) Y"
  and X: "igWls (asIMOD SEM) s X" and x_diff_y: "xs \<noteq> ys \<or> x \<noteq> y"
  and x_fresh_Y: "igFresh (asIMOD SEM) xs x Y"
  show "igSubstAbs (asIMOD SEM) ys Y y (igAbs (asIMOD SEM) xs x X) val =
        igAbs (asIMOD SEM) xs x (igSubst (asIMOD SEM) ys Y y X) val"
  proof(cases "sWlsVal SEM val")
    case False
    thus ?thesis unfolding asIMOD_igSubst asIMOD_igSubstAbs asIMOD_igAbs by simp
  next
    case True  
    hence Yval: "sWls SEM (asSort ys) (Y val)"
    using Y unfolding asIMOD_igWls by simp
    {fix sX assume sX: "sWls SEM (asSort xs) sX"
     let ?val_x = "val (x := sX)_xs"
     have "sWlsVal SEM ?val_x" using True sX by simp
     moreover have "eqBut ?val_x val xs x"
     unfolding eqBut_def updVal_def by simp
     ultimately have 1: "Y ?val_x = Y val"
     using True x_fresh_Y unfolding asIMOD_igFresh by simp
     let ?Left = "X ((val (y := Y val)_ys) (x := sX)_xs)"
     let ?Riight = "X (?val_x (y := Y ?val_x)_ys)"
     have "?Left = X (?val_x (y := Y val)_ys)"
     using x_diff_y by(auto simp add: updVal_commute)
     also have "\<dots> = ?Riight" using 1 by simp
     finally have "?Left = ?Riight" . 
    }  
    thus ?thesis using True Yval by(auto simp: asIMOD_igSubst asIMOD_igSubstAbs asIMOD_igAbs) 
  qed
qed

lemma asIMOD_igSubstIGOp: "igSubstIGOp (asIMOD SEM)" 
unfolding igSubstIGOp_def proof(clarify,rule ext)
  fix ys y Y delta inp binp val
  assume Y: "igWls (asIMOD SEM) (asSort ys) Y"
  and inp: "igWlsInp (asIMOD SEM) delta inp"
  and binp: "igWlsBinp (asIMOD SEM) delta binp"
  define inpsb binpsb where
  inpsb_def: "inpsb \<equiv> igSubstInp (asIMOD SEM) ys Y y inp"
             "binpsb \<equiv> igSubstBinp (asIMOD SEM) ys Y y binp"
  note inpsb_rev = inpsb_def[symmetric] 
  let ?sinpsb = "lift (\<lambda>X. X (val (y := Y val)_ys)) inp"
  let ?sbinpsb = "lift (\<lambda>A. A (val (y := Y val)_ys)) binp"
  show "igSubst (asIMOD SEM) ys Y y (igOp (asIMOD SEM) delta inp binp) val =
        igOp (asIMOD SEM) delta (igSubstInp (asIMOD SEM) ys Y y inp)
                              (igSubstBinp (asIMOD SEM) ys Y y binp) val"
  unfolding inpsb_rev unfolding asIMOD_igSubst asIMOD_igOp unfolding inpsb_def 
  apply(simp add: asIMOD_igSubstInp asIMOD_igSubstBinp)
  using Y unfolding asIMOD_def by auto
qed

lemma asIMOD_igSubstCls: "igSubstCls (asIMOD SEM)"
unfolding igSubstCls_def
using asIMOD_igSubstIGVar1 asIMOD_igSubstIGVar2 asIMOD_igSubstIGAbs asIMOD_igSubstIGOp by auto

text {* The fresh-swap-based congruence clause holds: *}

lemma updVal_swapVal_eqBut: "eqBut (val (x := sX)_xs) ((val (y := sX)_xs) ^[y \<and> x]_xs) xs y"
by (simp add: updVal_def swapVal_def eqBut_def sw_def) 

lemma asIMOD_igAbsCongS: "sWlsDisj SEM \<Longrightarrow> igAbsCongS (asIMOD SEM)"
unfolding igAbsCongS_def asIMOD_igFresh asIMOD_igSwap asIMOD_igAbs2 
apply safe apply (simp add: asIMOD_igAbs2) 
by (rule ext) (metis (hide_lams) updVal_swapVal_eqBut swapVal_preserves_sWls updVal_preserves_sWls) 

 

text {* The abstraction-renaming clause holds: *}

lemma asIMOD_igAbs3:
assumes "sWlsDisj SEM" and "igWls (asIMOD SEM) s X"
shows
"igAbs (asIMOD SEM) xs y (igSubst (asIMOD SEM) xs (igVar (asIMOD SEM) xs y) x X) =
 (\<lambda>val. if sWlsVal SEM val
            then sAbs xs (\<lambda>sX. if sWls SEM (asSort xs) sX
                                 then (igSubst (asIMOD SEM) xs (igVar (asIMOD SEM) xs y) x X) (val (y := sX)_xs)
                                 else sDummy SEM s)
            else undefined)"
using assms asIMOD_igVarIPresIGWls asIMOD_igSubstIPresIGWls
unfolding igVarIPresIGWls_def igSubstIPresIGWls_def
by (fastforce intro!: asIMOD_igAbs2)

lemma asIMOD_igAbsRen:
"sWlsDisj SEM \<Longrightarrow> igAbsRen (asIMOD SEM)"
unfolding igAbsRen_def asIMOD_igFresh asIMOD_igSwap apply safe
by (simp add: asIMOD_igAbs2 asIMOD_igAbs3)  
   (auto intro!: ext simp: asIMOD_igAbs2 asIMOD_igAbs3 eqBut_def asIMOD_igSubst asIMOD_igVar)

text {* The associated model forms well-structured models of all 4 kinds: *}

lemma asIMOD_wlsFSw:
assumes "wlsSEM SEM"
shows "iwlsFSw (asIMOD SEM)"
using assms unfolding wlsSEM_def iwlsFSw_def
using assms asIMOD_igWlsAllDisj asIMOD_igWlsAbsIsInBar 
asIMOD_igConsIPresIGWls asIMOD_igSwapAllIPresIGWlsAll 
asIMOD_igFreshCls asIMOD_igSwapCls asIMOD_igAbsCongS 
by auto

lemma asIMOD_wlsFSb:
assumes "wlsSEM SEM"
shows "iwlsFSb (asIMOD SEM)"
using assms unfolding wlsSEM_def iwlsFSb_def
using assms asIMOD_igWlsAllDisj asIMOD_igWlsAbsIsInBar 
asIMOD_igConsIPresIGWls[of SEM] asIMOD_igSubstAllIPresIGWlsAll 
asIMOD_igFreshCls  asIMOD_igSubstCls asIMOD_igAbsRen 
by auto

lemma asIMOD_wlsFSwSb: "wlsSEM SEM \<Longrightarrow> iwlsFSwSb (asIMOD SEM)"
unfolding iwlsFSwSb_def
using asIMOD_wlsFSw asIMOD_igSubstAllIPresIGWlsAll asIMOD_igSubstCls by auto

lemma asIMOD_wlsFSbSw: "wlsSEM SEM \<Longrightarrow> iwlsFSbSw (asIMOD SEM)"
unfolding iwlsFSbSw_def
using asIMOD_wlsFSb asIMOD_igSwapAllIPresIGWlsAll asIMOD_igSwapCls by auto

subsection {* The semantic interpretation  *}

text{* The well-definedness of the semantic interpretation, as well
as its associated substitution lemma and non-dependence of fresh variables,
are the end products of this theory.

Note that in order to establish these results either fresh-subst-swap or
fresh-swap-subst aligebras would do the job, and, moreover, if we did not care
about swapping, fresh-subst aligebras would do the job.  Therefore, our
exhaustive study of the model from previous section had a deigree of redundancy w.r.t. to our main
igoal -- we pursued it however in order to better illustrate the rich structure laying under
the apparent paucity of the notion of a semantic domain.  Next, we choose to employ
fresh-subst-swap aligebras to establish the required results. (Recall however that either aligebraic route
we take, the initial morphism turns out to be the same function.)*}

definition semInt where "semInt SEM \<equiv> iter (asIMOD SEM)"

definition semIntAbs where "semIntAbs SEM \<equiv> iterAbs (asIMOD SEM)"

lemma semIntAll_termFSwSbImorph:
"wlsSEM SEM \<Longrightarrow>
 termFSwSbImorph (semInt SEM) (semIntAbs SEM) (asIMOD SEM)"
unfolding semInt_def semInt_def semIntAbs_def
using asIMOD_wlsFSbSw iwlsFSbSw_iterAll_termFSwSbImorph by auto

lemma semInt_prWls:
"wlsSEM SEM \<Longrightarrow> prWls (semInt SEM) SEM"
unfolding prWls_def using semIntAll_termFSwSbImorph
unfolding termFSwSbImorph_def termFSwImorph_def ipresWlsAll_def ipresWls_def asIMOD_igWls by auto

lemma semIntAbs_prWlsAbs:
"wlsSEM SEM \<Longrightarrow> prWlsAbs (semIntAbs SEM) SEM"
unfolding prWlsAbs_def using semIntAll_termFSwSbImorph
unfolding termFSwSbImorph_def termFSwImorph_def ipresWlsAll_def ipresWlsAbs_def asIMOD_igWlsAbs by blast

lemma semIntAll_prWlsAll:
"wlsSEM SEM \<Longrightarrow> prWlsAll (semInt SEM) (semIntAbs SEM) SEM"
unfolding prWlsAll_def by(simp add: semInt_prWls semIntAbs_prWlsAbs)

lemma semInt_prVar:
"wlsSEM SEM \<Longrightarrow> prVar (semInt SEM) SEM"
using semIntAll_termFSwSbImorph
unfolding prVar_def termFSwSbImorph_def termFSwImorph_def ipresCons_def ipresVar_def asIMOD_igVar 
by fastforce

lemma semIntAll_prAbs:
fixes SEM :: "('index,'bindex,'varSort,'sort,'opSym,'sTerm)semDom"
assumes "wlsSEM SEM"
shows "prAbs (semInt SEM) (semIntAbs SEM) SEM"
proof-
  {fix xs s x X and val :: "('varSort,'var,'sTerm)val"
   assume xs_s: "isInBar (xs,s)" and X: "wls s X"
   and val: "sWlsVal SEM val"
   let ?L = "semIntAbs SEM (Abs xs x X)"
   let ?R = "\<lambda> val. sAbs xs (\<lambda>sX. if sWls SEM (asSort xs) sX
                              then semInt SEM X (val (x := sX)_xs)
                              else sDummy SEM s)"
   have "?L = igAbs (asIMOD SEM) xs x (semInt SEM X)"
   using xs_s X assms semIntAll_termFSwSbImorph[of SEM]
   unfolding termFSwSbImorph_def termFSwImorph_def ipresCons_def ipresAbs_def by auto
   moreover
   {have "prWls (semInt SEM) SEM" using assms semInt_prWls by auto
    hence 1: "sWls SEM s (semInt SEM X val)"
    using val X unfolding prWls_def by simp
    hence "(SOME s. sWls SEM s (semInt SEM X val)) = s"
    using 1 assms unfolding wlsSEM_def sWlsDisj_def by auto
    hence "igAbs (asIMOD SEM) xs x (semInt SEM X) val = ?R val"
    unfolding asIMOD_igAbs using val by fastforce
   }
   ultimately have "?L val = ?R val" by simp
  }
  thus ?thesis unfolding prAbs_def by auto
qed

lemma semIntAll_prOp:
assumes "wlsSEM SEM"
shows "prOp (semInt SEM) (semIntAbs SEM) SEM"
using assms semIntAll_termFSwSbImorph
unfolding prOp_def termFSwSbImorph_def termFSwImorph_def ipresCons_def ipresOp_def
asIMOD_igOp lift_comp comp_def by fastforce

lemma semIntAll_prCons:
assumes "wlsSEM SEM"
shows "prCons (semInt SEM) (semIntAbs SEM) SEM"
using assms unfolding prCons_def by(simp add: semInt_prVar semIntAll_prAbs semIntAll_prOp)

lemma semInt_prFresh:
assumes "wlsSEM SEM"
shows "prFresh (semInt SEM) SEM"
using assms semIntAll_termFSwSbImorph
unfolding prFresh_def termFSwSbImorph_def termFSwImorph_def ipresFreshAll_def ipresFresh_def
asIMOD_igFresh by fastforce

lemma semIntAbs_prFreshAbs:
assumes "wlsSEM SEM"
shows "prFreshAbs (semIntAbs SEM) SEM"
using assms semIntAll_termFSwSbImorph
unfolding prFreshAbs_def termFSwSbImorph_def termFSwImorph_def ipresFreshAll_def ipresFreshAbs_def
asIMOD_igFreshAbs by fastforce

lemma semIntAll_prFreshAll:
assumes "wlsSEM SEM"
shows "prFreshAll (semInt SEM) (semIntAbs SEM) SEM"
using assms unfolding prFreshAll_def by(simp add: semInt_prFresh semIntAbs_prFreshAbs)

lemma semInt_prSwap:
assumes "wlsSEM SEM"
shows "prSwap (semInt SEM) SEM"
using assms semIntAll_termFSwSbImorph
unfolding prSwap_def termFSwSbImorph_def termFSwImorph_def ipresSwapAll_def ipresSwap_def
asIMOD_igSwap by fastforce

lemma semIntAbs_prSwapAbs:
assumes "wlsSEM SEM"
shows "prSwapAbs (semIntAbs SEM) SEM"
using assms semIntAll_termFSwSbImorph
unfolding prSwapAbs_def termFSwSbImorph_def termFSwImorph_def ipresSwapAll_def ipresSwapAbs_def
asIMOD_igSwapAbs by fastforce

lemma semIntAll_prSwapAll:
assumes "wlsSEM SEM"
shows "prSwapAll (semInt SEM) (semIntAbs SEM) SEM"
using assms unfolding prSwapAll_def by(simp add: semInt_prSwap semIntAbs_prSwapAbs)

lemma semInt_prSubst:
assumes "wlsSEM SEM"
shows "prSubst (semInt SEM) SEM"
using assms semIntAll_termFSwSbImorph
unfolding prSubst_def termFSwSbImorph_def termFSwImorph_def ipresSubstAll_def ipresSubst_def
asIMOD_igSubst by fastforce

lemma semIntAbs_prSubstAbs:
assumes "wlsSEM SEM"
shows "prSubstAbs (semInt SEM) (semIntAbs SEM) SEM"
using assms semIntAll_termFSwSbImorph
unfolding prSubstAbs_def termFSwSbImorph_def termFSwImorph_def ipresSubstAll_def ipresSubstAbs_def
asIMOD_igSubstAbs by fastforce

lemma semIntAll_prSubstAll:
assumes "wlsSEM SEM"
shows "prSubstAll (semInt SEM) (semIntAbs SEM) SEM"
using assms unfolding prSubstAll_def by(simp add: semInt_prSubst semIntAbs_prSubstAbs)

theorem semIntAll_compInt:
assumes "wlsSEM SEM"
shows "compInt (semInt SEM) (semIntAbs SEM) SEM"
using assms unfolding compInt_def
by(simp add: semIntAll_prWlsAll semIntAll_prCons
semIntAll_prFreshAll semIntAll_prSwapAll semIntAll_prSubstAll)

lemmas semDom_simps = updVal_simps swapVal_simps

end (* context FixSyn *)

end
