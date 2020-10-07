section {* Binding Signatures and well-sorted terms *}

theory Well_Sorted_Terms
imports Terms
begin

text {*  This section introduces binding signatures
and well-sorted terms for them.  All the properties we proved for good terms are then
lifted to well-sorted terms.
*}

subsection {* Binding signatures *}

text{* A {\em (binding) signature} consists of:
\\- an indication of which sorts of variables can be injected in
which sorts of terms;
\\- for any operation symbol, dwelling in a type ``opSym",
an indication of its result sort, its (nonbinding) arity, and its binding arity.

In addition, we have a predicate, ``wlsOpSym", that specifies which operations symbols
are well-sorted (or well-structured)
\footnote
{
We shall use ``wls" in many contexts as a prefix indicating well-sortedness or
well-structuredness.
}
 -- only these operation symbols will be considered in
forming terms.  In other words, the relevant collection of operation symbols is given not by the
whole type ``opSym", but by the predicate ``wlsOpSym".  This bit of extra flexibility
will be useful when (pre)instantiating the signature to concrete syntaxes.
(Note that the ``wlsOpSym" condition will be required for well-sorted terms as part of the notion of
well-sorted (free and bound) input, ``wlsInp" and ``wlsBinp".)
  *}

record ('index,'bindex,'varSort,'sort,'opSym)signature =
  varSortAsSort :: "'varSort \<Rightarrow> 'sort"
  wlsOpSym :: "'opSym \<Rightarrow> bool"
  sortOf :: "'opSym \<Rightarrow> 'sort"
  arityOf :: "'opSym \<Rightarrow> ('index, 'sort)input"
  barityOf :: "'opSym \<Rightarrow> ('bindex, 'varSort * 'sort)input"

subsection {* The Binding Syntax locale *}

(* From now on, all work on binding syntax shall be developed in this locale
   (or an extension of it): *)

(*
   Note also that currently locales do not allow datatype defs or records,
   reason for which the type of models has been defined outside. *)

text {* For our signatures, we shall make some assumptions:
\\- For each sort of term, there is at most one sort of variables injectable  
in terms of that sort (i.e., ``varSortAsSort" is injective");
\\- The domains of arities (sets of indexes) are smaller than the set of variables
of each sort;
\\- The type of sorts is smaller than the set of variables
of each sort.

These are satisfiable assumptions, and in particular they are trivially satisfied by any finitary syntax
with bindings.
*}

definition varSortAsSort_inj where
"varSortAsSort_inj Delta ==
inj (varSortAsSort Delta)"

definition arityOf_lt_var where
"arityOf_lt_var (_ :: 'var) Delta ==
 \<forall> delta.
    wlsOpSym Delta delta \<longrightarrow> |{i. arityOf Delta delta i \<noteq> None}| <o |UNIV :: 'var set|"

definition barityOf_lt_var where
"barityOf_lt_var (_ :: 'var) Delta ==
 \<forall> delta.
    wlsOpSym Delta delta \<longrightarrow> |{i. barityOf Delta delta i \<noteq> None}| <o |UNIV :: 'var set|"

definition sort_lt_var where
"sort_lt_var (_ :: 'sort) (_ :: 'var) ==
 |UNIV :: 'sort set| <o |UNIV :: 'var set|"

locale FixSyn =
  fixes dummyV :: 'var
  and Delta :: "('index,'bindex,'varSort,'sort,'opSym)signature"
  assumes
  (* The ``FixVars" assumptions, minus ``varSort-lt-var" (which follows form the rest): *)
      FixSyn_var_infinite: "var_infinite (undefined :: 'var)"
  and FixSyn_var_regular: "var_regular (undefined :: 'var)"
  (*  Plus the following: *)
  and varSortAsSort_inj: "varSortAsSort_inj Delta"
  and arityOf_lt_var: "arityOf_lt_var (undefined :: 'var) Delta"
  and barityOf_lt_var: "barityOf_lt_var (undefined :: 'var) Delta"
  and sort_lt_var: "sort_lt_var (undefined :: 'sort) (undefined :: 'var)"

context FixSyn
begin
lemmas FixSyn_assms =
FixSyn_var_infinite FixSyn_var_regular
varSortAsSort_inj arityOf_lt_var barityOf_lt_var
sort_lt_var
end

subsection {* Definitions and basic properties of well-sortedness *}

subsubsection {* Notations and definitions *}

(* Sorted parameters (again, for use in proofs): *)

datatype ('index,'bindex,'varSort,'var,'opSym,'sort)paramS =
  ParS "'varSort \<Rightarrow> 'var list"
       "'sort \<Rightarrow> ('index,'bindex,'varSort,'var,'opSym)term list"
       "('varSort * 'sort) \<Rightarrow> ('index,'bindex,'varSort,'var,'opSym)abs list"
       "('index,'bindex,'varSort,'var,'opSym)env list"

fun varsOfS ::
"('index,'bindex,'varSort,'var,'opSym,'sort)paramS \<Rightarrow> 'varSort \<Rightarrow> 'var set"
where "varsOfS (ParS xLF _ _ _) xs = set (xLF xs)"

fun termsOfS ::
"('index,'bindex,'varSort,'var,'opSym,'sort)paramS \<Rightarrow>
 'sort \<Rightarrow> ('index,'bindex,'varSort,'var,'opSym)term set"
where "termsOfS (ParS _ XLF _ _) s = set (XLF s)"

fun absOfS ::
"('index,'bindex,'varSort,'var,'opSym,'sort)paramS \<Rightarrow>
 ('varSort * 'sort) \<Rightarrow> ('index,'bindex,'varSort,'var,'opSym)abs set"
where "absOfS (ParS _ _ ALF _) (xs,s) = set (ALF (xs,s))"

fun envsOfS ::
"('index,'bindex,'varSort,'var,'opSym,'sort)paramS \<Rightarrow> ('index,'bindex,'varSort,'var,'opSym)env set"
where "envsOfS (ParS _ _ _ rhoL) = set rhoL"

subsubsection {* Sublocale of ``FixVars" *}
  
lemma sort_lt_var_imp_varSort_lt_var:
assumes
**: "varSortAsSort_inj (Delta :: ('index,'bindex,'varSort,'sort,'opSym)signature)"
and ***: "sort_lt_var (undefined :: 'sort) (undefined :: 'var)"
shows "varSort_lt_var (undefined :: 'varSort) (undefined :: 'var)"
proof-
  have "|UNIV::'varSort set| \<le>o |UNIV::'sort set|"
  using card_of_ordLeq ** unfolding  varSortAsSort_inj_def by auto
  thus ?thesis
  using ordLeq_ordLess_trans assms
  unfolding sort_lt_var_def varSort_lt_var_def by blast
qed

sublocale FixSyn < FixVars
where dummyV = dummyV and dummyVS = "undefined::'varSort"
using FixSyn_assms 
by unfold_locales (auto simp add: sort_lt_var_imp_varSort_lt_var)  

subsubsection {* Abbreviations *}

(*********************************************)
context FixSyn   (* scope all throughout the file *)
begin

abbreviation asSort where "asSort == varSortAsSort Delta"
abbreviation wlsOpS where "wlsOpS == wlsOpSym Delta"
abbreviation stOf where "stOf == sortOf Delta"
abbreviation arOf where "arOf == arityOf Delta"
abbreviation barOf where "barOf == barityOf Delta"

abbreviation empInp ::
"('index,('index,'bindex,'varSort,'var,'opSym)term)input"
where "empInp == \<lambda>i. None"

abbreviation empAr :: "('index,'sort)input"
where "empAr == \<lambda>i. None"

abbreviation empBinp :: "('bindex,('index,'bindex,'varSort,'var,'opSym)abs)input"
where "empBinp == \<lambda>i. None"

abbreviation empBar :: "('bindex,'varSort * 'sort)input"
where "empBar == \<lambda>i. None"

lemma freshInp_empInp[simp]:
"freshInp xs x empInp"
unfolding freshInp_def liftAll_def by simp

lemma swapInp_empInp[simp]:
"(empInp %[x1 \<and> x2]_xs) = empInp"
unfolding swapInp_def lift_def by simp

lemma psubstInp_empInp[simp]:
"(empInp %[rho]) = empInp"
unfolding psubstInp_def lift_def by simp

lemma substInp_empInp[simp]:
"(empInp %[Y / y]_ys) = empInp"
unfolding substInp_def by simp

lemma vsubstInp_empInp[simp]:
"(empInp %[y1 // y]_ys) = empInp"
unfolding vsubstInp_def by simp

lemma freshBinp_empBinp[simp]:
"freshBinp xs x empBinp"
unfolding freshBinp_def liftAll_def by simp

lemma swapBinp_empBinp[simp]:
"(empBinp %%[x1 \<and> x2]_xs) = empBinp"
unfolding swapBinp_def lift_def by simp

lemma psubstBinp_empBinp[simp]:
"(empBinp %%[rho]) = empBinp"
unfolding psubstBinp_def lift_def by simp

lemma substBinp_empBinp[simp]:
"(empBinp %%[Y / y]_ys) = empBinp"
unfolding substBinp_def by simp

lemma vsubstBinp_empBinp[simp]:
"(empBinp %%[y1 // y]_ys) = empBinp"
unfolding vsubstBinp_def by simp

lemmas empInp_simps =
freshInp_empInp swapInp_empInp psubstInp_empInp substInp_empInp vsubstInp_empInp
freshBinp_empBinp swapBinp_empBinp psubstBinp_empBinp substBinp_empBinp vsubstBinp_empBinp

subsubsection {* Inner versions of the locale assumptions *}

lemma varSortAsSort_inj_INNER: "inj asSort"
using varSortAsSort_inj
unfolding varSortAsSort_inj_def by simp

lemma asSort_inj[simp]:
"(asSort xs = asSort ys) = (xs = ys)"
using varSortAsSort_inj_INNER unfolding inj_on_def by auto

lemma arityOf_lt_var_INNER:
assumes "wlsOpS delta"
shows "|{i. arityOf Delta delta i \<noteq> None}| <o |UNIV :: 'var set|"
using assms arityOf_lt_var unfolding arityOf_lt_var_def by simp

lemma barityOf_lt_var_INNER:
assumes "wlsOpS delta"
shows "|{i. barityOf Delta delta i \<noteq> None}| <o |UNIV :: 'var set|"
using assms barityOf_lt_var unfolding barityOf_lt_var_def by simp

lemma sort_lt_var_INNER:
"|UNIV :: 'sort set| <o |UNIV :: 'var set|"
using sort_lt_var unfolding sort_lt_var_def by simp

lemma sort_le_var:
"|UNIV :: 'sort set| \<le>o |UNIV :: 'var set|"
using sort_lt_var_INNER ordLess_imp_ordLeq by auto

lemma varSort_sort_lt_var:
"|UNIV :: ('varSort * 'sort) set| <o |UNIV :: 'var set|"
unfolding UNIV_Times_UNIV[symmetric]
using var_infinite_INNER varSort_lt_var_INNER sort_lt_var_INNER
by(rule card_of_Times_ordLess_infinite)

lemma varSort_sort_le_var:
"|UNIV :: ('varSort * 'sort) set| \<le>o |UNIV :: 'var set|"
using varSort_sort_lt_var ordLess_imp_ordLeq by auto

subsubsection {* Definitions of well-sorted items *}

text {* We shall only be interested in abstractions that pertain to some bound arities: *}

definition isInBar where
"isInBar xs_s ==
 \<exists> delta i. wlsOpS delta \<and> barOf delta i = Some xs_s"

text {* Well-sorted terms (according to the signature) are defined as expected (mutually inductively
together with well-sorted abstractions and inputs): *}

inductive
wls :: "'sort \<Rightarrow> ('index,'bindex,'varSort,'var,'opSym)term \<Rightarrow> bool"
and
wlsAbs :: "'varSort * 'sort \<Rightarrow> ('index,'bindex,'varSort,'var,'opSym)abs \<Rightarrow> bool"
and
wlsInp :: "'opSym \<Rightarrow> ('index,('index,'bindex,'varSort,'var,'opSym)term)input \<Rightarrow> bool"
and
wlsBinp :: "'opSym \<Rightarrow> ('bindex,('index,'bindex,'varSort,'var,'opSym)abs)input \<Rightarrow> bool"
where
Var: "wls (asSort xs) (Var xs x)"
|
Op: "\<lbrakk>wlsInp delta inp; wlsBinp delta binp\<rbrakk>  \<Longrightarrow> wls (stOf delta) (Op delta inp binp)"
|
Inp:
"\<lbrakk>wlsOpS delta;
  \<And> i. (arOf delta i = None \<and> inp i = None) \<or>
        (\<exists> s X. arOf delta i = Some s \<and> inp i = Some X \<and> wls s X)\<rbrakk>
 \<Longrightarrow> wlsInp delta inp"
|
Binp:
"\<lbrakk>wlsOpS delta;
  \<And> i. (barOf delta i = None \<and> binp i = None) \<or>
        (\<exists> us s A. barOf delta i = Some (us,s) \<and> binp i = Some A \<and> wlsAbs (us,s) A)\<rbrakk>
 \<Longrightarrow> wlsBinp delta binp"
|
Abs: "\<lbrakk>isInBar (xs,s); wls s X\<rbrakk> \<Longrightarrow> wlsAbs (xs,s) (Abs xs x X)"

lemmas Var_preserves_wls = wls_wlsAbs_wlsInp_wlsBinp.Var
lemmas Op_preserves_wls = wls_wlsAbs_wlsInp_wlsBinp.Op
lemmas Abs_preserves_wls = wls_wlsAbs_wlsInp_wlsBinp.Abs

lemma barOf_isInBar[simp]:
assumes "wlsOpS delta" and "barOf delta i = Some (us,s)"
shows "isInBar (us,s)"
unfolding isInBar_def using assms by blast

lemmas Cons_preserve_wls =
barOf_isInBar
Var_preserves_wls Op_preserves_wls
Abs_preserves_wls

declare Cons_preserve_wls [simp]

definition wlsEnv :: "('index,'bindex,'varSort,'var,'opSym)env \<Rightarrow> bool"
where
"wlsEnv rho ==
 (\<forall> ys. liftAll (wls (asSort ys)) (rho ys)) \<and>
 (\<forall> ys. |{y. rho ys y \<noteq> None}| <o |UNIV :: 'var set| )"

definition wlsPar :: "('index,'bindex,'varSort,'var,'opSym,'sort)paramS \<Rightarrow> bool"
where
"wlsPar P ==
 (\<forall> s. \<forall> X \<in> termsOfS P s. wls s X) \<and>
 (\<forall> xs s. \<forall> A \<in> absOfS P (xs,s). wlsAbs (xs,s) A) \<and>
 (\<forall> rho \<in> envsOfS P. wlsEnv rho)"

lemma ParS_preserves_wls[simp]:
assumes "\<And> s X. X \<in> set (XLF s) \<Longrightarrow> wls s X"
and "\<And> xs s A. A \<in> set (ALF (xs,s)) \<Longrightarrow> wlsAbs (xs,s) A"
and "\<And> rho. rho \<in> set rhoF \<Longrightarrow> wlsEnv rho"
shows "wlsPar (ParS xLF XLF ALF rhoF)"
using assms unfolding wlsPar_def by auto

lemma termsOfS_preserves_wls[simp]:
assumes "wlsPar P" and "X : termsOfS P s"
shows "wls s X"
using assms unfolding wlsPar_def by auto

lemma absOfS_preserves_wls[simp]:
assumes "wlsPar P" and "A : absOfS P (us,s)"
shows "wlsAbs (us,s) A"
using assms unfolding wlsPar_def by auto

lemma envsOfS_preserves_wls[simp]:
assumes "wlsPar P" and "rho : envsOfS P "
shows "wlsEnv rho"
using assms unfolding wlsPar_def by blast

lemma not_isInBar_absOfS_empty[simp]:
assumes *: "\<not> isInBar (us,s)" and **: "wlsPar P"
shows "absOfS P (us,s) = {}"
proof-
  {fix A assume "A : absOfS P (us,s)"
   hence "wlsAbs (us,s) A" using ** by simp
   hence False using * using wlsAbs.cases by auto
  }
  thus ?thesis by auto
qed

lemmas paramS_simps =
varsOfS.simps termsOfS.simps absOfS.simps envsOfS.simps
ParS_preserves_wls
termsOfS_preserves_wls absOfS_preserves_wls envsOfS_preserves_wls
not_isInBar_absOfS_empty

subsubsection {* Well-sorted exists *}

lemma wlsInp_iff:
"wlsInp delta inp =
 (wlsOpS delta \<and> sameDom (arOf delta) inp \<and> liftAll2 wls (arOf delta) inp)" 
by (simp add: wlsInp.simps wls_wlsAbs_wlsInp_wlsBinp.Inp sameDom_and_liftAll2_iff) 
 

lemma wlsBinp_iff:
"wlsBinp delta binp =
(wlsOpS delta \<and> sameDom (barOf delta) binp \<and> liftAll2 wlsAbs (barOf delta) binp)"
by (simp add: wlsBinp.simps wls_wlsAbs_wlsInp_wlsBinp.Inp sameDom_and_liftAll2_iff) 

lemma exists_asSort_wls:
"\<exists> X. wls (asSort xs) X"
by (intro exI[of _ "Var xs undefined"]) simp

lemma exists_wls_imp_exists_wlsAbs:
assumes  *: "isInBar (us,s)" and **: "\<exists> X. wls s X"
shows "\<exists> A. wlsAbs (us,s) A" 
proof-
  obtain X where "wls s X" using ** by blast
  hence "wlsAbs (us,s) (Abs us undefined X)" using * by simp
  thus ?thesis by blast
qed

lemma exists_asSort_wlsAbs:
assumes "isInBar (us,asSort xs)"
shows "\<exists> A. wlsAbs (us,asSort xs) A"
proof-
  obtain X where "wls (asSort xs) X" using exists_asSort_wls by auto
  thus ?thesis using assms exists_wls_imp_exists_wlsAbs by auto
qed

text {* Standard criterion for the non-emptiness of the sets of well-sorted terms for each sort,
by a well-founded relation and a function picking, for sorts not corresponding to varSorts,
an operation symbol as an ``inductive" witness for non-emptyness.
``witOpS" stands for ``witness operation symbol". *}

definition witOpS where
"witOpS s delta R ==
 wlsOpS delta \<and> stOf delta = s \<and>
 liftAll (\<lambda>s'. (s',s) : R) (arOf delta) \<and>
 liftAll (\<lambda>(us,s'). (s',s) : R) (barOf delta)"

lemma wf_exists_wls:
assumes wf: "wf R" and *: "\<And>s. (\<exists> xs. s = asSort xs) \<or> witOpS s (f s) R"
shows "\<exists> X. wls s X"
proof(induction rule: wf_induct[of R])
  case (2 s)  
  show ?case
  proof(cases "\<exists> xs. s = asSort xs")
    case True
    thus ?thesis using exists_asSort_wls by auto
  next
    let ?delta = "f s"
    case False
    hence delta: "wlsOpS ?delta" and st: "stOf ?delta = s"
    and ar: "liftAll (\<lambda>s'. (s',s) : R) (arOf ?delta)"
    and bar: "liftAll (\<lambda>(us,s'). (s',s) : R) (barOf ?delta)"
    using * unfolding witOpS_def by auto
    (*  *)
    have 1: "\<forall> i s'. arOf ?delta i = Some s' \<longrightarrow> (\<exists> X. wls s' X)"
    using ar 2 unfolding liftAll_def by simp
    let ?chi = "\<lambda>i s' X. arOf ?delta i = Some s' \<longrightarrow> wls s' X"
    define inp where  
    "inp \<equiv> (\<lambda>i. (if arOf ?delta i = None
                   then None
                   else Some (SOME X. \<forall> s'. ?chi i s' X)))" 
    have inp: "wlsInp ?delta inp"
    unfolding wlsInp_iff sameDom_def liftAll2_def using delta 
    by (auto simp: inp_def 1 someI2_ex split: if_splits)  
    (*  *)
    have 1: "\<forall> i us s'. barOf ?delta i = Some (us,s') \<longrightarrow> (\<exists> A. wlsAbs (us,s') A)"
    using bar 2 unfolding liftAll_def using delta exists_wls_imp_exists_wlsAbs by simp
    let ?chi = "\<lambda>i us s' A. barOf ?delta i = Some (us,s') \<longrightarrow> wlsAbs (us,s') A"
    define binp where  
    "binp \<equiv> (\<lambda>i. (if barOf ?delta i = None
                   then None
                   else Some (SOME A. \<forall> us s'. ?chi i us s' A)))" 
    have binp: "wlsBinp ?delta binp"
    unfolding wlsBinp_iff sameDom_def liftAll2_def using delta 
    by (auto simp: binp_def 1 someI2_ex split: if_splits) 
    (*  *)
    have "wls s (Op ?delta inp binp)"
    using inp binp st using Op_preserves_wls[of ?delta inp binp] by simp
    thus ?thesis by blast
  qed
qed(insert assms, auto)

lemma wf_exists_wlsAbs:
assumes "isInBar (us,s)"
and "wf R" and "\<And>s. (\<exists> xs. s = asSort xs) \<or> witOpS s (f s) R"
shows "\<exists> A. wlsAbs (us,s) A"
using assms by (auto intro: exists_wls_imp_exists_wlsAbs wf_exists_wls)


subsubsection {* Well-sorted implies Good *}

lemma wlsInp_empAr_empInp[simp]:
assumes "wlsOpS delta" and "arOf delta = empAr"
shows "wlsInp delta empInp"
using assms
unfolding wlsInp_iff sameDom_def liftAll2_def by auto

lemma wlsBinp_empBar_empBinp[simp]:
assumes "wlsOpS delta" and "barOf delta = empBar"
shows "wlsBinp delta empBinp"
using assms unfolding wlsBinp_iff sameDom_def liftAll2_def by auto

lemmas empInp_otherSimps =
wlsInp_empAr_empInp wlsBinp_empBar_empBinp

lemma wlsAll_implies_goodAll:
"(wls s X \<longrightarrow> good X) \<and>
 (wlsAbs (xs,s') A \<longrightarrow> goodAbs A) \<and>
 (wlsInp delta inp \<longrightarrow> goodInp inp) \<and>
 (wlsBinp delta binp \<longrightarrow> goodBinp binp)"
apply(induct rule: wls_wlsAbs_wlsInp_wlsBinp.induct) 
subgoal by auto
subgoal by auto 
subgoal unfolding goodInp_def liftAll_def 
by simp (smt Collect_cong arityOf_lt_var_INNER option.distinct(1) option.sel)
subgoal unfolding goodBinp_def liftAll_def 
by simp (smt Collect_cong barityOf_lt_var_INNER option.distinct(1) option.sel) 
subgoal by auto .

corollary wls_imp_good[simp]: "wls s X \<Longrightarrow> good X"
by(simp add: wlsAll_implies_goodAll)

corollary wlsAbs_imp_goodAbs[simp]: "wlsAbs (xs,s) A \<Longrightarrow> goodAbs A"
by(simp add: wlsAll_implies_goodAll)

corollary wlsInp_imp_goodInp[simp]: "wlsInp delta inp \<Longrightarrow> goodInp inp"
by(simp add: wlsAll_implies_goodAll)

corollary wlsBinp_imp_goodBinp[simp]: "wlsBinp delta binp \<Longrightarrow> goodBinp binp"
by(simp add: wlsAll_implies_goodAll)

lemma wlsEnv_imp_goodEnv[simp]: "wlsEnv rho \<Longrightarrow> goodEnv rho"
unfolding wlsEnv_def goodEnv_def liftAll_def
by simp (insert wls_imp_good, blast)

lemmas wlsAll_imp_goodAll =
wls_imp_good wlsAbs_imp_goodAbs
wlsInp_imp_goodInp wlsBinp_imp_goodBinp
wlsEnv_imp_goodEnv

subsubsection {* Swapping preserves well-sortedness *}

lemma swapAll_pres_wlsAll:
"(wls s X \<longrightarrow> wls s (X #[z1 \<and> z2]_zs)) \<and>
 (wlsAbs (xs,s') A \<longrightarrow> wlsAbs (xs,s') (A $[z1 \<and> z2]_zs)) \<and>
 (wlsInp delta inp \<longrightarrow> wlsInp delta (inp %[z1 \<and> z2]_zs)) \<and>
 (wlsBinp delta binp \<longrightarrow> wlsBinp delta (binp %%[z1 \<and> z2]_zs))"
proof(induct rule: wls_wlsAbs_wlsInp_wlsBinp.induct)
  case (Inp delta inp)
  then show ?case 
  unfolding wlsInp_iff sameDom_def liftAll2_def lift_def swapInp_def
  using option.sel by (fastforce simp add: split: option.splits)  
next
  case (Binp delta binp)
  then show ?case 
  unfolding wlsBinp_iff sameDom_def liftAll2_def lift_def swapBinp_def
  using option.sel by (fastforce simp add: split: option.splits) 
qed(insert Cons_preserve_wls, simp_all)

lemma swap_preserves_wls[simp]:
"wls s X \<Longrightarrow> wls s (X #[z1 \<and> z2]_zs)"
by(simp add: swapAll_pres_wlsAll)

lemma swap_preserves_wls2[simp]:
assumes "good X"
shows "wls s (X #[z1 \<and> z2]_zs) = wls s X"
using assms swap_preserves_wls[of s "X #[z1 \<and> z2]_zs" zs z1 z2] by auto

lemma swap_preserves_wls3:
assumes "good X" and "good Y"
and "(X #[x1 \<and> x2]_xs) = (Y #[y1 \<and> y2]_ys)"
shows "wls s X = wls s Y"
by (metis assms swap_preserves_wls2)

lemma swapAbs_preserves_wls[simp]:
"wlsAbs (xs,x) A \<Longrightarrow> wlsAbs (xs,x) (A $[z1 \<and> z2]_zs)"
by(simp add: swapAll_pres_wlsAll)

lemma swapInp_preserves_wls[simp]:
"wlsInp delta inp \<Longrightarrow> wlsInp delta (inp %[z1 \<and> z2]_zs)"
by(simp add: swapAll_pres_wlsAll)

lemma swapBinp_preserves_wls[simp]:
"wlsBinp delta binp \<Longrightarrow> wlsBinp delta (binp %%[z1 \<and> z2]_zs)"
by(simp add: swapAll_pres_wlsAll)

lemma swapEnvDom_preserves_wls:
assumes "wlsEnv rho"
shows "wlsEnv (swapEnvDom xs x y rho)"
proof-
  {fix xsa ys  let ?Left = "{ya. swapEnvDom xs x y rho ys ya \<noteq> None}"
   have "|{y} \<union> {ya. rho ys ya \<noteq> None}| <o |UNIV :: 'var set|"
   using assms var_infinite_INNER card_of_Un_singl_ordLess_infinite
   unfolding wlsEnv_def by fastforce
   hence "|{x,y} \<union> {ya. rho ys ya \<noteq> None}| <o |UNIV :: 'var set|"
   using var_infinite_INNER card_of_Un_singl_ordLess_infinite by fastforce
   moreover
   {have "?Left \<subseteq> {x,y} \<union> {ya. rho ys ya \<noteq> None}"
    unfolding swapEnvDom_def sw_def[abs_def] by auto
    hence "|?Left| \<le>o |{x,y} \<union> {ya. rho ys ya \<noteq> None}|"
    using card_of_mono1 by auto
   }
   ultimately have "|?Left| <o |UNIV :: 'var set|" 
   using ordLeq_ordLess_trans by blast
  }
  thus ?thesis using assms unfolding wlsEnv_def liftAll_def 
  by (auto simp add: swapEnvDom_def)
qed 

lemma swapEnvIm_preserves_wls:
assumes "wlsEnv rho"
shows "wlsEnv (swapEnvIm xs x y rho)"
using assms unfolding wlsEnv_def swapEnvIm_def liftAll_def lift_def 
by (auto split: option.splits) 

lemma swapEnv_preserves_wls[simp]:
assumes "wlsEnv rho"
shows "wlsEnv (rho &[z1 \<and> z2]_zs)"
unfolding swapEnv_def comp_def
using assms by(auto simp: swapEnvDom_preserves_wls swapEnvIm_preserves_wls)

lemmas swapAll_preserve_wls =
swap_preserves_wls swapAbs_preserves_wls
swapInp_preserves_wls swapBinp_preserves_wls
swapEnv_preserves_wls

lemma swapped_preserves_wls:
assumes "wls s X" and "(X,Y) \<in> swapped"
shows "wls s Y" 
proof-
  have "(X,Y) \<in> swapped \<Longrightarrow> wls s X \<longrightarrow> wls s Y"
  by (induct rule: swapped.induct) auto
  thus ?thesis using assms by simp
qed

subsubsection {* Inversion rules for well-sortedness *}

lemma wlsAll_inversion:
"(wls s X \<longrightarrow>
  (\<forall> xs x. X = Var xs x \<longrightarrow> s = asSort xs) \<and>
  (\<forall> delta inp binp. goodInp inp \<and> goodBinp binp \<and> X = Op delta inp binp \<longrightarrow>
                     stOf delta = s \<and> wlsInp delta inp \<and> wlsBinp delta binp))
\<and>
(wlsAbs xs_s A \<longrightarrow>
 isInBar xs_s \<and>
 (\<forall> x X. good X \<and> A = Abs (fst xs_s) x X \<longrightarrow>
         wls (snd xs_s) X))
\<and>
(wlsInp delta inp \<longrightarrow> True)
\<and>
(wlsBinp delta binp \<longrightarrow> True)"
proof(induct rule: wls_wlsAbs_wlsInp_wlsBinp.induct)
  case (Abs xs s X x)
  then show ?case using swap_preserves_wls3 wls_imp_good 
  by (metis FixVars.Abs_ainj_ex FixVars_axioms snd_conv)
qed (auto simp: Abs_ainj_ex)
 
lemma conjLeft: "\<lbrakk>phi1 \<and> phi2; phi1 \<Longrightarrow> chi\<rbrakk> \<Longrightarrow> chi"
by blast

lemma conjRight: "\<lbrakk>phi1 \<and> phi2; phi2 \<Longrightarrow> chi\<rbrakk> \<Longrightarrow> chi"
by blast

(* For the next three lemmas, I could not use the simp, auto etc.
powerhorses freely -- for some reason, they loop\<dots> *)

lemma wls_inversion[rule_format]:
"wls s X \<longrightarrow>
 (\<forall> xs x. X = Var xs x \<longrightarrow> s = asSort xs) \<and>
 (\<forall> delta inp binp. goodInp inp \<and> goodBinp binp \<and> X = Op delta inp binp \<longrightarrow>
                    stOf delta = s \<and> wlsInp delta inp \<and> wlsBinp delta binp)"
using wlsAll_inversion 
[of s X undefined undefined undefined undefined undefined]  
by (rule conjLeft) 

lemma wlsAbs_inversion[rule_format]:
"wlsAbs (xs,s) A \<longrightarrow>
 isInBar (xs,s) \<and>
 (\<forall> x X. good X \<and> A = Abs xs x X \<longrightarrow> wls s X)"
using wlsAll_inversion
[of undefined undefined "(xs,s)" A undefined undefined undefined]
by auto 

lemma wls_Var_simp[simp]:
"wls s (Var xs x) =  (s = asSort xs)"
using wls_inversion by auto

lemma wls_Op_simp[simp]:
assumes "goodInp inp" and "goodBinp binp"
shows
"wls s (Op delta inp binp) =
 (stOf delta = s \<and> wlsInp delta inp \<and> wlsBinp delta binp)"
using Op assms wls_inversion by blast 

lemma wls_Abs_simp[simp]:
assumes "good X"
shows "wlsAbs (xs,s) (Abs xs x X) = (isInBar (xs,s) \<and> wls s X)"
using Abs assms wlsAbs_inversion by blast 

lemma wlsAll_inversion2:
"(wls s X \<longrightarrow> True)
\<and>
(wlsAbs xs_s A \<longrightarrow>
 isInBar xs_s \<and>
 (\<exists> x X. wls (snd xs_s) X \<and> A = Abs (fst xs_s) x X))
\<and>
(wlsInp delta inp \<longrightarrow> True)
\<and>
(wlsBinp delta binp \<longrightarrow> True)"
by (induct rule: wls_wlsAbs_wlsInp_wlsBinp.induct)
  (auto simp add: Abs_ainj_ex simp del: not_None_eq)

lemma wlsAbs_inversion2[rule_format]:
"wlsAbs (xs,s) A \<longrightarrow>
 isInBar (xs,s) \<and> (\<exists> x X. wls s X \<and> A = Abs xs x X)"
using wlsAll_inversion2 by auto

corollary wlsAbs_Abs_varSort:
assumes X: "good X" and wlsAbs: "wlsAbs (xs,s) (Abs xs' x X)"
shows "xs = xs'" 
by (metis Abs_ainj_all X wlsAbs wlsAbs_inversion2 wls_imp_good)

lemma wlsAbs:
"wlsAbs (xs,s) A \<longleftrightarrow> 
 isInBar (xs,s) \<and> (\<exists> x X. wls s X \<and> A = Abs xs x X)"
using Abs wlsAbs_inversion2 by blast

lemma wlsAbs_Abs[simp]:
assumes X: "good X"
shows "wlsAbs (xs',s) (Abs xs x X) = (isInBar (xs',s) \<and> xs = xs' \<and> wls s X)"
using assms wlsAbs_Abs_varSort by fastforce 

lemmas Cons_wls_simps =
wls_Var_simp wls_Op_simp wls_Abs_simp wlsAbs_Abs

subsection {* Induction principles for well-sorted terms *}

subsubsection {* Regular induction *}

(* See also the subsection on substitution of variables for variables
from the section on compositional properties
for an induction principle involving a choice between swap, subst and skeleton
for the abstraction case.  *)

theorem wls_templateInduct[case_names rel Var Op Abs]:
assumes
rel: "\<And> s X Y. \<lbrakk>wls s X;  (X,Y) \<in> rel s\<rbrakk> \<Longrightarrow> wls s Y \<and> skel Y = skel X" and
Var: "\<And> xs x. phi (asSort xs) (Var xs x)" and
Op:
"\<And> delta inp binp.
   \<lbrakk>wlsInp delta inp;  wlsBinp delta binp;
    liftAll2 phi (arOf delta) inp; liftAll2 phiAbs (barOf delta) binp\<rbrakk>
   \<Longrightarrow> phi (stOf delta) (Op delta inp binp)" and
Abs:
"\<And> s xs x X.
   \<lbrakk>isInBar (xs,s); wls s X; \<And> Y. (X,Y) \<in> rel s \<Longrightarrow> phi s Y\<rbrakk>
   \<Longrightarrow> phiAbs (xs,s) (Abs xs x X)"
shows
"(wls s X \<longrightarrow> phi s X) \<and>
 (wlsAbs (xs,s') A \<longrightarrow> phiAbs (xs,s') A)"
proof-
  have "(good X \<longrightarrow> (\<forall> s. wls s X \<longrightarrow> phi s X)) \<and>
        (goodAbs A \<longrightarrow> (\<forall> xs s. wlsAbs (xs,s) A \<longrightarrow> phiAbs (xs,s) A))"
  apply(induct rule: term_templateInduct[of "{(X,Y). \<exists> s. wls s X \<and> (X,Y) \<in> rel s}"])
  subgoal using rel wls_imp_good by blast 
  subgoal using Var by auto
  subgoal by (auto intro!: Op simp: wlsInp_iff wlsBinp_iff liftAll_def liftAll2_def)
  subgoal using Abs rel by simp blast . 
  thus ?thesis by auto
qed

theorem wls_rawInduct[case_names Var Op Abs]:
assumes
Var: "\<And> xs x. phi (asSort xs) (Var xs x)" and
Op:
"\<And> delta inp binp.
   \<lbrakk>wlsInp delta inp;  wlsBinp delta binp;
    liftAll2 phi (arOf delta) inp; liftAll2 phiAbs (barOf delta) binp\<rbrakk>
   \<Longrightarrow> phi (stOf delta) (Op delta inp binp)" and
Abs: "\<And> s xs x X. \<lbrakk>isInBar (xs,s); wls s X; phi s X\<rbrakk> \<Longrightarrow> phiAbs (xs,s) (Abs xs x X)"
shows
"(wls s X \<longrightarrow> phi s X) \<and>
 (wlsAbs (xs,s') A \<longrightarrow> phiAbs (xs,s') A)"
by (induct rule: wls_templateInduct[of "\<lambda>s. Id"]) (simp_all add: assms)

subsubsection {* Fresh induction *}

text {* First for an unspecified notion of parameter:  *}

theorem wls_templateInduct_fresh[case_names Par Rel Var Op Abs]:
fixes s X xs s' A phi phiAbs rel
and vars :: "'varSort \<Rightarrow> 'var set"
and terms :: "'sort \<Rightarrow> ('index,'bindex,'varSort,'var,'opSym)term set"
and abs :: "('varSort * 'sort) \<Rightarrow> ('index,'bindex,'varSort,'var,'opSym)abs set"
and envs :: "('index,'bindex,'varSort,'var,'opSym)env set"
assumes
PAR:
"\<And> xs us s.
   ( |vars xs| <o |UNIV :: 'var set| \<or> finite (vars xs)) \<and>
   ( |terms s| <o |UNIV :: 'var set| \<or> finite (terms s)) \<and>
   ( |abs (us,s)| <o |UNIV :: 'var set| \<or> finite (abs (us,s))) \<and>
   (\<forall> X \<in> terms s. wls s X) \<and>
   (\<forall> A \<in> abs (us,s). wlsAbs (us,s) A) \<and>
   ( |envs| <o |UNIV :: 'var set| \<or> finite (envs)) \<and>
   (\<forall> rho \<in> envs. wlsEnv rho)" and
rel: "\<And> s X Y. \<lbrakk>wls s X;  (X,Y) \<in> rel s\<rbrakk> \<Longrightarrow> wls s Y \<and> skel Y = skel X" and
Var: "\<And> xs x. phi (asSort xs) (Var xs x)" and
Op:
"\<And> delta inp binp.
    \<lbrakk>wlsInp delta inp; wlsBinp delta binp;
     liftAll2 (\<lambda>s X. phi s X) (arOf delta) inp;
     liftAll2 (\<lambda>(us,s) A. phiAbs (us,s) A) (barOf delta) binp\<rbrakk>
    \<Longrightarrow> phi (stOf delta) (Op delta inp binp)" and
Abs:
"\<And> s xs x X.
   \<lbrakk>isInBar (xs,s); wls s X;
    x \<notin> vars xs;
    \<And> s' Y. Y \<in> terms s' \<Longrightarrow> fresh xs x Y;
    \<And> xs' s' A. A \<in> abs (xs',s') \<Longrightarrow> freshAbs xs x A;
    \<And> rho. rho \<in> envs \<Longrightarrow> freshEnv xs x rho;
    \<And> Y. (X,Y) \<in> rel s \<Longrightarrow> phi s Y\<rbrakk>
   \<Longrightarrow> phiAbs (xs,s) (Abs xs x X)"
shows
"(wls s X \<longrightarrow> phi s X) \<and>
 (wlsAbs (xs,s') A \<longrightarrow> phiAbs (xs,s') A)"
proof-
  let ?terms = "\<Union> s. terms s"
  let ?abs = "\<Union> xs s. abs (xs,s)"
  have "\<forall> s. |terms s| <o |UNIV :: 'var set|"
  using PAR var_infinite_INNER finite_ordLess_infinite2 by blast
  hence 1:"|\<Union>s. terms s| <o |UNIV :: 'var set|"
  using sort_lt_var_INNER var_regular_INNER regular_UNION by blast
  have "\<forall> us s. |abs (us,s)| <o |UNIV :: 'var set|"
  using PAR var_infinite_INNER finite_ordLess_infinite2 by blast
  hence "\<forall> us. |\<Union>s. abs (us,s)| <o |UNIV :: 'var set|"
  by(auto simp add: sort_lt_var_INNER var_regular_INNER regular_UNION)
  hence 2: "|\<Union> us s. abs (us,s)| <o |UNIV :: 'var set|"
  using varSort_lt_var_INNER var_regular_INNER by(auto simp add: regular_UNION)
  (* *)
  have "(good X \<longrightarrow> (\<forall> s. wls s X \<longrightarrow> phi s X)) \<and>
        (goodAbs A \<longrightarrow> (\<forall> xs s. wlsAbs (xs,s) A \<longrightarrow> phiAbs (xs,s) A))"
  apply(induct rule: term_templateInduct_fresh
             [of vars ?terms ?abs envs
                 "{(X,Y). \<exists> s. wls s X \<and> (X,Y) \<in> rel s}"])
  subgoal for xs
  using PAR 1 2 apply simp_all using wls_imp_good wlsAbs_imp_goodAbs by blast+
  subgoal using assms by simp (meson wls_imp_good)
  subgoal using assms by simp
  subgoal using assms by simp  
    (smt liftAll2_def liftAll_def option.distinct(1) 
    option.sel wlsBinp.cases wlsInp_iff)
  subgoal using assms by simp metis . 
  thus ?thesis by auto
qed

text{* A version of the above not employing any relation for
  the abstraction case: *}

theorem wls_rawInduct_fresh[case_names Par Var Op Abs]:
fixes s X xs s' A phi phiAbs
and vars :: "'varSort \<Rightarrow> 'var set"
and terms :: "'sort \<Rightarrow> ('index,'bindex,'varSort,'var,'opSym)term set"
and abs :: "('varSort * 'sort) \<Rightarrow> ('index,'bindex,'varSort,'var,'opSym)abs set"
and envs :: "('index,'bindex,'varSort,'var,'opSym)env set"
assumes
PAR:
"\<And> xs us s.
   ( |vars xs| <o |UNIV :: 'var set| \<or> finite (vars xs)) \<and>
   ( |terms s| <o |UNIV :: 'var set| \<or> finite (terms s)) \<and>
   (\<forall> X \<in> terms s. wls s X) \<and>
   ( |abs (us,s)| <o |UNIV :: 'var set| \<or> finite (abs (us,s))) \<and>
   (\<forall> A \<in> abs (us,s). wlsAbs (us,s) A) \<and>
   ( |envs| <o |UNIV :: 'var set| \<or> finite (envs)) \<and>
   (\<forall> rho \<in> envs. wlsEnv rho)" and
Var: "\<And> xs x. phi (asSort xs) (Var xs x)" and
Op:
"\<And> delta inp binp.
   \<lbrakk>wlsInp delta inp; wlsBinp delta binp;
    liftAll2 (\<lambda>s X. phi s X) (arOf delta) inp;
    liftAll2 (\<lambda>(us,s) A. phiAbs (us,s) A) (barOf delta) binp\<rbrakk>
   \<Longrightarrow> phi (stOf delta) (Op delta inp binp)" and
Abs:
"\<And> s xs x X.
   \<lbrakk>isInBar (xs,s); wls s X;
    x \<notin> vars xs;
    \<And> s' Y. Y \<in> terms s' \<Longrightarrow> fresh xs x Y;
    \<And> us s' A. A \<in> abs (us,s') \<Longrightarrow> freshAbs xs x A;
    \<And> rho. rho \<in> envs \<Longrightarrow> freshEnv xs x rho;
    phi s X\<rbrakk>
   \<Longrightarrow> phiAbs (xs,s) (Abs xs x X)"
shows
"(wls s X \<longrightarrow> phi s X) \<and>
 (wlsAbs (xs,s') A \<longrightarrow> phiAbs (xs,s') A)"
apply(induct rule: wls_templateInduct_fresh[of vars terms abs envs "\<lambda>s. Id"])
using assms by auto

text{* Then for our notion of sorted parameter:  *}

theorem wls_induct_fresh[case_names Par Var Op Abs]:
fixes X :: "('index,'bindex,'varSort,'var,'opSym)term" and s and
      A :: "('index,'bindex,'varSort,'var,'opSym)abs" and xs s' and
      P :: "('index,'bindex,'varSort,'var,'opSym,'sort)paramS" and phi phiAbs
assumes
P: "wlsPar P" and
Var: "\<And> xs x. phi (asSort xs) (Var xs x)" and
Op:
"\<And> delta inp binp.
   \<lbrakk>wlsInp delta inp; wlsBinp delta binp;
    liftAll2 (\<lambda>s X. phi s X) (arOf delta) inp;
    liftAll2 (\<lambda>(us,s) A. phiAbs (us,s) A) (barOf delta) binp\<rbrakk>
   \<Longrightarrow> phi (stOf delta) (Op delta inp binp)" and
Abs:
"\<And> s xs x X.
   \<lbrakk>isInBar (xs,s); wls s X;
    x \<notin> varsOfS P xs;
    \<And> s' Y. Y \<in> termsOfS P s' \<Longrightarrow> fresh xs x Y;
    \<And> us s' A. A \<in> absOfS P (us,s') \<Longrightarrow> freshAbs xs x A;
    \<And> rho. rho \<in> envsOfS P \<Longrightarrow> freshEnv xs x rho;
    phi s X\<rbrakk>
   \<Longrightarrow> phiAbs (xs,s) (Abs xs x X)"
shows
"(wls s X \<longrightarrow> phi s X) \<and>
 (wlsAbs (xs,s') A \<longrightarrow> phiAbs (xs,s') A)"
proof(induct rule: wls_rawInduct_fresh
      [of "varsOfS P" "termsOfS P" "absOfS P" "envsOfS P" _ _ s X xs s' A])
  case (Par xs us s)
  then show ?case using assms by(cases P) simp
qed(insert assms, simp_all) 

subsubsection {* The syntactic constructs are almost free (on well-sorted terms) *}

(* Recall theorem Var_inj. *)

theorem wls_Op_inj[simp]:
assumes "wlsInp delta inp" and "wlsBinp delta binp"
and "wlsInp delta' inp'" and "wlsBinp delta' binp'"
shows
"(Op delta inp binp = Op delta' inp' binp') =
 (delta = delta' \<and> inp = inp' \<and> binp = binp')"
using assms by simp

lemma wls_Abs_ainj_all:
assumes "wls s X" and "wls s' X'"
shows
"(Abs xs x X = Abs xs' x' X') =
 (xs = xs' \<and>
  (\<forall> y. (y = x \<or> fresh xs y X) \<and> (y = x' \<or> fresh xs y X') \<longrightarrow>
        (X #[y \<and> x]_xs) = (X' #[y \<and> x']_xs)))"
using assms by(simp add: Abs_ainj_all)

theorem wls_Abs_swap_all:
assumes "wls s X" and "wls s X'"
shows
"(Abs xs x X = Abs xs x' X') =
 (\<forall> y. (y = x \<or> fresh xs y X) \<and> (y = x' \<or> fresh xs y X') \<longrightarrow>
       (X #[y \<and> x]_xs) = (X' #[y \<and> x']_xs))"
using assms by(simp add: wls_Abs_ainj_all)

lemma wls_Abs_ainj_ex:
assumes  "wls s X" and "wls s X'"
shows
"(Abs xs x X = Abs xs' x' X') =
 (xs = xs' \<and>
  (\<exists> y. y \<notin> {x,x'} \<and> fresh xs y X \<and> fresh xs y X' \<and>
        (X #[y \<and> x]_xs) = (X' #[y \<and> x']_xs)))"
using assms by(simp add: Abs_ainj_ex)

theorem wls_Abs_swap_ex:
assumes  "wls s X" and "wls s X'"
shows
"(Abs xs x X = Abs xs x' X') =
 (\<exists> y. y \<notin> {x,x'} \<and> fresh xs y X \<and> fresh xs y X' \<and>
       (X #[y \<and> x]_xs) = (X' #[y \<and> x']_xs))"
using assms by(simp add: wls_Abs_ainj_ex)

theorem wls_Abs_inj[simp]:
assumes "wls s X" and "wls s X'"
shows
"(Abs xs x X = Abs xs x X') =
 (X = X')"
using assms by (auto simp: wls_Abs_swap_all)

theorem wls_Abs_swap_cong[fundef_cong]:
assumes "wls s X" and "wls s X'"
and "fresh xs y X" and "fresh xs y X'"  and "(X #[y \<and> x]_xs) = (X' #[y \<and> x']_xs)"
shows "Abs xs x X = Abs xs x' X'"
using assms by (intro Abs_cong) auto

theorem wls_Abs_swap_fresh[simp]:
assumes "wls s X" and "fresh xs x' X"
shows "Abs xs x' (X #[x' \<and> x]_xs) = Abs xs x X"
using assms by(simp add: Abs_swap_fresh)

theorem wls_Var_diff_Op[simp]:
assumes "wlsInp delta inp" and "wlsBinp delta binp"
shows "Var xs x \<noteq> Op delta inp binp"
using assms by auto

theorem wls_Op_diff_Var[simp]:
assumes "wlsInp delta inp" and "wlsBinp delta binp"
shows "Op delta inp binp \<noteq> Var xs x"
using assms by auto

theorem wls_nchotomy:
assumes "wls s X"
shows
"(\<exists> xs x. asSort xs = s \<and> X = Var xs x) \<or>
 (\<exists> delta inp binp. stOf delta = s \<and> wlsInp delta inp \<and> wlsBinp delta binp
                    \<and> X = Op delta inp binp)"
 using assms wls.simps by force

lemmas wls_cases = wls_wlsAbs_wlsInp_wlsBinp.inducts(1)

lemmas wlsAbs_nchotomy = wlsAbs_inversion2 

theorem wlsAbs_cases:
assumes "wlsAbs (xs,s) A"
and "\<And> x X. \<lbrakk>isInBar (xs,s); wls s X\<rbrakk> \<Longrightarrow> phiAbs (xs,s) (Abs xs x X)"
shows "phiAbs (xs,s) A"
using assms wlsAbs_nchotomy by blast

lemma wls_disjoint:
assumes "wls s X" and "wls s' X"
shows "s = s'" 
using assms term_nchotomy wls_imp_good by fastforce
 
lemma wlsAbs_disjoint:
assumes "wlsAbs (xs,s) A" and "wlsAbs (xs',s') A"
shows "xs = xs' \<and> s = s'"
using assms abs_nchotomy wlsAbs_imp_goodAbs wls_disjoint by fastforce

lemmas wls_freeCons =
Var_inj wls_Op_inj wls_Var_diff_Op wls_Op_diff_Var wls_Abs_swap_fresh

subsection {* The non-construct operators preserve well-sortedness  *}

lemma idEnv_preserves_wls[simp]:
"wlsEnv idEnv" 
proof-
  have "goodEnv idEnv" by simp
  thus ?thesis unfolding wlsEnv_def goodEnv_def liftAll_def idEnv_def by auto
qed

lemma updEnv_preserves_wls[simp]:
assumes "wlsEnv rho" and "wls (asSort xs) X"
shows "wlsEnv (rho [x \<leftarrow> X]_xs)" 
proof-
  {fix ys
   let ?L = "{y. rho ys y \<noteq> None}"
   let ?R = "{y. (rho [x \<leftarrow> X]_xs) ys y \<noteq> None}"
   have "?R \<le> ?L Un {x}" by auto
   hence "|?R| \<le>o |?L Un {x}|" by simp
   moreover
   {have "|?L| <o |UNIV :: 'var set|"
    using assms unfolding wlsEnv_def by simp
    moreover have "|{x}| <o |UNIV :: 'var set|"
    using var_infinite_INNER finite_ordLess_infinite by auto
    ultimately have "|?L Un {x}| <o  |UNIV :: 'var set|"
    using var_infinite_INNER card_of_Un_ordLess_infinite by blast
   }
   ultimately have "|?R| <o |UNIV :: 'var set|"
   using ordLeq_ordLess_trans by blast
  } note 0 = this
  have 1: "goodEnv (rho [x \<leftarrow> X]_xs)" using assms by simp
  show ?thesis unfolding wlsEnv_def goodEnv_def 
   using 0 1 assms unfolding wlsEnv_def liftAll_def by auto
qed

lemma getEnv_preserves_wls[simp]:
assumes "wlsEnv rho" and "rho xs x = Some X"
shows "wls (asSort xs) X"
using assms unfolding wlsEnv_def liftAll_def by simp

lemmas envOps_preserve_wls =
idEnv_preserves_wls updEnv_preserves_wls
getEnv_preserves_wls

lemma psubstAll_preserves_wlsAll:
assumes P: "wlsPar P"
shows
"(wls s X \<longrightarrow> (\<forall> rho \<in> envsOfS P. wls s (X #[rho]))) \<and>
 (wlsAbs (xs,s') A \<longrightarrow> (\<forall> rho \<in> envsOfS P. wlsAbs (xs,s') (A $[rho])))"
proof(induct rule: wls_induct_fresh[of P]) 
  case (Var xs x)
  show ?case 
  using assms apply safe subgoal for rho
  apply(cases "rho xs x") apply simp_all
  using getEnv_preserves_wls wlsPar_def by blast+ .
next
  case (Op delta inp binp)
  then show ?case using assms
  by (auto simp: 
  wlsInp_iff psubstInp_def wlsBinp_iff psubstBinp_def liftAll2_def lift_def 
  sameDom_def intro!: Op_preserves_wls split: option.splits)  
qed(insert assms, auto) 

lemma psubst_preserves_wls[simp]:
"\<lbrakk>wls s X; wlsEnv rho\<rbrakk> \<Longrightarrow> wls s (X #[rho])"
using psubstAll_preserves_wlsAll[of "ParS (\<lambda>_. []) (\<lambda>_. []) (\<lambda>_. []) [rho]"]
unfolding wlsPar_def by auto

lemma psubstAbs_preserves_wls[simp]:
"\<lbrakk>wlsAbs (xs,s) A; wlsEnv rho\<rbrakk> \<Longrightarrow> wlsAbs (xs,s) (A $[rho])"
using psubstAll_preserves_wlsAll[of "ParS (\<lambda>_. []) (\<lambda>_. []) (\<lambda>_. []) [rho]"]
unfolding wlsPar_def by auto

lemma psubstInp_preserves_wls[simp]:
assumes "wlsInp delta inp" and "wlsEnv rho"
shows "wlsInp delta (inp %[rho])"
using assms by (auto simp: wlsInp_iff psubstInp_def liftAll2_def lift_def 
 sameDom_def intro!: Op_preserves_wls split: option.splits)
 
lemma psubstBinp_preserves_wls[simp]:
assumes "wlsBinp delta binp" and "wlsEnv rho"
shows "wlsBinp delta (binp %%[rho])"
using assms by (auto simp: wlsBinp_iff psubstBinp_def liftAll2_def lift_def 
 sameDom_def intro!: Op_preserves_wls split: option.splits)

lemma psubstEnv_preserves_wls[simp]:
assumes "wlsEnv rho" and "wlsEnv rho'"
shows "wlsEnv (rho &[rho'])"
proof-
  {fix ys y Y
   assume "(rho &[rho']) ys y = Some Y"
   hence "wls (asSort ys) Y"
   using assms unfolding psubstEnv_def wlsEnv_def liftAll_def 
   by (cases "rho ys y") (auto simp add: assms) 
  }  
  moreover have "goodEnv (rho &[rho'])" using assms by simp
  ultimately show ?thesis 
  unfolding goodEnv_def wlsEnv_def psubstEnv_def wlsEnv_def liftAll_def 
  by (auto simp add: assms) 
qed

lemmas psubstAll_preserve_wls =
psubst_preserves_wls psubstAbs_preserves_wls
psubstInp_preserves_wls psubstBinp_preserves_wls
psubstEnv_preserves_wls

lemma subst_preserves_wls[simp]:
assumes "wls s X" and "wls (asSort ys) Y"
shows "wls s (X #[Y / y]_ys)"
using assms unfolding subst_def by simp

lemma substAbs_preserves_wls[simp]:
assumes "wlsAbs (xs,s) A" and "wls (asSort ys) Y"
shows "wlsAbs (xs,s) (A $[Y / y]_ys)"
using assms unfolding substAbs_def by simp

lemma substInp_preserves_wls[simp]:
assumes "wlsInp delta inp" and "wls (asSort ys) Y"
shows "wlsInp delta (inp %[Y / y]_ys)"
using assms unfolding substInp_def by simp

lemma substBinp_preserves_wls[simp]:
assumes "wlsBinp delta binp" and "wls (asSort ys) Y"
shows "wlsBinp delta (binp %%[Y / y]_ys)"
using assms unfolding substBinp_def by simp

lemma substEnv_preserves_wls[simp]:
assumes "wlsEnv rho" and "wls (asSort ys) Y"
shows "wlsEnv (rho &[Y / y]_ys)"
using assms unfolding substEnv_def by simp

lemmas substAll_preserve_wls =
subst_preserves_wls substAbs_preserves_wls
substInp_preserves_wls substBinp_preserves_wls
substEnv_preserves_wls

lemma vsubst_preserves_wls[simp]:
assumes "wls s Y"
shows "wls s (Y #[x1 // x]_xs)"
using assms unfolding vsubst_def by simp

lemma vsubstAbs_preserves_wls[simp]:
assumes "wlsAbs (us,s) A"
shows "wlsAbs (us,s) (A $[x1 // x]_xs)"
using assms unfolding vsubstAbs_def by simp

lemma vsubstInp_preserves_wls[simp]:
assumes "wlsInp delta inp"
shows "wlsInp delta (inp %[x1 // x]_xs)"
using assms unfolding vsubstInp_def by simp

lemma vsubstBinp_preserves_wls[simp]:
assumes "wlsBinp delta binp"
shows "wlsBinp delta (binp %%[x1 // x]_xs)"
using assms unfolding vsubstBinp_def by simp

lemma vsubstEnv_preserves_wls[simp]:
assumes "wlsEnv rho"
shows "wlsEnv (rho &[x1 // x]_xs)"
using assms unfolding vsubstEnv_def by simp

lemmas vsubstAll_preserve_wls = vsubst_preserves_wls vsubstAbs_preserves_wls
vsubstInp_preserves_wls vsubstBinp_preserves_wls vsubstEnv_preserves_wls

lemmas all_preserve_wls = Cons_preserve_wls swapAll_preserve_wls psubstAll_preserve_wls envOps_preserve_wls
substAll_preserve_wls vsubstAll_preserve_wls

subsection {* Simplification rules for swapping, substitution, freshness and skeleton *}

(* Recall theorem swap_Var_simp.  *)

theorem wls_swap_Op_simp[simp]:
assumes "wlsInp delta inp" and "wlsBinp delta binp"
shows
"((Op delta inp binp) #[x1 \<and> x2]_xs) =
 Op delta (inp %[x1 \<and> x2]_xs) (binp %%[x1 \<and> x2]_xs)"
using assms by simp

theorem wls_swapAbs_simp[simp]:
assumes "wls s X"
shows "((Abs xs x X) $[y1 \<and> y2]_ys) = Abs xs (x @xs[y1 \<and> y2]_ys) (X #[y1 \<and> y2]_ys)"
using assms by simp

lemmas wls_swapAll_simps =
swap_Var_simp wls_swap_Op_simp wls_swapAbs_simp

(* Recall theorem fresh_Var_simp. *)

theorem wls_fresh_Op_simp[simp]:
assumes "wlsInp delta inp" and "wlsBinp delta binp"
shows
"fresh xs x (Op delta inp binp) =
 (freshInp xs x inp \<and> freshBinp xs x binp)"
using assms by simp

theorem wls_freshAbs_simp[simp]:
assumes "wls s X"
shows "freshAbs ys y (Abs xs x X) = (ys = xs \<and> y = x \<or> fresh ys y X)"
using assms by simp

lemmas wls_freshAll_simps =
fresh_Var_simp wls_fresh_Op_simp wls_freshAbs_simp

(* Recall theorem skel_Var_simp *)

theorem wls_skel_Op_simp[simp]:
assumes "wlsInp delta inp" and "wlsBinp delta binp"
shows
"skel (Op delta inp binp) = Branch (skelInp inp) (skelBinp binp)"
using assms by simp

(* The next is not a simplification rule, but belongs here: *)

lemma wls_skelInp_def2:
assumes "wlsInp delta inp"
shows "skelInp inp = lift skel inp"
using assms by(simp add: skelInp_def2)

lemma wls_skelBinp_def2:
assumes "wlsBinp delta binp"
shows "skelBinp binp = lift skelAbs binp"
using assms by(simp add: skelBinp_def2)

theorem wls_skelAbs_simp[simp]:
assumes "wls s X"
shows "skelAbs (Abs xs x X) = Branch (\<lambda>i. Some (skel X)) Map.empty"
using assms by simp

lemmas wls_skelAll_simps =
skel_Var_simp wls_skel_Op_simp wls_skelAbs_simp

theorem wls_psubst_Var_simp1[simp]:
assumes "wlsEnv rho" and "rho xs x = None"
shows "((Var xs x) #[rho]) = Var xs x"
using assms by simp

theorem wls_psubst_Var_simp2[simp]:
assumes "wlsEnv rho" and "rho xs x = Some X"
shows "((Var xs x) #[rho]) = X"
using assms by simp

theorem wls_psubst_Op_simp[simp]:
assumes "wlsInp delta inp" and "wlsBinp delta binp" and "wlsEnv rho"
shows
"((Op delta inp binp) #[rho]) = Op delta (inp %[rho]) (binp %%[rho])"
using assms by simp

theorem wls_psubstAbs_simp[simp]:
assumes "wls s X" and "wlsEnv rho" and "freshEnv xs x rho"
shows "((Abs xs x X) $[rho]) = Abs xs x (X #[rho])"
  using assms by simp

lemmas wls_psubstAll_simps =
wls_psubst_Var_simp1 wls_psubst_Var_simp2 wls_psubst_Op_simp wls_psubstAbs_simp

(* Recall lemmas getEnv_idEnv, getEnv_updEnv1 and getEnv_updEnv2. *)

lemmas wls_envOps_simps =
getEnv_idEnv getEnv_updEnv1 getEnv_updEnv2

theorem wls_subst_Var_simp1[simp]:
assumes "wls (asSort ys) Y"
and "ys \<noteq> xs \<or> y \<noteq> x "
shows "((Var xs x) #[Y / y]_ys) = Var xs x"
using assms unfolding subst_def by auto

theorem wls_subst_Var_simp2[simp]:
assumes "wls (asSort xs) Y"
shows "((Var xs x) #[Y / x]_xs) = Y"
using assms unfolding subst_def by auto

theorem wls_subst_Op_simp[simp]:
assumes "wls (asSort ys) Y"
 and "wlsInp delta inp" and "wlsBinp delta binp"
shows
"((Op delta inp binp) #[Y / y]_ys) =
 Op delta (inp %[Y / y]_ys) (binp %%[Y / y]_ys)"
using assms unfolding subst_def substInp_def
                      substAbs_def substBinp_def by auto

theorem wls_substAbs_simp[simp]:
assumes "wls (asSort ys) Y"
and "wls s X" and "xs \<noteq> ys \<or> x \<noteq> y" and "fresh xs x Y"
shows "((Abs xs x X) $[Y / y]_ys) = Abs xs x (X #[Y / y]_ys)"
proof-
  have "freshEnv xs x (idEnv [y \<leftarrow> Y]_ys)" unfolding freshEnv_def liftAll_def
  using assms by simp
  thus ?thesis using assms unfolding subst_def substAbs_def by auto
qed

lemmas wls_substAll_simps =
wls_subst_Var_simp1 wls_subst_Var_simp2 wls_subst_Op_simp wls_substAbs_simp

(* Recall theorem vsubst_Var_simp. *)

theorem wls_vsubst_Op_simp[simp]:
assumes "wlsInp delta inp" and "wlsBinp delta binp"
shows
"((Op delta inp binp) #[y1 // y]_ys) =
 Op delta (inp %[y1 // y]_ys) (binp %%[y1 // y]_ys)"
using assms unfolding vsubst_def vsubstInp_def
                      vsubstAbs_def vsubstBinp_def by simp

theorem wls_vsubstAbs_simp[simp]:
assumes "wls s X" and
        "xs \<noteq> ys \<or> x \<notin> {y,y1}"
shows "((Abs xs x X) $[y1 // y]_ys) = Abs xs x (X #[y1 // y]_ys)"
using assms unfolding vsubst_def vsubstAbs_def by simp

lemmas wls_vsubstAll_simps =
vsubst_Var_simp wls_vsubst_Op_simp wls_vsubstAbs_simp

(* Recall theorem swap_swapped. *)

theorem wls_swapped_skel:
assumes "wls s X" and "(X,Y) \<in> swapped"
shows "skel Y = skel X"
apply(rule swapped_skel) using assms by auto

theorem wls_obtain_rep:
assumes "wls s X" and FRESH: "fresh xs x' X"
shows "\<exists> X'. skel X' = skel X \<and> (X,X') \<in> swapped \<and> wls s X' \<and> Abs xs x X = Abs xs x' X'"
proof-
  have 0: "skel (X #[x' \<and> x]_xs) = skel X" using assms by(simp add: skel_swap)
  have 1: "wls s (X #[x' \<and> x]_xs)" using assms swap_preserves_wls by auto
  have 2: "(X, X #[x' \<and> x]_xs) \<in> swapped" using Var swap_swapped by auto
  show ?thesis using assms 0 1 2 by fastforce
qed

lemmas wls_allOpers_simps =
wls_swapAll_simps
wls_freshAll_simps
wls_skelAll_simps
wls_envOps_simps
wls_psubstAll_simps
wls_substAll_simps
wls_vsubstAll_simps

subsection {* The ability to pick fresh variables *}

theorem wls_single_non_fresh_ordLess_var:
"wls s X \<Longrightarrow> |{x. \<not> fresh xs x X}| <o |UNIV :: 'var set|"
by(simp add: single_non_fresh_ordLess_var)

theorem wls_single_non_freshAbs_ordLess_var:
"wlsAbs (us,s) A \<Longrightarrow> |{x. \<not> freshAbs xs x A}| <o |UNIV :: 'var set|"
by(simp add: single_non_freshAbs_ordLess_var)

theorem wls_obtain_fresh:
fixes V::"'varSort \<Rightarrow> 'var set" and
      XS::"'sort \<Rightarrow> ('index,'bindex,'varSort,'var,'opSym)term set" and
      AS::"'varSort \<Rightarrow> 'sort \<Rightarrow> ('index,'bindex,'varSort,'var,'opSym)abs set" and
      Rho::"('index,'bindex,'varSort,'var,'opSym)env set" and zs
assumes VVar: "\<forall> xs. |V xs| <o |UNIV :: 'var set| \<or> finite (V xs)"
and XSVar: "\<forall> s. |XS s| <o |UNIV :: 'var set| \<or> finite (XS s)"
and ASVar: "\<forall> xs s. |AS xs s| <o |UNIV :: 'var set| \<or> finite (AS xs s)"
and XSwls: "\<forall> s. \<forall> X \<in> XS s. wls s X"
and ASwls: "\<forall> xs s. \<forall> A \<in> AS xs s. wlsAbs (xs,s) A"
and RhoVar: "|Rho| <o |UNIV :: 'var set| \<or> finite Rho"
and Rhowls: "\<forall> rho \<in> Rho. wlsEnv rho"
shows
"\<exists> z. (\<forall> xs. z \<notin> V xs) \<and>
      (\<forall> s. \<forall> X \<in> XS s. fresh zs z X) \<and>
      (\<forall> xs s. \<forall> A \<in> AS xs s. freshAbs zs z A) \<and>
      (\<forall> rho \<in> Rho. freshEnv zs z rho)"
proof-
  let ?VG = "\<Union> xs. V xs"    let ?XSG = "\<Union> s. XS s"   let ?ASG = "\<Union> xs s. AS xs s"
  have "\<forall> xs. |V xs| <o |UNIV :: 'var set|" using VVar finite_ordLess_var by auto
  hence 1: "|?VG| <o |UNIV :: 'var set|"
  using var_regular_INNER varSort_lt_var_INNER regular_UNION by blast
  have "\<forall> s. |XS s| <o |UNIV :: 'var set|" using XSVar finite_ordLess_var by auto
  hence 2: "|?XSG| <o |UNIV :: 'var set|"
  using var_regular_INNER sort_lt_var_INNER regular_UNION by blast
  have "\<forall> xs s. |AS xs s| <o |UNIV :: 'var set|" using ASVar finite_ordLess_var by auto
  hence "\<forall> xs. |\<Union> s. AS xs s| <o |UNIV :: 'var set|"
  using var_regular_INNER sort_lt_var_INNER regular_UNION by blast
  hence 3: "|?ASG| <o |UNIV :: 'var set|"
  using var_regular_INNER varSort_lt_var_INNER by (auto simp add: regular_UNION)
  have "\<exists> z. z \<notin> ?VG \<and>
             (\<forall> X \<in> ?XSG. fresh zs z X) \<and>
             (\<forall> A \<in> ?ASG. freshAbs zs z A) \<and>
             (\<forall> rho \<in> Rho. freshEnv zs z rho)"
  using assms 1 2 3 by (intro obtain_fresh) fastforce+
  thus ?thesis by auto
qed

theorem wls_obtain_fresh_paramS:
assumes "wlsPar P"
shows
"\<exists> z.
 (\<forall> xs. z \<notin> varsOfS P xs) \<and>
 (\<forall> s. \<forall> X \<in> termsOfS P s. fresh zs z X) \<and>
 (\<forall> us s. \<forall> A \<in> absOfS P (us,s). freshAbs zs z A) \<and>
 (\<forall> rho \<in> envsOfS P. freshEnv zs z rho)"
using assms  by(cases P) (auto intro: wls_obtain_fresh)

lemma wlsAbs_freshAbs_nchotomy:
assumes A: "wlsAbs (xs,s) A" and fresh: "freshAbs xs x A"
shows "\<exists> X. wls s X \<and> A = Abs xs x X"
proof-
  {assume "wlsAbs (xs,s) A"
   hence "freshAbs xs x A \<longrightarrow> (\<exists> X. wls s X \<and> A = Abs xs x X)"
   using fresh wls_obtain_rep[of s _ xs x] by (fastforce elim!: wlsAbs_cases)
  }
  thus ?thesis using assms by auto
qed

theorem wlsAbs_fresh_nchotomy:
assumes A: "wlsAbs (xs,s) A" and P: "wlsPar P"
shows "\<exists> x X. A = Abs xs x X \<and>
               wls s X \<and>
               (\<forall> ys. x \<notin> varsOfS P ys) \<and>
               (\<forall> s'. \<forall> Y \<in> termsOfS P s'. fresh xs x Y) \<and>
               (\<forall> us s'. \<forall> B \<in> absOfS P (us,s'). freshAbs xs x B) \<and>
               (\<forall> rho \<in> envsOfS P. freshEnv xs x rho)"
proof-
  let ?chi =
  "\<lambda> x. (\<forall> xs. x \<notin> varsOfS P xs) \<and>
        (\<forall> s'. \<forall> Y \<in> termsOfS P s'. fresh xs x Y) \<and>
        (\<forall> us s'.\<forall> B \<in> (if us = xs \<and> s' = s then {A} else {}) \<union> absOfS P (us,s'). freshAbs xs x B) \<and>
        (\<forall> rho \<in> envsOfS P. freshEnv xs x rho)"
  have "\<exists> x. ?chi x" 
  using A P by (intro wls_obtain_fresh) (cases P, auto)+
  then obtain x where 1: "?chi x" by blast
  hence "freshAbs xs x A" by fastforce
  then obtain X where X: "wls s X" and 2: "A = Abs xs x X"
  using A 1 wlsAbs_freshAbs_nchotomy[of xs s A x] by auto
  thus ?thesis using 1 by blast
qed

theorem wlsAbs_fresh_cases:
assumes "wlsAbs (xs,s) A" and "wlsPar P"
and "\<And> x X.
          \<lbrakk>wls s X;
           \<And> ys. x \<notin> varsOfS P ys;
           \<And> s' Y. Y \<in> termsOfS P s' \<Longrightarrow> fresh xs x Y;
           \<And> us s' B. B \<in> absOfS P (us,s') \<Longrightarrow> freshAbs xs x B;
           \<And> rho. rho \<in> envsOfS P \<Longrightarrow> freshEnv xs x rho\<rbrakk>
           \<Longrightarrow> phi (xs,s) (Abs xs x X) P"
shows "phi (xs,s) A P"
by (metis assms wlsAbs_fresh_nchotomy)
 

subsection {* Compositionality properties of freshness and swapping *}

subsubsection {* W.r.t. terms *}

theorem wls_swap_ident[simp]:
assumes "wls s X"
shows "(X #[x \<and> x]_xs) = X"
using assms by simp

theorem wls_swap_compose:
assumes "wls s X"
shows "((X #[x \<and> y]_zs) #[x' \<and> y']_zs') =
       ((X #[x' \<and> y']_zs') #[(x @zs[x' \<and> y']_zs') \<and> (y @zs[x' \<and> y']_zs')]_zs)"
using assms by (intro swap_compose) auto

theorem wls_swap_commute:
"\<lbrakk>wls s X; zs \<noteq> zs' \<or> {x,y} \<inter> {x',y'} = {}\<rbrakk> \<Longrightarrow>
 ((X #[x \<and> y]_zs) #[x' \<and> y']_zs') = ((X #[x' \<and> y']_zs') #[x \<and> y]_zs)"
by (intro swap_commute) auto

theorem wls_swap_involutive[simp]:
assumes "wls s X"
shows "((X #[x \<and> y]_zs) #[x \<and> y]_zs) = X"
using assms by simp

theorem wls_swap_inj[simp]:
assumes "wls s X" and "wls s X'"
shows
"((X #[x \<and> y]_zs) = (X' #[x \<and> y]_zs)) =
 (X = X')"
using assms by (metis wls_swap_involutive)

(* Recall theorem swap_sym. *)

theorem wls_swap_involutive2[simp]:
assumes "wls s X"
shows "((X #[x \<and> y]_zs) #[y \<and> x]_zs) = X"
using assms by (simp  add: swap_sym)

theorem wls_swap_preserves_fresh[simp]:
assumes "wls s X"
shows "fresh xs (x @xs[y1 \<and> y2]_ys) (X #[y1 \<and> y2]_ys) = fresh xs x X"
using assms by simp

theorem wls_swap_preserves_fresh_distinct:
assumes "wls s X" and
       "xs \<noteq> ys \<or> x \<notin> {y1,y2}"
shows "fresh xs x (X #[y1 \<and> y2]_ys) = fresh xs x X"
using assms by(intro swap_preserves_fresh_distinct) auto

theorem wls_fresh_swap_exchange1:
assumes "wls s X"
shows "fresh xs x2 (X #[x1 \<and> x2]_xs) = fresh xs x1 X"
using assms by (intro fresh_swap_exchange1) auto

theorem wls_fresh_swap_exchange2:
assumes "wls s X"
shows "fresh xs x2 (X #[x2 \<and> x1]_xs) = fresh xs x1 X"
using assms by (intro fresh_swap_exchange2) fastforce+

theorem wls_fresh_swap_id[simp]:
assumes "wls s X" and "fresh xs x1 X"  and "fresh xs x2 X"
shows "(X #[x1 \<and> x2]_xs) = X"
using assms by simp

theorem wls_fresh_swap_compose:
assumes "wls s X" and "fresh xs y X"  and "fresh xs z X"
shows "((X #[y \<and> x]_xs) #[z \<and> y]_xs) = (X #[z \<and> x]_xs)"
using assms by (intro fresh_swap_compose) auto

theorem wls_skel_swap:
assumes "wls s X"
shows "skel (X #[x1 \<and> x2]_xs) = skel X"
using assms by (intro skel_swap) auto

subsubsection {* W.r.t. environments *}

theorem wls_swapEnv_ident[simp]:
assumes "wlsEnv rho"
shows "(rho &[x \<and> x]_xs) = rho"
using assms by simp

theorem wls_swapEnv_compose:
assumes "wlsEnv rho"
shows "((rho &[x \<and> y]_zs) &[x' \<and> y']_zs') =
       ((rho &[x' \<and> y']_zs') &[(x @zs[x' \<and> y']_zs') \<and> (y @zs[x' \<and> y']_zs')]_zs)"
using assms by (intro swapEnv_compose) auto

theorem wls_swapEnv_commute:
"\<lbrakk>wlsEnv rho; zs \<noteq> zs' \<or> {x,y} \<inter> {x',y'} = {}\<rbrakk> \<Longrightarrow>
 ((rho &[x \<and> y]_zs) &[x' \<and> y']_zs') = ((rho &[x' \<and> y']_zs') &[x \<and> y]_zs)"
by (intro swapEnv_commute) fastforce+

theorem wls_swapEnv_involutive[simp]:
assumes "wlsEnv rho"
shows "((rho &[x \<and> y]_zs) &[x \<and> y]_zs) = rho"
using assms by simp

theorem wls_swapEnv_inj[simp]:
assumes "wlsEnv rho" and "wlsEnv rho'"
shows
"((rho &[x \<and> y]_zs) = (rho' &[x \<and> y]_zs)) =
 (rho = rho')" 
by (metis assms wls_swapEnv_involutive) 

(* Recall theorem swapEnv_sym. *)

theorem wls_swapEnv_involutive2[simp]:
assumes "wlsEnv rho"
shows "((rho &[x \<and> y]_zs) &[y \<and> x]_zs) = rho"
using assms by(simp add: swapEnv_sym)

theorem wls_swapEnv_preserves_freshEnv[simp]:
assumes "wlsEnv rho"
shows "freshEnv xs (x @xs[y1 \<and> y2]_ys) (rho &[y1 \<and> y2]_ys) = freshEnv xs x rho"
using assms by simp

theorem wls_swapEnv_preserves_freshEnv_distinct:
assumes "wlsEnv rho"
       "xs \<noteq> ys \<or> x \<notin> {y1,y2}"
shows "freshEnv xs x (rho &[y1 \<and> y2]_ys) = freshEnv xs x rho"
using assms by (intro swapEnv_preserves_freshEnv_distinct) auto

theorem wls_freshEnv_swapEnv_exchange1:
assumes "wlsEnv rho"
shows "freshEnv xs x2 (rho &[x1 \<and> x2]_xs) = freshEnv xs x1 rho"
using assms by (intro freshEnv_swapEnv_exchange1) auto

theorem wls_freshEnv_swapEnv_exchange2:
assumes "wlsEnv rho"
shows "freshEnv xs x2 (rho &[x2 \<and> x1]_xs) = freshEnv xs x1 rho"
using assms by (intro freshEnv_swapEnv_exchange2) auto

theorem wls_freshEnv_swapEnv_id[simp]:
assumes "wlsEnv rho" and "freshEnv xs x1 rho" and "freshEnv xs x2 rho"
shows "(rho &[x1 \<and> x2]_xs) = rho"
using assms by simp

theorem wls_freshEnv_swapEnv_compose:
assumes "wlsEnv rho" and "freshEnv xs y rho" and "freshEnv xs z rho"
shows "((rho &[y \<and> x]_xs) &[z \<and> y]_xs) = (rho &[z \<and> x]_xs)"
using assms by (intro freshEnv_swapEnv_compose) auto

subsubsection {* W.r.t. abstractions *}

theorem wls_swapAbs_ident[simp]:
"wlsAbs (us,s) A \<Longrightarrow> (A $[x \<and> x]_xs) = A"
by (elim wlsAbs_cases) auto

theorem wls_swapAbs_compose:
"wlsAbs (us,s) A \<Longrightarrow>
 ((A $[x \<and> y]_zs) $[x' \<and> y']_zs') =
 ((A $[x' \<and> y']_zs') $[(x @zs[x' \<and> y']_zs') \<and> (y @zs[x' \<and> y']_zs')]_zs)"
by (erule wlsAbs_cases) (simp, metis sw_compose wls_swap_compose)

theorem wls_swapAbs_commute:
assumes "zs \<noteq> zs' \<or> {x,y} \<inter> {x',y'} = {}"
shows
"wlsAbs (us,s) A \<Longrightarrow>
 ((A $[x \<and> y]_zs) $[x' \<and> y']_zs') = ((A $[x' \<and> y']_zs') $[x \<and> y]_zs)"
using assms by (elim wlsAbs_cases) (simp add: sw_commute wls_swap_commute)

theorem wls_swapAbs_involutive[simp]:
"wlsAbs (us,s) A \<Longrightarrow> ((A $[x \<and> y]_zs) $[x \<and> y]_zs) = A"
by (erule wlsAbs_cases) simp_all

theorem wls_swapAbs_sym:
"wlsAbs (us,s) A \<Longrightarrow> (A $[x \<and> y]_zs) = (A $[y \<and> x]_zs)"
by (erule wlsAbs_cases) (auto simp add: swap_sym sw_sym)

theorem wls_swapAbs_inj[simp]:
assumes "wlsAbs (us,s) A" and "wlsAbs (us,s) A'"
shows
"((A $[x \<and> y]_zs) = (A' $[x \<and> y]_zs)) =
 (A = A')" 
by (metis assms wls_swapAbs_involutive)

theorem wls_swapAbs_involutive2[simp]:
"wlsAbs (us,s) A \<Longrightarrow> ((A $[x \<and> y]_zs) $[y \<and> x]_zs) = A"
using wls_swapAbs_sym[of us s A zs x y] by auto

theorem wls_swapAbs_preserves_freshAbs[simp]:
"wlsAbs (us,s) A
 \<Longrightarrow> freshAbs xs (x @xs[y1 \<and> y2]_ys) (A $[y1 \<and> y2]_ys) = freshAbs xs x A"
by (erule wlsAbs_cases)   
  (simp_all add: sw_def wls_fresh_swap_exchange1 wls_fresh_swap_exchange2 
wls_swap_preserves_fresh_distinct) 

theorem wls_swapAbs_preserves_freshAbs_distinct:
"\<lbrakk>wlsAbs (us,s) A; xs \<noteq> ys \<or> x \<notin> {y1,y2}\<rbrakk>
 \<Longrightarrow> freshAbs xs x (A $[y1 \<and> y2]_ys) = freshAbs xs x A"
apply(erule wlsAbs_cases) apply simp_all
unfolding sw_def by (auto simp: wls_swap_preserves_fresh_distinct)

theorem wls_freshAbs_swapAbs_exchange1:
"wlsAbs (us,s) A
 \<Longrightarrow> freshAbs xs x2 (A $[x1 \<and> x2]_xs) = freshAbs xs x1 A"
apply(erule wlsAbs_cases) apply simp_all
unfolding sw_def by (auto simp add: wls_fresh_swap_exchange1)

theorem wls_freshAbs_swapAbs_exchange2:
"wlsAbs (us,s) A
 \<Longrightarrow> freshAbs xs x2 (A $[x2 \<and> x1]_xs) = freshAbs xs x1 A"
apply(erule wlsAbs_cases) apply simp_all
unfolding sw_def by (auto simp add: wls_fresh_swap_exchange2)

theorem wls_freshAbs_swapAbs_id[simp]:
assumes "wlsAbs (us,s) A"
and "freshAbs xs x1 A" and "freshAbs xs x2 A"
shows "(A $[x1 \<and> x2]_xs) = A"
using assms by simp

lemma wls_freshAbs_swapAbs_compose_aux:
"\<lbrakk>wlsAbs (us,s) A; wlsPar P\<rbrakk> \<Longrightarrow>
 \<forall> x y z. {x,y,z} \<subseteq> varsOfS P xs \<and> freshAbs xs y A \<and> freshAbs xs z A \<longrightarrow>
           ((A $[y \<and> x]_xs) $[z \<and> y]_xs) = (A $[z \<and> x]_xs)"
apply(erule wlsAbs_fresh_cases)  
by simp_all (metis fresh_swap_compose sw_def wls_imp_good) 

theorem wls_freshAbs_swapAbs_compose:
assumes "wlsAbs (us,s) A"
and "freshAbs xs y A"  and "freshAbs xs z A"
shows "((A $[y \<and> x]_xs) $[z \<and> y]_xs) = (A $[z \<and> x]_xs)"
proof-
  let ?P =
  "ParS (\<lambda>xs'. if xs' = xs then [x,y,z] else []) (\<lambda>s.[]) (\<lambda>_. []) [] ::
  ('index, 'bindex, 'varSort, 'var, 'opSym, 'sort) paramS"
  show ?thesis
  using assms wls_freshAbs_swapAbs_compose_aux[of us s A ?P xs]
  unfolding wlsPar_def by simp
qed

theorem wls_skelAbs_swapAbs:
"wlsAbs (us,s) A
 \<Longrightarrow> skelAbs (A $[x1 \<and> x2]_xs) = skelAbs A"
by (erule wlsAbs_cases) (auto simp: wls_skel_swap)

lemmas wls_swapAll_freshAll_otherSimps =
wls_swap_ident wls_swap_involutive wls_swap_inj wls_swap_involutive2 wls_swap_preserves_fresh wls_fresh_swap_id

wls_swapAbs_ident wls_swapAbs_involutive wls_swapAbs_inj wls_swapAbs_involutive2 wls_swapAbs_preserves_freshAbs
wls_freshAbs_swapAbs_id

wls_swapEnv_ident wls_swapEnv_involutive wls_swapEnv_inj wls_swapEnv_involutive2 wls_swapEnv_preserves_freshEnv
wls_freshEnv_swapEnv_id

subsection {* Compositionality properties for the other operators *}

subsubsection {* Environment identity, update and ``get" versus other operators *}

(* Recall lemmas getEnv_idEnv, getEnv_updEnv_idEnv, getEnv_updEnv1, getEnv_updEnv2,
subst_psubst_idEnv, vsubst_psubst_idEnv, substEnv_psubstEnv_idEnv, vsubstEnv_psubstEnv_idEnv,
freshEnv_idEnv,
swapEnv_idEnv, psubstEnv_idEnv, substEnv_idEnv, vsubstEnv_idEnv. *)

theorem wls_psubst_idEnv[simp]:
"wls s X \<Longrightarrow> (X #[idEnv]) = X"
by simp

theorem wls_psubstEnv_idEnv_id[simp]:
"wlsEnv rho \<Longrightarrow> (rho &[idEnv]) = rho"
by simp

(* Recall lemmas updEnv_overwrite, updEnv_commute,
   freshEnv_updEnv_E1, freshEnv_updEnv_E2, freshEnv_updEnv_E3, freshEnv_updEnv_E4,
   freshEnv_updEnv_I,
   swapEnv_updEnv *)

theorem wls_swapEnv_updEnv_fresh:
assumes "zs \<noteq> ys \<or> y \<notin> {z1,z2}" and "wls (asSort ys) Y"
and "fresh zs z1 Y" and "fresh zs z2 Y"
shows "((rho [y \<leftarrow> Y]_ys) &[z1 \<and> z2]_zs) = ((rho &[z1 \<and> z2]_zs) [y \<leftarrow> Y]_ys)"
using assms by (simp add: swapEnv_updEnv_fresh)

(* Recall lemmas psubstEnv_updEnv, psubstEnv_updEnv_idEnv,
   substEnv_updEnv,  vsubstEnv_updEnv, getEnv_ext *)

(* Recall lemmas freshEnv_getEnv1 freshEnv_getEnv2 freshEnv_getEnv swapEnv_getEnv1 swapEnv_getEnv2
   getEnv_psubstEnv_None getEnv_psubstEnv_Some
   getEnv_substEnv1 getEnv_substEnv2 getEnv_substEnv3 getEnv_substEnv4
   getEnv_vsubstEnv1 getEnv_vsubstEnv2 getEnv_vsubstEnv3 getEnv_vsubstEnv4. *)

subsubsection {* Substitution versus other operators  *}

(* Recall definition freshImEnvAt_def. *)

theorem wls_fresh_psubst:
assumes "wls s X" and "wlsEnv rho"
shows
"fresh zs z (X #[rho]) =
 (\<forall> ys y. fresh ys y X \<or> freshImEnvAt zs z rho ys y)"
using assms by(simp add: fresh_psubst)

theorem wls_fresh_psubst_E1:
assumes "wls s X" and "wlsEnv rho"
and "rho ys y = None" and "fresh zs z (X #[rho])"
shows "fresh ys y X \<or> (ys \<noteq> zs \<or> y \<noteq> z)"
using assms fresh_psubst_E1[of X rho ys y zs z] by simp

theorem wls_fresh_psubst_E2:
assumes "wls s X" and "wlsEnv rho"
and "rho ys y = Some Y" and "fresh zs z (X #[rho])"
shows "fresh ys y X \<or> fresh zs z Y"
using assms fresh_psubst_E2[of X rho ys y Y zs z] by simp

theorem wls_fresh_psubst_I1:
assumes "wls s X" and "wlsEnv rho"
and "fresh zs z X" and "freshEnv zs z rho"
shows "fresh zs z (X #[rho])"
using assms by(simp add: fresh_psubst_I1)

theorem wls_psubstEnv_preserves_freshEnv:
assumes "wlsEnv rho" and "wlsEnv rho'"
and fresh: "freshEnv zs z rho"  "freshEnv zs z rho'"
shows "freshEnv zs z (rho &[rho'])"
using assms by(simp add: psubstEnv_preserves_freshEnv)

theorem wls_fresh_psubst_I:
assumes "wls s X" and "wlsEnv rho"
and "rho zs z = None \<Longrightarrow> fresh zs z X" and
    "\<And> ys y Y. rho ys y = Some Y \<Longrightarrow> fresh ys y X \<or> fresh zs z Y"
shows "fresh zs z (X #[rho])"
using assms by(simp add: fresh_psubst_I)

theorem wls_fresh_subst:
assumes "wls s X" and "wls (asSort ys) Y"
shows "fresh zs z (X #[Y / y]_ys) =
       (((zs = ys \<and> z = y) \<or> fresh zs z X) \<and> (fresh ys y X \<or> fresh zs z Y))"
using assms by(simp add: fresh_subst)

theorem wls_fresh_vsubst:
assumes "wls s X"
shows "fresh zs z (X #[y1 // y]_ys) =
       (((zs = ys \<and> z = y) \<or> fresh zs z X) \<and> (fresh ys y X \<or> (zs \<noteq> ys \<or> z \<noteq> y1)))"
using assms by(simp add: fresh_vsubst)

theorem wls_subst_preserves_fresh:
assumes "wls s X" and "wls (asSort ys) Y"
and "fresh zs z X" and "fresh zs z Y"
shows "fresh zs z (X #[Y / y]_ys)"
using assms by(simp add: subst_preserves_fresh)

theorem wls_substEnv_preserves_freshEnv:
assumes "wlsEnv rho" and "wls (asSort ys) Y"
and "freshEnv zs z rho" and "fresh zs z Y" and "zs \<noteq> ys \<or> z \<noteq> y"
shows "freshEnv zs z (rho &[Y / y]_ys)"
using assms by(simp add: substEnv_preserves_freshEnv)

theorem wls_vsubst_preserves_fresh:
assumes "wls s X"
and "fresh zs z X" and "zs \<noteq> ys \<or> z \<noteq> y1"
shows "fresh zs z (X #[y1 // y]_ys)"
using assms by(simp add: vsubst_preserves_fresh)

theorem wls_vsubstEnv_preserves_freshEnv:
assumes "wlsEnv rho"
and "freshEnv zs z rho" and "zs \<noteq> ys \<or> z \<notin> {y,y1}"
shows "freshEnv zs z (rho &[y1 // y]_ys)"
using assms by(simp add: vsubstEnv_preserves_freshEnv)

theorem wls_fresh_fresh_subst[simp]:
assumes "wls (asSort ys) Y" and "wls s  X"
and "fresh ys y Y"
shows "fresh ys y (X #[Y / y]_ys)"
using assms by(simp add: fresh_fresh_subst)

theorem wls_diff_fresh_vsubst[simp]:
assumes "wls s X"
and "y \<noteq> y1"
shows "fresh ys y (X #[y1 // y]_ys)"
using assms by(simp add: diff_fresh_vsubst)

theorem wls_fresh_subst_E1:
assumes "wls s X" and "wls (asSort ys) Y"
and "fresh zs z (X #[Y / y]_ys)" and "zs \<noteq> ys \<or> z \<noteq> y"
shows "fresh zs z X"
using assms fresh_subst_E1[of X Y zs z ys y] by simp

theorem wls_fresh_vsubst_E1:
assumes "wls s X"
and "fresh zs z (X #[y1 // y]_ys)" and "zs \<noteq> ys \<or> z \<noteq> y"
shows "fresh zs z X"
using assms fresh_vsubst_E1[of X zs z ys y1 y] by simp

theorem wls_fresh_subst_E2:
assumes "wls s X" and "wls (asSort ys) Y"
and "fresh zs z (X #[Y / y]_ys)"
shows "fresh ys y X \<or> fresh zs z Y"
using assms fresh_subst_E2[of X Y zs z ys y] by simp

theorem wls_fresh_vsubst_E2:
assumes "wls s X"
and "fresh zs z (X #[y1 // y]_ys)"
shows "fresh ys y X \<or> zs \<noteq> ys \<or> z \<noteq> y1"
using assms fresh_vsubst_E2[of X zs z ys y1 y] by simp

theorem wls_psubst_cong[fundef_cong]:
assumes "wls s X" and "wlsEnv rho" and "wlsEnv rho'"
and "\<And> ys y. fresh ys y X \<or> rho ys y = rho' ys y"
shows "(X #[rho]) = (X #[rho'])"
using assms by (simp add: psubst_cong)

theorem wls_fresh_psubst_updEnv:
assumes "wls (asSort ys) Y" and "wls s X" and "wlsEnv rho"
and "fresh ys y X"
shows "(X #[rho [y \<leftarrow> Y]_ys]) = (X #[rho])"
using assms by(simp add: fresh_psubst_updEnv)

theorem wls_freshEnv_psubst_ident[simp]:
assumes "wls s X" and "wlsEnv rho"
and "\<And> zs z. freshEnv zs z rho \<or> fresh zs z X"
shows "(X #[rho]) = X"
using assms by simp

theorem wls_fresh_subst_ident[simp]:
assumes "wls (asSort ys) Y" and "wls s X" and "fresh ys y X"
shows "(X #[Y / y]_ys) = X"
using assms by(simp add: fresh_subst_ident)

theorem wls_substEnv_updEnv_fresh:
assumes "wls (asSort xs) X" and "wls (asSort ys) Y" and "fresh ys y X"
shows "((rho [x \<leftarrow> X]_xs) &[Y / y]_ys) = ((rho &[Y / y]_ys) [x \<leftarrow> X]_xs)"
using assms by(simp add: substEnv_updEnv_fresh)

theorem wls_fresh_substEnv_updEnv[simp]:
assumes "wlsEnv rho" and "wls (asSort ys) Y"
and "freshEnv ys y rho"
shows "(rho &[Y / y]_ys) = (rho [y \<leftarrow> Y]_ys)"
using assms by simp

theorem wls_fresh_vsubst_ident[simp]:
assumes "wls s X" and "fresh ys y X"
shows "(X #[y1 // y]_ys) = X"
using assms by(simp add: fresh_vsubst_ident)

theorem wls_vsubstEnv_updEnv_fresh:
assumes "wls s X" and "fresh ys y X"
shows "((rho [x \<leftarrow> X]_xs) &[y1 // y]_ys) = ((rho &[y1 // y]_ys) [x \<leftarrow> X]_xs)"
using assms by(simp add: vsubstEnv_updEnv_fresh)

theorem wls_fresh_vsubstEnv_updEnv[simp]:
assumes "wlsEnv rho"
and "freshEnv ys y rho"
shows "(rho &[y1 // y]_ys) = (rho [y \<leftarrow> Var ys y1]_ys)"
using assms by simp

theorem wls_swap_psubst:
assumes "wls s X" and "wlsEnv rho"
shows "((X #[rho]) #[z1 \<and> z2]_zs) = ((X #[z1 \<and> z2]_zs) #[rho &[z1 \<and> z2]_zs])"
using assms by(simp add: swap_psubst)

theorem wls_swap_subst:
assumes "wls s  X" and "wls (asSort ys) Y"
shows "((X #[Y / y]_ys) #[z1 \<and> z2]_zs) = ((X #[z1 \<and> z2]_zs) #[(Y #[z1 \<and> z2]_zs) / (y @ys[z1 \<and> z2]_zs)]_ys)"
using assms by(simp add: swap_subst)

theorem wls_swap_vsubst:
assumes "wls s X"
shows "((X #[y1 // y]_ys) #[z1 \<and> z2]_zs) = ((X #[z1 \<and> z2]_zs) #[(y1 @ys[z1 \<and> z2]_zs) // (y @ys[z1 \<and> z2]_zs)]_ys)"
using assms by(simp add: swap_vsubst)

theorem wls_swapEnv_psubstEnv:
assumes "wlsEnv rho" and "wlsEnv rho'"
shows "((rho &[rho']) &[z1 \<and> z2]_zs) = ((rho &[z1 \<and> z2]_zs) &[rho' &[z1 \<and> z2]_zs])"
using assms by(simp add: swapEnv_psubstEnv)

theorem wls_swapEnv_substEnv:
assumes "wls (asSort ys) Y" and "wlsEnv rho"
shows "((rho &[Y / y]_ys) &[z1 \<and> z2]_zs) =
       ((rho &[z1 \<and> z2]_zs) &[(Y #[z1 \<and> z2]_zs) / (y @ys[z1 \<and> z2]_zs)]_ys)"
using assms by(simp add: swapEnv_substEnv)

theorem wls_swapEnv_vsubstEnv:
assumes "wlsEnv rho"
shows "((rho &[y1 // y]_ys) &[z1 \<and> z2]_zs) =
       ((rho &[z1 \<and> z2]_zs) &[(y1 @ys[z1 \<and> z2]_zs) // (y @ys[z1 \<and> z2]_zs)]_ys)"
using assms by(simp add: swapEnv_vsubstEnv)

theorem wls_psubst_compose:
assumes "wls s X" and "wlsEnv rho" and "wlsEnv rho'"
shows "((X #[rho]) #[rho']) = (X #[(rho &[rho'])])"
using assms by(simp add: psubst_compose)

theorem wls_psubstEnv_compose:
assumes "wlsEnv rho" and "wlsEnv rho'" and "wlsEnv rho''"
shows "((rho &[rho']) &[rho'']) = (rho &[(rho' &[rho''])])"
using assms by(simp add: psubstEnv_compose)

theorem wls_psubst_subst_compose:
assumes "wls s X" and "wls (asSort ys) Y" and "wlsEnv rho"
shows "((X #[Y / y]_ys) #[rho]) = (X #[(rho [y \<leftarrow> (Y #[rho])]_ys)])"
using assms by(simp add: psubst_subst_compose)

theorem wls_psubst_subst_compose_freshEnv:
assumes "wlsEnv rho" and "wls s X" and "wls (asSort ys) Y"
and "freshEnv ys y rho"
shows "((X #[Y / y]_ys) #[rho]) = ((X #[rho]) #[(Y #[rho]) / y]_ys)"
using assms by (simp add: psubst_subst_compose_freshEnv)

theorem wls_psubstEnv_substEnv_compose_freshEnv:
assumes "wlsEnv rho" and "wlsEnv rho'" and "wls (asSort ys) Y"
assumes "freshEnv ys y rho'"
shows "((rho &[Y / y]_ys) &[rho']) = ((rho &[rho']) &[(Y #[rho']) / y]_ys)"
using assms by (simp add: psubstEnv_substEnv_compose_freshEnv)

theorem wls_psubstEnv_substEnv_compose:
assumes "wlsEnv rho" and "wls (asSort ys) Y" and "wlsEnv rho'"
shows "((rho &[Y / y]_ys) &[rho']) = (rho &[(rho' [y \<leftarrow> (Y #[rho'])]_ys)])"
using assms by(simp add: psubstEnv_substEnv_compose)

theorem wls_psubst_vsubst_compose:
assumes "wls s X" and "wlsEnv rho"
shows "((X #[y1 // y]_ys) #[rho]) = (X #[(rho [y \<leftarrow> ((Var ys y1) #[rho])]_ys)])"
using assms by(simp add: psubst_vsubst_compose)

theorem wls_psubstEnv_vsubstEnv_compose:
assumes "wlsEnv rho" and "wlsEnv rho'"
shows "((rho &[y1 // y]_ys) &[rho']) = (rho &[(rho' [y \<leftarrow> ((Var ys y1) #[rho'])]_ys)])"
using assms by(simp add: psubstEnv_vsubstEnv_compose)

theorem wls_subst_psubst_compose:
assumes "wls s X" and "wls (asSort ys) Y" and "wlsEnv rho"
shows "((X #[rho]) #[Y / y]_ys) = (X #[(rho &[Y / y]_ys)])"
using assms by(simp add: subst_psubst_compose)

theorem wls_substEnv_psubstEnv_compose:
assumes "wlsEnv rho" and "wls (asSort ys) Y" and "wlsEnv rho'"
shows "((rho &[rho']) &[Y / y]_ys) = (rho &[(rho' &[Y / y]_ys)])"
using assms by(simp add: substEnv_psubstEnv_compose)

theorem wls_vsubst_psubst_compose:
assumes "wls s X" and "wlsEnv rho"
shows "((X #[rho]) #[y1 // y]_ys) = (X #[(rho &[y1 // y]_ys)])"
using assms by(simp add: vsubst_psubst_compose)

theorem wls_vsubstEnv_psubstEnv_compose:
assumes "wlsEnv rho" and "wlsEnv rho'"
shows "((rho &[rho']) &[y1 // y]_ys) = (rho &[(rho' &[y1 // y]_ys)])"
using assms by(simp add: vsubstEnv_psubstEnv_compose)

theorem wls_subst_compose1:
assumes "wls s X" and "wls (asSort ys) Y1" and "wls (asSort ys) Y2"
shows "((X #[Y1 / y]_ys) #[Y2 / y]_ys) = (X #[(Y1 #[Y2 / y]_ys) / y]_ys)"
using assms by(simp add: subst_compose1)

theorem wls_substEnv_compose1:
assumes "wlsEnv rho" and "wls (asSort ys) Y1" and "wls (asSort ys) Y2"
shows "((rho &[Y1 / y]_ys) &[Y2 / y]_ys) = (rho &[(Y1 #[Y2 / y]_ys) / y]_ys)"
using assms by(simp add: substEnv_compose1)

theorem wls_subst_vsubst_compose1:
assumes "wls s X" and "wls (asSort ys) Y" and "y \<noteq> y1"
shows "((X #[y1 // y]_ys) #[Y / y]_ys) = (X #[y1 // y]_ys)"
using assms by(simp add: subst_vsubst_compose1)

theorem wls_substEnv_vsubstEnv_compose1:
assumes "wlsEnv rho" and "wls (asSort ys) Y" and "y \<noteq> y1"
shows "((rho &[y1 // y]_ys) &[Y / y]_ys) = (rho &[y1 // y]_ys)"
using assms by(simp add: substEnv_vsubstEnv_compose1)

theorem wls_vsubst_subst_compose1:
assumes "wls s X" and "wls (asSort ys) Y"
shows "((X #[Y / y]_ys) #[y1 // y]_ys) = (X #[(Y #[y1 // y]_ys) / y]_ys)"
using assms by(simp add: vsubst_subst_compose1)

theorem wls_vsubstEnv_substEnv_compose1:
assumes "wlsEnv rho" and "wls (asSort ys) Y"
shows "((rho &[Y / y]_ys) &[y1 // y]_ys) = (rho &[(Y #[y1 // y]_ys) / y]_ys)"
using assms by(simp add: vsubstEnv_substEnv_compose1)

theorem wls_vsubst_compose1:
assumes "wls s X"
shows "((X #[y1 // y]_ys) #[y2 // y]_ys) = (X #[(y1 @ys[y2 / y]_ys) // y]_ys)"
using assms by(simp add: vsubst_compose1)

theorem wls_vsubstEnv_compose1:
assumes "wlsEnv rho"
shows "((rho &[y1 // y]_ys) &[y2 // y]_ys) = (rho &[(y1 @ys[y2 / y]_ys) // y]_ys)"
using assms by(simp add: vsubstEnv_compose1)

theorem wls_subst_compose2:
assumes  "wls s X" and "wls (asSort ys) Y" and "wls (asSort zs) Z"
and "ys \<noteq> zs \<or> y \<noteq> z" and fresh: "fresh ys y Z"
shows "((X #[Y / y]_ys) #[Z / z]_zs) = ((X #[Z / z]_zs) #[(Y #[Z / z]_zs) / y]_ys)"
using assms by(simp add: subst_compose2)

theorem wls_substEnv_compose2:
assumes  "wlsEnv rho" and "wls (asSort ys) Y" and "wls (asSort zs) Z"
and "ys \<noteq> zs \<or> y \<noteq> z" and fresh: "fresh ys y Z"
shows "((rho &[Y / y]_ys) &[Z / z]_zs) = ((rho &[Z / z]_zs) &[(Y #[Z / z]_zs) / y]_ys)"
using assms by(simp add: substEnv_compose2)

theorem wls_subst_vsubst_compose2:
assumes  "wls s X" and "wls (asSort zs) Z"
and "ys \<noteq> zs \<or> y \<noteq> z" and fresh: "fresh ys y Z"
shows "((X #[y1 // y]_ys) #[Z / z]_zs) = ((X #[Z / z]_zs) #[((Var ys y1) #[Z / z]_zs) / y]_ys)"
using assms by(simp add: subst_vsubst_compose2)

theorem wls_substEnv_vsubstEnv_compose2:
assumes  "wlsEnv rho" and "wls (asSort zs) Z"
and "ys \<noteq> zs \<or> y \<noteq> z" and fresh: "fresh ys y Z"
shows "((rho &[y1 // y]_ys) &[Z / z]_zs) = ((rho &[Z / z]_zs) &[((Var ys y1) #[Z / z]_zs) / y]_ys)"
using assms by(simp add: substEnv_vsubstEnv_compose2)

theorem wls_vsubst_subst_compose2:
assumes  "wls s X" and "wls (asSort ys) Y"
and "ys \<noteq> zs \<or> y \<notin> {z,z1}"
shows "((X #[Y / y]_ys) #[z1 // z]_zs) = ((X #[z1 // z]_zs) #[(Y #[z1 // z]_zs) / y]_ys)"
using assms by(simp add: vsubst_subst_compose2)

theorem wls_vsubstEnv_substEnv_compose2:
assumes  "wlsEnv rho" and "wls (asSort ys) Y"
and "ys \<noteq> zs \<or> y \<notin> {z,z1}"
shows "((rho &[Y / y]_ys) &[z1 // z]_zs) = ((rho &[z1 // z]_zs) &[(Y #[z1 // z]_zs) / y]_ys)"
using assms by(simp add: vsubstEnv_substEnv_compose2)

theorem wls_vsubst_compose2:
assumes  "wls s X"
and "ys \<noteq> zs \<or> y \<notin> {z,z1}"
shows "((X #[y1 // y]_ys) #[z1 // z]_zs) = ((X #[z1 // z]_zs) #[(y1 @ys[z1 / z]_zs) // y]_ys)"
using assms by(simp add: vsubst_compose2)

theorem wls_vsubstEnv_compose2:
assumes  "wlsEnv rho"
and "ys \<noteq> zs \<or> y \<notin> {z,z1}"
shows "((rho &[y1 // y]_ys) &[z1 // z]_zs) =
       ((rho &[z1 // z]_zs) &[(y1 @ys[z1 / z]_zs) // y]_ys)"
using assms by(simp add: vsubstEnv_compose2)

subsubsection {* Properties specific to variable-for-variable substitution *}

theorem wls_vsubst_ident[simp]:
assumes "wls s X"
shows "(X #[z // z]_zs) = X"
using assms by(simp add: vsubst_ident)

theorem wls_subst_ident[simp]:
assumes "wls s  X"
shows "(X #[(Var zs z) / z]_zs) = X"
using assms by simp

theorem wls_vsubst_eq_swap:
assumes "wls s X" and "y1 = y2 \<or> fresh ys y1 X"
shows "(X #[y1 // y2]_ys) = (X #[y1 \<and> y2]_ys)"
using assms by(simp add: vsubst_eq_swap)

theorem wls_skel_vsubst:
assumes "wls s X"
shows "skel (X #[y1 // y2]_ys) = skel X"
using assms by(simp add: skel_vsubst)

theorem wls_subst_vsubst_trans:
assumes  "wls s X" and "wls (asSort ys) Y" and "fresh ys y1 X"
shows "((X #[y1 // y]_ys) #[Y / y1]_ys) = (X #[Y / y]_ys)"
using assms by (simp add: subst_vsubst_trans)

theorem wls_vsubst_trans:
assumes  "wls s X" and "fresh ys y1 X"
shows "((X #[y1 // y]_ys) #[y2 // y1]_ys) = (X #[y2 // y]_ys)"
using assms by (simp add: vsubst_trans)

theorem wls_vsubst_commute:
assumes "wls s X"
and "xs \<noteq> xs' \<or> {x,y} \<inter> {x',y'} = {}" and "fresh xs x X" and "fresh xs' x' X"
shows "((X #[x // y]_xs) #[x' // y']_xs') = ((X #[x' // y']_xs') #[x // y]_xs)"
using assms by(simp add: vsubst_commute)

(* The next lemmas do not have ``good" counterparts: *)

theorem wls_induct[case_names Var Op Abs]:
assumes
Var: "\<And> xs x. phi (asSort xs) (Var xs x)" and
Op:
"\<And> delta inp binp.
   \<lbrakk>wlsInp delta inp; wlsBinp delta binp;
    liftAll2 phi (arOf delta) inp; liftAll2 phiAbs (barOf delta) binp\<rbrakk>
   \<Longrightarrow> phi (stOf delta) (Op delta inp binp)" and
Abs:
"\<And> s xs x X.
   \<lbrakk>isInBar (xs,s); wls s X;
    \<And> Y. (X,Y) \<in> swapped \<Longrightarrow> phi s Y;
    \<And> ys y1 y2. phi s (X #[y1 // y2]_ys);
    \<And> Y. \<lbrakk>wls s Y; skel Y = skel X\<rbrakk> \<Longrightarrow> phi s Y\<rbrakk>
   \<Longrightarrow> phiAbs (xs,s) (Abs xs x X)"
shows
"(wls s X \<longrightarrow> phi s X) \<and>
 (wlsAbs (xs,s') A \<longrightarrow> phiAbs (xs,s') A)"
apply(induction rule: wls_templateInduct
[of "\<lambda>s. swapped \<union> {(X, X #[y1 // y2]_ys)| X ys y1 y2. True}
         \<union> {(X,Y). wls s Y \<and> skel Y = skel X}"])
by (auto simp add: assms swapped_preserves_wls swapped_skel wls_skel_vsubst 
   intro!: Abs) 

theorem wls_Abs_vsubst_all_aux:
assumes "wls s X" and "wls s X'"
shows
"(Abs xs x X = Abs xs x' X') =
 (\<forall> y. (y = x \<or> fresh xs y X) \<and> (y = x' \<or> fresh xs y X') \<longrightarrow>
       (X #[y // x]_xs) = (X' #[y // x']_xs))"
using assms wls_Abs_swap_all by (simp add: wls_vsubst_eq_swap)

theorem wls_Abs_vsubst_ex:
assumes  "wls s X" and "wls s X'"
shows
"(Abs xs x X = Abs xs x' X') =
 (\<exists> y. y \<notin> {x,x'} \<and> fresh xs y X \<and> fresh xs y X' \<and>
       (X #[y // x]_xs) = (X' #[y // x']_xs))"
proof-
  let ?phi = "\<lambda> f y. y \<notin> {x,x'} \<and> fresh xs y X \<and> fresh xs y X'
                     \<and> (f xs y x X) = (f xs y x' X')"
  {assume "Abs xs x X = Abs xs x' X'"
   then obtain y where "?phi swap y" using assms wls_Abs_swap_ex by auto
   hence "?phi (\<lambda> xs y x X. (X #[y // x]_xs)) y"
   using assms by(simp add: wls_vsubst_eq_swap)
   hence "\<exists> y. ?phi (\<lambda> xs y x X. (X #[y // x]_xs)) y" by auto
  }
  moreover
  {fix y assume  "?phi (\<lambda> xs y x X. (X #[y // x]_xs)) y"
   hence "?phi swap y" using assms by(auto simp add: wls_vsubst_eq_swap)
   hence "Abs xs x X = Abs xs x' X'" using assms wls_Abs_swap_ex by auto
  }
  ultimately show ?thesis by auto
qed

theorem wls_Abs_vsubst_all:
assumes "wls s X" and "wls s X'"
shows
"(Abs xs x X = Abs xs x' X') =
 (\<forall> y. (X #[y // x]_xs) = (X' #[y // x']_xs))"
proof(rule iffI, clarify)
  assume "\<forall> y. (X #[y // x]_xs) = (X' #[y // x']_xs)"
  thus "Abs xs x X = Abs xs x' X'"
  using assms by(auto simp add: wls_Abs_vsubst_all_aux)
next
  fix y
  assume "Abs xs x X = Abs xs x' X'"
  then obtain z where z_fresh: "fresh xs z X \<and> fresh xs z X'"
  and "(X #[z // x]_xs) = (X' #[z // x']_xs)"
  using assms by(auto simp add: wls_Abs_vsubst_ex)
  hence "((X #[z // x]_xs) #[y // z]_xs) = ((X' #[z // x']_xs) #[y // z]_xs)" by simp
  thus "(X #[y // x]_xs) = (X' #[y // x']_xs)"
  using assms z_fresh wls_vsubst_trans by auto
qed

theorem wls_Abs_subst_all:
assumes "wls s X" and "wls s X'"
shows
"(Abs xs x X = Abs xs x' X') =
 (\<forall> Y. wls (asSort xs) Y \<longrightarrow> (X #[Y / x]_xs) = (X' #[Y / x']_xs))"
proof(rule iffI, clarify)
  assume "\<forall> Y. wls (asSort xs) Y \<longrightarrow> (X #[Y / x]_xs) = (X' #[Y / x']_xs)"
  hence "\<forall> y. (X #[y // x]_xs) = (X' #[y // x']_xs)"
  unfolding vsubst_def by simp
  thus "Abs xs x X = Abs xs x' X'"
  using assms wls_Abs_vsubst_all by auto
next
  fix Y assume Y: "wls (asSort xs) Y"
  assume "Abs xs x X = Abs xs x' X'"
  then obtain z where z_fresh: "fresh xs z X \<and> fresh xs z X'"
  and "(X #[z // x]_xs) = (X' #[z // x']_xs)"
  using assms by(auto simp add: wls_Abs_vsubst_ex)
  hence "((X #[z // x]_xs) #[Y / z]_xs) = ((X' #[z // x']_xs) #[Y / z]_xs)" by simp
  thus "(X #[Y / x]_xs) = (X' #[Y / x']_xs)"
  using assms z_fresh Y wls_subst_vsubst_trans by auto
qed

lemma Abs_inj_fresh[simp]:
assumes X: "wls s X" and X': "wls s X'"
and fresh_X: "fresh ys x X" and fresh_X': "fresh ys x' X'"
and eq: "Abs ys x X = Abs ys x' X'"
shows "X = X'"
proof-
  obtain z where "(X #[z // x]_ys) = (X' #[z // x']_ys)"
  using X X' eq by(auto simp add: wls_Abs_vsubst_ex)
  thus ?thesis using X X' fresh_X fresh_X' by simp
qed

theorem wls_Abs_vsubst_cong:
assumes "wls s X" and "wls s X'"
and "fresh xs y X" and "fresh xs y X'"  and "(X #[y // x]_xs) = (X' #[y // x']_xs)"
shows "Abs xs x X = Abs xs x' X'"
using assms by (intro wls_Abs_swap_cong) (auto simp: wls_vsubst_eq_swap)

theorem wls_Abs_vsubst_fresh[simp]:
assumes "wls s X" and "fresh xs x' X"
shows "Abs xs x' (X #[x' // x]_xs) = Abs xs x X"
using assms by(simp add: wls_vsubst_eq_swap)

theorem wls_Abs_subst_Var_fresh[simp]:
assumes "wls s X" and "fresh xs x' X"
shows "Abs xs x' (subst xs (Var xs x') x X) = Abs xs x X"
using assms wls_Abs_vsubst_fresh unfolding vsubst_def by simp

theorem wls_Abs_vsubst_congSTR:
assumes "wls s X" and "wls s X'"
and "y = x \<or> fresh xs y X" "y = x' \<or> fresh xs y X'"
and "(X #[y // x]_xs) = (X' #[y // x']_xs)"
shows "Abs xs x X = Abs xs x' X'"
by (metis assms wls_Abs_vsubst_fresh wls_vsubst_ident)

subsubsection {* Abstraction versions of the properties *}

(* Environment identity and update versus other operators *)

theorem wls_psubstAbs_idEnv[simp]:
"wlsAbs (us,s) A \<Longrightarrow> (A $[idEnv]) = A"
by simp

(* Substitution versus other operators  *)

theorem wls_freshAbs_psubstAbs:
assumes "wlsAbs (us,s) A" and "wlsEnv rho"
shows
"freshAbs zs z (A $[rho]) =
 (\<forall> ys y. freshAbs ys y A \<or> freshImEnvAt zs z rho ys y)"
using assms by(simp add: freshAbs_psubstAbs)

theorem wls_freshAbs_psubstAbs_E1:
assumes "wlsAbs (us,s) A" and "wlsEnv rho"
and "rho ys y = None" and "freshAbs zs z (A $[rho])"
shows "freshAbs ys y A \<or> (ys \<noteq> zs \<or> y \<noteq> z)"
using assms freshAbs_psubstAbs_E1[of A rho ys y zs z] by simp

theorem wls_freshAbs_psubstAbs_E2:
assumes "wlsAbs (us,s) A" and "wlsEnv rho"
and "rho ys y = Some Y" and "freshAbs zs z (A $[rho])"
shows "freshAbs ys y A \<or> fresh zs z Y"
using assms freshAbs_psubstAbs_E2[of A rho ys y Y zs z] by simp

theorem wls_freshAbs_psubstAbs_I1:
assumes "wlsAbs (us,s) A" and "wlsEnv rho"
and "freshAbs zs z A" and "freshEnv zs z rho"
shows "freshAbs zs z (A $[rho])"
using assms by(simp add: freshAbs_psubstAbs_I1)

theorem wls_freshAbs_psubstAbs_I:
assumes "wlsAbs (us,s) A" and "wlsEnv rho"
and "rho zs z = None \<Longrightarrow> freshAbs zs z A" and
    "\<And> ys y Y. rho ys y = Some Y \<Longrightarrow> freshAbs ys y A \<or> fresh zs z Y"
shows "freshAbs zs z (A $[rho])"
using assms by(simp add: freshAbs_psubstAbs_I)

theorem wls_freshAbs_substAbs:
assumes "wlsAbs (us,s) A" and "wls (asSort ys) Y"
shows "freshAbs zs z (A $[Y / y]_ys) =
       (((zs = ys \<and> z = y) \<or> freshAbs zs z A) \<and> (freshAbs ys y A \<or> fresh zs z Y))"
using assms by(simp add: freshAbs_substAbs)

theorem wls_freshAbs_vsubstAbs:
assumes "wlsAbs (us,s) A"
shows "freshAbs zs z (A $[y1 // y]_ys) =
       (((zs = ys \<and> z = y) \<or> freshAbs zs z A) \<and>
        (freshAbs ys y A \<or> (zs \<noteq> ys \<or> z \<noteq> y1)))"
using assms by(simp add: freshAbs_vsubstAbs)

theorem wls_substAbs_preserves_freshAbs:
assumes "wlsAbs (us,s) A" and "wls (asSort ys) Y"
and "freshAbs zs z A" and "fresh zs z Y"
shows "freshAbs zs z (A $[Y / y]_ys)"
using assms by(simp add: substAbs_preserves_freshAbs)

theorem wls_vsubstAbs_preserves_freshAbs:
assumes "wlsAbs (us,s) A"
and "freshAbs zs z A" and "zs \<noteq> ys \<or> z \<noteq> y1"
shows "freshAbs zs z (A $[y1 // y]_ys)"
using assms by(simp add: vsubstAbs_preserves_freshAbs)

theorem wls_fresh_freshAbs_substAbs[simp]:
assumes "wls (asSort ys) Y" and "wlsAbs (us,s) A"
and "fresh ys y Y"
shows "freshAbs ys y (A $[Y / y]_ys)"
using assms by simp

theorem wls_diff_freshAbs_vsubstAbs[simp]:
assumes "wlsAbs (us,s) A"
and "y \<noteq> y1"
shows "freshAbs ys y (A $[y1 // y]_ys)"
using assms by simp

theorem wls_freshAbs_substAbs_E1:
assumes "wlsAbs (us,s) A" and "wls (asSort ys) Y"
and "freshAbs zs z (A $[Y / y]_ys)" and "z \<noteq> y \<or> zs \<noteq> ys"
shows "freshAbs zs z A"
using assms freshAbs_substAbs_E1[of A Y zs z ys y] by auto

theorem wls_freshAbs_vsubstAbs_E1:
assumes "wlsAbs (us,s) A"
and "freshAbs zs z (A $[y1 // y]_ys)" and "z \<noteq> y \<or> zs \<noteq> ys"
shows "freshAbs zs z A"
using assms freshAbs_vsubstAbs_E1[of A zs z ys y1 y] by auto

theorem wls_freshAbs_substAbs_E2:
assumes "wlsAbs (us,s) A" and "wls (asSort ys) Y"
and "freshAbs zs z (A $[Y / y]_ys)"
shows "freshAbs ys y A \<or> fresh zs z Y"
using assms freshAbs_substAbs_E2[of A Y zs z ys] by simp

theorem wls_freshAbs_vsubstAbs_E2:
assumes "wlsAbs (us,s) A"
and "freshAbs zs z (A $[y1 // y]_ys)"
shows "freshAbs ys y A \<or> zs \<noteq> ys \<or> z \<noteq> y1"
using assms freshAbs_vsubstAbs_E2[of A zs z ys y1 y] by simp

theorem wls_psubstAbs_cong[fundef_cong]:
assumes "wlsAbs (us,s) A" and "wlsEnv rho" and "wlsEnv rho'"
and "\<And> ys y. freshAbs ys y A \<or> rho ys y = rho' ys y"
shows "(A $[rho]) = (A $[rho'])"
using assms by(simp add: psubstAbs_cong)

theorem wls_freshAbs_psubstAbs_updEnv:
assumes "wls (asSort xs) X" and "wlsAbs (us,s) A" and "wlsEnv rho"
and "freshAbs xs x A"
shows "(A $[rho [x \<leftarrow> X]_xs]) = (A $[rho])"
using assms by(simp add: freshAbs_psubstAbs_updEnv)

lemma wls_freshEnv_psubstAbs_ident[simp]:
assumes "wlsAbs (us,s) A" and "wlsEnv rho"
and "\<And> zs z. freshEnv zs z rho \<or> freshAbs zs z A"
shows "(A $[rho]) = A"
using assms by simp

theorem wls_freshAbs_substAbs_ident[simp]:
assumes "wls (asSort xs) X" and "wlsAbs (us,s) A" and "freshAbs xs x A"
shows "(A $[X / x]_xs) = A"
using assms by simp

theorem wls_substAbs_Abs[simp]:
assumes "wls s X" and "wls (asSort xs) Y"
shows "((Abs xs x X) $[Y / x]_xs) = Abs xs x X"
using assms by simp

theorem wls_freshAbs_vsubstAbs_ident[simp]:
assumes "wlsAbs (us,s) A" and "freshAbs xs x A"
shows "(A $[x1 // x]_xs) = A"
using assms by(simp add: freshAbs_vsubstAbs_ident)

theorem wls_swapAbs_psubstAbs:
assumes "wlsAbs (us,s) A" and "wlsEnv rho"
shows "((A $[rho]) $[z1 \<and> z2]_zs) = ((A $[z1 \<and> z2]_zs) $[rho &[z1 \<and> z2]_zs])"
using assms by(simp add: swapAbs_psubstAbs)

theorem wls_swapAbs_substAbs:
assumes "wlsAbs (us,s) A" and "wls (asSort ys) Y"
shows "((A $[Y / y]_ys) $[z1 \<and> z2]_zs) =
       ((A $[z1 \<and> z2]_zs) $[(Y #[z1 \<and> z2]_zs) / (y @ys[z1 \<and> z2]_zs)]_ys)"
using assms by(simp add: swapAbs_substAbs)

theorem wls_swapAbs_vsubstAbs:
assumes "wlsAbs (us,s) A"
shows "((A $[y1 // y]_ys) $[z1 \<and> z2]_zs) =
       ((A $[z1 \<and> z2]_zs) $[(y1 @ys[z1 \<and> z2]_zs) // (y @ys[z1 \<and> z2]_zs)]_ys)"
using assms by(simp add: swapAbs_vsubstAbs)

theorem wls_psubstAbs_compose:
assumes "wlsAbs (us,s) A" and "wlsEnv rho" and "wlsEnv rho'"
shows "((A $[rho]) $[rho']) = (A $[(rho &[rho'])])"
using assms by(simp add: psubstAbs_compose)

theorem wls_psubstAbs_substAbs_compose:
assumes "wlsAbs (us,s) A" and "wls (asSort ys) Y" and "wlsEnv rho"
shows "((A $[Y / y]_ys) $[rho]) = (A $[(rho [y \<leftarrow> (Y #[rho])]_ys)])"
using assms by(simp add: psubstAbs_substAbs_compose)

theorem wls_psubstAbs_substAbs_compose_freshEnv:
assumes "wlsEnv rho" and "wlsAbs (us,s) A" and "wls (asSort ys) Y"
assumes "freshEnv ys y rho"
shows "((A $[Y / y]_ys) $[rho]) = ((A $[rho]) $[(Y #[rho]) / y]_ys)"
using assms by (simp add: psubstAbs_substAbs_compose_freshEnv)

theorem wls_psubstAbs_vsubstAbs_compose:
assumes "wlsAbs (us,s) A" and "wlsEnv rho"
shows "((A $[y1 // y]_ys) $[rho]) = (A $[(rho [y \<leftarrow> ((Var ys y1) #[rho])]_ys)])"
using assms by(simp add: psubstAbs_vsubstAbs_compose)

theorem wls_substAbs_psubstAbs_compose:
assumes "wlsAbs (us,s) A" and "wls (asSort ys) Y" and "wlsEnv rho"
shows "((A $[rho]) $[Y / y]_ys) = (A $[(rho &[Y / y]_ys)])"
using assms by(simp add: substAbs_psubstAbs_compose)

theorem wls_vsubstAbs_psubstAbs_compose:
assumes "wlsAbs (us,s) A" and "wlsEnv rho"
shows "((A $[rho]) $[y1 // y]_ys) = (A $[(rho &[y1 // y]_ys)])"
using assms by(simp add: vsubstAbs_psubstAbs_compose)

theorem wls_substAbs_compose1:
assumes "wlsAbs (us,s) A" and "wls (asSort ys) Y1" and "wls (asSort ys) Y2"
shows "((A $[Y1 / y]_ys) $[Y2 / y]_ys) = (A $[(Y1 #[Y2 / y]_ys) / y]_ys)"
using assms by(simp add: substAbs_compose1)

theorem wls_substAbs_vsubstAbs_compose1:
assumes "wlsAbs (us,s) A" and "wls (asSort ys) Y" and "y \<noteq> y1"
shows "((A $[y1 // y]_ys) $[Y / y]_ys) = (A $[y1 // y]_ys)"
using assms by(simp add: substAbs_vsubstAbs_compose1)

theorem wls_vsubstAbs_substAbs_compose1:
assumes "wlsAbs (us,s) A" and "wls (asSort ys) Y"
shows "((A $[Y / y]_ys) $[y1 // y]_ys) = (A $[(Y #[y1 // y]_ys) / y]_ys)"
using assms by(simp add: vsubstAbs_substAbs_compose1)

theorem wls_vsubstAbs_compose1:
assumes "wlsAbs (us,s) A"
shows "((A $[y1 // y]_ys) $[y2 // y]_ys) = (A $[(y1 @ys[y2 / y]_ys) // y]_ys)"
using assms by(simp add: vsubstAbs_compose1)

theorem wls_substAbs_compose2:
assumes  "wlsAbs (us,s) A" and "wls (asSort ys) Y" and "wls (asSort zs) Z"
and "ys \<noteq> zs \<or> y \<noteq> z" and fresh: "fresh ys y Z"
shows "((A $[Y / y]_ys) $[Z / z]_zs) = ((A $[Z / z]_zs) $[(Y #[Z / z]_zs) / y]_ys)"
using assms by(simp add: substAbs_compose2)

theorem wls_substAbs_vsubstAbs_compose2:
assumes "wlsAbs (us,s) A" and "wls (asSort zs) Z"
and "ys \<noteq> zs \<or> y \<noteq> z" and fresh: "fresh ys y Z"
shows "((A $[y1 // y]_ys) $[Z / z]_zs) = ((A $[Z / z]_zs) $[((Var ys y1) #[Z / z]_zs) / y]_ys)"
using assms by(simp add: substAbs_vsubstAbs_compose2)

theorem wls_vsubstAbs_substAbs_compose2:
assumes "wlsAbs (us,s) A" and "wls (asSort ys) Y"
and "ys \<noteq> zs \<or> y \<notin> {z,z1}"
shows "((A $[Y / y]_ys) $[z1 // z]_zs) = ((A $[z1 // z]_zs) $[(Y #[z1 // z]_zs) / y]_ys)"
using assms by(simp add: vsubstAbs_substAbs_compose2)

theorem wls_vsubstAbs_compose2:
assumes  "wlsAbs (us,s) A"
and "ys \<noteq> zs \<or> y \<notin> {z,z1}"
shows "((A $[y1 // y]_ys) $[z1 // z]_zs) = ((A $[z1 // z]_zs) $[(y1 @ys[z1 / z]_zs) // y]_ys)"
using assms by(simp add: vsubstAbs_compose2)

(* Properties specific to variable-for-variable substitution *)

theorem wls_vsubstAbs_ident[simp]:
assumes "wlsAbs (us,s) A"
shows "(A $[z // z]_zs) = A"
using assms by(simp add: vsubstAbs_ident)

theorem wls_substAbs_ident[simp]:
assumes "wlsAbs (us,s) A"
shows "(A $[(Var zs z) / z]_zs) = A"
using assms by simp

theorem wls_vsubstAbs_eq_swapAbs:
assumes "wlsAbs (us,s) A" and "y1 = y2 \<or> freshAbs ys y1 A"
shows "(A $[y1 // y2]_ys) = (A $[y1 \<and> y2]_ys)" 
using assms vsubstAll_swapAll[of "Par [y1, y2] [] [] []" _ _ A]
unfolding goodPar_def by auto

theorem wls_skelAbs_vsubstAbs:
assumes "wlsAbs (us,s) A"
shows "skelAbs (A $[y1 // y2]_ys) = skelAbs A"
using assms by(simp add: skelAbs_vsubstAbs)

theorem wls_substAbs_vsubstAbs_trans:
assumes "wlsAbs (us,s) A" and "wls (asSort ys) Y" and "freshAbs ys y1 A"
shows "((A $[y1 // y]_ys) $[Y / y1]_ys) = (A $[Y / y]_ys)"
using assms by(simp add: substAbs_vsubstAbs_trans)

theorem wls_vsubstAbs_trans:
assumes "wlsAbs (us,s) A" and "freshAbs ys y1 A"
shows "((A $[y1 // y]_ys) $[y2 // y1]_ys) = (A $[y2 // y]_ys)"
using assms by(simp add: vsubstAbs_trans)

theorem wls_vsubstAbs_commute:
assumes "wlsAbs (us,s) A"
and "xs \<noteq> xs' \<or> {x,y} \<inter> {x',y'} = {}" and "freshAbs xs x A" and "freshAbs xs' x' A"
shows "((A $[x // y]_xs) $[x' // y']_xs') = ((A $[x' // y']_xs') $[x // y]_xs)"
proof-
  have "freshAbs xs' x' (A $[x // y]_xs)"
  using assms by(auto simp: vsubstAbs_preserves_freshAbs)
  moreover have "freshAbs xs x (A $[x' // y']_xs')"
  using assms by(auto simp: vsubstAbs_preserves_freshAbs)
  ultimately show ?thesis using assms 
  by (auto simp: vsubstAbs_eq_swapAbs intro!: wls_swapAbs_commute)
qed

lemmas wls_psubstAll_freshAll_otherSimps =
wls_psubst_idEnv wls_psubstEnv_idEnv_id wls_psubstAbs_idEnv
wls_freshEnv_psubst_ident wls_freshEnv_psubstAbs_ident

lemmas wls_substAll_freshAll_otherSimps =
wls_fresh_fresh_subst wls_fresh_subst_ident wls_fresh_substEnv_updEnv wls_subst_ident
wls_fresh_freshAbs_substAbs wls_freshAbs_substAbs_ident wls_substAbs_ident
wls_Abs_subst_Var_fresh

lemmas wls_vsubstAll_freshAll_otherSimps =
wls_diff_fresh_vsubst wls_fresh_vsubst_ident wls_fresh_vsubstEnv_updEnv wls_vsubst_ident
wls_diff_freshAbs_vsubstAbs wls_freshAbs_vsubstAbs_ident wls_vsubstAbs_ident
wls_Abs_vsubst_fresh

lemmas wls_allOpers_otherSimps =
wls_swapAll_freshAll_otherSimps
wls_psubstAll_freshAll_otherSimps
wls_substAll_freshAll_otherSimps
wls_vsubstAll_freshAll_otherSimps

subsection {* Operators for down-casting and case-analyzing well-sorted items  *}

text{* The features developed here may occasionally turn out more convenient than obtaining
the desired effect by hand, via the corresponding nchotomies.
E.g., when we want to perform the case-analysis uniformly, as part of a
function definition, the operators defined in the subsection save some tedious
definitions and proofs pertaining to Hilbert choice.   *}

subsubsection {* For terms  *}

(* Definitions: *)

definition isVar where
"isVar s (X :: ('index,'bindex,'varSort,'var,'opSym)term) ==
 \<exists> xs x. s = asSort xs \<and> X = Var xs x"

definition castVar where
"castVar s (X :: ('index,'bindex,'varSort,'var,'opSym)term) ==
 SOME xs_x. s = asSort (fst xs_x) \<and> X = Var (fst xs_x) (snd xs_x)"

definition isOp where
"isOp s X \<equiv>
 \<exists> delta inp binp.
   wlsInp delta inp \<and> wlsBinp delta binp \<and> s = stOf delta \<and> X = Op delta inp binp"

definition castOp where
"castOp s X \<equiv>
 SOME delta_inp_binp.
   wlsInp (fst3 delta_inp_binp) (snd3 delta_inp_binp) \<and>
   wlsBinp (fst3 delta_inp_binp) (trd3 delta_inp_binp) \<and>
   s = stOf (fst3 delta_inp_binp) \<and>
   X = Op (fst3 delta_inp_binp) (snd3 delta_inp_binp) (trd3 delta_inp_binp)"

definition sortTermCase where
"sortTermCase fVar fOp s X \<equiv>
 if isVar s X then fVar (fst (castVar s X)) (snd (castVar s X))
                else if isOp s X then fOp (fst3 (castOp s X)) (snd3 (castOp s X))  (trd3 (castOp s X))
                     else undefined"

(* Properties of isVar and castVar: *)

lemma isVar_asSort_Var[simp]:
"isVar (asSort xs) (Var xs x)"
unfolding isVar_def by auto

lemma not_isVar_Op[simp]:
"\<not> isVar s (Op delta inp binp)"
unfolding isVar_def by auto

lemma isVar_imp_wls:
"isVar s X \<Longrightarrow> wls s X"
unfolding isVar_def by auto

lemmas isVar_simps =
isVar_asSort_Var not_isVar_Op

lemma castVar_asSort_Var[simp]:
"castVar (asSort xs) (Var xs x) = (xs,x)"
unfolding castVar_def by (rule some_equality) auto

lemma isVar_castVar:
assumes "isVar s X"
shows "asSort (fst (castVar s X)) = s \<and>
       Var (fst (castVar s X)) (snd (castVar s X)) = X"
using assms isVar_def by auto

lemma asSort_castVar[simp]:
"isVar s X \<Longrightarrow> asSort (fst (castVar s X)) = s"
using isVar_castVar by auto

lemma Var_castVar[simp]:
"isVar s X \<Longrightarrow> Var (fst (castVar s X)) (snd (castVar s X)) = X"
using isVar_castVar by auto

lemma castVar_inj[simp]:
assumes *: "isVar s X" and **: "isVar s' X'"
shows "(castVar s X = castVar s' X') = (s = s' \<and> X = X')"
using assms Var_castVar asSort_castVar by fastforce 

lemmas castVar_simps =
castVar_asSort_Var
asSort_castVar Var_castVar castVar_inj

(* Properties of isOp and castOp: *)

lemma isOp_stOf_Op[simp]:
"\<lbrakk>wlsInp delta inp; wlsBinp delta binp\<rbrakk>
 \<Longrightarrow> isOp (stOf delta) (Op delta inp binp)"
unfolding isOp_def by auto

lemma not_isOp_Var[simp]:
"\<not> isOp s (Var xs X)"
unfolding isOp_def by auto

lemma isOp_imp_wls:
"isOp s X \<Longrightarrow> wls s X"
unfolding isOp_def by auto

lemmas isOp_simps =
isOp_stOf_Op not_isOp_Var

lemma castOp_stOf_Op[simp]:
assumes "wlsInp delta inp" and "wlsBinp delta binp"
shows "castOp (stOf delta) (Op delta inp binp) = (delta,inp,binp)"
using assms unfolding castOp_def by (intro some_equality) auto

lemma isOp_castOp:
assumes "isOp s X"
shows "wlsInp (fst3 (castOp s X)) (snd3 (castOp s X)) \<and>
       wlsBinp (fst3 (castOp s X)) (trd3 (castOp s X)) \<and>
       stOf (fst3 (castOp s X)) = s \<and>
       Op (fst3 (castOp s X)) (snd3 (castOp s X)) (trd3 (castOp s X)) = X"
proof-
  let ?phi = "\<lambda> DIB. wlsInp (fst3 DIB) (snd3 DIB) \<and>
                      wlsBinp (fst3 DIB) (trd3 DIB) \<and>
                      s = stOf (fst3 DIB) \<and>
                      X = Op (fst3 DIB) (snd3 DIB) (trd3 DIB)"
  obtain delta inp binp where "?phi (delta,inp,binp)"
  using assms unfolding isOp_def by auto
  hence "?phi (castOp s X)" using someI[of ?phi] by simp
  thus ?thesis by simp
qed

lemma wlsInp_castOp[simp]:
"isOp s X \<Longrightarrow> wlsInp (fst3 (castOp s X)) (snd3 (castOp s X))"
using isOp_castOp by auto

lemma wlsBinp_castOp[simp]:
"isOp s X \<Longrightarrow> wlsBinp (fst3 (castOp s X)) (trd3 (castOp s X))"
using isOp_castOp by auto

lemma stOf_castOp[simp]:
"isOp s X \<Longrightarrow> stOf (fst3 (castOp s X)) = s"
using isOp_castOp by auto

lemma Op_castOp[simp]:
"isOp s X \<Longrightarrow>
 Op (fst3 (castOp s X)) (snd3 (castOp s X)) (trd3 (castOp s X)) = X"
using isOp_castOp by auto

lemma castOp_inj[simp]:
assumes "isOp s X" and "isOp s' X'"
shows "(castOp s X = castOp s' X') = (s = s' \<and> X = X')"
using assms Op_castOp stOf_castOp by fastforce
 
lemmas castOp_simps =
castOp_stOf_Op wlsInp_castOp wlsBinp_castOp
stOf_castOp Op_castOp castOp_inj

(* isVar and castVar versus isOp and castOp: *)

lemma not_isVar_isOp:
"\<not> (isVar s X \<and> isOp s X)"
unfolding isVar_def isOp_def by auto

lemma isVar_or_isOp:
"wls s X \<Longrightarrow> isVar s X \<or> isOp s X"
by(erule wls_cases) auto

(* Properties of the case-analysis operator: *)

lemma sortTermCase_asSort_Var_simp[simp]:
"sortTermCase fVar fOp (asSort xs) (Var xs x) = fVar xs x"
unfolding sortTermCase_def by auto

lemma sortTermCase_stOf_Op_simp[simp]:
"\<lbrakk>wlsInp delta inp; wlsBinp delta binp\<rbrakk> \<Longrightarrow>
 sortTermCase fVar fOp (stOf delta) (Op delta inp binp) = fOp delta inp binp"
unfolding sortTermCase_def by auto

lemma sortTermCase_cong[fundef_cong]:
assumes "\<And> xs x. fVar xs x = gVar xs x"
and "\<And> delta inp binp. \<lbrakk>wlsInp delta inp; wlsInp delta inp\<rbrakk>
                        \<Longrightarrow> fOp delta inp binp = gOp delta inp binp"
shows "wls s X \<Longrightarrow>
       sortTermCase fVar fOp s X = sortTermCase gVar gOp s X"
apply(erule wls_cases) using assms by auto

lemmas sortTermCase_simps =
sortTermCase_asSort_Var_simp
sortTermCase_stOf_Op_simp

lemmas term_cast_simps =
isOp_simps castOp_simps sortTermCase_simps

subsubsection {* For abstractions *}

text {* Here, the situation will be different than that of terms, since:
\\- an abstraction can only be built using ``Abs", hence we need no ``is" operators;
\\- the constructor ``Abs" for abstractions is not injective, so need a more subtle condition
on the case-analysis operator.

Yet another difference is that when casting an abstraction ``A" such that ``wlsAbs (xs,s) A",
we need to cast only the value ``A", and not the sorting part``xs s", since the latter
already contains the desired information. Consequently, below, in the arguments for the case-analysis
operator, the sorts ``xs s" come before the function ``f", and the latter doesnot take sorts into account. *}

(* Definitions: *)

definition castAbs where
"castAbs xs s A \<equiv> SOME x_X. wls s (snd x_X) \<and> A = Abs xs (fst x_X) (snd x_X)"

definition absCase where
"absCase xs s f A \<equiv> if wlsAbs (xs,s) A then f (fst (castAbs xs s A)) (snd (castAbs xs s A)) else undefined"

definition compatAbsSwap where
"compatAbsSwap xs s f \<equiv>
 \<forall> x X x' X'. (\<forall> y. (y = x \<or> fresh xs y X) \<and> (y = x' \<or> fresh xs y X')
                    \<longrightarrow> (X #[y \<and> x]_xs) = (X' #[y \<and> x']_xs))
              \<longrightarrow> f x X = f x' X'"

definition compatAbsSubst where
"compatAbsSubst xs s f \<equiv>
 \<forall> x X x' X'. (\<forall> Y. wls (asSort xs) Y \<longrightarrow> (X #[Y / x]_xs) = (X' #[Y / x']_xs))
              \<longrightarrow> f x X = f x' X'"

definition compatAbsVsubst where
"compatAbsVsubst xs s f \<equiv>
 \<forall> x X x' X'. (\<forall> y. (X #[y // x]_xs) = (X' #[y // x']_xs))
              \<longrightarrow> f x X = f x' X'"

(* Properties of castAbs: *)

lemma wlsAbs_castAbs:
assumes "wlsAbs (xs,s) A"
shows "wls s (snd (castAbs xs s A)) \<and>
       Abs xs (fst (castAbs xs s A)) (snd (castAbs xs s A)) = A"
proof-
  let ?phi = "\<lambda> x_X. wls s (snd x_X) \<and>
                     A = Abs xs (fst x_X) (snd x_X)"
  obtain x X where "?phi (x,X)" using assms wlsAbs_nchotomy[of xs s A] by auto
  hence "?phi (castAbs xs s A)" unfolding castAbs_def using someI[of ?phi] by auto
  thus ?thesis by simp
qed

lemma wls_castAbs[simp]:
"wlsAbs (xs,s) A \<Longrightarrow> wls s (snd (castAbs xs s A))"
using wlsAbs_castAbs by auto

lemma Abs_castAbs[simp]:
"wlsAbs (xs,s) A \<Longrightarrow> Abs xs (fst (castAbs xs s A)) (snd (castAbs xs s A)) = A"
using wlsAbs_castAbs by auto

lemma castAbs_Abs_swap:
assumes "isInBar (xs,s)" and X: "wls s X"
and yxX: "y = x \<or> fresh xs y X" and yx'X': "y = x' \<or> fresh xs y X'"
and *: "castAbs xs s (Abs xs x X) = (x',X')"
shows "(X #[y \<and> x]_xs) = (X' #[y \<and> x']_xs)"
proof-
  have "wlsAbs (xs,s) (Abs xs x X)" using assms by simp
  moreover
  have "x' = fst (castAbs xs s (Abs xs x X))" and
       "X' = snd (castAbs xs s (Abs xs x X))" using * by auto
  ultimately
  have "wls s X'" and "Abs xs x X = Abs xs x' X'" by auto
  thus ?thesis using yxX yx'X' X by(auto simp add: wls_Abs_swap_all)
qed

lemma castAbs_Abs_subst:
assumes isInBar: "isInBar (xs,s)"
and X: "wls s X" and Y: "wls (asSort xs) Y"
and *: "castAbs xs s (Abs xs x X) = (x',X')"
shows "(X #[Y / x]_xs) = (X' #[Y / x']_xs)"
proof-
  have "wlsAbs (xs,s) (Abs xs x X)" using isInBar X by simp
  moreover
  have "x' = fst (castAbs xs s (Abs xs x X))" and
       "X' = snd (castAbs xs s (Abs xs x X))" using * by auto
  ultimately
  have "wls s X'" and "Abs xs x X = Abs xs x' X'" by auto
  thus ?thesis using Y X by(auto simp add: wls_Abs_subst_all)
qed

lemma castAbs_Abs_vsubst:
assumes "isInBar (xs,s)" and "wls s X"
and "castAbs xs s (Abs xs x X) = (x',X')"
shows "(X #[y // x]_xs) = (X' #[y // x']_xs)"
using assms unfolding vsubst_def  
by (intro castAbs_Abs_subst) auto

lemma castAbs_inj[simp]:
assumes *: "wlsAbs (xs,s) A" and **: "wlsAbs (xs,s) A'"
shows "(castAbs xs s A = castAbs xs s A') = (A = A')"
using assms Abs_castAbs by fastforce

lemmas castAbs_simps =
wls_castAbs Abs_castAbs castAbs_inj

(* Properties of the case-analysis operator: *)

lemma absCase_Abs_swap[simp]:
assumes isInBar: "isInBar (xs,s)" and X: "wls s X"
and f_compat: "compatAbsSwap xs s f"
shows "absCase xs s f (Abs xs x X) = f x X"
proof-
  obtain x' X' where 1: "castAbs xs s (Abs xs x X) = (x',X')"
  by (cases "castAbs xs s (Abs xs x X)", auto)
  hence 2: "absCase xs s f (Abs xs x X) = f x' X'"
  unfolding absCase_def using isInBar X by auto
  have "\<And> y. (y = x \<or> fresh xs y X) \<and> (y = x' \<or> fresh xs y X')
              \<Longrightarrow> (X #[y \<and> x]_xs) = (X' #[y \<and> x']_xs)"
  using isInBar X 1 by(simp add: castAbs_Abs_swap)
  hence "f x X = f x' X'" using f_compat
  unfolding compatAbsSwap_def by fastforce
  thus ?thesis using 2 by simp
qed

lemma absCase_Abs_subst[simp]:
assumes isInBar: "isInBar (xs,s)" and X: "wls s X"
and f_compat: "compatAbsSubst xs s f"
shows "absCase xs s f (Abs xs x X) = f x X"
proof-
  obtain x' X' where 1: "castAbs xs s (Abs xs x X) = (x',X')"
  by (cases "castAbs xs s (Abs xs x X)") auto
  hence 2: "absCase xs s f (Abs xs x X) = f x' X'"
  unfolding absCase_def using isInBar X by auto
  have "\<And> Y. wls (asSort xs) Y \<Longrightarrow> (X #[Y / x]_xs) = (X' #[Y / x']_xs)"
  using isInBar X 1 by(simp add: castAbs_Abs_subst)
  hence "f x X = f x' X'" using f_compat unfolding compatAbsSubst_def by blast
  thus ?thesis using 2 by simp
qed

lemma compatAbsVsubst_imp_compatAbsSubst[simp]:
"compatAbsVsubst xs s f \<Longrightarrow> compatAbsSubst xs s f"
unfolding compatAbsSubst_def compatAbsVsubst_def
vsubst_def by auto

lemma absCase_Abs_vsubst[simp]:
assumes "isInBar (xs,s)" and "wls s X"
and "compatAbsVsubst xs s f"
shows "absCase xs s f (Abs xs x X) = f x X"
using assms by(simp add: absCase_Abs_subst)

lemma absCase_cong[fundef_cong]:
assumes "compatAbsSwap xs s f \<or> compatAbsSubst xs s f \<or> compatAbsVsubst xs s f"
and "compatAbsSwap xs s f' \<or> compatAbsSubst xs s f' \<or> compatAbsVsubst xs s f'"
and "\<And> x X. wls s X \<Longrightarrow> f x X = f' x X"
shows "wlsAbs (xs,s) A \<Longrightarrow>
       absCase xs s f A = absCase xs s f' A"
apply(erule wlsAbs_cases) using assms by auto

lemmas absCase_simps = absCase_Abs_swap absCase_Abs_subst
compatAbsVsubst_imp_compatAbsSubst absCase_Abs_vsubst

lemmas abs_cast_simps = castAbs_simps absCase_simps

lemmas cast_simps = term_cast_simps abs_cast_simps

lemmas wls_item_simps =
wlsAll_imp_goodAll  paramS_simps Cons_wls_simps all_preserve_wls
wls_freeCons wls_allOpers_simps wls_allOpers_otherSimps Abs_inj_fresh cast_simps


(* Since the transition from good terms to well-sorted terms is complete, we
no longer need the ``good" layer: *) 

lemmas wls_copy_of_good_item_simps = good_freeCons  good_allOpers_simps good_allOpers_otherSimps
param_simps  all_preserve_good

declare wls_copy_of_good_item_simps [simp del]
declare qItem_simps [simp del]   declare qItem_versus_item_simps [simp del]

end (* context FixSyn  *)

end

