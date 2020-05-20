section\<open>Syntax of Terms and Clauses\<close>
theory TermsAndClauses
imports Preliminaries
begin

text
\<open>These are used for both unsorted and many-sorted FOL, the difference being that,
for the latter, the signature will fix a variable typing.\<close>

text\<open>Terms:\<close>

datatype 'fsym trm =
  Var var |
  Fn 'fsym "'fsym trm list"

text\<open>Atomic formulas (atoms):\<close>

datatype ('fsym, 'psym) atm =
  Eq "'fsym trm" "'fsym trm" |
  Pr 'psym "'fsym trm list"

text\<open>Literals:\<close>

datatype ('fsym, 'psym) lit =
  Pos "('fsym, 'psym) atm" |
  Neg "('fsym, 'psym) atm"

text\<open>Clauses:\<close>

type_synonym ('fsym, 'psym) cls = "('fsym, 'psym) lit list"

text\<open>Problems:\<close>

type_synonym ('fsym, 'psym) prob = "('fsym, 'psym) cls set"

lemma trm_induct[case_names Var Fn, induct type: trm]:
assumes "\<And> x. \<phi> (Var x)"
and "\<And> f Tl. list_all \<phi> Tl \<Longrightarrow> \<phi> (Fn f Tl)"
shows "\<phi> T"
using assms unfolding list_all_iff by (rule trm.induct) metis

fun vars where
"vars (Var x) = {x}"
|
"vars (Fn f Tl) = \<Union> (vars ` (set Tl))"

fun varsA where
"varsA (Eq T1 T2) = vars T1 \<union> vars T2"
|
"varsA (Pr p Tl) = \<Union> (set (map vars Tl))"

fun varsL where
"varsL (Pos at) = varsA at"
|
"varsL (Neg at) = varsA at"

definition "varsC c = \<Union> (set (map varsL c))"

definition "varsPB \<Phi> = \<Union> {varsC c | c. c \<in> \<Phi>}"

text\<open>Substitution:\<close>

fun subst where
"subst \<pi> (Var x) = \<pi> x"
|
"subst \<pi> (Fn f Tl) = Fn f (map (subst \<pi>) Tl)"

fun substA where
"substA \<pi> (Eq T1 T2) = Eq (subst \<pi> T1) (subst \<pi> T2)"
|
"substA \<pi> (Pr p Tl) = Pr p (map (subst \<pi>) Tl)"

fun substL where
"substL \<pi> (Pos at) = Pos (substA \<pi> at)"
|
"substL \<pi> (Neg at) = Neg (substA \<pi> at)"

definition "substC \<pi> c = map (substL \<pi>) c"

definition "substPB \<pi> \<Phi> = {substC \<pi> c | c. c \<in> \<Phi>}"

lemma subst_cong:
assumes "\<And> x. x \<in> vars T \<Longrightarrow> \<pi>1 x = \<pi>2 x"
shows "subst \<pi>1 T = subst \<pi>2 T"
using assms by (induct T, auto simp add: list_all_iff)

lemma substA_congA:
assumes "\<And> x. x \<in> varsA at \<Longrightarrow> \<pi>1 x = \<pi>2 x"
shows "substA \<pi>1 at = substA \<pi>2 at"
using assms subst_cong[of _ \<pi>1 \<pi>2]
by (cases at, fastforce+)

lemma substL_congL:
assumes "\<And> x. x \<in> varsL l \<Longrightarrow> \<pi>1 x = \<pi>2 x"
shows "substL \<pi>1 l = substL \<pi>2 l"
using assms substA_congA[of _ \<pi>1 \<pi>2] by (cases l, auto)

lemma substC_congC:
assumes "\<And> x. x \<in> varsC c \<Longrightarrow> \<pi>1 x = \<pi>2 x"
shows "substC \<pi>1 c = substC \<pi>2 c"
using substL_congL[of _ \<pi>1 \<pi>2] assms unfolding substC_def varsC_def
by (induct c, auto)

lemma substPB_congPB:
assumes "\<And> x. x \<in> varsPB \<Phi> \<Longrightarrow> \<pi>1 x = \<pi>2 x"
shows "substPB \<pi>1 \<Phi> = substPB \<pi>2 \<Phi>"
using substC_congC[of _ \<pi>1 \<pi>2] assms unfolding substPB_def varsPB_def
by simp_all (metis (lifting) substC_congC) 

lemma vars_subst:
"vars (subst \<pi> T) = (\<Union> x \<in> vars T. vars (\<pi> x))"
by (induct T) (auto simp add: list_all_iff)

lemma varsA_substA:
"varsA (substA \<pi> at) = (\<Union> x \<in> varsA at. vars (\<pi> x))"
using vars_subst[of \<pi>] by (cases at, auto)

lemma varsL_substL:
"varsL (substL \<pi> l) = (\<Union> x \<in> varsL l. vars (\<pi> x))"
using varsA_substA[of \<pi>] by (cases l, auto)

lemma varsC_substC:
"varsC (substC \<pi> c) = (\<Union> x \<in> varsC c. vars (\<pi> x))"
apply(induct c) unfolding substC_def varsC_def
  apply fastforce
  unfolding substC_def varsC_def map_map set_map
  unfolding comp_def varsL_substL by blast

lemma varsPB_Un[simp]: "varsPB (\<Phi>1 \<union> \<Phi>2) = varsPB \<Phi>1 \<union> varsPB \<Phi>2"
unfolding varsPB_def by auto

lemma varsC_append[simp]: "varsC (c1 @ c2) = varsC c1 \<union> varsC c2"
unfolding varsC_def by auto

lemma varsPB_sappend_incl[simp]:
"varsPB (\<Phi>1 @@ \<Phi>2) \<subseteq>  varsPB \<Phi>1 \<union> varsPB \<Phi>2"
by (unfold varsPB_def sappend_def, fastforce)

lemma varsPB_sappend[simp]:
assumes 1: "\<Phi>1 \<noteq> {}" and 2: "\<Phi>2 \<noteq> {}"
shows "varsPB (\<Phi>1 @@ \<Phi>2) = varsPB \<Phi>1 \<union> varsPB \<Phi>2"
proof safe
  fix x
  {assume "x \<in> varsPB \<Phi>1"
   then obtain c1 c2 where "x \<in> varsC c1" and "c1 \<in> \<Phi>1" and "c2 \<in> \<Phi>2"
   using 2 unfolding varsPB_def by auto
   thus "x \<in> varsPB (\<Phi>1 @@ \<Phi>2)" unfolding sappend_def varsPB_def by fastforce
  }
  {assume "x \<in> varsPB \<Phi>2"
   then obtain c1 c2 where "x \<in> varsC c2" and "c1 \<in> \<Phi>1" and "c2 \<in> \<Phi>2"
   using 1 unfolding varsPB_def by auto
   thus "x \<in> varsPB (\<Phi>1 @@ \<Phi>2)" unfolding sappend_def varsPB_def by fastforce
  }
qed(unfold varsPB_def sappend_def, fastforce)

lemma varsPB_substPB:
"varsPB (substPB \<pi> \<Phi>) = (\<Union> x \<in> varsPB \<Phi>. vars (\<pi> x))" (is "_ = ?K")
proof safe
  fix x assume "x \<in> varsPB (substPB \<pi> \<Phi>)"
  then obtain c where "c \<in> \<Phi>" and "x \<in> varsC (substC \<pi> c)"
  unfolding varsPB_def substPB_def by auto
  thus "x \<in> ?K" unfolding varsC_substC varsPB_def by auto
next
  fix x y assume "y \<in> varsPB \<Phi>" and x: "x \<in> vars (\<pi> y)"
  then obtain c where c: "c \<in> \<Phi>" and "y \<in> varsC c" unfolding varsPB_def by auto
  hence "x \<in> varsC (substC \<pi> c)" using x unfolding varsC_substC by auto
  thus "x \<in> varsPB (substPB \<pi> \<Phi>)" using c unfolding varsPB_def substPB_def by auto
qed

lemma subst_o:
"subst (subst \<pi>1 o \<pi>2) T = subst \<pi>1 (subst \<pi>2 T)"
apply(induct T) by (auto simp add: list_all_iff)

lemma o_subst:
"subst \<pi>1 o subst \<pi>2 = subst (subst \<pi>1 o \<pi>2)"
apply(rule ext) apply(subst comp_def) unfolding subst_o[symmetric] ..

lemma substA_o:
"substA (subst \<pi>1 o \<pi>2) at = substA \<pi>1 (substA \<pi>2 at)"
using subst_o[of \<pi>1 \<pi>2] by (cases at, auto)

lemma o_substA:
"substA \<pi>1 o substA \<pi>2 = substA (subst \<pi>1 o \<pi>2)"
apply(rule ext) apply(subst comp_def) unfolding substA_o[symmetric] ..

lemma substL_o:
"substL (subst \<pi>1 o \<pi>2) l = substL \<pi>1 (substL \<pi>2 l)"
using substA_o[of \<pi>1 \<pi>2] by (cases l, auto)

lemma o_substL:
"substL \<pi>1 o substL \<pi>2 = substL (subst \<pi>1 o \<pi>2)"
apply(rule ext) apply(subst comp_def) unfolding substL_o[symmetric] ..

lemma substC_o:
"substC (subst \<pi>1 o \<pi>2) c = substC \<pi>1 (substC \<pi>2 c)"
using substL_o[of \<pi>1 \<pi>2] unfolding substC_def by (induct c, auto)

lemma o_substC:
"substC \<pi>1 o substC \<pi>2 = substC (subst \<pi>1 o \<pi>2)"
apply(rule ext) apply(subst comp_def) unfolding substC_o[symmetric] ..

lemma substPB_o:
"substPB (subst \<pi>1 o \<pi>2) \<Phi> = substPB \<pi>1 (substPB \<pi>2 \<Phi>)"
using substC_o[of \<pi>1 \<pi>2] unfolding substPB_def by auto

lemma o_substPB:
"substPB \<pi>1 o substPB \<pi>2 = substPB (subst \<pi>1 o \<pi>2)"
apply(rule ext) apply(subst comp_def) unfolding substPB_o[symmetric] ..

lemma finite_vars: "finite (vars T)"
by(induct T, auto simp add: list_all_iff)

lemma finite_varsA: "finite (varsA at)"
using finite_vars by (cases at, auto)

lemma finite_varsL: "finite (varsL l)"
using finite_varsA by (cases l, auto)

lemma finite_varsC: "finite (varsC c)"
using finite_varsL unfolding varsC_def by (induct c, auto)

lemma finite_varsPB: "finite \<Phi> \<Longrightarrow> finite (varsPB \<Phi>)"
using finite_varsC unfolding varsPB_def by (auto intro!: finite_Union)

end
