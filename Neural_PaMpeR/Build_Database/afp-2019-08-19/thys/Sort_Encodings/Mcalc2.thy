section \<open>The Second Monotonicity Calculus\<close>
theory Mcalc2
imports Mono
begin



subsection\<open>Extension policies\<close>

text\<open>Extension policy: copy, true or false extension:\<close>

datatype epol = Cext | Text | Fext

text\<open>Problem with infinite knowledge and predicate-extension policy:\<close>

locale ProblemIkPol = ProblemIk wtFsym wtPsym arOf resOf parOf \<Phi> infTp
for wtFsym :: "'fsym \<Rightarrow> bool" and wtPsym :: "'psym \<Rightarrow> bool"
and arOf :: "'fsym \<Rightarrow> 'tp list"
and resOf and parOf and \<Phi> and infTp
+ fixes (* the predicate-extension policy *) pol :: "'tp \<Rightarrow> 'psym \<Rightarrow> epol"
and (* guard of a variable occurring in a certain literal of a certain clause: *)
    grdOf ::
"('fsym, 'psym) cls \<Rightarrow> ('fsym, 'psym) lit \<Rightarrow> var \<Rightarrow> ('fsym, 'psym) lit"


context ProblemIkPol begin

subsection\<open>Naked variables\<close>

fun nv2T where
"nv2T (Var x) = {x}"
|
"nv2T (Fn f Tl) = {}"

fun nv2L where
"nv2L (Pos (Eq T1 T2)) = nv2T T1 \<union> nv2T T2"
|
"nv2L (Neg (Eq T1 T2)) = {}"
|
"nv2L (Pos (Pr p Tl)) = {x \<in> \<Union> (set (map nv2T Tl)) . pol (tpOfV x) p = Fext}"
|
"nv2L (Neg (Pr p Tl)) = {x \<in> \<Union> (set (map nv2T Tl)) . pol (tpOfV x) p = Text}"

definition "nv2C c \<equiv> \<Union> (set (map nv2L c))"

lemma in_nv2T: "x \<in> nv2T T \<longleftrightarrow> T = Var x"
apply(cases T)
  apply (metis equals0D nv2T.simps singleton_iff)
  by simp

lemma nv2T_vars[simp]: "x \<in> nv2T T \<Longrightarrow> x \<in> vars T"
by (induct T, auto split: if_splits)

lemma nv2L_varsL[simp]:
assumes "x \<in> nv2L l" shows "x \<in> varsL l"
proof (cases l)
  case (Pos at)
  show ?thesis proof(cases at)
    case (Pr p Tl) thus ?thesis using assms unfolding Pos
    apply(cases "pol (tpOfV x) p", simp_all) by (metis nv2T_vars)
  qed(insert assms, unfold Pos, auto)
next
  case (Neg at)
  show ?thesis proof(cases at)
    case (Pr p Tl) thus ?thesis using assms unfolding Neg
    apply(cases "pol (tpOfV x) p", simp_all) by (metis nv2T_vars)
  qed(insert assms, unfold Neg, auto)
qed

lemma nv2C_varsC[simp]: "x \<in> nv2C c \<Longrightarrow> x \<in> varsC c"
unfolding varsC_def nv2C_def by (induct c, auto)

subsection\<open>The calculus\<close>

text\<open>The notion of a literal being a guard for a (typed) variable:\<close>

fun isGuard :: "var \<Rightarrow> ('fsym,'psym) lit \<Rightarrow> bool" where
"isGuard x (Pos (Eq T1 T2)) \<longleftrightarrow> False"
|
"isGuard x (Neg (Eq T1 T2)) \<longleftrightarrow>
 (T1 = Var x \<and> (\<exists> f Tl. T2 = Fn f Tl)) \<or>
 (T2 = Var x \<and> (\<exists> f Tl. T1 = Fn f Tl))"
|
"isGuard x (Pos (Pr p Tl)) \<longleftrightarrow> x \<in> \<Union> (set (map nv2T Tl)) \<and> pol (tpOfV x) p = Text"
|
"isGuard x (Neg (Pr p Tl)) \<longleftrightarrow> x \<in> \<Union> (set (map nv2T Tl)) \<and> pol (tpOfV x) p = Fext"


text\<open>The monotonicity calculus from the Classen et. al. paper, applied
to non-infinite types only: it checks that any variable in any literal of any clause
is indeed guarded by its guard:\<close>

inductive mcalc2 (infix "\<turnstile>2" 40) where
 [simp]: "infTp \<sigma> \<Longrightarrow> \<sigma> \<turnstile>2 c"
|[simp]: "(\<And> l x. \<lbrakk>l \<in> set c; x \<in> nv2L l; tpOfV x = \<sigma>\<rbrakk>
         \<Longrightarrow> isGuard x (grdOf c l x)) \<Longrightarrow> \<sigma> \<turnstile>2 c"

lemma mcalc2_iff:
"\<sigma> \<turnstile>2 c \<longleftrightarrow>
 infTp \<sigma> \<or> (\<forall> l x. l \<in> set c \<and> x \<in> nv2L l \<and> tpOfV x = \<sigma> \<longrightarrow> isGuard x (grdOf c l x))"
unfolding mcalc2.simps by auto

end (* context ProblemIk *)

locale ProblemIkPolMcalc2 = ProblemIkPol wtFsym wtPsym arOf resOf parOf \<Phi> infTp pol grdOf
for wtFsym :: "'fsym \<Rightarrow> bool" and wtPsym :: "'psym \<Rightarrow> bool"
and arOf :: "'fsym \<Rightarrow> 'tp list"
and resOf and parOf and \<Phi> and infTp and pol and grdOf
+ assumes
(* well-definednedd of the guard: *)
    grdOf: "\<And> c l x. \<lbrakk>c \<in> \<Phi>; l \<in> set c; x \<in> nv2L l; \<not> infTp (tpOfV x)\<rbrakk>
                     \<Longrightarrow> grdOf c l x \<in> set c"
and mcalc2: "\<And> \<sigma> c. c \<in> \<Phi> \<Longrightarrow> \<sigma> \<turnstile>2 c"
begin
lemma wtL_grdOf[simp]:
assumes "c \<in> \<Phi>" and "l \<in> set c" and "x \<in> nv2L l" and "\<not> infTp (tpOfV x)"
shows "wtL (grdOf c l x)"
using grdOf[OF assms] by (metis assms list_all_iff wtC_def wtPB_def wt_\<Phi>)
end

locale ModelIkPolMcalc2 =
ModelIk wtFsym wtPsym arOf resOf parOf \<Phi> infTp intT intF intP +
ProblemIkPolMcalc2 wtFsym wtPsym arOf resOf parOf \<Phi> infTp pol grdOf
for wtFsym :: "'fsym \<Rightarrow> bool" and wtPsym :: "'psym \<Rightarrow> bool"
and arOf :: "'fsym \<Rightarrow> 'tp list"
and resOf and parOf and \<Phi> and infTp pol and grdOf and intT and intF and intP


end
