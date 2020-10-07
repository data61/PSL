section\<open>Untyped (Unsorted) First-Order Logic\<close>
theory U
imports TermsAndClauses
begin

text\<open>Even though untyped FOL is a particular case of many-typed FOL, we find 
it convenient to represent it separately.\<close>

subsection \<open>Signatures\<close>

locale Signature =
fixes
    wtFsym :: "'fsym \<Rightarrow> bool"
and wtPsym :: "'psym \<Rightarrow> bool"
and arOf :: "'fsym \<Rightarrow> nat"
and parOf :: "'psym \<Rightarrow> nat"
assumes countable_wtFsym: "countable {f::'fsym. wtFsym f}"
and countable_wtPsym: "countable {p::'psym. wtPsym p}"
begin

(* Well-typed terms *)
fun wt where
"wt (Var x) \<longleftrightarrow> True"
|
"wt (Fn f Tl) \<longleftrightarrow> wtFsym f \<and> list_all wt Tl \<and> arOf f = length Tl"

lemma wt_induct[elim, consumes 1, case_names Var Fn, induct pred: wt]:
assumes T: "wt T"
and Var: "\<And> x. \<phi> (Var x)"
and Fn:
"\<And> f Tl.
   \<lbrakk>wtFsym f; list_all wt Tl; arOf f = length Tl; list_all \<phi> Tl\<rbrakk>
 \<Longrightarrow> \<phi> (Fn f Tl)"
shows "\<phi> T"
proof-
  have "wt T \<longrightarrow> \<phi> T"
  apply (induct T) using Var Fn by (auto simp: list_all_iff)
  thus ?thesis using T by auto
qed

(* Well-typed substitutions *)
definition "wtSB \<pi> \<equiv> \<forall> x. wt (\<pi> x)"

lemma wtSB_wt[simp]: "wtSB \<pi> \<Longrightarrow> wt (\<pi> x)"
unfolding wtSB_def by auto

lemma wt_subst[simp]:
assumes "wtSB \<pi>" and "wt T"
shows "wt (subst \<pi> T)"
using assms by (induct T) (auto simp: list_all_length)


lemma wtSB_o:
assumes 1: "wtSB \<pi>1" and 2: "wtSB \<pi>2"
shows "wtSB (subst \<pi>1 o \<pi>2)"
using 2 unfolding wtSB_def using 1 by auto


end (* context Signature *)


subsection \<open>Structures\<close>

(* Environment *)
type_synonym 'univ env = "var \<Rightarrow> 'univ"

(* Structure *)
locale Struct = Signature wtFsym wtPsym arOf parOf
for wtFsym and wtPsym
and arOf :: "'fsym \<Rightarrow> nat"
and parOf :: "'psym \<Rightarrow> nat"
+
fixes
    D :: "'univ \<Rightarrow> bool"
and intF :: "'fsym \<Rightarrow> 'univ list \<Rightarrow> 'univ"
and intP :: "'psym \<Rightarrow> 'univ list \<Rightarrow> bool"
assumes
NE_D: "NE D" and
intF: "\<lbrakk>wtFsym f; length al = arOf f; list_all D al\<rbrakk> \<Longrightarrow> D (intF f al)"
and
dummy: "parOf = parOf \<and> intF = intF \<and> intP = intP"
begin

(* Well-typed environment *)
definition "wtE \<xi> \<equiv> \<forall> x. D (\<xi> x)"

lemma wtTE_D[simp]: "wtE \<xi> \<Longrightarrow> D (\<xi> x)"
unfolding wtE_def by simp

(* Interpretation of terms: *)
fun int where
"int \<xi> (Var x) = \<xi> x"
|
"int \<xi> (Fn f Tl) = intF f (map (int \<xi>) Tl)"

(* Soundness of typing w.r.t. interpretation: *)
lemma wt_int:
assumes wtE: "wtE \<xi>" and wt_T: "wt T"
shows "D (int \<xi> T)"
using wt_T apply(induct T)
apply (metis int.simps(1) wtE wtE_def)
unfolding int.simps apply(rule intF)
unfolding list_all_map comp_def by auto

lemma int_cong:
assumes "\<And>x. x \<in> vars T \<Longrightarrow> \<xi>1 x = \<xi>2 x"
shows "int \<xi>1 T = int \<xi>2 T"
using assms apply(induct T) apply simp_all unfolding list_all_iff
using map_ext by metis

lemma int_o:
"int (int \<xi> o \<rho>) T = int \<xi> (subst \<rho> T)"
apply(induct T) apply simp_all  unfolding list_all_iff o_def 
using map_ext by (metis (lifting, no_types))

lemmas int_subst = int_o[symmetric]

lemma int_o_subst:
"int \<xi> o subst \<rho> = int (int \<xi> o \<rho>)"
apply(rule ext) apply(subst comp_def) unfolding int_o[symmetric] ..

lemma wtE_o:
assumes 1: "wtE \<xi>" and 2: "wtSB \<rho>"
shows "wtE (int \<xi> o \<rho>)"
unfolding wtE_def apply safe
unfolding comp_def apply(rule wt_int[OF 1]) using 2 by auto

end


context Signature begin

text\<open>Well-typed (i.e., well-formed) atoms, literals, caluses and problems:\<close>

fun wtA where
"wtA (Eq T1 T2) \<longleftrightarrow> wt T1 \<and> wt T2"
|
"wtA (Pr p Tl) \<longleftrightarrow> wtPsym p \<and> list_all wt Tl \<and> parOf p = length Tl"

fun wtL where
"wtL (Pos a) \<longleftrightarrow> wtA a"
|
"wtL (Neg a) \<longleftrightarrow> wtA a"

definition "wtC \<equiv> list_all wtL"

definition "wtPB \<Phi> \<equiv> \<forall> c \<in> \<Phi>. wtC c"

end (* context Signature *)


context Struct begin

(* Satisfaction of atoms: *)
fun satA where
"satA \<xi> (Eq T1 T2) \<longleftrightarrow> int \<xi> T1 = int \<xi> T2"
|
"satA \<xi> (Pr r Tl) \<longleftrightarrow> intP r (map (int \<xi>) Tl)"

(* Satisfaction literals: *)
fun satL where
"satL \<xi> (Pos a) \<longleftrightarrow> satA \<xi> a"
|
"satL \<xi> (Neg a) \<longleftrightarrow> \<not> satA \<xi> a"

(* Satisfaction of clauses: *)
definition "satC \<xi> \<equiv> list_ex (satL \<xi>)"

(* satisfaction of problems *)
definition "satPB \<xi> \<Phi> \<equiv> \<forall> c \<in> \<Phi>. satC \<xi> c"

definition "SAT \<Phi> \<equiv> \<forall> \<xi>. wtE \<xi> \<longrightarrow> satPB \<xi> \<Phi>"

end (* context Struct *)


subsection\<open>Problems\<close>

locale Problem = Signature wtFsym wtPsym arOf parOf
for wtFsym and wtPsym
and arOf :: "'fsym \<Rightarrow> nat"
and parOf :: "'psym \<Rightarrow> nat"
+
fixes \<Phi> :: "('fsym, 'psym) prob"
assumes wt_\<Phi>: "wtPB \<Phi>"


subsection\<open>Models of a problem\<close>

locale Model =
  Problem wtFsym wtPsym arOf parOf \<Phi> +
  Struct wtFsym wtPsym arOf parOf D intF intP
for wtFsym and wtPsym
and arOf :: "'fsym \<Rightarrow> nat"
and parOf :: "'psym \<Rightarrow> nat"
and \<Phi> :: "('fsym, 'psym) prob"
and D :: "'univ \<Rightarrow> bool"
and intF :: "'fsym \<Rightarrow> 'univ list \<Rightarrow> 'univ"
and intP :: "'psym \<Rightarrow> 'univ list \<Rightarrow> bool"
+
assumes SAT: "SAT \<Phi>"


end
