section\<open>The First Monotonicity Calculus\<close>
theory Mcalc
imports Mono
begin

context ProblemIk begin

subsection\<open>Naked variables\<close>

fun nvT where
"nvT (Var x) = {x}"
|
"nvT (Fn f Tl) = {}"

fun nvA where
"nvA (Eq T1 T2) = nvT T1 \<union> nvT T2"
|
"nvA (Pr p Tl) = {}"

fun nvL where
"nvL (Pos at) = nvA at"
|
"nvL (Neg at) = {}"

definition "nvC c \<equiv> \<Union> (set (map nvL c))"

definition "nvPB \<equiv> \<Union> c \<in> \<Phi>. nvC c"

lemma nvT_vars[simp]: "x \<in> nvT T \<Longrightarrow> x \<in> vars T"
by (induct T) (auto split: if_splits)

lemma nvA_varsA[simp]: "x \<in> nvA at \<Longrightarrow> x \<in> varsA at"
by (cases at, auto)

lemma nvL_varsL[simp]: "x \<in> nvL l \<Longrightarrow> x \<in> varsL l"
by (cases l, auto)

lemma nvC_varsC[simp]: "x \<in> nvC c \<Longrightarrow> x \<in> varsC c"
unfolding varsC_def nvC_def by(induct c, auto)

lemma nvPB_varsPB[simp]: "x \<in> nvPB \<Longrightarrow> x \<in> varsPB \<Phi>"
unfolding varsPB_def nvPB_def by auto


subsection\<open>The calculus\<close>

inductive mcalc (infix "\<turnstile>" 40) where
 [simp]: "infTp \<sigma> \<Longrightarrow> \<sigma> \<turnstile> c"
|[simp]: "(\<forall> x \<in> nvC c. tpOfV x \<noteq> \<sigma>) \<Longrightarrow> \<sigma> \<turnstile> c"

lemma mcalc_iff: "\<sigma> \<turnstile> c \<longleftrightarrow> infTp \<sigma> \<or> (\<forall> x \<in> nvC c. tpOfV x \<noteq> \<sigma>)"
unfolding mcalc.simps by simp

end (* context ProblemIk *)

locale ProblemIkMcalc = ProblemIk wtFsym wtPsym arOf resOf parOf \<Phi> infTp
for wtFsym :: "'fsym \<Rightarrow> bool" and wtPsym :: "'psym \<Rightarrow> bool"
and arOf :: "'fsym \<Rightarrow> 'tp list"
and resOf and parOf and \<Phi> and infTp
+ assumes mcalc: "\<And> \<sigma> c. c \<in> \<Phi> \<Longrightarrow> \<sigma> \<turnstile> c"

locale ModelIkMcalc =
ModelIk wtFsym wtPsym arOf resOf parOf \<Phi> infTp intT intF intP +
ProblemIkMcalc wtFsym wtPsym arOf resOf parOf \<Phi> infTp
for wtFsym :: "'fsym \<Rightarrow> bool" and wtPsym :: "'psym \<Rightarrow> bool"
and arOf :: "'fsym \<Rightarrow> 'tp list"
and resOf and parOf and \<Phi> and infTp and intT and intF and intP

subsection\<open>Extension of a structure to an infinite structure
by adding indistinguishable elements\<close>

context ModelIkMcalc begin

text\<open>The projection from univ to a structure:\<close>

definition proj where "proj \<sigma> a \<equiv> if intT \<sigma> a then a else pickT \<sigma>"

lemma intT_proj[simp]: "intT \<sigma> (proj \<sigma> a)"
unfolding proj_def using pickT by auto

lemma proj_id[simp]: "intT \<sigma> a \<Longrightarrow> proj \<sigma> a = a"
unfolding proj_def by auto

lemma surj_proj:
assumes "intT \<sigma> a"   shows "\<exists> b. proj \<sigma> b = a"
using assms by (intro exI[of _ a]) simp

definition "I_intT \<sigma> (a::univ) \<equiv> infTp \<sigma> \<longrightarrow> intT \<sigma> a"
definition "I_intF f al \<equiv> intF f (map2 proj (arOf f) al)"
definition "I_intP p al \<equiv> intP p (map2 proj (parOf p) al)"

lemma not_infTp_I_intT[simp]: "\<not> infTp \<sigma> \<Longrightarrow> I_intT \<sigma> a" unfolding I_intT_def by simp

lemma infTp_I_intT[simp]: "infTp \<sigma> \<Longrightarrow> I_intT \<sigma> a = intT \<sigma> a" unfolding I_intT_def by simp

lemma NE_I_intT: "NE (I_intT \<sigma>)"
using NE_intT by (cases "infTp \<sigma>", auto)

lemma I_intF:
assumes f: "wtFsym f" and al: "list_all2 I_intT (arOf f) al"
shows "I_intT (resOf f) (I_intF f al)"
unfolding I_intT_def I_intF_def apply safe apply(rule intF[OF f])
using al unfolding list_all2_length by auto

lemma Tstruct_I_intT: "Tstruct I_intT"
by standard (rule NE_I_intT)

lemma inf_I_intT: "infinite {a. I_intT \<sigma> a}"
by (cases "infTp \<sigma>", auto)

lemma InfStruct: "IInfStruct I_intT I_intF I_intP"
apply standard using NE_I_intT I_intF Tstruct_I_intT inf_I_intT by auto

end (* context ModelIkMcalc *)

sublocale ModelIkMcalc < InfStruct where
intT = I_intT and intF = I_intF and intP = I_intP
using InfStruct .

subsection\<open>The soundness of the calculus\<close>

text\<open>In what follows, ``Ik'' stands for the original
(augmented with infiniteness-knowledge)
and ``I'' for the infinite structure constructed from it
through the above sublocale statement.\<close>


context ModelIkMcalc begin

text\<open>The environment translation along the projection:\<close>
definition "transE \<xi> \<equiv> \<lambda> x. proj (tpOfV x) (\<xi> x)"

lemma transE[simp]: "transE \<xi> x = proj (tpOfV x) (\<xi> x)"
unfolding transE_def by simp

lemma wtE_transE[simp]: "I.wtE \<xi> \<Longrightarrow> Ik.wtE (transE \<xi>)"
unfolding Ik.wtE_def I.wtE_def transE_def by auto

abbreviation "Ik_intT \<equiv> intT"
abbreviation "Ik_intF \<equiv> intF"
abbreviation "Ik_intP \<equiv> intP"

lemma Ik_intT_int:
assumes wt: "Ik.wt T" and \<xi>: "I.wtE \<xi>"
and snv: "\<And> \<sigma>. infTp \<sigma> \<or> (\<forall> x \<in> nvT T. tpOfV x \<noteq> \<sigma>)"
shows "Ik_intT (tpOf T) (I.int \<xi> T)"
proof(cases "\<exists> x. T = Var x")
  case True then obtain x where T: "T = Var x" by auto
  show ?thesis proof(cases "infTp (tpOf T)")
    case True thus ?thesis using T using wtE_transE[OF \<xi>]
    by (metis I.wt_int I_intT_def \<xi> wt)
  next
    case False hence "\<forall> x \<in> nvT T. tpOfV x \<noteq> tpOf T" using snv by auto
    hence "Ik.full (tpOf T)" using T by (cases T, simp_all)
    thus ?thesis unfolding Ik.full_def by simp
  qed
next
  case False hence nonVar: "\<not> (\<exists> x. T = Var x)" by (cases T, auto)
  thus ?thesis using nonVar wt apply(induct T, force)
  unfolding I_intF_def tpOf.simps int.simps
  apply(rule Ik.intF, simp) apply(rule listAll2_map2I) by auto
qed

lemma int_transE_proj:
  assumes wt: "Ik.wt T"
  shows "Ik.int (transE \<xi>) T = proj (tpOf T) (I.int \<xi> T)"
  using wt proof (induct T)
  case (Fn f Tl)
  have 0: "Ik_intT (resOf f) (I_intF f (map (int \<xi>) Tl))" (is "Ik_intT ?\<sigma> ?a")
    unfolding I_intF_def apply(rule Ik.intF)
    using Fn unfolding list_all2_length list_all_iff by auto
  have 1: "proj ?\<sigma> ?a = ?a" using proj_id[OF 0] .
  show ?case
    using [[unfold_abs_def = false]]
    unfolding Ik.int.simps int.simps tpOf.simps 1
    unfolding I_intF_def apply(rule arg_cong[of _ _ "intF f"])
  proof (rule nth_equalityI)
    have l[simp]: "length (arOf f) = length Tl" using Fn by simp
    fix i assume "i < length (map (Ik.int (transE \<xi>)) Tl)"
    hence i[simp]: "i < length Tl" by simp
    have 0: "arOf f ! i = tpOf (Tl ! i)" using Fn by simp
    have [simp]: "Ik.int (transE \<xi>) (Tl ! i) = proj (arOf f ! i) (I.int \<xi> (Tl ! i))"
      unfolding 0 using Fn by (auto simp: list_all_length transE_def)
    show "map (Ik.int (transE \<xi>)) Tl ! i =
          map2 proj (arOf f) (map (I.int \<xi>) Tl) ! i"
      using Fn unfolding list_all_length by simp
  qed(use Fn in simp)
qed simp

lemma int_transE_snv[simp]:
assumes wt: "Ik.wt T" and \<xi>: "I.wtE \<xi>" and snv: "\<And> \<sigma>. infTp \<sigma> \<or> (\<forall> x \<in> nvT T. tpOfV x \<noteq> \<sigma>)"
shows "Ik.int (transE \<xi>) T = I.int \<xi> T"
unfolding int_transE_proj[OF wt] apply(rule proj_id)
using Ik_intT_int[OF wt \<xi> snv] .

lemma int_transE_Fn:
assumes wt: "list_all wt Tl" and f: "wtFsym f" and \<xi>: "I.wtE \<xi>"
and ar: "arOf f = map tpOf Tl"
shows "Ik.int (transE \<xi>) (Fn f Tl) = I.int \<xi> (Fn f Tl)"
apply(rule int_transE_snv) using assms by auto

lemma intP_transE[simp]:
assumes wt: "list_all wt Tl" and p: "wtPsym p" and ar: "parOf p = map tpOf Tl"
shows "Ik_intP p (map (Ik.int (transE \<xi>)) Tl) = I_intP p (map (I.int \<xi>) Tl)"
unfolding I_intP_def apply(rule arg_cong[of _ _ "Ik_intP p"])
apply(rule nth_equalityI) using assms
using int_transE_proj unfolding list_all_length by auto

lemma satA_snvA_transE[simp]:
assumes wtA: "Ik.wtA at" and \<xi>: "I.wtE \<xi>"
and pA: "\<And> \<sigma>. infTp \<sigma> \<or> (\<forall> x \<in> nvA at. tpOfV x \<noteq> \<sigma>)"
shows "Ik.satA (transE \<xi>) at \<longleftrightarrow> I.satA \<xi> at"
using assms apply (cases at, simp_all add: ball_Un) by (metis int_transE_snv)

(* The next contrapositive twist is crucial for proving satL_transE: *)
lemma satA_transE[simp]:
assumes wtA: "Ik.wtA at" and "I.satA \<xi> at"
shows "Ik.satA (transE \<xi>) at"
using assms apply(cases at) using int_transE_proj by auto

lemma satL_snvL_transE[simp]:
assumes wtL: "Ik.wtL l" and \<xi>: "I.wtE \<xi>"
and pL: "\<And> \<sigma>. infTp \<sigma> \<or> (\<forall> x \<in> nvL l. tpOfV x \<noteq> \<sigma>)" and "Ik.satL (transE \<xi>) l"
shows "I.satL \<xi> l"
using assms by (cases l) auto

lemma satC_snvC_transE[simp]:
assumes wtC: "Ik.wtC c" and \<xi>: "I.wtE \<xi>"
and pC: "\<And> \<sigma>. \<sigma> \<turnstile> c" and "Ik.satC (transE \<xi>) c"
shows "I.satC \<xi> c"
using assms unfolding Ik.mcalc_iff Ik.satC_def satC_def Ik.wtC_def nvC_def
unfolding list_all_iff list_ex_iff apply simp by (metis nth_mem satL_snvL_transE)

lemma satPB_snvPB_transE[simp]:
assumes \<xi>: "I.wtE \<xi>"  shows "I.satPB \<xi> \<Phi>"
using Ik.wt_\<Phi> Ik.sat_\<Phi>[OF wtE_transE[OF \<xi>]]
using mcalc \<xi> unfolding Ik.satPB_def satPB_def Ik.wtPB_def nvPB_def by auto

lemma I_SAT: "I.SAT \<Phi>" unfolding I.SAT_def by auto

lemma InfModel: "IInfModel I_intT I_intF I_intP"
by standard (rule I_SAT)

end (* context ModelIkMcalc *)

sublocale ModelIkMcalc < inf?: InfModel where
intT = I_intT and intF = I_intF and intP = I_intP
using InfModel .

context ProblemIkMcalc begin

abbreviation "MModelIkMcalc \<equiv> ModelIkMcalc wtFsym wtPsym arOf resOf parOf \<Phi> infTp"

theorem monot: monot
unfolding monot_def proof safe
  fix intT intF intP assume "MModel intT intF intP"
  hence M: "MModelIkMcalc intT intF intP"
  unfolding ModelIkMcalc_def ModelIk_def apply safe ..
  show "\<exists> intTI intFI intPI. IInfModel intTI intFI intPI"
  using ModelIkMcalc.InfModel[OF M] by auto
qed

end (* context ProblemIkMcalc *)

text\<open>Final theorem in sublocale form: Any problem that passes the
  monotonicity calculus is monotonic:\<close>

sublocale ProblemIkMcalc < MonotProblem
by standard (rule monot)

end
