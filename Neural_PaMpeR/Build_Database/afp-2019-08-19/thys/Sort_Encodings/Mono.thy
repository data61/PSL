section\<open>Monotonicity\<close>
theory Mono imports CM begin


subsection\<open>Fullness and infiniteness\<close>

text\<open>In a structure, a full type is one that contains all elements of univ (the fixed countable universe):\<close>

definition (in Tstruct) "full \<sigma> \<equiv> \<forall> d. intT \<sigma> d"

locale FullStruct = F? : Struct +
assumes full: "full \<sigma>"
begin
lemma full2[simp]: "intT \<sigma> d"
using full unfolding full_def by simp

lemma full_True: "intT = (\<lambda> \<sigma> D. True)"
apply(intro ext) by auto
end

locale FullModel =
F? : Model wtFsym wtPsym arOf resOf parOf \<Phi> intT intF intP +
F? : FullStruct wtFsym wtPsym arOf resOf parOf intT intF intP
for wtFsym :: "'fsym \<Rightarrow> bool" and wtPsym :: "'psym \<Rightarrow> bool"
and arOf :: "'fsym \<Rightarrow> 'tp list"
and resOf and parOf and \<Phi> and intT and intF and intP

text\<open>An infinite structure is one with all carriers infinite:\<close>

locale InfStruct = I? : Struct +
assumes inf: "infinite {a. intT \<sigma> a}"

locale InfModel =
I? : Model wtFsym wtPsym arOf resOf parOf \<Phi> intT intF intP +
I? : InfStruct wtFsym wtPsym arOf resOf parOf intT intF intP
for wtFsym :: "'fsym \<Rightarrow> bool" and wtPsym :: "'psym \<Rightarrow> bool"
and arOf :: "'fsym \<Rightarrow> 'tp list"
and resOf and parOf and \<Phi> and intT and intF and intP

context Problem begin
abbreviation "SStruct \<equiv> Struct wtFsym wtPsym arOf resOf"
abbreviation "FFullStruct \<equiv> FullStruct wtFsym wtPsym arOf resOf"
abbreviation "IInfStruct \<equiv> InfStruct wtFsym wtPsym arOf resOf"

abbreviation "MModel \<equiv> Model wtFsym wtPsym arOf resOf parOf \<Phi>"
abbreviation "FFullModel \<equiv> FullModel wtFsym wtPsym arOf resOf parOf \<Phi>"
abbreviation "IInfModel \<equiv> InfModel wtFsym wtPsym arOf resOf parOf \<Phi>"
end

text\<open>Problem that deduces some infiniteness constraints:\<close>

locale ProblemIk = Ik? : Problem wtFsym wtPsym arOf resOf parOf \<Phi>
for wtFsym :: "'fsym \<Rightarrow> bool" and wtPsym :: "'psym \<Rightarrow> bool"
and arOf :: "'fsym \<Rightarrow> 'tp list"
and resOf and parOf and \<Phi>
+
fixes infTp :: "'tp \<Rightarrow> bool"
(* infTp assumes that \<Phi> implies infiniteness on the infTp-marked types,
i.e., any model of \<Phi> is infinite on these types: *)
assumes infTp:
"\<And> \<sigma> intT intF intP (a::univ). \<lbrakk>infTp \<sigma>; MModel intT intF intP\<rbrakk> \<Longrightarrow> infinite {a. intT \<sigma> a}"

locale ModelIk =
Ik? : ProblemIk wtFsym wtPsym arOf resOf parOf \<Phi> infTp +
Ik? : Model wtFsym wtPsym arOf resOf parOf \<Phi> intT intF intP
for wtFsym :: "'fsym \<Rightarrow> bool" and wtPsym :: "'psym \<Rightarrow> bool"
and arOf :: "'fsym \<Rightarrow> 'tp list"
and resOf and parOf and \<Phi> and infTp and intT and intF and intP
begin
lemma infTp_infinite[simp]: "infTp \<sigma> \<Longrightarrow> infinite {a. intT \<sigma> a}"
apply(rule ProblemIk.infTp[of wtFsym wtPsym arOf resOf parOf \<Phi> infTp])
apply unfold_locales by simp
end


subsection\<open>Monotonicity\<close>

context Problem begin
(* Monotonicity: *)
definition
"monot \<equiv>
 (\<exists> intT intF intP. MModel intT intF intP)
 \<longrightarrow>
 (\<exists> intTI intFI intPI. IInfModel intTI intFI intPI)"
end

locale MonotProblem = Problem +
assumes monot: monot

locale MonotProblemIk =
MonotProblem wtFsym wtPsym arOf resOf parOf \<Phi> +
ProblemIk wtFsym wtPsym arOf resOf parOf \<Phi> infTp
for wtFsym :: "'fsym \<Rightarrow> bool" and wtPsym :: "'psym \<Rightarrow> bool"
and arOf :: "'fsym \<Rightarrow> 'tp list" and resOf and parOf and \<Phi> and infTp

context MonotProblem
begin

definition "MI_pred K \<equiv> IInfModel (fst3 K) (snd3 K) (trd3 K)"

definition "MI \<equiv> SOME K. MI_pred K"

lemma MI_pred:
assumes "MModel intT intF intP"
shows "\<exists> K. MI_pred K"
proof-
  obtain T F R where "MI_pred (T,F,R)"
  using monot assms unfolding monot_def MI_pred_def by auto
  thus ?thesis by blast
qed

lemma MI_pred_MI:
assumes "MModel intT intF intP"
shows "MI_pred MI"
using MI_pred[OF assms] unfolding MI_def by (rule someI_ex)

definition "intTI \<equiv> fst3 MI"
definition "intFI \<equiv> snd3 MI"
definition "intPI \<equiv> trd3 MI"

lemma InfModel_intTI_intFI_intPI:
assumes "MModel intT intF intP"
shows "IInfModel intTI intFI intPI"
using MI_pred_MI[OF assms]
unfolding MI_pred_def intFI_def intPI_def intTI_def .

end (* context MonotProblem *)

locale MonotModel = M? : MonotProblem + M? : Model

context MonotModel begin

lemma InfModelI: "IInfModel intTI intFI intPI"
apply(rule MonotProblem.InfModel_intTI_intFI_intPI)
apply standard
done

end

(* Trivial fact: Any monotonic problem that has a model also has an infinite model: *)
sublocale MonotModel < InfModel where
intT = intTI and intF = intFI and intP = intPI
using InfModelI .


context InfModel begin

definition "toFull \<sigma> \<equiv> SOME F. bij_betw F {a::univ. intT \<sigma> a} (UNIV::univ set)"
definition "fromFull \<sigma> \<equiv> inv_into {a::univ. intT \<sigma> a} (toFull \<sigma>)"

definition "intTF \<sigma> a \<equiv> True"
definition "intFF f al \<equiv> toFull (resOf f) (intF f (map2 fromFull (arOf f) al))"
definition "intPF p al \<equiv> intP p (map2 fromFull (parOf p) al)"

lemma intTF: "intTF \<sigma> a"
unfolding intTF_def by auto

lemma ex_toFull: "\<exists> F. bij_betw F {a::univ. intT \<sigma> a} (UNIV::univ set)"
by (metis inf card_of_ordIso card_of_UNIV countable_univ UnE
          countable_infinite not_ordLeq_ordLess ordLeq_ordLess_Un_ordIso)

lemma toFull: "bij_betw (toFull \<sigma>) {a. intT \<sigma> a} UNIV"
by (metis (lifting) ex_toFull someI_ex toFull_def)

lemma toFull_fromFull[simp]: "toFull \<sigma> (fromFull \<sigma> a) = a"
by (metis UNIV_I bij_betw_inv_into_right fromFull_def toFull)

lemma fromFull_toFull[simp]: "intT \<sigma> a \<Longrightarrow> fromFull \<sigma> (toFull \<sigma> a) = a"
by (metis CollectI bij_betw_inv_into_left toFull fromFull_def)

lemma fromFull_inj[simp]: "fromFull \<sigma> a = fromFull \<sigma> b \<longleftrightarrow> a = b"
by (metis toFull_fromFull)

lemma toFull_inj[simp]:
assumes "intT \<sigma> a" and "intT \<sigma> b"
shows "toFull \<sigma> a = toFull \<sigma> b \<longleftrightarrow> a = b"
by (metis assms fromFull_toFull)

lemma fromFull[simp]: "intT \<sigma> (fromFull \<sigma> a)"
unfolding fromFull_def
apply(rule inv_into_into[of a "toFull \<sigma>" "{a. intT \<sigma> a}", simplified])
using toFull unfolding bij_betw_def by auto

lemma toFull_iff_fromFull:
assumes "intT \<sigma> a"
shows "toFull \<sigma> a = b \<longleftrightarrow> a = fromFull \<sigma> b"
by (metis assms fromFull_toFull toFull_fromFull)

lemma Tstruct: "Tstruct intTF"
apply(unfold_locales) unfolding intTF_def by simp

lemma FullStruct: "FullStruct wtFsym wtPsym arOf resOf intTF intFF intPF"
apply (unfold_locales) unfolding intTF_def Tstruct.full_def[OF Tstruct] by auto

end (* locale InfModel *)

sublocale InfModel < FullStruct
where intT = intTF and intF = intFF and intP = intPF
using FullStruct .


context InfModel begin

definition "kE \<xi> \<equiv> \<lambda> x. fromFull (tpOfV x) (\<xi> x)"

lemma kE[simp]: "kE \<xi> x = fromFull (tpOfV x) (\<xi> x)"
unfolding kE_def by simp

lemma wtE[simp]: "F.wtE \<xi>"
unfolding F.wtE_def by simp

lemma kE_wtE[simp]: "I.wtE (kE \<xi>)"
unfolding I.wtE_def kE_def by simp

lemma kE_int_toFull:
assumes \<xi>: "I.wtE (kE \<xi>)" and T: "wt T"
shows "toFull (tpOf T) (I.int (kE \<xi>) T) = F.int \<xi> T"
using T proof(induct T)
  case (Fn f Tl)
  have 0: "map (I.int (kE \<xi>)) Tl =
           map2 fromFull (arOf f) (map (F.int \<xi>) Tl)"
  (is "map ?F Tl = map2 fromFull (arOf f) (map ?H Tl)"
   is "?L = ?R")
  proof(rule nth_equalityI)
    have l: "length Tl = length (arOf f)" using Fn by simp
    thus "length ?L = length ?R" by simp
    fix i assume "i < length ?L"  hence i: "i < length Tl" by simp
    let ?toFull = "toFull (arOf f!i)"   let ?fromFull = "fromFull (arOf f!i)"
    have tp: "tpOf (Tl ! i) = arOf f ! i" using Fn(2) i unfolding list_all_length by auto
    have wt: "wt (Tl!i)" using Fn i by (auto simp: list_all_iff)
    have "intT (arOf f!i) (?F (Tl!i))" using I.wt_int[OF \<xi> wt] unfolding tp .
    moreover have "?toFull (?F (Tl!i)) = ?H (Tl!i)"
      using Fn tp i by (auto simp: list_all_iff kE_def)
    ultimately have "?F (Tl!i) = fromFull (arOf f!i) (?H (Tl!i))"
      using toFull_iff_fromFull by blast
    thus "?L!i = ?R!i" using l i by simp
  qed
  show ?case unfolding I.int.simps F.int.simps tpOf.simps unfolding intFF_def 0 ..
qed simp

lemma kE_int[simp]:
assumes \<xi>: "I.wtE (kE \<xi>)" and T: "wt T"
shows "I.int (kE \<xi>) T = fromFull (tpOf T) (F.int \<xi> T)"
using kE_int_toFull[OF assms]
unfolding toFull_iff_fromFull[OF I.wt_int[OF \<xi> T]] .

lemma map_kE_int[simp]:
  assumes \<xi>: "I.wtE (kE \<xi>)" and T: "list_all wt Tl"
  shows "map (I.int (kE \<xi>)) Tl = map2 fromFull (map tpOf Tl) (map (F.int \<xi>) Tl)"
  apply(rule nth_equalityI)
   apply (metis (lifting) length_map length_map2)
  by (metis T \<xi> kE_int length_map list_all_length nth_map nth_map2)

lemma kE_satA[simp]:
assumes at: "wtA at" and \<xi>: "I.wtE (kE \<xi>)"
shows "I.satA (kE \<xi>) at \<longleftrightarrow> F.satA \<xi> at"
using assms by (cases at, auto simp add: intPF_def)

lemma kE_satL[simp]:
assumes l: "wtL l" and \<xi>: "I.wtE (kE \<xi>)"
shows "I.satL (kE \<xi>) l \<longleftrightarrow> F.satL \<xi> l"
using assms by (cases l, auto)

lemma kE_satC[simp]:
assumes c: "wtC c" and \<xi>: "I.wtE (kE \<xi>)"
shows "I.satC (kE \<xi>) c \<longleftrightarrow> F.satC \<xi> c"
unfolding I.satC_def F.satC_def
using assms by(induct c, auto simp add: wtC_def)

lemma kE_satPB:
assumes \<xi>: "I.wtE (kE \<xi>)"  shows "F.satPB \<xi> \<Phi>"
using I.sat_\<Phi>[OF assms]
using wt_\<Phi> assms unfolding I.satPB_def F.satPB_def
by (auto simp add: wtPB_def)

lemma F_SAT: "F.SAT \<Phi>"
unfolding F.SAT_def using kE_satPB kE_wtE by auto

lemma FullModel: "FullModel wtFsym wtPsym arOf resOf parOf \<Phi> intTF intFF intPF"
apply (unfold_locales) using F_SAT .

end (* context InfModel *)

sublocale InfModel < FullModel where
intT = intTF and intF = intFF and intP = intPF
using FullModel .


context MonotProblem begin

definition "intTF \<equiv> InfModel.intTF"
definition "intFF \<equiv> InfModel.intFF arOf resOf intTI intFI"
definition "intPF \<equiv> InfModel.intPF parOf intTI intPI"

text\<open>Strengthening of the infiniteness condition for monotonicity,
replacing infininetess by fullness:\<close>

theorem FullModel_intTF_intFF_intPF:
assumes "MModel intT intF intP"
shows "FFullModel intTF intFF intPF"
unfolding intTF_def intFF_def intPF_def
apply(rule InfModel.FullModel) using InfModel_intTI_intFI_intPI[OF assms] .

end (* context MonotProblem *)

sublocale MonotModel < FullModel where
intT = intTF and intF = intFF and intP = intPF
using FullModel .

end
