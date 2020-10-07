section \<open>The type-erasure translation from many-typed to untyped FOL\<close>
theory E imports Mono CU
begin

(* This is the only development that uses UFOL *)


subsection\<open>Preliminaries\<close>


(* Problem:
sublocale M.Signature < U.Signature
where arOf = "length o arOf" and parOf = "length o parOf"
yields error:
*** Duplicate constant declaration "local.wt_graph" vs. "local.wt_graph"
*)


(* Temporary solution: Isomorphic copy of the MFOL hierarchy: *)
locale M_Signature = M? : Sig.Signature
locale M_Problem = M? : M.Problem
locale M_MonotModel = M? : MonotModel wtFsym wtPsym arOf resOf parOf \<Phi> intT intF intP
for wtFsym :: "'fsym \<Rightarrow> bool" and wtPsym :: "'psym \<Rightarrow> bool"
and arOf :: "'fsym \<Rightarrow> 'tp list"
and resOf and parOf and intT and intF and intP and \<Phi>
locale M_FullStruct = M? : FullStruct
locale M_FullModel = M? : FullModel

sublocale M_FullStruct < M_Signature ..
sublocale M_Problem < M_Signature ..
sublocale M_FullModel < M_FullStruct ..
sublocale M_MonotModel < M_FullStruct where
intT = intTF and intF = intFF and intP = intPF ..
sublocale M_MonotModel < M_FullModel where
intT = intTF and intF = intFF and intP = intPF ..


context Sig.Signature begin

end (* context Signature.Signature *)


subsection\<open>The translation\<close>

sublocale M_Signature < U.Signature
where arOf = "length o arOf" and parOf = "length o parOf"
by standard (auto simp: countable_wtFsym countable_wtPsym)


(* In our implicitly-typed setting, ``e" is just the identity. *)

context M_Signature begin

(* Well-typedness of the translation: *)
lemma wt[simp]: "M.wt T \<Longrightarrow> wt T"
by (induct T, auto simp add: list_all_iff)

lemma wtA[simp]: "M.wtA at \<Longrightarrow> wtA at"
apply(cases at) by (auto simp add: list_all_iff)

lemma wtL[simp]: "M.wtL l \<Longrightarrow> wtL l"
apply(cases l) by auto

lemma wtC[simp]: "M.wtC c \<Longrightarrow> wtC c"
unfolding M.wtC_def wtC_def by (induct c, auto)

lemma wtPB[simp]: "M.wtPB \<Phi> \<Longrightarrow> wtPB \<Phi>"
unfolding M.wtPB_def wtPB_def by auto

end (* context M_Signature *)


subsection\<open>Completeness\<close>

(* In our implicitly-typed setting, ``e" is just the identity. *)

text\<open>The next puts together an M$\_$signature with a structure for its U.flattened signature:\<close>

locale UM_Struct =
M? : M_Signature wtFsym wtPsym arOf resOf parOf +
U? : CU.Struct wtFsym wtPsym "length o arOf" "length o parOf" D intF intP
for wtFsym :: "'fsym \<Rightarrow> bool" and wtPsym :: "'psym \<Rightarrow> bool"
and arOf :: "'fsym \<Rightarrow> 'tp list"
and resOf and parOf and D and intF and intP

sublocale UM_Struct < M? : M.Struct where intT = "\<lambda> \<sigma>. D"
  apply standard
  apply(rule NE_D)
  unfolding list_all2_list_all apply(rule intF) by auto

context UM_Struct begin

lemma wtE[simp]: "M.wtE \<xi> \<Longrightarrow> U.wtE \<xi>"
unfolding U.wtE_def M.wtE_def by auto

lemma int_e[simp]: "U.int \<xi> T = M.int \<xi> T"
by (induct T, simp_all add: list_all_iff) (metis map_eq_conv)

lemma int_o_e[simp]: "U.int \<xi> = M.int \<xi>"
unfolding int_e fun_eq_iff by simp

lemma satA_e[simp]: "U.satA \<xi> at \<longleftrightarrow> M.satA \<xi> at"
by (cases at) auto

lemma satL_e[simp]: "U.satL \<xi> l \<longleftrightarrow> M.satL \<xi> l"
apply(cases l) by auto

lemma satC_e[simp]: "U.satC \<xi> c \<longleftrightarrow> M.satC \<xi> c"
unfolding M.satC_def U.satC_def by (induct c, simp_all)

lemma satPB_e[simp]: "U.satPB \<xi> \<Phi> \<longleftrightarrow> M.satPB \<xi> \<Phi>"
unfolding M.satPB_def U.satPB_def by auto

theorem completeness:
assumes "U.SAT \<Phi>"  shows "M.SAT \<Phi>"
using assms unfolding M.SAT_def satPB_e U.SAT_def by auto

end (* context UM_Struct *)

locale UM_Model =
  M_Problem wtFsym wtPsym arOf resOf parOf \<Phi> +
  UM_Struct wtFsym wtPsym arOf resOf parOf D intF intP +
  CU.Model wtFsym wtPsym  "length o arOf" "length o parOf" \<Phi>
          D intF intP
for wtFsym :: "'fsym \<Rightarrow> bool" and wtPsym :: "'psym \<Rightarrow> bool"
and arOf :: "'fsym \<Rightarrow> 'tp list"
and resOf and parOf and \<Phi> and D and intF and intP
begin

theorem M_U_completeness: "MModel (\<lambda>\<sigma>::'tp. D) intF intP"
apply standard apply(rule completeness[OF SAT]) .

end (* context UM_Model *)

text\<open>Global statement of completeness : UM$\_$Model consists
of an M.problem and an U.model satisfying the U.translation of this problem.
It is stated that it yields a model for the M.problem.\<close>
sublocale UM_Model < CM.Model where intT = "\<lambda> \<sigma>. D"
using M_U_completeness .


subsection\<open>Soundness for monotonic problems\<close>

sublocale M_FullStruct < U? : CU.Struct
where arOf = "length o arOf" and parOf = "length o parOf" and D = "intT any"
apply standard
  apply(rule NE_intT)
  apply (rule full2)
  unfolding full_True list_all2_list_all by auto


context M_FullModel begin

lemma wtE[simp]: "U.wtE \<xi> \<Longrightarrow> F.wtE \<xi>"
unfolding U.wtE_def F.wtE_def by auto

lemma int_e[simp]: "U.int \<xi> T = F.int \<xi> T"
by (induct T, simp_all add: list_all_iff) (metis map_eq_conv)

lemma int_o_e[simp]: "U.int \<xi> = F.int \<xi>"
unfolding fun_eq_iff by auto

lemma satA_e[simp]: "U.satA \<xi> at \<longleftrightarrow> F.satA \<xi> at"
by (cases at) auto

lemma satL_e[simp]: "U.satL \<xi> l \<longleftrightarrow> F.satL \<xi> l"
by (cases l) auto

lemma satC_e[simp]: "U.satC \<xi> c \<longleftrightarrow> F.satC \<xi> c"
unfolding F.satC_def U.satC_def by (induct c, simp_all)

lemma satPB_e[simp]: "U.satPB \<xi> \<Phi> \<longleftrightarrow> F.satPB \<xi> \<Phi>"
unfolding F.satPB_def U.satPB_def by auto

theorem soundness: "U.SAT \<Phi>"
unfolding U.SAT_def using sat_\<Phi> satPB_e by auto

lemma U_Model:
"CU.Model wtFsym wtPsym (length \<circ> arOf) (length \<circ> parOf) \<Phi> (intT any) intF intP"
by standard (rule wtPB[OF wt_\<Phi>], rule soundness)

end (* context M_FullModel *)


sublocale M_FullModel < CU.Model
where arOf = "length o arOf" and parOf = "length o parOf" and D = "intT any"
using U_Model .

context M_MonotModel begin

theorem M_U_soundness:
"CU.Model wtFsym wtPsym (length \<circ> arOf) (length \<circ> parOf) \<Phi>
  (InfModel.intTF (any::'tp))
  (InfModel.intFF arOf resOf intTI intFI) (InfModel.intPF parOf intTI intPI)"
apply(rule M_FullModel.U_Model)
unfolding M_FullModel_def apply(rule InfModel.FullModel)
apply(rule MonotModel.InfModelI) ..

end (* context M_MonotModel *)


text\<open>Global statement of the soundness theorem: M$\_$MonotModel consists
of a monotonic F.problem satisfied by an F.model.
It is stated that this yields an U.Model for the translated problem.\<close>

sublocale M_MonotModel < CU.Model
where arOf = "length o arOf" and parOf = "length o parOf"
and \<Phi> = \<Phi> and D = "intTF (any::'tp)" and intF = intFF and intP = intPF
using M_U_soundness .


end
