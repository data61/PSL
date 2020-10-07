section\<open>Guard-Based Encodings\<close>
theory G
imports T_G_Prelim Mcalc2C
begin


subsection\<open>The guard translation\<close>

text\<open>The extension of the function symbols with type witnesses:\<close>

datatype ('fsym,'tp) efsym = Oldf 'fsym | Wit 'tp

text\<open>The extension of the predicate symbols with type guards:\<close>

datatype ('psym,'tp) epsym = Oldp 'psym | Guard 'tp

text\<open>Extension of the partitioned infinitely augmented problem
for dealing with guards:\<close>

locale ProblemIkTpartG =
Ik? : ProblemIkTpart wtFsym wtPsym arOf resOf parOf \<Phi> infTp prot protFw
for wtFsym :: "'fsym \<Rightarrow> bool"
and wtPsym :: "'psym \<Rightarrow> bool"
and arOf :: "'fsym \<Rightarrow> 'tp list"
and resOf and parOf and \<Phi> and infTp and prot and protFw +
fixes (* Further refinement of prot: *)
    protCl :: "'tp \<Rightarrow> bool" (* types aimed to be classically protected *)
assumes
    protCl_prot[simp]: "\<And> \<sigma>. protCl \<sigma> \<Longrightarrow> prot \<sigma>"
    (* In order to add classical (implicational) guards, one needs
      backwards closure on the ranks of function symbols*)
and protCl_fsym: "\<And> f. protCl (resPf f) \<Longrightarrow> list_all protCl (arOf f)"

locale ModelIkTpartG =
Ik? : ProblemIkTpartG wtFsym wtPsym arOf resOf parOf \<Phi> infTp prot protFw protCl +
Ik? : ModelIkTpart wtFsym wtPsym arOf resOf parOf \<Phi> infTp prot protFw intT intF intP
for wtFsym :: "'fsym \<Rightarrow> bool"
and wtPsym :: "'psym \<Rightarrow> bool"
and arOf :: "'fsym \<Rightarrow> 'tp list"
and resOf and parOf and \<Phi> and infTp and prot and protFw and protCl
and intT and intF and intP


context ProblemIkTpartG
begin

lemma protCl_resOf_arOf[simp]:
assumes "protCl (resOf f)" and "i < length (arOf f)"
shows "protCl (arOf f ! i)"
using assms protCl_fsym unfolding list_all_length by auto

text\<open>``GE'' stands for ``guard encoding'':\<close>

fun GE_wtFsym where
 "GE_wtFsym (Oldf f) \<longleftrightarrow> wtFsym f"
|"GE_wtFsym (Wit \<sigma>) \<longleftrightarrow> \<not> isRes \<sigma> \<or> protCl \<sigma>"

fun GE_arOf where
 "GE_arOf (Oldf f) = arOf f"
|"GE_arOf (Wit \<sigma>) = []"

fun GE_resOf where
 "GE_resOf (Oldf f) = resOf f"
|"GE_resOf (Wit \<sigma>) = \<sigma>"

fun GE_wtPsym where
 "GE_wtPsym (Oldp p) \<longleftrightarrow> wtPsym p"
|"GE_wtPsym (Guard \<sigma>) \<longleftrightarrow> \<not> unprot \<sigma>"

fun GE_parOf where
 "GE_parOf (Oldp p) = parOf p"
|"GE_parOf (Guard \<sigma>) = [\<sigma>]"


lemma countable_GE_wtFsym: "countable (Collect GE_wtFsym)" (is "countable ?K")
proof-
  let ?F = "\<lambda> ef. case ef of Oldf f \<Rightarrow> Inl f | Wit \<sigma> \<Rightarrow> Inr \<sigma>"
  let ?U = "UNIV::'tp set"  let ?L = "(Collect wtFsym) <+> ?U"
  have "inj_on ?F ?K" unfolding inj_on_def apply clarify
  apply(case_tac x, simp_all) by (case_tac y, simp_all)+
  moreover have "?F ` ?K \<subseteq> ?L" apply clarify by (case_tac ef, auto)
  ultimately have "|?K| \<le>o |?L|" unfolding card_of_ordLeq[symmetric] by auto
  moreover have "countable ?L" using countable_wtFsym countable_tp
  by (metis countable_Plus)
  ultimately show ?thesis by(rule countable_ordLeq)
qed

lemma countable_GE_wtPsym: "countable (Collect GE_wtPsym)" (is "countable ?K")
proof-
  let ?F = "\<lambda> ep. case ep of Oldp p \<Rightarrow> Inl p | Guard \<sigma> \<Rightarrow> Inr \<sigma>"
  let ?U = "UNIV::'tp set"  let ?L = "(Collect wtPsym) <+> ?U"
  have "inj_on ?F ?K" unfolding inj_on_def apply clarify
  apply(case_tac x, simp_all) by (case_tac y, simp_all)+
  moreover have "?F ` ?K \<subseteq> ?L" apply clarify by (case_tac ep, auto)
  ultimately have "|?K| \<le>o |?L|" unfolding card_of_ordLeq[symmetric] by auto
  moreover have "countable ?L" using countable_wtPsym countable_tp
  by (metis countable_Plus)
  ultimately show ?thesis by(rule countable_ordLeq)
qed

end (* context ProblemIkTpartG *)

sublocale ProblemIkTpartG < GE? : Signature
where wtFsym = GE_wtFsym and wtPsym = GE_wtPsym
and arOf = GE_arOf and resOf = GE_resOf and parOf = GE_parOf
apply standard
using countable_tp countable_GE_wtFsym countable_GE_wtPsym by auto


context ProblemIkTpartG
begin

text\<open>The guarding literal of a variable:\<close>

definition grdLit :: "var \<Rightarrow> (('fsym, 'tp) efsym, ('psym, 'tp) epsym) lit"
where "grdLit x \<equiv> Neg (Pr (Guard (tpOfV x)) [Var x])"

text\<open>The (set of) guarding literals of a literal and of a clause:\<close>

(* of a literal: *)
fun glitOfL ::
"('fsym, 'psym) lit \<Rightarrow> (('fsym, 'tp) efsym, ('psym, 'tp) epsym) lit set"
where
"glitOfL (Pos at) =
 {grdLit x | x. x \<in> varsA at \<and> (prot (tpOfV x) \<or> (protFw (tpOfV x) \<and> x \<in> nvA at))}"
|
"glitOfL (Neg at) = {grdLit x | x. x \<in> varsA at \<and> prot (tpOfV x)}"

(* of a clause: *)
definition "glitOfC c \<equiv> \<Union> (set (map glitOfL c))"

lemma finite_glitOfL[simp]: "finite (glitOfL l)"
proof-
  have "glitOfL l \<subseteq> grdLit ` {x . x \<in> varsL l}" by (cases l, auto)
  thus ?thesis by (metis Collect_mem_eq finite_surj finite_varsL)
qed

lemma finite_glitOfC[simp]: "finite (glitOfC c)"
unfolding glitOfC_def apply(rule finite_Union) using finite_glitOfL by auto

fun gT where
"gT (Var x) = Var x"
|
"gT (Fn f Tl) = Fn (Oldf f) (map gT Tl)"

fun gA where
"gA (Eq T1 T2) = Eq (gT T1) (gT T2)"
|
"gA (Pr p Tl) = Pr (Oldp p) (map gT Tl)"

fun gL where
"gL (Pos at) = Pos (gA at)"
|
"gL (Neg at) = Neg (gA at)"

definition "gC c \<equiv> (map gL c) @ (list (glitOfC c))"

lemma set_gC[simp]: "set (gC c) = gL ` (set c) \<union> glitOfC c"
unfolding gC_def by simp


text\<open>The extra axioms:\<close>

text\<open>The function axioms:\<close>

(* conclusion (atom): *)
definition "cOfFax f = Pr (Guard (resOf f)) [Fn (Oldf f) (getTvars (arOf f))]"
(* hypotheses (list of atoms): *)
definition "hOfFax f = map2 (Pr o Guard) (arOf f) (map singl (getTvars (arOf f)))"
(* The axiom (clause) for non-classically-decorated (lightweight and featherweigh) types: *)
definition "fax f \<equiv> [Pos (cOfFax f)]"
(* The axiom (clause) for classically-decorated types: *)
definition "faxCD f \<equiv> map Neg (hOfFax f) @ fax f"
(* The set of axioms: *)
definition
"Fax \<equiv> {fax f | f. wtFsym f \<and> \<not> unprot (resOf f) \<and> \<not> protCl (resOf f)} \<union>
       {faxCD f | f. wtFsym f \<and> protCl (resOf f)}"

text\<open>The witness axioms:\<close>

(* The axiom (clause): *)
definition "wax \<sigma> \<equiv> [Pos (Pr (Guard \<sigma>) [Fn (Wit \<sigma>) []])]"
(* The set of axioms: *)
definition "Wax \<equiv> {wax \<sigma> | \<sigma>. \<not> unprot \<sigma> \<and> (\<not> isRes \<sigma> \<or> protCl \<sigma>)}"

definition "gPB = gC ` \<Phi> \<union> Fax \<union> Wax"

text\<open>Well-typedness of the translation:\<close>

lemma tpOf_g[simp]: "GE.tpOf (gT T) = Ik.tpOf T"
by (cases T) auto

lemma wt_g[simp]: "Ik.wt T \<Longrightarrow> GE.wt (gT T)"
by (induct T, auto simp add: list_all_iff)

lemma wtA_gA[simp]: "Ik.wtA at \<Longrightarrow> GE.wtA (gA at)"
by (cases at, auto simp add: list_all_iff)

lemma wtL_gL[simp]: "Ik.wtL l \<Longrightarrow> GE.wtL (gL l)"
by (cases l, auto)

lemma wtC_map_gL[simp]: "Ik.wtC c \<Longrightarrow> GE.wtC (map gL c)"
unfolding Ik.wtC_def GE.wtC_def by (induct c, auto)

lemma wtL_grdLit_unprot[simp]: "\<not> unprot (tpOfV x) \<Longrightarrow> GE.wtL (grdLit x)"
unfolding grdLit_def by auto

lemma wtL_grdLit[simp]: "prot (tpOfV x) \<or> protFw (tpOfV x) \<Longrightarrow> GE.wtL (grdLit x)"
apply(rule wtL_grdLit_unprot) unfolding unprot_def by auto

lemma wtL_glitOfL[simp]: "l' \<in> glitOfL l \<Longrightarrow> GE.wtL l'"
by (cases l, auto)

lemma wtL_glitOfC[simp]: "l' \<in> glitOfC c \<Longrightarrow> GE.wtL l'"
unfolding glitOfC_def GE.wtC_def by (induct c, auto)

lemma wtC_list_glitOfC[simp]: "GE.wtC (list (glitOfC c))"
unfolding glitOfC_def GE.wtC_def by auto

lemma wtC_gC[simp]: "Ik.wtC c \<Longrightarrow> GE.wtC (gC c)"
unfolding gC_def by simp

lemma wtA_cOfFax_unprot[simp]: "\<lbrakk>wtFsym f; \<not> unprot (resOf f)\<rbrakk> \<Longrightarrow> GE.wtA (cOfFax f)"
unfolding cOfFax_def by simp

lemma wtA_cOfFax[simp]:
"\<lbrakk>wtFsym f; prot (resOf f) \<or> protFw (resOf f)\<rbrakk> \<Longrightarrow> GE.wtA (cOfFax f)"
apply(rule wtA_cOfFax_unprot) unfolding unprot_def by auto

lemma wtA_hOfFax[simp]:
"\<lbrakk>wtFsym f; protCl (resOf f)\<rbrakk> \<Longrightarrow> list_all GE.wtA (hOfFax f)"
unfolding hOfFax_def unfolding list_all_length
by (auto simp add: singl_def unprot_def)

lemma wtC_fax_unprot[simp]: "\<lbrakk>wtFsym f; \<not> unprot (resOf f)\<rbrakk> \<Longrightarrow> GE.wtC (fax f)"
unfolding fax_def GE.wtC_def by auto

lemma wtC_fax[simp]: "\<lbrakk>wtFsym f; prot (resOf f) \<or> protFw (resOf f)\<rbrakk> \<Longrightarrow> GE.wtC (fax f)"
apply(rule wtC_fax_unprot) unfolding unprot_def by auto

lemma wtC_faxCD[simp]: "\<lbrakk>wtFsym f; protCl (resOf f)\<rbrakk> \<Longrightarrow> GE.wtC (faxCD f)"
unfolding faxCD_def GE.wtC_append apply(rule conjI)
  using wtA_hOfFax[unfolded list_all_length] apply(simp add: GE.wtC_def list_all_length)
  by simp

lemma wtPB_Fax[simp]: "GE.wtPB Fax"
unfolding Fax_def GE.wtPB_def by auto

lemma wtC_wax_unprot[simp]: "\<lbrakk>\<not> unprot \<sigma>; \<not> isRes \<sigma> \<or> protCl \<sigma>\<rbrakk> \<Longrightarrow> GE.wtC (wax \<sigma>)"
unfolding wax_def GE.wtC_def by simp

lemma wtC_wax[simp]: "\<lbrakk>prot \<sigma> \<or> protFw \<sigma>; \<not> isRes \<sigma> \<or> protCl \<sigma>\<rbrakk> \<Longrightarrow> GE.wtC (wax \<sigma>)"
apply(rule wtC_wax_unprot) unfolding unprot_def by auto

lemma wtPB_Wax[simp]: "GE.wtPB Wax"
unfolding Wax_def GE.wtPB_def by auto

lemma wtPB_gC_\<Phi>[simp]: "GE.wtPB (gC ` \<Phi>)"
using Ik.wt_\<Phi> unfolding Ik.wtPB_def GE.wtPB_def by auto

lemma wtPB_tPB[simp]: "GE.wtPB gPB" unfolding gPB_def by simp
(*  *)

lemma wtA_Guard:
assumes "GE.wtA (Pr (Guard \<sigma>) Tl)"
shows "\<exists> T. Tl = [T] \<and> GE.wt T \<and> tpOf T = \<sigma>"
using assms by simp (metis (hide_lams, no_types) list.inject map_eq_Cons_conv 
                           list_all_simps map_is_Nil_conv neq_Nil_conv)

lemma wt_Wit:
assumes "GE.wt (Fn (Wit \<sigma>) Tl)"  shows "Tl = []"
using assms by simp

lemma tpOf_Wit: "GE.tpOf (Fn (Wit \<sigma>) Tl) = \<sigma>" by simp

end (* context ProblemIkTpartG *)


subsection\<open>Soundness\<close>

context ModelIkTpartG begin

(* The identity-guard extension of a given structure of the original signature *)
fun GE_intF where
 "GE_intF (Oldf f) al = intF f al"
|"GE_intF (Wit \<sigma>) al = pickT \<sigma>"
(* note: for witnesses, we only care about al being [] *)

fun GE_intP where
 "GE_intP (Oldp p) al = intP p al"
|"GE_intP (Guard \<sigma>) al = True"
(* note: for guards, we only care about al being a singleton *)

end (* context ModelIkTpartG *)

sublocale ModelIkTpartG < GE? : Struct
where wtFsym = GE_wtFsym and wtPsym = GE_wtPsym and
arOf = GE_arOf and resOf = GE_resOf and parOf = GE_parOf
and intF = GE_intF and intP = GE_intP
proof
  fix ef al assume "GE_wtFsym ef" and "list_all2 intT (GE_arOf ef) al"
  thus "intT (GE_resOf ef) (GE_intF ef al)"
  using intF by (cases ef, auto)
qed auto

context ModelIkTpartG begin

lemma g_int[simp]: "GE.int \<xi> (gT T) = Ik.int \<xi> T"
proof (induct T)
  case (Fn f Tl)
  hence 0: "map (GE.int \<xi> \<circ> gT) Tl = map (Ik.int \<xi>) Tl"
  unfolding list_eq_iff list_all_iff by auto
  show ?case by (simp add: 0)
qed auto

lemma map_g_int[simp]: "map (GE.int \<xi> \<circ> gT) Tl = map (Ik.int \<xi>) Tl"
unfolding list_eq_iff list_all_iff by auto

lemma gA_satA[simp]: "GE.satA \<xi> (gA at) \<longleftrightarrow> Ik.satA \<xi> at"
apply(cases at) by auto

lemma gL_satL[simp]: "GE.satL \<xi> (gL l) \<longleftrightarrow> Ik.satL \<xi> l"
apply(cases l) by auto

lemma map_gL_satC[simp]: "GE.satC \<xi> (map gL c) \<longleftrightarrow> Ik.satC \<xi> c"
unfolding GE.satC_def Ik.satC_def by (induct c, auto)

lemma gC_satC[simp]:
assumes "Ik.satC \<xi> c"  shows "GE.satC \<xi> (gC c)"
using assms unfolding gC_def by simp

lemma gC_\<Phi>_satPB[simp]:
assumes "Ik.satPB \<xi> \<Phi>"  shows "GE.satPB \<xi> (gC ` \<Phi>)"
using assms unfolding GE.satPB_def Ik.satPB_def by auto

lemma Fax_Wax_satPB:
"GE.satPB \<xi> (Fax) \<and> GE.satPB \<xi> (Wax)"
unfolding GE.satPB_def GE.satC_def Fax_def Wax_def
by (auto simp add: cOfFax_def hOfFax_def fax_def faxCD_def wax_def)

lemmas Fax_satPB[simp] = Fax_Wax_satPB[THEN conjunct1]
lemmas Wax_satPB[simp] = Fax_Wax_satPB[THEN conjunct2]

lemma soundness: "GE.SAT gPB"
unfolding GE.SAT_def gPB_def using SAT unfolding Ik.SAT_def by auto

theorem G_soundness:
"Model GE_wtFsym GE_wtPsym GE_arOf GE_resOf GE_parOf gPB intT GE_intF GE_intP"
apply standard using wtPB_tPB soundness by auto

end (* context ModelIkTpartG *)

(* Soundness theorem in sublocale form: Given a problem (with indicated
type partition) and a model for it, we obtain a model of the tag-extended (GE)
problem: *)
sublocale ModelIkTpartG < GE? : Model
where wtFsym = GE_wtFsym and wtPsym = GE_wtPsym and
arOf = GE_arOf and resOf = GE_resOf and parOf = GE_parOf
and \<Phi> = gPB and intF = GE_intF and intP = GE_intP
using G_soundness .


subsection\<open>Completeness\<close>

(* Problem with type partition and model of its guard-encoding translation: *)
locale ProblemIkTpartG_GEModel =
Ik? : ProblemIkTpartG wtFsym wtPsym arOf resOf parOf \<Phi> infTp prot protFw protCl +
GE? : Model "ProblemIkTpartG.GE_wtFsym wtFsym resOf protCl"
            "ProblemIkTpartG.GE_wtPsym wtPsym prot protFw"
            "ProblemIkTpartG.GE_arOf arOf" "ProblemIkTpartG.GE_resOf resOf"
            "ProblemIkTpartG.GE_parOf parOf"
            gPB eintT eintF eintP
for wtFsym :: "'fsym \<Rightarrow> bool"
and wtPsym :: "'psym \<Rightarrow> bool"
and arOf :: "'fsym \<Rightarrow> 'tp list"
and resOf and parOf and \<Phi> and infTp and prot and protFw and protCl
and eintT and eintF and eintP

context ProblemIkTpartG_GEModel begin

text\<open>The reduct structure of a given structure in the guard-extended signature:\<close>
definition
"intT \<sigma> a \<equiv>
 if unprot \<sigma> then eintT \<sigma> a
 else eintT \<sigma> a \<and> eintP (Guard \<sigma>) [a]"
definition
"intF f al \<equiv> eintF (Oldf f) al"
definition
"intP p al \<equiv> eintP (Oldp p) al"

(* Semantic rephrasings of the fact that the (guarded problem) model satisfies
   Fax and Wax *)
lemma GE_Guard_all: (* fixme: messy proof *)
assumes f: "wtFsym f"
and al: "list_all2 eintT (arOf f) al"
shows
"(\<not> unprot (resOf f) \<and> \<not> protCl (resOf f)
  \<longrightarrow> eintP (Guard (resOf f)) [eintF (Oldf f) al])
 \<and>
 (protCl (resOf f) \<longrightarrow>
  list_all2 (eintP \<circ> Guard) (arOf f) (map singl al)
  \<longrightarrow> eintP (Guard (resOf f)) [eintF (Oldf f) al])"
(is "(?A1 \<longrightarrow> ?C) \<and>
     (?A2 \<longrightarrow> ?H2 \<longrightarrow> ?C)")
proof(intro conjI impI)
  define xl where "xl = getVars (arOf f)"
  have l[simp]: "length xl = length al" "length al = length (arOf f)"
                "length (getTvars (arOf f)) = length (arOf f)"
  unfolding xl_def using al unfolding list_all2_iff by auto
  have 1[simp]: "\<And> i. i < length (arOf f) \<Longrightarrow> tpOfV (xl!i) = (arOf f)!i"
  unfolding xl_def by auto
  have xl[simp]: "distinct xl" unfolding xl_def using distinct_getVars by auto
  define \<xi> where "\<xi> = pickE xl al"
  have \<xi>: "GE.wtE \<xi>" unfolding \<xi>_def apply(rule wtE_pickE) using al list_all2_nthD by auto
  have [simp]: "\<And> i. i < length (arOf f) \<Longrightarrow> \<xi> (xl ! i) = al ! i"
  using al unfolding \<xi>_def by (auto simp: list_all2_length intro: pickE)
  have 0: "map (GE.int \<xi>) (getTvars (arOf f)) = al"
  apply(rule nth_equalityI)
  using al by (auto simp: list_all2_length getTvars_def xl_def[symmetric])
  have 1:
  "GE.satC \<xi> (map Neg (map2 (Pr \<circ> Guard) (arOf f) (map singl (getTvars (arOf f))))) \<longleftrightarrow>
   \<not> list_all2 (eintP \<circ> Guard) (arOf f) (map singl al)"
  unfolding GE.satC_def list_ex_length list_all2_map2 singl_def
  unfolding list_all2_length
  by (auto simp add: map_zip_map2 singl_def getTvars_def xl_def[symmetric])
  have Fax: "GE.satPB \<xi> Fax" using GE.sat_\<Phi>[OF \<xi>] unfolding gPB_def by simp
  {assume ?A1
   hence "GE.satC \<xi> (fax f)" using f Fax unfolding GE.satPB_def Fax_def by auto
   thus ?C unfolding fax_def cOfFax_def GE.satC_def by (simp add: 0)
  }
  {assume ?A2 and ?H2
   hence "GE.satC \<xi> (faxCD f)" using f Fax unfolding GE.satPB_def Fax_def by auto
   thus ?C using \<open>?H2\<close>
   unfolding faxCD_def fax_def cOfFax_def hOfFax_def
   unfolding GE.satC_append 1 unfolding GE.satC_def by (simp add: 0)
  }
qed

lemma GE_Guard_not_unprot_protCl:
assumes f: "wtFsym f" and f2: "\<not> unprot (resOf f)" "\<not> protCl (resOf f)"
and al: "list_all2 eintT (arOf f) al"
shows "eintP (Guard (resOf f)) [intF f al]"
using GE_Guard_all[OF f al] f2 unfolding intF_def by auto

lemma GE_Guard_protCl:
assumes f: "wtFsym f" and f2: "protCl (resOf f)" and al: "list_all2 eintT (arOf f) al"
and H: "list_all2 (eintP \<circ> Guard) (arOf f) (map singl al)"
shows "eintP (Guard (resOf f)) [intF f al]"
using GE_Guard_all[OF f al] f2 H unfolding intF_def by auto

lemma GE_Guard_not_unprot:
assumes f: "wtFsym f" and f2: "\<not> unprot (resOf f)" and al: "list_all2 eintT (arOf f) al"
and H: "list_all2 (eintP \<circ> Guard) (arOf f) (map singl al)"
shows "eintP (Guard (resOf f)) [intF f al]"
apply(cases "protCl (resOf f)")
  using GE_Guard_protCl[OF f _ al H] apply fastforce
  using GE_Guard_not_unprot_protCl[OF f f2 _ al] by simp

lemma GE_Wit:
assumes \<sigma>: "\<not> unprot \<sigma>" "\<not> isRes \<sigma> \<or> protCl \<sigma>"
shows "eintP (Guard \<sigma>) [eintF (Wit \<sigma>) []]"
proof-
  define \<xi> where "\<xi> = pickE [] []"
  have \<xi>: "GE.wtE \<xi>" unfolding \<xi>_def apply(rule wtE_pickE) by auto
  have "GE.satPB \<xi> Wax" using GE.sat_\<Phi>[OF \<xi>] unfolding gPB_def by simp
  hence "GE.satC \<xi> (wax \<sigma>)" unfolding Wax_def GE.satPB_def using \<sigma> by auto
  thus ?thesis unfolding satC_def wax_def by simp
qed

lemma NE_intT_forget: "NE (intT \<sigma>)"
proof-
  obtain a where a: "eintT \<sigma> a" using GE.NE_intT by blast
  show ?thesis
  proof(cases "unprot \<sigma>")
    case True
      thus ?thesis using a unfolding intT_def by auto
  next
    case False note unprot = False
      show ?thesis proof(cases "isRes \<sigma>")
      case True then obtain f where f: "wtFsym f" and \<sigma>: "\<sigma> = resOf f"
      unfolding isRes_def by auto
      define al where "al = map pickT (arOf f)"
      have al: "list_all2 eintT (arOf f) al"
      unfolding al_def list_all2_map2 unfolding list_all2_length by auto
      define a where "a = intF f al"
      have a: "eintT \<sigma> a" unfolding a_def \<sigma> intF_def using f al
      by (metis GE_arOf.simps GE_resOf.simps GE_wtFsym.simps GE.intF)
      show ?thesis proof (cases "protCl \<sigma>")
        case True
        define a where "a = eintF (Wit \<sigma>) []"
        have "eintT \<sigma> a" unfolding a_def
        by (metis True GE_arOf.simps GE_resOf.simps GE_wtFsym.simps intF list_all2_Nil)
        moreover have "eintP (Guard \<sigma>) [a]"
        unfolding a_def using GE_Wit[OF unprot] True by simp
        ultimately show ?thesis using unprot unfolding intT_def by auto
      next
        case False
        hence "eintP (Guard \<sigma>) [a]"
        using unprot GE_Guard_not_unprot_protCl[OF f _ _ al] unfolding \<sigma> a_def by simp
        thus ?thesis using unprot a unfolding intT_def by auto
      qed
    next
      case False
      define a where "a = eintF (Wit \<sigma>) []"
      have "eintT \<sigma> a" unfolding a_def
      by (metis False GE_arOf.simps GE_resOf.simps GE_wtFsym.simps intF list_all2_Nil)
      moreover have "eintP (Guard \<sigma>) [a]"
      unfolding a_def using GE_Wit[OF unprot] False by simp
      ultimately show ?thesis using unprot unfolding intT_def by auto
    qed
  qed
qed

lemma wt_intF:
assumes f: "wtFsym f" and al: "list_all2 intT (arOf f) al"
shows "intT (resOf f) (intF f al)"
proof-
  have 0: "list_all2 eintT (arOf f) al"
  using al unfolding intT_def[abs_def] list_all2_length by metis
  hence "eintT (resOf f) (eintF (Oldf f) al)"
  by (metis GE_arOf.simps GE_resOf.simps GE_wtFsym.simps f al GE.intF)
  hence 1: "eintT (resOf f) (intF f al)" unfolding intF_def by simp
  show ?thesis  proof(cases "unprot (resOf f)")
    case True thus ?thesis unfolding intT_def by (simp add: 1)
  next
    case False note unprot = False
    have "eintP (Guard (resOf f)) [intF f al]"
    proof(cases "protCl (resOf f)")
      case False show ?thesis using GE_Guard_not_unprot_protCl[OF f unprot False 0] .
    next
      case True
      hence "list_all protCl (arOf f)" using protCl_fsym by simp
      hence "list_all (\<lambda> \<sigma>. \<not> unprot \<sigma>) (arOf f)"
      unfolding list_all_length unprot_def by auto
      hence 2: "list_all2 (eintP \<circ> Guard) (arOf f) (map singl al)"
      using al unfolding intT_def[abs_def] list_all2_length list_all_length
      singl_def[abs_def] by auto
      show ?thesis using GE_Guard_protCl[OF f True 0 2] .
    qed
    thus ?thesis using unprot unfolding intT_def by (simp add: 1)
  qed
qed

lemma Struct: "Struct wtFsym wtPsym arOf resOf intT intF intP"
apply standard using NE_intT_forget wt_intF by auto

end (* context ProblemIkTpartG_GEModel *)

sublocale ProblemIkTpartG_GEModel < Ik? : Struct
where intT = intT and intF = intF and intP = intP
using Struct .


context ProblemIkTpartG_GEModel begin

lemma wtE[simp]: "Ik.wtE \<xi> \<Longrightarrow> GE.wtE \<xi>"
unfolding Ik.wtE_def GE.wtE_def intT_def by metis

lemma int_g[simp]: "GE.int \<xi> (gT T) = Ik.int \<xi> T"
proof (induct T)
  case (Fn f Tl)
  let ?ar = "arOf f" let ?r = "resOf f"
  have 0: "map (Ik.int \<xi>) Tl = map (GE.int \<xi> \<circ> gT) Tl"
  apply(rule nth_equalityI) using Fn unfolding list_all_length by auto
  show ?case
  using [[unfold_abs_def = false]]
  unfolding Ik.int.simps GE.int.simps gT.simps unfolding intF_def
  using Fn by (simp add: 0)
qed auto

lemma map_int_g[simp]:
"map (Ik.int \<xi>) Tl = map (GE.int \<xi> \<circ> gT) Tl"
apply(rule nth_equalityI) unfolding list_all_length by auto

lemma satA_gA[simp]: "GE.satA \<xi> (gA at) \<longleftrightarrow> Ik.satA \<xi> at"
by (cases at) (auto simp add: intP_def)

lemma satL_gL[simp]: "GE.satL \<xi> (gL l) \<longleftrightarrow> Ik.satL \<xi> l"
by (cases l) auto

lemma satC_map_gL[simp]: "GE.satC \<xi> (map gL c) \<longleftrightarrow> Ik.satC \<xi> c"
unfolding GE.satC_def Ik.satC_def by (induct c) auto

lemma wtE_not_grdLit_unprot[simp]: (* crucial: *)
assumes "Ik.wtE \<xi>" and "\<not> unprot (tpOfV x)"
shows "\<not> GE.satL \<xi> (grdLit x)"
using assms unfolding Ik.wtE_def intT_def grdLit_def by simp

lemma wtE_not_grdLit[simp]:
assumes "Ik.wtE \<xi>" and "prot (tpOfV x) \<or> protFw (tpOfV x)"
shows "\<not> GE.satL \<xi> (grdLit x)"
apply(rule wtE_not_grdLit_unprot) using assms unfolding unprot_def by auto

lemma wtE_not_glitOfL[simp]:
assumes "Ik.wtE \<xi>"
shows "\<not> GE.satC \<xi> (list (glitOfL l))"
using assms unfolding GE.satC_def list_ex_list[OF finite_glitOfL]
by (cases l, auto)

lemma wtE_not_glitOfC[simp]:
assumes "Ik.wtE \<xi>"
shows "\<not> GE.satC \<xi> (list (glitOfC c))"
using wtE_not_glitOfL[OF assms]
unfolding GE.satC_def list_ex_list[OF finite_glitOfC] list_ex_list[OF finite_glitOfL]
unfolding glitOfC_def by auto

lemma satC_gC[simp]:
assumes "Ik.wtE \<xi>" and "GE.satC \<xi> (gC c)"
shows "Ik.satC \<xi> c"
using assms unfolding gC_def by simp

lemma satPB_gPB[simp]:
assumes "Ik.wtE \<xi>" and "GE.satPB \<xi> (gC ` \<Phi>)"
shows "Ik.satPB \<xi> \<Phi>"
using Ik.wt_\<Phi> assms unfolding GE.satPB_def Ik.satPB_def by (auto simp add: Ik.wtPB_def)

lemma completeness: "Ik.SAT \<Phi>"
unfolding Ik.SAT_def proof safe
  fix \<xi> assume \<xi>: "Ik.wtE \<xi>" hence "GE.wtE \<xi>" by simp
  hence "GE.satPB \<xi> gPB" by (rule GE.sat_\<Phi>)
  hence "GE.satPB \<xi> (gC ` \<Phi>)" unfolding gPB_def by simp
  thus "Ik.satPB \<xi> \<Phi>" using \<xi> by simp
qed

lemma G_completeness: "Model wtFsym wtPsym arOf resOf parOf \<Phi> intT intF intP"
apply standard using completeness .

end (* context ProblemIkTpartG_GEModel *)

(* Completeness theorem in sublocale form: Given a problem (with indicated
type partition) and a model for its guard-translated problem,
we obtain a model of the original problem: *)

sublocale ProblemIkTpartG_GEModel < Ik? : Model
where intT = intT and intF = intF and intP = intP
using G_completeness .


subsection\<open>The result of the guard translation is an infiniteness-augmented problem\<close>

(* An observation similar to the corresponding one for tags applies here.  *)

sublocale ProblemIkTpartG < GE? : Problem
where wtFsym = GE_wtFsym and wtPsym = GE_wtPsym
and arOf = GE_arOf and resOf = GE_resOf and parOf = GE_parOf
and \<Phi> = gPB
apply standard
apply auto
done

sublocale ProblemIkTpartG < GE? : ProblemIk
where wtFsym = GE_wtFsym and wtPsym = GE_wtPsym
and arOf = GE_arOf and resOf = GE_resOf and parOf = GE_parOf
and \<Phi> = gPB
proof
  fix \<sigma> eintT eintF eintP a  assume \<sigma>: "infTp \<sigma>"
  assume M: "Model GE_wtFsym GE_wtPsym GE_arOf GE_resOf GE_parOf gPB eintT eintF eintP"
  let ?GE_intT = "ProblemIkTpartG_GEModel.intT prot protFw eintT eintP"
  let ?GE_intF = "ProblemIkTpartG_GEModel.intF eintF"
  let ?GE_intP = "ProblemIkTpartG_GEModel.intP eintP"
  have 0: "ProblemIkTpartG_GEModel wtFsym wtPsym arOf resOf parOf
                                   \<Phi> infTp prot protFw protCl eintT eintF eintP"
  using M unfolding ProblemIkTpartG_GEModel_def apply safe ..
  hence MM: "Ik.MModel ?GE_intT ?GE_intF ?GE_intP"
  by (rule ProblemIkTpartG_GEModel.G_completeness)
  have "infinite {a. ?GE_intT \<sigma> a}" using infTp[OF \<sigma> MM] .
  moreover have "{a. ?GE_intT \<sigma> a} \<subseteq> {a. eintT \<sigma> a}"
  using ProblemIkTpartG_GEModel.intT_def[OF 0] by auto
  ultimately show "infinite {a. eintT \<sigma> a}" using infinite_super by blast
qed


subsection\<open>The verification of the second monotonicity calculus criterion
for the guarded problem\<close>

context ProblemIkTpartG begin

fun pol where
"pol _ (Oldp p) = Cext"
|
"pol _ (Guard \<sigma>) = Fext"

lemma pol_ct: "pol \<sigma>1 p = pol \<sigma>2 p"
by(cases p, auto)

definition "grdOf c l x = grdLit x"
end

sublocale ProblemIkTpartG < GE?: ProblemIkPol
where wtFsym = GE_wtFsym and wtPsym = GE_wtPsym
and arOf = GE_arOf and resOf = GE_resOf and parOf = GE_parOf
and \<Phi> = gPB and pol = pol and grdOf = grdOf ..

context ProblemIkTpartG begin

lemma nv2_nv[simp]: "GE.nv2T (gT T) = GE.nvT T"
apply (induct T) by auto

lemma nv2L_nvL[simp]: "GE.nv2L (gL l) = GE.nvL l"
proof(cases l)
  case (Pos at) thus ?thesis by (cases at, simp_all)
next
  case (Neg at) thus ?thesis by (cases at, auto)
qed

lemma nv2L:
assumes "l \<in> set c" and mc: "GE.mcalc \<sigma> c"
shows "infTp \<sigma> \<or> (\<forall> x \<in> GE.nv2L (gL l). tpOfV x \<noteq> \<sigma>)"
using assms mc nv2L_nvL unfolding GE.mcalc_iff GE.nvC_def apply simp
using nv2L_nvL[of l]
by (metis empty_subsetI equalityI nv2L_nvL)

(* The guarding literals are guarded: *)
lemma isGuard_grdLit[simp]: "GE.isGuard x (grdLit x)"
unfolding grdLit_def by auto

lemma nv2L_grdLit[simp]: "GE.nv2L (grdLit x) = {}"
unfolding grdLit_def by auto

lemma mcalc_mcalc2: "GE.mcalc \<sigma> c \<Longrightarrow> GE.mcalc2 \<sigma> (gC c)"
using nv2L unfolding GE.mcalc2_iff gC_def glitOfC_def grdOf_def by auto

lemma nv2L_wax[simp]: "l' \<in> set (wax \<sigma>) \<Longrightarrow> GE.nv2L l' = {}"
unfolding wax_def by auto

lemma nv2L_Wax:
assumes "c' \<in> Wax" and "l' \<in> set c'"
shows "GE.nv2L l' = {}"
using assms unfolding Wax_def by auto

lemma nv2L_cOfFax[simp]: "GE.nv2L (Pos (cOfFax \<sigma>)) = {}"
unfolding cOfFax_def by auto

lemma nv2L_hOfFax[simp]:
assumes "at \<in> set (hOfFax \<sigma>)"
shows "GE.nv2L (Neg at) = {}"
using assms unfolding hOfFax_def by auto

lemma nv2L_fax[simp]: "l \<in> set (fax \<sigma>) \<Longrightarrow> GE.nv2L l = {}"
unfolding fax_def by auto

lemma nv2L_faxCD[simp]: "l \<in> set (faxCD \<sigma>) \<Longrightarrow> GE.nv2L l = {}"
unfolding faxCD_def by auto

lemma nv2L_Fax:
assumes "c' \<in> Fax" and "l' \<in> set c'"
shows "GE.nv2L l' = {}"
using assms unfolding Fax_def by auto

lemma grdOf:
assumes c': "c' \<in> gPB" and l': "l' \<in> set c'"
and x: "x \<in> GE.nv2L l'" and i: "\<not> infTp (tpOfV x)"
shows "grdOf c' l' x \<in> set c' \<and> GE.isGuard x (grdOf c' l' x)"
proof(cases "c' \<in> Fax \<union> Wax")
  case True thus ?thesis using x l' nv2L_Wax nv2L_Fax by force
next
  case False then obtain c where c': "c' = gC c" and c: "c \<in> \<Phi>"
  using c' unfolding gPB_def by auto
  show ?thesis
  proof(cases "l' \<in> glitOfC c")
    case True then obtain l where l: "l \<in> set c" and l': "l' \<in> glitOfL l"
    unfolding glitOfC_def by auto
    then obtain x1 where "l' = grdLit x1" using l' by (cases l rule: lit.exhaust) auto
    hence "GE.nv2L l' = {}" by simp
    thus ?thesis using x by simp
  next
    let ?\<sigma> = "tpOfV x"
    case False then obtain l where l: "l \<in> set c" and l': "l' = gL l"
    using l' unfolding c' gC_def by auto
    hence x: "x \<in> GE.nvL l" using x by simp
    hence "x \<in> GE.nvC c" using l unfolding GE.nvC_def by auto
    hence "\<not> GE.mcalc ?\<sigma> c" using i unfolding GE.mcalc_iff by auto
    hence tp: "prot ?\<sigma> \<or> protFw ?\<sigma>" using unprot_mcalc[OF _ c] unfolding unprot_def by auto
    moreover obtain at where l_at: "l = Pos at" using x by(cases l, auto)
    moreover have "x \<in> varsA at" using x unfolding l_at by auto
    ultimately have "grdLit x \<in> glitOfL l" using x unfolding l_at by force
    thus ?thesis using l x unfolding grdOf_def c' gC_def glitOfC_def by auto
  qed
qed

lemma mcalc2:
assumes c': "c' \<in> gPB"
shows "GE.mcalc2 \<sigma> c'"
proof(cases "c' \<in> Fax \<union> Wax")
  case True thus ?thesis using nv2L_Wax nv2L_Fax
  unfolding GE.mcalc2_iff by fastforce
next
  case False hence c': "c' \<in> gPB" using c' unfolding gPB_def by auto
  show ?thesis unfolding GE.mcalc2_iff using grdOf[OF c'] by auto
qed


end (* context ProblemIkTpartG *)


sublocale ProblemIkTpartG < GE?: ProblemIkPolMcalc2C
where wtFsym = GE_wtFsym and wtPsym = GE_wtPsym
and arOf = GE_arOf and resOf = GE_resOf and parOf = GE_parOf
and \<Phi> = gPB and pol = pol and grdOf = grdOf
apply standard using grdOf mcalc2
apply (auto simp: pol_ct)
done

(* We already know that ProblemIkMcalc < MonotProblem, so by transitivity we obtain
the following main theorem, stating that the guard translation yields a monotonic
problem *)

context ProblemIkTpartG begin

theorem G_monotonic:
"MonotProblem GE_wtFsym GE_wtPsym GE_arOf GE_resOf GE_parOf gPB" ..

end (* context ProblemIkTpartG *)


(* Also in sublocale form: *)

sublocale ProblemIkTpartG < GE?: MonotProblem
where wtFsym = GE_wtFsym and wtPsym = GE_wtPsym
and arOf = GE_arOf and resOf = GE_resOf and parOf = GE_parOf
and \<Phi> = gPB
using G_monotonic .



end
