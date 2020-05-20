section\<open>Tag-Based Encodings\<close>
theory T 
imports T_G_Prelim
begin


subsection\<open>The tag translation\<close>

text\<open>The extension of the function symbols with type tags and type witnesses:\<close>

datatype ('fsym,'tp) efsym = Oldf 'fsym | Tag 'tp | Wit 'tp


context ProblemIkTpart
begin

text\<open>``TE'' stands for ``tag encoding''\<close>

fun TE_wtFsym where
 "TE_wtFsym (Oldf f) \<longleftrightarrow> wtFsym f"
|"TE_wtFsym (Tag \<sigma>) \<longleftrightarrow> True"
|"TE_wtFsym (Wit \<sigma>) \<longleftrightarrow> \<not> isRes \<sigma>"

fun TE_arOf where
 "TE_arOf (Oldf f) = arOf f"
|"TE_arOf (Tag \<sigma>) = [\<sigma>]"
|"TE_arOf (Wit \<sigma>) = []"

fun TE_resOf where
 "TE_resOf (Oldf f) = resOf f"
|"TE_resOf (Tag \<sigma>) = \<sigma>"
|"TE_resOf (Wit \<sigma>) = \<sigma>"

lemma countable_TE_wtFsym: "countable (Collect TE_wtFsym)" (is "countable ?K")
proof-
  let ?F = "\<lambda> ef. case ef of Oldf f \<Rightarrow> Inl f | Tag \<sigma> \<Rightarrow> Inr (Inl \<sigma>) | Wit \<sigma> \<Rightarrow> Inr (Inr \<sigma>)"
  let ?U = "(UNIV::'tp set) <+> (UNIV::'tp set)"
  let ?L = "(Collect wtFsym) <+> ?U"
  have "inj_on ?F ?K" unfolding inj_on_def apply clarify
  apply(case_tac x, simp_all) by (case_tac y, simp_all)+
  moreover have "?F ` ?K \<subseteq> ?L" apply clarify by (case_tac ef, auto)
  ultimately have "|?K| \<le>o |?L|" unfolding card_of_ordLeq[symmetric] by auto
  moreover have "countable ?L" using countable_wtFsym countable_tp
  by (metis countable_Plus)
  ultimately show ?thesis by(rule countable_ordLeq)
qed

end (* context ProblemIkTpart *)

sublocale ProblemIkTpart < TE? : Signature
where wtFsym = TE_wtFsym and arOf = TE_arOf and resOf = TE_resOf
apply standard
using countable_tp countable_TE_wtFsym countable_wtPsym by auto


context ProblemIkTpart
begin

(* encoding of non-naked terms *)
fun tNN where
"tNN (Var x) =
 (if unprot (tpOfV x) \<or> protFw (tpOfV x) then Var x else Fn (Tag (tpOfV x)) [Var x])"
|
"tNN (Fn f Tl) = (if unprot (resOf f) \<or> protFw (resOf f)
                    then Fn (Oldf f) (map tNN Tl)
                    else Fn (Tag (resOf f)) [Fn (Oldf f) (map tNN Tl)])"

fun tT where
"tT (Var x) = (if unprot (tpOfV x) then Var x else Fn (Tag (tpOfV x)) [Var x])"
|
"tT t = tNN t"

fun tL where
"tL (Pos (Eq T1 T2)) = Pos (Eq (tT T1) (tT T2))"
|
"tL (Neg (Eq T1 T2)) = Neg (Eq (tNN T1) (tNN T2))"
|
"tL (Pos (Pr p Tl)) = Pos (Pr p (map tNN Tl))"
|
"tL (Neg (Pr p Tl)) = Neg (Pr p (map tNN Tl))"

definition "tC \<equiv> map tL"

(* The extra axioms: *)

(* The function axioms: *)
(* Lefthand side: *)
definition "rOfFax f = Fn (Oldf f) (getTvars (arOf f))"
(* Righthand side: *)
definition "lOfFax f = Fn (Tag (resOf f)) [rOfFax f]"
definition "Fax \<equiv> {[Pos (Eq (lOfFax f) (rOfFax f))] | f. wtFsym f}"

(* The witness axioms: *)
(* Lefthand side: *)
definition "rOfWax \<sigma> = Fn (Wit \<sigma>) []"
(* Righthand side: *)
definition "lOfWax \<sigma> = Fn (Tag \<sigma>) [rOfWax \<sigma>]"
definition "Wax \<equiv> {[Pos (Eq (lOfWax \<sigma>) (rOfWax \<sigma>))] | \<sigma>. \<not> isRes \<sigma> \<and> protFw \<sigma>}"

definition "tPB = tC ` \<Phi> \<union> Fax \<union> Wax"

(* Well-typedness of the translation: *)
lemma tpOf_tNN[simp]: "TE.tpOf (tNN T) = Ik.tpOf T"
by (induct T) auto

lemma tpOf_t[simp]: "TE.tpOf (tT T) = Ik.tpOf T"
by (cases T) auto

lemma wt_tNN[simp]: "Ik.wt T \<Longrightarrow> TE.wt (tNN T)"
by (induct T, auto simp add: list_all_iff)

lemma wt_t[simp]: "Ik.wt T \<Longrightarrow> TE.wt (tT T)"
by (cases T, auto simp add: list_all_iff)

lemma wtL_tL[simp]: "Ik.wtL l \<Longrightarrow> TE.wtL (tL l)"
apply(cases l) apply (rename_tac [!] atm) apply(case_tac [!] atm)
by (auto simp add: list_all_iff)

lemma wtC_tC[simp]: "Ik.wtC c \<Longrightarrow> TE.wtC (tC c)"
unfolding tC_def Ik.wtC_def TE.wtC_def by (induct c, auto)

lemma tpOf_rOfFax[simp]: "TE.tpOf (rOfFax f) = resOf f"
unfolding rOfFax_def by simp

lemma tpOf_lOfFax[simp]: "TE.tpOf (lOfFax f) = resOf f"
unfolding lOfFax_def by simp

lemma tpOf_rOfWax[simp]: "TE.tpOf (rOfWax \<sigma>) = \<sigma>"
unfolding rOfWax_def by simp

lemma tpOf_lOfWax[simp]: "TE.tpOf (lOfWax \<sigma>) = \<sigma>"
unfolding lOfWax_def by simp

lemma wt_rOfFax[simp]: "wtFsym f \<Longrightarrow> TE.wt (rOfFax f)"
unfolding rOfFax_def by simp

lemma wt_lOfFax[simp]: "wtFsym f \<Longrightarrow> TE.wt (lOfFax f)"
unfolding lOfFax_def by simp

lemma wt_rOfWax[simp]: "\<not> isRes \<sigma> \<Longrightarrow> TE.wt (rOfWax \<sigma>)"
unfolding rOfWax_def by simp

lemma wt_lOfWax[simp]: "\<not> isRes \<sigma> \<Longrightarrow> TE.wt (lOfWax \<sigma>)"
unfolding lOfWax_def by simp

lemma wtPB_Fax[simp]: "TE.wtPB Fax" unfolding Fax_def TE.wtPB_def TE.wtC_def by auto

lemma wtPB_Wax[simp]: "TE.wtPB Wax" unfolding Wax_def TE.wtPB_def TE.wtC_def by auto

lemma wtPB_tC_\<Phi>[simp]: "TE.wtPB (tC ` \<Phi>)"
using Ik.wt_\<Phi> unfolding Ik.wtPB_def TE.wtPB_def by auto

lemma wtPB_tPB[simp]: "TE.wtPB tPB" unfolding tPB_def by simp
(*  *)

lemma wt_Tag:
assumes "TE.wt (Fn (Tag \<sigma>) Tl)"
shows "\<exists> T. Tl = [T] \<and> TE.wt T \<and> tpOf T = \<sigma>"
using assms 
by simp (metis (hide_lams, no_types) list.inject list_all_simps(1) map_eq_Cons_conv neq_Nil_conv)

lemma tpOf_Tag: "TE.tpOf (Fn (Tag \<sigma>) Tl) = \<sigma>" by simp

lemma wt_Wit:
assumes "TE.wt (Fn (Wit \<sigma>) Tl)"
shows "Tl = []"
using assms by simp

lemma tpOf_Wit: "TE.tpOf (Fn (Wit \<sigma>) Tl) = \<sigma>" by simp

end (* context ProblemIkTpart *)


subsection\<open>Soundness\<close>

context ModelIkTpart begin

(* The identity-tag extension of a given structure of the original signature *)
fun TE_intF where
 "TE_intF (Oldf f) al = intF f al"
|"TE_intF (Tag \<sigma>) al = hd al"
|"TE_intF (Wit \<sigma>) al = pickT \<sigma>"
(* note: for tags, we only care about al being the singleton list [a],
   and hence the interpretation returns a; for witnesses, we only care
   about al being [] *)

end (* context ModelIkTpart *)

sublocale ModelIkTpart < TE? : Struct
where wtFsym = TE_wtFsym and arOf = TE_arOf and resOf = TE_resOf and intF = TE_intF
proof
  fix ef al assume "TE_wtFsym ef" and "list_all2 intT (TE_arOf ef) al"
  thus "intT (TE_resOf ef) (TE_intF ef al)"
  using intF by (cases ef, auto)
qed auto

context ModelIkTpart begin

lemma tNN_int[simp]: "TE.int \<xi> (tNN T) = Ik.int \<xi> T"
proof(induct T)
  case (Fn f Tl)
  hence 0: "map (TE.int \<xi> \<circ> tNN) Tl = map (Ik.int \<xi>) Tl"
  unfolding list_eq_iff list_all_iff by auto
  show ?case by (simp add: 0)
qed auto

lemma map_tNN_int[simp]: "map (TE.int \<xi> \<circ> tNN) Tl = map (Ik.int \<xi>) Tl"
unfolding list_eq_iff list_all_iff by auto

lemma t_int[simp]: "TE.int \<xi> (tT T) = Ik.int \<xi> T"
by (cases T, auto)

lemma map_t_int[simp]: "map (TE.int \<xi> \<circ> tT) Tl = map (Ik.int \<xi>) Tl"
unfolding list_eq_iff list_all_iff by auto

lemma tL_satL[simp]: "TE.satL \<xi> (tL l) \<longleftrightarrow> Ik.satL \<xi> l"
apply(cases l) apply (rename_tac [!] atm) apply(case_tac [!] atm) by auto

lemma tC_satC[simp]: "TE.satC \<xi> (tC c) \<longleftrightarrow> Ik.satC \<xi> c"
unfolding TE.satC_def Ik.satC_def tC_def by (induct c, auto)

lemma tC_\<Phi>_satPB[simp]: "TE.satPB \<xi> (tC ` \<Phi>) \<longleftrightarrow> Ik.satPB \<xi> \<Phi>"
unfolding TE.satPB_def Ik.satPB_def by auto

lemma Fax_Wax_satPB:
"TE.satPB \<xi> (Fax) \<and> TE.satPB \<xi> (Wax)"
unfolding TE.satPB_def TE.satC_def Fax_def Wax_def
by (auto simp add: lOfFax_def rOfFax_def lOfWax_def rOfWax_def)

lemmas Fax_satPB[simp] = Fax_Wax_satPB[THEN conjunct1]
lemmas Wax_satPB[simp] = Fax_Wax_satPB[THEN conjunct2]

lemma soundness: "TE.SAT tPB"
unfolding TE.SAT_def tPB_def using SAT unfolding Ik.SAT_def by auto

theorem T_soundness:
"Model TE_wtFsym wtPsym TE_arOf TE_resOf parOf tPB intT TE_intF intP"
apply standard using wtPB_tPB soundness by auto

end (* context ModelIkTpart *)



(* Soundness theorem in sublocale form: Given a problem (with indicated
type partition) and a model for it, we obtain a model of the tag-extended (TE)
problem: *)
sublocale ModelIkTpart < TE? : Model
where wtFsym = TE_wtFsym and arOf = TE_arOf and resOf = TE_resOf
and \<Phi> = tPB and intF = TE_intF
apply standard using wtPB_tPB soundness by auto


subsection\<open>Completeness\<close>

(* iimg B f transforms f into a function f' having the same B-range as f
and such that it is the identity on its B-image, namely, \<forall> b \<in> B. f' (f' a) = f' a;
also, it holds that \<forall> b \<in> B. f' (f b) = f b *)
definition "iimg B f a \<equiv> if a \<in> f ` B then a else f a"

lemma inImage_iimg[simp]: "a \<in> f ` B \<Longrightarrow> iimg B f a = a"
unfolding iimg_def by auto

lemma not_inImage_iimg[simp]: "a \<notin> f ` B \<Longrightarrow> iimg B f a = f a"
unfolding iimg_def by auto

lemma iimg[simp]: "a \<in> B \<Longrightarrow> iimg B f (f a) = f a"
by (cases "a \<in> f ` B", auto)

(* Problem with type partition and model of its tag-encoding translation: *)

locale ProblemIkTpart_TEModel =
Ik? : ProblemIkTpart wtFsym wtPsym arOf resOf parOf \<Phi> infTp prot protFw +
TE? : Model "ProblemIkTpart.TE_wtFsym wtFsym resOf" wtPsym
           "ProblemIkTpart.TE_arOf arOf" "ProblemIkTpart.TE_resOf resOf" parOf
           tPB eintT eintF eintP
for wtFsym :: "'fsym \<Rightarrow> bool"
and wtPsym :: "'psym \<Rightarrow> bool"
and arOf :: "'fsym \<Rightarrow> 'tp list"
and resOf and parOf and \<Phi> and infTp and prot and protFw
and eintT and eintF and eintP

context ProblemIkTpart_TEModel begin

(* new tag semantics (taking as input elements, instead of singleton lists): *)
definition
"ntsem \<sigma> \<equiv>
 if unprot \<sigma> \<or> protFw \<sigma> then id
                   else iimg {b. eintT \<sigma> b} (eintF (Tag \<sigma>) o singl)"

lemma unprot_ntsem[simp]: "unprot \<sigma> \<or> protFw \<sigma> \<Longrightarrow> ntsem \<sigma> a = a"
unfolding ntsem_def by simp

lemma protFw_ntsem[simp]: "protFw \<sigma> \<Longrightarrow> ntsem \<sigma> a = a"
unfolding ntsem_def by simp

lemma inImage_ntsem[simp]:
"a \<in> (eintF (Tag \<sigma>) o singl) ` {b. eintT \<sigma> b} \<Longrightarrow> ntsem \<sigma> a = a"
unfolding ntsem_def by simp

lemma not_unprot_inImage_ntsem[simp]:
assumes "\<not> unprot \<sigma>" and "\<not> protFw \<sigma>" and "a \<notin> (eintF (Tag \<sigma>) o singl) ` {b. eintT \<sigma> b}"
shows "ntsem \<sigma> a = eintF (Tag \<sigma>) [a]"
using assms unfolding ntsem_def by (simp add: singl_def)

(* crucial: *)
lemma ntsem[simp]:
"eintT \<sigma> b \<Longrightarrow> ntsem \<sigma> (eintF (Tag \<sigma>) [b]) = eintF (Tag \<sigma>) [b]"
unfolding singl_def[symmetric] by simp

lemma eintT_ntsem:
assumes a: "eintT \<sigma> a"  shows "eintT \<sigma> (ntsem \<sigma> a)"
proof(cases "unprot \<sigma> \<or> protFw \<sigma>")
  case False note unprot = False show ?thesis
  proof(cases "a \<in> (eintF (Tag \<sigma>) o singl) ` {b. eintT \<sigma> b}")
    case False hence 1: "ntsem \<sigma> a = eintF (Tag \<sigma>) [a]" using unprot by simp
    show ?thesis unfolding 1 using a TE.intF
    by (metis TE_arOf.simps TE_resOf.simps TE_wtFsym.simps list_all2_Cons list_all2_Nil)
  qed(insert a, auto)
qed(insert a, simp)

(* The reduct structure of a given structure in the tag-extended signature: *)
definition
"intT \<sigma> a \<equiv>
 if unprot \<sigma> then eintT \<sigma> a
 else if protFw \<sigma> then eintT \<sigma> a \<and> eintF (Tag \<sigma>) [a] = a
 else eintT \<sigma> a \<and> a \<in> (eintF (Tag \<sigma>) o singl) ` {b. eintT \<sigma> b}"
definition
"intF f al \<equiv>
 if unprot (resOf f) \<or> protFw (resOf f)
   then eintF (Oldf f) (map2 ntsem (arOf f) al)
   else eintF (Tag (resOf f)) [eintF (Oldf f) (map2 ntsem (arOf f) al)]"
definition
"intP p al \<equiv> eintP p (map2 ntsem (parOf p) al)"

(* Semantic rephrasings of the fact that the (tagged problem) model satisfies
   Fax and Wax *)
lemma TE_Tag: (* fixme: messy proof *)
assumes f: "wtFsym f" and al: "list_all2 eintT (arOf f) al"
shows "eintF (Tag (resOf f)) [eintF (Oldf f) al] = eintF (Oldf f) al"
proof-
  define xl where "xl = getVars (arOf f)"
  have l[simp]: "length xl = length al" "length al = length (arOf f)"
  unfolding xl_def using al unfolding list_all2_iff by auto
  have 1[simp]: "\<And> i. i < length (arOf f) \<Longrightarrow> tpOfV (xl!i) = (arOf f)!i"
  unfolding xl_def by auto
  have xl[simp]: "distinct xl" unfolding xl_def using distinct_getVars by auto
  define \<xi> where "\<xi> = pickE xl al"
  have \<xi>: "TE.wtE \<xi>" unfolding \<xi>_def apply(rule wtE_pickE)
  using al  list_all2_nthD by auto
  have [simp]: "\<And> i. i < length (arOf f) \<Longrightarrow> \<xi> (xl ! i) = al ! i"
  using al unfolding \<xi>_def by (auto simp: list_all2_length intro: pickE)
  have 0: "map (TE.int \<xi>) (getTvars (arOf f)) = al"
  apply(rule nth_equalityI)
  using al by (auto simp: list_all2_length getTvars_def xl_def[symmetric])
  have "TE.satPB \<xi> Fax" using TE.sat_\<Phi>[OF \<xi>] unfolding tPB_def by simp
  hence "TE.satC \<xi> [Pos (Eq (lOfFax f) (rOfFax f))]"
  unfolding TE.satPB_def Fax_def using f by auto
  hence "TE.satA \<xi> (Eq (lOfFax f) (rOfFax f))" unfolding TE.satC_def by simp
  thus ?thesis using al by (simp add: lOfFax_def rOfFax_def 0)
qed

lemma TE_Wit:
assumes \<sigma>: "\<not> isRes \<sigma>" "protFw \<sigma>"
shows "eintF (Tag \<sigma>) [eintF (Wit \<sigma>) []] = eintF (Wit \<sigma>) []"
proof-
  define \<xi> where "\<xi> = pickE [] []"
  have \<xi>: "TE.wtE \<xi>" unfolding \<xi>_def apply(rule wtE_pickE) by auto
  have "TE.satPB \<xi> Wax" using TE.sat_\<Phi>[OF \<xi>] unfolding tPB_def by simp
  hence "TE.satC \<xi> [Pos (Eq (lOfWax \<sigma>) (rOfWax \<sigma>))]"
  unfolding TE.satPB_def Wax_def using \<sigma> by auto
  hence "TE.satA \<xi> (Eq (lOfWax \<sigma>) (rOfWax \<sigma>))" unfolding TE.satC_def by auto
  thus ?thesis unfolding TE.satA.simps lOfWax_def rOfWax_def by simp
qed

lemma NE_intT_forget: "NE (intT \<sigma>)"
proof-
  obtain b where b: "eintT \<sigma> b" using TE.NE_intT by blast
  show ?thesis proof(cases "unprot \<sigma>")
    case True thus ?thesis using b unfolding intT_def by auto
  next
    case False note unprot = False show ?thesis
    proof(cases "protFw \<sigma>")
      case True note protFw = True show ?thesis proof(cases "isRes \<sigma>")
        case True then obtain f where f: "wtFsym f" and \<sigma>: "\<sigma> = resOf f"
        unfolding isRes_def by auto
        define al where "al = map pickT (arOf f)"
        have al: "list_all2 eintT (arOf f) al"
        unfolding al_def list_all2_map2 unfolding list_all2_length by auto
        define a where "a = eintF (Oldf f) al"
        have "eintT \<sigma> a" unfolding a_def \<sigma> using f al
        by (metis TE_arOf.simps TE_resOf.simps TE_wtFsym.simps TE.intF)
        moreover have "eintF (Tag \<sigma>) [a] = a" unfolding \<sigma> a_def using TE_Tag[OF f al] .
        ultimately show ?thesis using unprot protFw unfolding intT_def by auto
      next
        case False
        define a where "a = eintF (Wit \<sigma>) []"
        have "eintT \<sigma> a" unfolding a_def
        by (metis False TE_arOf.simps TE_resOf.simps TE_wtFsym.simps TE.intF list_all2_NilR)
        moreover have "eintF (Tag \<sigma>) [a] = a" unfolding a_def using TE_Wit[OF False protFw] .
        ultimately show ?thesis using unprot protFw unfolding intT_def by auto
      qed
    next
      case False  hence "eintT \<sigma> (eintF (Tag \<sigma>) [b])"
      using b list_all2_Cons list_all2_NilL
      by (metis TE.intF TE_arOf.simps TE_resOf.simps TE_wtFsym.simps)
      hence "intT \<sigma> (eintF (Tag \<sigma>) [b])"
      unfolding intT_def singl_def[abs_def] using b False by auto
      thus ?thesis by blast
    qed
  qed
qed

lemma wt_intF:
assumes f: "wtFsym f" and al: "list_all2 intT (arOf f) al"
shows "intT (resOf f) (intF f al)"
proof-
  let ?t = "eintF (Tag (resOf f))"
  let ?t'al = "map2 ntsem (arOf f) al"
  have al: "list_all2 eintT (arOf f) al"
  using al unfolding list_all2_length intT_def by metis
  have 0: "list_all2 eintT (arOf f) ?t'al"
  proof(rule listAll2_map2I)
    show l: "length (arOf f) = length al"
    using al unfolding list_all2_length by simp
    fix i assume "i < length (arOf f)"
    hence 1: "eintT (arOf f ! i) (al ! i)"
    using al unfolding list_all2_length by simp
    show "eintT (arOf f ! i) (ntsem (arOf f ! i) (al ! i))"
    using eintT_ntsem[OF 1] .
  qed
  hence 1: "eintT (resOf f) (eintF (Oldf f) ?t'al)"
  by (metis TE_arOf.simps TE_resOf.simps TE_wtFsym.simps f TE.intF)
  show ?thesis  proof(cases "unprot (resOf f)")
    case True thus ?thesis unfolding intF_def intT_def by (simp add: 1)
  next
    case False note unprot = False show ?thesis proof(cases "protFw (resOf f)")
      case True thus ?thesis using unprot TE_Tag[OF f 0] 1
      unfolding intF_def intT_def by simp
    next
      case False
      have "eintT (resOf f) (intF f al)" using intF_def 0 1 TE_Tag f by auto
      moreover have
      "intF f al \<in> (eintF (Tag (resOf f)) o singl) ` {b. eintT (resOf f) b}"
      unfolding intF_def using 1 unprot False by (auto simp add: singl_def)
      ultimately show ?thesis using False unfolding intT_def by simp
    qed
  qed
qed

lemma Struct: "Struct wtFsym wtPsym arOf resOf intT intF intP"
apply standard using NE_intT_forget wt_intF by auto

end (* context ProblemIkTpart_TEModel *)

sublocale ProblemIkTpart_TEModel < Ik? : Struct
where intT = intT and intF = intF and intP = intP
using Struct .


context ProblemIkTpart_TEModel begin

(* The inverse of the tag function (required for translating environments backwards)*)
definition
"invt \<sigma> a \<equiv> if unprot \<sigma> \<or> protFw \<sigma> then a else (SOME b. eintT \<sigma> b \<and> eintF (Tag \<sigma>) [b] = a)"

lemma unprot_invt[simp]: "unprot \<sigma> \<or> protFw \<sigma> \<Longrightarrow> invt \<sigma> a = a"
unfolding invt_def by auto

lemma invt_invt_inImage:
assumes \<sigma>: "\<not> unprot \<sigma>" "\<not> protFw \<sigma>"
and a: "a \<in> (eintF (Tag \<sigma>) o singl) ` {b. eintT \<sigma> b}"
shows "eintT \<sigma> (invt \<sigma> a) \<and> eintF (Tag \<sigma>) [invt \<sigma> a] = a"
proof-
  obtain b where "eintT \<sigma> b" and "eintF (Tag \<sigma>) [b] = a"
  using a unfolding image_def singl_def[symmetric] by auto
  thus ?thesis using \<sigma> unfolding invt_def apply simp apply(rule someI_ex) by auto
qed

lemmas invt[simp] = invt_invt_inImage[THEN conjunct1]
lemmas invt_inImage[simp] = invt_invt_inImage[THEN conjunct2]


(* We translate the environments of the tag-extended-problem model
to environments of its original-signature reduct: *)  term invt
definition "eenv \<xi> x \<equiv> invt (tpOfV x) (\<xi> x)"

lemma wt_eenv:
assumes \<xi>: "Ik.wtE \<xi>"  shows "TE.wtE (eenv \<xi>)"
unfolding TE.wtE_def proof safe
  fix x let ?\<sigma> = "TE.tpOfV x"
  show "eintT ?\<sigma> (eenv \<xi> x)" proof(cases "unprot ?\<sigma>")
    case True note unprot = True
    thus ?thesis unfolding eenv_def by (metis \<xi> Ik.wtTE_intT intT_def unprot_invt)
  next
    case False note unprot = False show ?thesis proof(cases "protFw ?\<sigma>")
      case True thus ?thesis unfolding eenv_def using unprot \<xi>
      by (metis Ik.wtTE_intT intT_def unprot_invt)
    next
      case False thus ?thesis unfolding eenv_def using unprot \<xi>
      by (metis (no_types) \<xi> Ik.wtE_def intT_def invt)
    qed
  qed
qed

lemma int_tNN[simp]:
assumes T: "Ik.Ik.wt T" and \<xi>: "Ik.wtE \<xi>"
shows "TE.int (eenv \<xi>) (tNN T) = Ik.int \<xi> T"
using T proof(induct T)
  case (Var x) let ?\<sigma> = "TE.tpOfV x"  show ?case
  proof(cases "unprot ?\<sigma>")
    case False note unprot = False
    show ?thesis proof(cases "protFw ?\<sigma>")
      case True thus ?thesis using unprot \<xi>
      unfolding eenv_def Ik.wtE_def intT_def by simp
    next
      case False  hence "\<xi> x \<in> (eintF (Tag ?\<sigma>) \<circ> singl) ` {b. eintT ?\<sigma> b}"
        using \<xi> unprot unfolding wtE_def intT_def singl_def[abs_def] by (simp cong del: image_cong_simp)
      thus ?thesis using unprot unfolding eenv_def using False by simp
    qed
  qed(unfold eenv_def, simp)
next
  case (Fn f Tl)
  let ?e\<xi> = "eenv \<xi>" let ?ar = "arOf f" let ?r = "resOf f"
  have l: "length ?ar = length Tl" using Fn by simp
  have 0: "map2 ntsem ?ar (map (Ik.int \<xi>) Tl) =
           map (TE.int ?e\<xi> \<circ> tNN) Tl"  (is "?L = ?R")
  proof(rule nth_equalityI)
    fix i assume "i < length ?L"
    hence i: "i < length ?ar" using l by simp
    hence 1: "TE.int (eenv \<xi>) (tNN (Tl!i)) = Ik.int \<xi> (Tl!i)"
      using Fn by (auto simp: list_all_length)
    have 2: "?ar ! i = Ik.Ik.tpOf (Tl!i)" using Fn i by simp
    have 3: "intT (?ar ! i) (Ik.int \<xi> (Tl ! i))"
      unfolding 2 apply(rule wt_int)
      using Fn \<xi> i by (auto simp: list_all_length)
    show "?L!i = ?R!i" apply (cases "unprot (?ar ! i) \<or> protFw (?ar ! i)")
      using i 1 l 3 unfolding intT_def by auto
  qed(insert l, auto)
  show ?case apply(cases "unprot ?r \<or> protFw ?r")
    using [[unfold_abs_def = false]]
    unfolding Ik.int.simps TE.int.simps tT.simps unfolding intF_def using Fn 0 by auto
qed

lemma map_int_tNN[simp]:
assumes Tl: "list_all Ik.Ik.wt Tl" and \<xi>: "Ik.wtE \<xi>"
shows
"map2 ntsem (map Ik.Ik.tpOf Tl) (map (Ik.int \<xi>) Tl) =
 map (TE.int (eenv \<xi>) \<circ> tNN) Tl"
proof-
  {fix i assume i: "i < length Tl"
   hence wt: "Ik.Ik.wt (Tl!i)" using Tl unfolding list_all_length by simp
   have "intT (Ik.Ik.tpOf (Tl!i)) (Ik.int \<xi> (Tl!i))" using Ik.wt_int[OF \<xi> wt] .
  }
  thus ?thesis
  using [[unfold_abs_def = false]]
  using assms unfolding intT_def list_all_length
  unfolding list_eq_iff apply clarsimp by (metis inImage_ntsem unprot_ntsem)
qed

lemma int_t[simp]:
assumes T: "Ik.Ik.wt T" and \<xi>: "Ik.wtE \<xi>"
shows "TE.int (eenv \<xi>) (tT T) = Ik.int \<xi> T"
using T proof(induct T)
  case (Var x) let ?\<sigma> = "tpOfV x"  show ?case
  proof(cases "unprot ?\<sigma>")
    case False note unprot = False
    show ?thesis proof(cases "protFw ?\<sigma>")
      case True thus ?thesis using unprot \<xi>
      unfolding eenv_def Ik.wtE_def intT_def by simp
    next
      case False  hence "\<xi> x \<in> (eintF (Tag ?\<sigma>) \<circ> singl) ` {b. eintT ?\<sigma> b}"
      using \<xi> unprot unfolding wtE_def intT_def singl_def[abs_def] by (simp cong del: image_cong_simp)
      thus ?thesis using unprot unfolding eenv_def using False by simp
    qed
  qed(unfold eenv_def, simp)
next
  case (Fn f Tl)
  let ?e\<xi> = "eenv \<xi>"  let ?ar = "arOf f"  let ?r = "resOf f"
  have l: "length ?ar = length Tl" using Fn by simp
  have ar: "?ar = map Ik.Ik.tpOf Tl" using Fn by simp
  have 0: "map2 ntsem ?ar (map (Ik.int \<xi>) Tl) = map (TE.int ?e\<xi> \<circ> tNN) Tl"
  unfolding ar apply(rule map_int_tNN[OF _ \<xi>]) using Fn by simp
  show ?case apply(cases "unprot ?r \<or> protFw ?r")
  using [[unfold_abs_def = false]]
  unfolding  Ik.int.simps TE.int.simps tT.simps unfolding intF_def using Fn 0 by auto
qed

lemma map_int_t[simp]:
assumes Tl: "list_all Ik.Ik.wt Tl" and \<xi>: "Ik.wtE \<xi>"
shows
"map2 ntsem (map Ik.Ik.tpOf Tl) (map (Ik.int \<xi>) Tl) =
 map (TE.int (eenv \<xi>) \<circ> tT) Tl"
proof-
  {fix i assume i: "i < length Tl"
   hence wt: "Ik.Ik.wt (Tl!i)" using Tl unfolding list_all_length by simp
   have "intT (Ik.Ik.tpOf (Tl!i)) (Ik.int \<xi> (Tl!i))" using wt_int[OF \<xi> wt] .
  }
  thus ?thesis
  using [[unfold_abs_def = false]]
  using assms unfolding intT_def list_all_length
  unfolding list_eq_iff apply clarsimp by (metis inImage_ntsem unprot_ntsem)
qed

lemma satL_tL[simp]:
assumes l: "Ik.Ik.wtL l" and \<xi>: "Ik.wtE \<xi>"
shows "TE.satL (eenv \<xi>) (tL l) \<longleftrightarrow> Ik.satL \<xi> l"
using assms apply(cases l) apply (rename_tac [!] atm) by (case_tac [!] atm) (auto simp add: intP_def)

lemma satC_tC[simp]:
assumes l: "Ik.Ik.wtC c" and \<xi>: "Ik.wtE \<xi>"
shows "TE.satC (eenv \<xi>) (tC c) \<longleftrightarrow> Ik.satC \<xi> c"
unfolding TE.satC_def Ik.satC_def
using assms by (induct c, auto simp add: Ik.Ik.wtC_def tC_def)

lemma satPB_tPB[simp]:
assumes \<xi>: "Ik.wtE \<xi>"
shows "TE.satPB (eenv \<xi>) (tC ` \<Phi>) \<longleftrightarrow> Ik.satPB \<xi> \<Phi>"
using Ik.wt_\<Phi> assms unfolding TE.satPB_def Ik.satPB_def by (auto simp add: Ik.Ik.wtPB_def)

lemma completeness: "Ik.SAT \<Phi>"
unfolding Ik.SAT_def proof safe
  fix \<xi> assume \<xi>: "Ik.wtE \<xi>" hence "TE.wtE (eenv \<xi>)" by(rule wt_eenv)
  hence "TE.satPB (eenv \<xi>) tPB" by (rule TE.sat_\<Phi>)
  hence "TE.satPB (eenv \<xi>) (tC ` \<Phi>)" unfolding tPB_def by simp
  thus "Ik.satPB \<xi> \<Phi>" using \<xi> by simp
qed

lemma T_completeness: "Model wtFsym wtPsym arOf resOf parOf \<Phi> intT intF intP"
by standard (rule completeness)

end (* context ProblemIkTpart_TEModel *)

(* Completeness theorem in sublocale form: Given a problem (with indicated
type partition) and a model for its tag-translated problem,
we obtain a model of the original problem: *)

sublocale ProblemIkTpart_TEModel < O? : Model
where intT = intT and intF = intF and intP = intP
using T_completeness .


subsection\<open>The result of the tag translation is an infiniteness-augmented problem\<close>

(* Note that basic fact, merely stating that
the translation is well-defined between infiniteness-augmented problems,
is only proved at this late stage since it requires completeness.
This is an interesting dependency, not spotted in the paper. *)

sublocale ProblemIkTpart < TE? : Problem
where wtFsym = TE_wtFsym and arOf = TE_arOf and resOf = TE_resOf
and \<Phi> = tPB
apply standard by auto

sublocale ProblemIkTpart < TE? : ProblemIk
where wtFsym = TE_wtFsym and arOf = TE_arOf and resOf = TE_resOf
and \<Phi> = tPB
proof
  fix \<sigma> eintT eintF eintP a  assume \<sigma>: "infTp \<sigma>"
  assume M: "Model TE_wtFsym wtPsym TE_arOf TE_resOf parOf tPB eintT eintF eintP"
  let ?TE_intT = "ProblemIkTpart_TEModel.intT prot protFw eintT eintF"
  let ?TE_intF = "ProblemIkTpart_TEModel.intF arOf resOf prot protFw eintT eintF"
  let ?TE_intP = "ProblemIkTpart_TEModel.intP parOf prot protFw eintT eintF eintP"
  have 0: "ProblemIkTpart_TEModel wtFsym wtPsym arOf resOf parOf
                                   \<Phi> infTp prot protFw eintT eintF eintP"
  using M unfolding ProblemIkTpart_TEModel_def apply safe apply standard done
  hence MM: "Ik.MModel ?TE_intT ?TE_intF ?TE_intP"
  by (rule ProblemIkTpart_TEModel.T_completeness)
  have "infinite {a. ?TE_intT \<sigma> a}" using infTp[OF \<sigma> MM] .
  moreover have "{a. ?TE_intT \<sigma> a} \<subseteq> {a. eintT \<sigma> a}"
  using ProblemIkTpart_TEModel.intT_def[OF 0] by auto
  ultimately show "infinite {a. eintT \<sigma> a}" using infinite_super by blast
qed


subsection\<open>The verification of the first monotonicity calculus criterion
for the tagged problem\<close>

context ProblemIkTpart begin

lemma nvT_t[simp]: "\<not> unprot \<sigma> \<Longrightarrow> (\<forall> x \<in> TE.nvT (tT T). tpOfV x \<noteq> \<sigma>)"
apply(induct T) by auto

lemma nvL_tL[simp]: "\<not> unprot \<sigma> \<Longrightarrow> (\<forall> x \<in> TE.nvL (tL l). tpOfV x \<noteq> \<sigma>)"
apply(cases l) apply(rename_tac [!] atm) apply(case_tac [!] atm) by auto (metis nvT_t)+

lemma nvC_tC[simp]: "\<not> unprot \<sigma> \<Longrightarrow> (\<forall> x \<in> TE.nvC (tC c). tpOfV x \<noteq> \<sigma>)"
unfolding tC_def TE.nvC_def apply (induct c)
by auto (metis (full_types) nvL_tL)+

lemma unprot_nvT_t[simp]:
"unprot (tpOfV x) \<Longrightarrow> x \<in> TE.nvT (tT T) \<longleftrightarrow> x \<in>  TE.nvT T"
by (induct T, auto)

lemma tpL_nvT_tL[simp]:
"unprot (tpOfV x) \<Longrightarrow> x \<in> TE.nvL (tL l) \<longleftrightarrow> x \<in> TE.nvL l"
by (cases l, rename_tac [!] atm, case_tac [!] atm, auto)

lemma unprot_nvC_tC[simp]:
"unprot (tpOfV x) \<Longrightarrow> x \<in> TE.nvC (tC c) \<longleftrightarrow> x \<in> TE.nvC c"
unfolding tC_def TE.nvC_def apply (induct c) by auto

(* The added axioms are monotonic *)
lemma nv_OfFax[simp]:
"x \<notin> TE.nvT (lOfFax f)"  "x \<notin> TE.nvT (rOfFax f)"
unfolding lOfFax_def rOfFax_def lOfWax_def rOfWax_def by auto

lemma nv_OfWax[simp]:
"x \<notin> TE.nvT (lOfWax \<sigma>')"  "x \<notin> TE.nvT (rOfWax \<sigma>')"
unfolding lOfFax_def rOfFax_def lOfWax_def rOfWax_def by auto

lemma nvC_Fax: "c \<in> Fax \<Longrightarrow> TE.nvC c = {}" unfolding Fax_def TE.nvC_def by auto
lemma mcalc_Fax: "c \<in> Fax \<Longrightarrow> TE.mcalc \<sigma> c" using nvC_Fax unfolding TE.mcalc_iff by auto
lemma nvC_Wax: "c \<in> Wax \<Longrightarrow> TE.nvC c = {}" unfolding Wax_def TE.nvC_def by auto
lemma mcalc_Wax: "c \<in> Wax \<Longrightarrow> TE.mcalc \<sigma> c" using nvC_Wax[of c] by simp


end (* context ProblemIkTpart *)

sublocale ProblemIkTpart < TE?: ProblemIkMcalc
where wtFsym = TE_wtFsym and arOf = TE_arOf and resOf = TE_resOf
and \<Phi> = tPB
proof
  fix \<sigma> c assume "c \<in> tPB"
  thus "TE.mcalc \<sigma> c" unfolding tPB_def proof safe
    fix d assume d: "d \<in> \<Phi>" thus "TE.mcalc \<sigma> (tC d)"
    using unprot_mcalc[OF _ d] unfolding TE.mcalc_iff by (cases "unprot \<sigma>", auto, force)
  qed(insert mcalc_Fax mcalc_Wax, blast+)
qed

(* We already know that ProblemIkMcalc < MonotProblem, so by transitivity we obtain
the following main theorem, stating that the tag translation yields a monotonic
problem *)
context ProblemIkTpart begin

theorem T_monotonic:
"MonotProblem TE_wtFsym wtPsym TE_arOf TE_resOf parOf tPB" ..

end (* context ProblemIkTpart *)


sublocale ProblemIkTpart < TE?: MonotProblem
where wtFsym = TE_wtFsym and arOf = TE_arOf and resOf = TE_resOf and \<Phi> = tPB
using T_monotonic .


end
