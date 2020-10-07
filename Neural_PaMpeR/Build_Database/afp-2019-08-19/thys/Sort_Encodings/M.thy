theory M
imports TermsAndClauses Sig
begin  


subsection\<open>Well-typed (well-formed) terms, clauses, literals and problems\<close>

context Signature begin

text\<open>The type of a term\<close>
fun tpOf where
"tpOf (Var x) = tpOfV x"
|
"tpOf (Fn f Tl) = resOf f"

(* Well-typed terms *)
fun wt where
"wt (Var x) \<longleftrightarrow> True"
|
"wt (Fn f Tl) \<longleftrightarrow>
 wtFsym f \<and> list_all wt Tl \<and> arOf f = map tpOf Tl"

(* Well-typed atoms (atomic formulas) *)
fun wtA where
"wtA (Eq T1 T2) \<longleftrightarrow> wt T1 \<and> wt T2 \<and> tpOf T1 = tpOf T2"
|
"wtA (Pr p Tl) \<longleftrightarrow>
 wtPsym p \<and> list_all wt Tl \<and> parOf p = map tpOf Tl"

(* Well-typed literals *)
fun wtL where
"wtL (Pos a) \<longleftrightarrow> wtA a"
|
"wtL (Neg a) \<longleftrightarrow> wtA a"

(* Well-typed clauses *)
definition "wtC \<equiv> list_all wtL"

lemma wtC_append[simp]: "wtC (c1 @ c2) \<longleftrightarrow> wtC c1 \<and> wtC c2"
unfolding wtC_def by simp

(* Well-typed problems *)
definition "wtPB \<Phi> \<equiv> \<forall> c \<in> \<Phi>. wtC c"

lemma wtPB_Un[simp]: "wtPB (\<Phi>1 \<union> \<Phi>2) \<longleftrightarrow> wtPB \<Phi>1 \<and> wtPB \<Phi>2"
unfolding wtPB_def by auto

lemma wtPB_UN[simp]: "wtPB (\<Union> i \<in> I. \<Phi> i) \<longleftrightarrow> (\<forall> i \<in> I. wtPB (\<Phi> i))"
unfolding wtPB_def by auto

lemma wtPB_sappend[simp]:
assumes "wtPB \<Phi>1" and "wtPB \<Phi>2"  shows "wtPB (\<Phi>1 @@ \<Phi>2)"
using assms unfolding wtPB_def sappend_def by auto

(* Well-typed substitutions *)
definition "wtSB \<pi> \<equiv> \<forall> x. wt (\<pi> x) \<and> tpOf (\<pi> x) = tpOfV x"

lemma wtSB_wt[simp]: "wtSB \<pi> \<Longrightarrow> wt (\<pi> x)"
unfolding wtSB_def by auto

lemma wtSB_tpOf[simp]: "wtSB \<pi> \<Longrightarrow> tpOf (\<pi> x) = tpOfV x"
unfolding wtSB_def by auto

lemma wt_tpOf_subst:
assumes "wtSB \<pi>" and "wt T"
shows "wt (subst \<pi> T) \<and> tpOf (subst \<pi> T) = tpOf T"
using assms apply(induct T) by (auto simp add: list_all_iff)

lemmas wt_subst[simp] = wt_tpOf_subst[THEN conjunct1]
lemmas tpOf_subst[simp] = wt_tpOf_subst[THEN conjunct2]

lemma wtSB_o:
assumes 1: "wtSB \<pi>1" and 2: "wtSB \<pi>2"
shows "wtSB (subst \<pi>1 o \<pi>2)"
using 2 unfolding wtSB_def using 1 by auto

(* Getting variable terms for given types: *)
definition "getTvars \<sigma>l \<equiv> map Var (getVars \<sigma>l)"

lemma length_getTvars[simp]: "length (getTvars \<sigma>l) = length \<sigma>l"
unfolding getTvars_def by auto

lemma wt_getTvars[simp]: "list_all wt (getTvars \<sigma>l)"
unfolding list_all_length getTvars_def by simp

lemma wt_nth_getTvars[simp]:
"i < length \<sigma>l \<Longrightarrow> wt (getTvars \<sigma>l ! i)"
unfolding getTvars_def by auto

lemma map_tpOf_getTvars[simp]: "map tpOf (getTvars \<sigma>l) = \<sigma>l"
unfolding getTvars_def unfolding list_eq_iff by auto

lemma tpOf_nth_getTvars[simp]:
"i < length \<sigma>l \<Longrightarrow> tpOf (getTvars \<sigma>l ! i) = \<sigma>l ! i"
unfolding getTvars_def by auto

end (* context Signature *)


subsection \<open>Structures\<close>

text\<open>We split a structre into a ``type structure'' that interprets the types 
and the rest of the structure that interprets the function and relation symbols.\<close>

text\<open>Type structures:\<close>

locale Tstruct =
fixes intT :: "'tp \<Rightarrow> 'univ \<Rightarrow> bool"
assumes NE_intT: "NE (intT \<sigma>)"

text\<open>Environment:\<close>

type_synonym ('tp,'univ) env = "'tp \<Rightarrow> var \<Rightarrow> 'univ"

text\<open>Structures:\<close>

locale Struct = Signature wtFsym wtPsym arOf resOf parOf +
                Tstruct intT
for wtFsym and wtPsym
and arOf :: "'fsym \<Rightarrow> 'tp list"
and resOf :: "'fsym \<Rightarrow> 'tp"
and parOf :: "'psym \<Rightarrow> 'tp list"
and intT :: "'tp \<Rightarrow> 'univ \<Rightarrow> bool"
+
fixes
    intF :: "'fsym \<Rightarrow> 'univ list \<Rightarrow> 'univ"
and intP :: "'psym \<Rightarrow> 'univ list \<Rightarrow> bool"
assumes
intF: "\<lbrakk>wtFsym f; list_all2 intT (arOf f) al\<rbrakk> \<Longrightarrow> intT (resOf f) (intF f al)"
and
dummy: "intP = intP"
begin

text\<open>Well-typed environment:\<close>

definition "wtE \<xi> \<equiv> \<forall> x. intT (tpOfV x) (\<xi> x)"

lemma wtTE_intT[simp]: "wtE \<xi> \<Longrightarrow> intT (tpOfV x) (\<xi> x)"
unfolding wtE_def dom_def by auto

(* Picking an element from the domain of a given type: *)
definition "pickT \<sigma> \<equiv> SOME a. intT \<sigma> a"

lemma pickT[simp]: "intT \<sigma> (pickT \<sigma>)"
unfolding pickT_def apply(rule someI_ex) using NE_intT by auto

text\<open>Picking a well-typed environment:\<close>

definition
"pickE (xl::var list) al \<equiv>
 SOME \<xi>. wtE \<xi> \<and> (\<forall> i < length xl. \<xi> (xl!i) = al!i)"

lemma ex_pickE:
assumes "length xl = length al"
and "distinct xl" and "\<And> i. i < length xl \<Longrightarrow> intT (tpOfV (xl!i)) (al!i)"
shows "\<exists> \<xi>. wtE \<xi> \<and> (\<forall> i < length xl. \<xi> (xl!i) = al!i)"
using assms
proof(induct rule: list_induct2)
  case Nil show ?case apply(rule exI[of _ "\<lambda> x. pickT (tpOfV x)"])
  unfolding wtE_def by auto
next
  case (Cons x xl a al)
  then obtain \<xi> where 1: "wtE \<xi>" and 2: "\<forall> i < length xl. \<xi> (xl!i) = al!i" by force
  define \<xi>' where "\<xi>' x' = (if x = x' then a else \<xi> x')" for x'
  show ?case
  proof(rule exI[of _ \<xi>'], unfold wtE_def, safe)
    fix x' show "intT (tpOfV x') (\<xi>' x')"
    using 1 Cons.prems(2)[of 0] unfolding \<xi>'_def by auto
  next
    fix i assume i: "i < length (x # xl)"
    thus "\<xi>' ((x # xl) ! i) = (a # al) ! i"
    proof(cases i)
      case (Suc j) hence j: "j < length xl" using i by auto
      have "\<not> x = (x # xl) ! i" using Suc i Cons.prems(1) by auto
      thus ?thesis using Suc using j Cons.prems(1) Cons.hyps 2 unfolding \<xi>'_def by auto
    qed(insert Cons.prems(1) Cons.hyps 2, unfold \<xi>'_def, simp)
  qed
qed

lemma wtE_pickE_pickE:
assumes "length xl = length al"
and "distinct xl" and "\<And> i. i < length xl \<Longrightarrow> intT (tpOfV (xl!i)) (al!i)"
shows "wtE (pickE xl al) \<and> (\<forall> i. i < length xl \<longrightarrow> pickE xl al (xl!i) = al!i)"
proof-
  let ?phi = "\<lambda> \<xi>. wtE \<xi> \<and> (\<forall> i < length xl. \<xi> (xl!i) = al!i)"
  show ?thesis unfolding pickE_def apply(rule someI_ex[of ?phi])
  using ex_pickE[OF assms] by simp
qed

lemmas wtE_pickE[simp] = wtE_pickE_pickE[THEN conjunct1]

lemma pickE[simp]:
assumes "length xl = length al"
and "distinct xl" and "\<And> i. i < length xl \<Longrightarrow> intT (tpOfV (xl!i)) (al!i)"
and "i < length xl"
shows "pickE xl al (xl!i) = al!i"
using assms wtE_pickE_pickE by auto

definition "pickAnyE \<equiv> pickE [] []"

lemma wtE_pickAnyE[simp]: "wtE pickAnyE"
unfolding pickAnyE_def by (rule wtE_pickE) auto

(* Interpretation of terms: *)
fun int where
"int \<xi> (Var x) = \<xi> x"
|
"int \<xi> (Fn f Tl) = intF f (map (int \<xi>) Tl)"

(* Satisfaction of atoms: *)
fun satA where
"satA \<xi> (Eq T1 T2) \<longleftrightarrow> int \<xi> T1 = int \<xi> T2"
|
"satA \<xi> (Pr p Tl) \<longleftrightarrow> intP p (map (int \<xi>) Tl)"

(* Satisfaction literals: *)
fun satL where
"satL \<xi> (Pos a) \<longleftrightarrow> satA \<xi> a"
|
"satL \<xi> (Neg a) \<longleftrightarrow> \<not> satA \<xi> a"

(* Satisfaction of clauses: *)
definition "satC \<xi> \<equiv> list_ex (satL \<xi>)"

lemma satC_append[simp]: "satC \<xi> (c1 @ c2) \<longleftrightarrow> satC \<xi> c1 \<or> satC \<xi> c2"
unfolding satC_def by auto

lemma satC_iff_set: "satC \<xi> c \<longleftrightarrow> (\<exists> l \<in> set c. satL \<xi> l)"
unfolding satC_def Bex_set[symmetric] ..

(* satisfaction of problems *)
definition "satPB \<xi> \<Phi> \<equiv> \<forall> c \<in> \<Phi>. satC \<xi> c"

lemma satPB_Un[simp]: "satPB \<xi> (\<Phi>1 \<union> \<Phi>2) \<longleftrightarrow> satPB \<xi> \<Phi>1 \<and> satPB \<xi> \<Phi>2"
unfolding satPB_def by auto

lemma satPB_UN[simp]: "satPB \<xi> (\<Union> i \<in> I. \<Phi> i) \<longleftrightarrow> (\<forall> i \<in> I. satPB \<xi> (\<Phi> i))"
unfolding satPB_def by auto

lemma satPB_sappend[simp]: "satPB \<xi> (\<Phi>1 @@ \<Phi>2) \<longleftrightarrow> satPB \<xi> \<Phi>1 \<or> satPB \<xi> \<Phi>2"
unfolding satPB_def sappend_def by (fastforce simp: satC_append)

definition "SAT \<Phi> \<equiv> \<forall> \<xi>. wtE \<xi> \<longrightarrow> satPB \<xi> \<Phi>"

lemma SAT_UN[simp]: "SAT (\<Union> i \<in> I. \<Phi> i) \<longleftrightarrow> (\<forall> i \<in> I. SAT (\<Phi> i))"
unfolding SAT_def by auto

text\<open>Soundness of typing w.r.t. interpretation:\<close>

lemma wt_int:
assumes wtE: "wtE \<xi>" and wt: "wt T"
shows "intT (tpOf T) (int \<xi> T)"
using wt apply(induct T) using wtE
by (auto intro!: intF simp add: list_all2_map_map)

lemma int_cong:
assumes "\<And>x. x \<in> vars T \<Longrightarrow> \<xi>1 x = \<xi>2 x"
shows "int \<xi>1 T = int \<xi>2 T"
using assms proof(induct T)
  case (Fn f Tl)
  hence 1: "map (int \<xi>1) Tl = map (int \<xi>2) Tl"
  unfolding list_all_iff by (auto intro: map_ext)
  show ?case apply simp by (metis 1)
qed auto

lemma satA_cong:
assumes "\<And>x. x \<in> varsA at \<Longrightarrow> \<xi>1 x = \<xi>2 x"
shows "satA \<xi>1 at \<longleftrightarrow> satA \<xi>2 at"
using assms int_cong[of _ \<xi>1 \<xi>2]
apply(cases at) apply(fastforce intro!: int_cong[of _ \<xi>1 \<xi>2])
apply simp by (metis (hide_lams, mono_tags) map_eq_conv)

lemma satL_cong:
assumes "\<And> x. x \<in> varsL l \<Longrightarrow> \<xi>1 x = \<xi>2 x"
shows "satL \<xi>1 l \<longleftrightarrow> satL \<xi>2 l"
using assms satA_cong[of _ \<xi>1 \<xi>2] by (cases l, auto)

lemma satC_cong:
assumes "\<And> x. x \<in> varsC c \<Longrightarrow> \<xi>1 x = \<xi>2 x"
shows "satC \<xi>1 c \<longleftrightarrow> satC \<xi>2 c"
using assms satL_cong[of _ \<xi>1 \<xi>2] unfolding satC_def varsC_def
apply (induct c) by (fastforce intro!: satL_cong[of _ \<xi>1 \<xi>2])+

lemma satPB_cong:
assumes "\<And> x. x \<in> varsPB \<Phi> \<Longrightarrow> \<xi>1 x = \<xi>2 x"
shows "satPB \<xi>1 \<Phi> \<longleftrightarrow> satPB \<xi>2 \<Phi>"
by (force simp: satPB_def varsPB_def intro!: satC_cong ball_cong assms)

lemma int_o:
"int (int \<xi> o \<rho>) T = int \<xi> (subst \<rho> T)"
apply(induct T) apply simp_all unfolding list_all_iff o_def
using map_ext by (metis (lifting, no_types))

lemmas int_subst = int_o[symmetric]

lemma int_o_subst:
"int \<xi> o subst \<rho> = int (int \<xi> o \<rho>)"
apply(rule ext) apply(subst comp_def) unfolding int_o[symmetric] ..

lemma satA_o:
"satA (int \<xi> o \<rho>) at = satA \<xi> (substA \<rho> at)"
by (cases at, simp_all add: int_o_subst int_o[of \<xi> \<rho>])

lemmas satA_subst = satA_o[symmetric]

lemma satA_o_subst:
"satA \<xi> o substA \<rho> = satA (int \<xi> o \<rho>)"
apply(rule ext) apply(subst comp_def) unfolding satA_o[symmetric] ..

lemma satL_o:
"satL (int \<xi> o \<rho>) l = satL \<xi> (substL \<rho> l)"
using satA_o[of \<xi> \<rho>] by (cases l, simp_all)

lemmas satL_subst = satL_o[symmetric]

lemma satL_o_subst:
"satL \<xi> o substL \<rho> = satL (int \<xi> o \<rho>)"
apply(rule ext) apply(subst comp_def) unfolding satL_o[symmetric] ..

lemma satC_o:
"satC (int \<xi> o \<rho>) c = satC \<xi> (substC \<rho> c)"
using satL_o[of \<xi> \<rho>] unfolding satC_def substC_def by (induct c, auto)

lemmas satC_subst = satC_o[symmetric]

lemma satC_o_subst:
"satC \<xi> o substC \<rho> = satC (int \<xi> o \<rho>)"
apply(rule ext) apply(subst comp_def) unfolding satC_o[symmetric] ..

lemma satPB_o:
"satPB (int \<xi> o \<rho>) \<Phi> = satPB \<xi> (substPB \<rho> \<Phi>)"
using satC_o[of \<xi> \<rho>] unfolding satPB_def substPB_def by auto

lemmas satPB_subst = satPB_o[symmetric]

lemma satPB_o_subst:
"satPB \<xi> o substPB \<rho> = satPB (int \<xi> o \<rho>)"
apply(rule ext) apply(subst comp_def) unfolding satPB_o[symmetric] ..

lemma wtE_o:
assumes 1: "wtE \<xi>" and 2: "wtSB \<rho>"
shows "wtE (int \<xi> o \<rho>)"
unfolding wtE_def proof
  fix x have 0: "tpOfV x = tpOf (\<rho> x)" using 2 by auto
  show "intT (tpOfV x) ((int \<xi> \<circ> \<rho>) x)" apply(subst 0) unfolding comp_def
  apply(rule wt_int[OF 1]) using 2 by auto
qed

(* fixme: unify compE and int \<xi> o \<rho>, since they are the same *)
definition "compE \<rho> \<xi> x \<equiv> int \<xi> (\<rho> x)"

lemma wtE_compE:
assumes "wtSB \<rho>" and "wtE \<xi>"  shows "wtE (compE \<rho> \<xi>)"
unfolding wtE_def using assms wt_int
unfolding wtSB_def compE_def by fastforce

lemma compE_upd: "compE (\<rho> (x := T)) \<xi> = (compE \<rho> \<xi>) (x := int \<xi> T)"
unfolding compE_def[abs_def] by auto

end (* context Struct *)


context Signature begin

(* The function symbols of: *)

fun fsyms where
"fsyms (Var x) = {}"
|
"fsyms (Fn f Tl) = {f} \<union> \<Union> (set (map fsyms Tl))"

fun fsymsA where
"fsymsA (Eq T1 T2) = fsyms T1 \<union> fsyms T2"
|
"fsymsA (Pr p Tl) = \<Union> (set (map fsyms Tl))"

fun fsymsL where
"fsymsL (Pos at) = fsymsA at"
|
"fsymsL (Neg at) = fsymsA at"

definition "fsymsC c = \<Union> (set (map fsymsL c))"

definition "fsymsPB \<Phi> = \<Union> {fsymsC c | c. c \<in> \<Phi>}"

lemma fsyms_int_cong:
assumes S1: "Struct wtFsym wtPsym arOf resOf intT intF1 intP"
and S2: "Struct wtFsym wtPsym arOf resOf intT intF2 intP"
and 0: "\<And> f. f \<in> fsyms T \<Longrightarrow> intF1 f = intF2 f"
shows "Struct.int intF1 \<xi> T = Struct.int intF2 \<xi> T"
using 0 proof(induct T)
  case (Fn f Tl)
  hence 1: "map (Struct.int intF1 \<xi>) Tl = map (Struct.int intF2 \<xi>) Tl"
  unfolding list_all_iff map_ext by auto
  show ?case 
  using Fn Struct.int.simps[OF S1, of \<xi>] Struct.int.simps[OF S2, of \<xi>] apply simp
  using 1 by metis
qed (auto simp: Struct.int.simps[OF S1, of \<xi>] Struct.int.simps[OF S2, of \<xi>])

lemma fsyms_satA_cong:
assumes S1: "Struct wtFsym wtPsym arOf resOf intT intF1 intP"
and S2: "Struct wtFsym wtPsym arOf resOf intT intF2 intP"
and 0: "\<And> f. f \<in> fsymsA at \<Longrightarrow> intF1 f = intF2 f"
shows "Struct.satA intF1 intP \<xi> at \<longleftrightarrow> Struct.satA intF2 intP \<xi> at"
using 0 fsyms_int_cong[OF S1 S2]
apply(cases at)
apply(fastforce intro!: fsyms_int_cong[OF S1 S2, of _ \<xi>]
                simp: Struct.satA.simps[OF S1, of \<xi>] Struct.satA.simps[OF S2, of \<xi>])
apply (simp add: Struct.satA.simps[OF S1, of \<xi>] Struct.satA.simps[OF S2, of \<xi>])
by (metis (hide_lams, mono_tags) map_eq_conv)

lemma fsyms_satL_cong:
assumes S1: "Struct wtFsym wtPsym arOf resOf intT intF1 intP"
and S2: "Struct wtFsym wtPsym arOf resOf intT intF2 intP"
and 0: "\<And> f. f \<in> fsymsL l \<Longrightarrow> intF1 f = intF2 f"
shows "Struct.satL intF1 intP \<xi> l \<longleftrightarrow> Struct.satL intF2 intP \<xi> l"
using 0 fsyms_satA_cong[OF S1 S2]
by (cases l, auto simp: Struct.satL.simps[OF S1, of \<xi>] Struct.satL.simps[OF S2, of \<xi>])

lemma fsyms_satC_cong:
assumes S1: "Struct wtFsym wtPsym arOf resOf intT intF1 intP"
and S2: "Struct wtFsym wtPsym arOf resOf intT intF2 intP"
and 0: "\<And> f. f \<in> fsymsC c \<Longrightarrow> intF1 f = intF2 f"
shows "Struct.satC intF1 intP \<xi> c \<longleftrightarrow> Struct.satC intF2 intP \<xi> c"
using 0 fsyms_satL_cong[OF S1 S2]
unfolding Struct.satC_def[OF S1] Struct.satC_def[OF S2] fsymsC_def
apply (induct c) by (fastforce intro!: fsyms_satL_cong[OF S1 S2])+

lemma fsyms_satPB_cong:
assumes S1: "Struct wtFsym wtPsym arOf resOf intT intF1 intP"
and S2: "Struct wtFsym wtPsym arOf resOf intT intF2 intP"
and 0: "\<And> f. f \<in> fsymsPB \<Phi> \<Longrightarrow> intF1 f = intF2 f"
shows "Struct.satPB intF1 intP \<xi> \<Phi> \<longleftrightarrow> Struct.satPB intF2 intP \<xi> \<Phi>"
by (force simp: Struct.satPB_def[OF S1] Struct.satPB_def[OF S2] fsymsPB_def
          intro!: fsyms_satC_cong[OF S1 S2] ball_cong 0)

lemma fsymsPB_Un[simp]: "fsymsPB (\<Phi>1 \<union> \<Phi>2) = fsymsPB \<Phi>1 \<union> fsymsPB \<Phi>2"
unfolding fsymsPB_def by auto

lemma fsymsC_append[simp]: "fsymsC (c1 @ c2) = fsymsC c1 \<union> fsymsC c2"
unfolding fsymsC_def by auto

lemma fsymsPB_sappend_incl[simp]:
"fsymsPB (\<Phi>1 @@ \<Phi>2) \<subseteq>  fsymsPB \<Phi>1 \<union> fsymsPB \<Phi>2"
by (unfold fsymsPB_def sappend_def, fastforce)

lemma fsymsPB_sappend[simp]:
assumes 1: "\<Phi>1 \<noteq> {}" and 2: "\<Phi>2 \<noteq> {}"
shows "fsymsPB (\<Phi>1 @@ \<Phi>2) = fsymsPB \<Phi>1 \<union> fsymsPB \<Phi>2"
proof safe
  fix x
  {assume "x \<in> fsymsPB \<Phi>1"
   then obtain c1 c2 where "x \<in> fsymsC c1" and "c1 \<in> \<Phi>1" and "c2 \<in> \<Phi>2"
   using 2 unfolding fsymsPB_def by auto
   thus "x \<in> fsymsPB (\<Phi>1 @@ \<Phi>2)" unfolding sappend_def fsymsPB_def by fastforce
  }
  {assume "x \<in> fsymsPB \<Phi>2"
   then obtain c1 c2 where "x \<in> fsymsC c2" and "c1 \<in> \<Phi>1" and "c2 \<in> \<Phi>2"
   using 1 unfolding fsymsPB_def by auto
   thus "x \<in> fsymsPB (\<Phi>1 @@ \<Phi>2)" unfolding sappend_def fsymsPB_def by fastforce
  }
qed(unfold fsymsPB_def sappend_def, fastforce)

lemma Struct_upd:
assumes "Struct wtFsym wtPsym arOf resOf intT intF intP"
and "\<And> al. list_all2 intT (arOf ef) al \<Longrightarrow> intT (resOf ef) (EF al)"
shows "Struct wtFsym wtPsym arOf resOf intT (intF (ef := EF)) intP"
apply standard using assms
unfolding Struct_def Struct_axioms_def Tstruct_def by auto

end (* context Signature *)


subsection\<open>Problems\<close>

text\<open>A problem is a potentially infinitary formula in clausal form, i.e., 
a potentially infinite conjunction of clauses.\<close>

locale Problem = Signature wtFsym wtPsym arOf resOf parOf
for wtFsym wtPsym
and arOf :: "'fsym \<Rightarrow> 'tp list"
and resOf :: "'fsym \<Rightarrow> 'tp"
and parOf :: "'psym \<Rightarrow> 'tp list"
+
fixes \<Phi> :: "('fsym, 'psym) prob"
assumes wt_\<Phi>: "wtPB \<Phi>"


subsection\<open>Models of a problem\<close>

text\<open>Model of a problem:\<close>

locale Model = Problem + Struct +
assumes SAT: "SAT \<Phi>"
begin
lemma sat_\<Phi>: "wtE \<xi> \<Longrightarrow> satPB \<xi> \<Phi>"
using SAT unfolding SAT_def by auto
end


end
