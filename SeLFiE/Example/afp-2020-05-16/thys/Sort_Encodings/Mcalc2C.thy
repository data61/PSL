(* A particular case of the second calculus, with policy constant on types: *)
theory Mcalc2C
imports Mcalc2
begin

subsection\<open>Constant policy on types\<close>

text\<open>Currently our soundness proof only covers the case of the calculus
having different extension policies for different predicates, but not
for differnt types versus the same predicate. This is sufficient for our purpose
of proving soundness of the guard encodings.\<close>

locale ProblemIkPolMcalc2C =
ProblemIkPolMcalc2 wtFsym wtPsym arOf resOf parOf \<Phi> infTp pol grdOf
for wtFsym :: "'fsym \<Rightarrow> bool" and wtPsym :: "'psym \<Rightarrow> bool"
and arOf :: "'fsym \<Rightarrow> 'tp list"
and resOf and parOf and \<Phi> and infTp and pol and grdOf
+ assumes pol_ct: "pol \<sigma>1 P = pol \<sigma>2 P"

context ProblemIkPolMcalc2C begin

definition "polC \<equiv> pol any"

lemma pol_polC: "pol \<sigma> P = polC P"
unfolding polC_def using pol_ct by auto

lemma nv2L_simps[simp]:
"nv2L (Pos (Pr p Tl)) = (case polC p of Fext \<Rightarrow> \<Union> (set (map nv2T Tl)) |_ \<Rightarrow> {})"
"nv2L (Neg (Pr p Tl)) = (case polC p of Text \<Rightarrow> \<Union> (set (map nv2T Tl)) |_ \<Rightarrow> {})"
by (auto split: epol.splits simp: pol_polC)

declare nv2L.simps(3,4)[simp del]

lemma isGuard_simps[simp]:
"isGuard x (Pos (Pr p Tl)) \<longleftrightarrow> x \<in> \<Union> (set (map nv2T Tl)) \<and> polC p = Text"
"isGuard x (Neg (Pr p Tl)) \<longleftrightarrow> x \<in> \<Union> (set (map nv2T Tl)) \<and> polC p = Fext"
by (auto simp: pol_polC)

declare isGuard.simps(3,4)[simp del]


end (* context  ProblemIkPolMcalc2 *)


locale ModelIkPolMcalc2C =
ModelIk wtFsym wtPsym arOf resOf parOf \<Phi> infTp intT intF intP +
ProblemIkPolMcalc2C wtFsym wtPsym arOf resOf parOf \<Phi> infTp pol grdOf
for wtFsym :: "'fsym \<Rightarrow> bool" and wtPsym :: "'psym \<Rightarrow> bool"
and arOf :: "'fsym \<Rightarrow> 'tp list"
and resOf and parOf and \<Phi> and infTp pol and grdOf and intT and intF and intP


subsection\<open>Extension of a structure to an infinte structure
by adding indistinguishable elements\<close>

context ModelIkPolMcalc2C begin

(* The projection from univ to a structure: *)
definition proj where "proj \<sigma> a \<equiv> if intT \<sigma> a then a else pickT \<sigma>"

lemma intT_proj[simp]: "intT \<sigma> (proj \<sigma> a)"
unfolding proj_def using pickT by auto

lemma proj_id[simp]: "intT \<sigma> a \<Longrightarrow> proj \<sigma> a = a"
unfolding proj_def by auto

lemma map_proj_id[simp]:
assumes "list_all2 intT \<sigma>l al"
shows "map2 proj \<sigma>l al = al"
apply(rule nth_equalityI)
using assms unfolding list_all2_length by auto

lemma surj_proj:
assumes "intT \<sigma> a"   shows "\<exists> b. proj \<sigma> b = a"
using assms by (intro exI[of _ a]) simp

definition "I_intT \<sigma> (a::univ) \<equiv> infTp \<sigma> \<longrightarrow> intT \<sigma> a"
definition "I_intF f al \<equiv> intF f (map2 proj (arOf f) al)"
definition
"I_intP p al \<equiv>
 case polC p of
   Cext \<Rightarrow> intP p (map2 proj (parOf p) al)
  |Text \<Rightarrow> if list_all2 intT (parOf p) al then intP p al else True
  |Fext \<Rightarrow> if list_all2 intT (parOf p) al then intP p al else False"

lemma not_infTp_I_intT[simp]: "\<not> infTp \<sigma> \<Longrightarrow> I_intT \<sigma> a"
unfolding I_intT_def by simp

lemma infTp_I_intT[simp]: "infTp \<sigma> \<Longrightarrow> I_intT \<sigma> a = intT \<sigma> a"
unfolding I_intT_def by simp

lemma NE_I_intT: "NE (I_intT \<sigma>)"
using NE_intT by (cases "infTp \<sigma>", auto)

lemma I_intP_Cext[simp]:
"polC p = Cext \<Longrightarrow> I_intP p al = intP p (map2 proj (parOf p) al)"
unfolding I_intP_def by simp

lemma I_intP_Text_imp[simp]:
assumes "polC p = Text" and "intP p al"
shows "I_intP p al"
using assms unfolding I_intP_def by auto

lemma I_intP_Fext_imp[simp]:
assumes "polC p = Fext" and "\<not> intP p al"
shows "\<not> I_intP p al"
using assms unfolding I_intP_def by (cases "list_all2 intT (parOf p) al", auto)

lemma I_intP_intT[simp]:
assumes "list_all2 intT (parOf p) al"
shows "I_intP p al = intP p al"
using assms unfolding I_intP_def by (cases "polC p") auto

lemma I_intP_Text_not_intT[simp]:
assumes "polC p = Text" and "\<not> list_all2 intT (parOf p) al"
shows "I_intP p al"
using assms unfolding I_intP_def by auto

lemma I_intP_Fext_not_intT[simp]:
assumes "polC p = Fext" and "\<not> list_all2 intT (parOf p) al"
shows "\<not> I_intP p al"
using assms unfolding I_intP_def by auto

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

end (* context ModelIkPolMcalc2C *)

sublocale ModelIkPolMcalc2C < InfStruct where
intT = I_intT and intF = I_intF and intP = I_intP
using InfStruct .

subsection\<open>The soundness of the calculus\<close>

(* In what follows, ``Ik" stands for the original
(augmented with infiniteness-knowledge)
and ``I" for the infinite structure constructed from it
through the above sublocale statement. *)

context ModelIkPolMcalc2C begin
(* The environment translation along the projection: *)
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
and nv2T: "infTp (Ik.tpOf T) \<or> (\<forall> x \<in> nv2T T. tpOfV x \<noteq> Ik.tpOf T)"
shows "Ik_intT (Ik.tpOf T) (I.int \<xi> T)"
proof(cases "\<exists> x. T = Var x")
  case True then obtain x where T: "T = Var x" by auto
  show ?thesis proof(cases "infTp (tpOf T)")
    case True thus ?thesis using T using wtE_transE[OF \<xi>]
    by (metis I.wt_int I_intT_def \<xi> wt)
  next
    case False hence "\<forall> x \<in> nv2T T. tpOfV x \<noteq> tpOf T" using nv2T by auto
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
  qed(insert Fn, simp)
qed simp

lemma int_transE_nv2T:
assumes wt: "Ik.wt T" and \<xi>: "I.wtE \<xi>"
and nv2T: "infTp (Ik.tpOf T) \<or> (\<forall> x \<in> nv2T T. tpOfV x \<noteq> Ik.tpOf T)"
shows "Ik.int (transE \<xi>) T = I.int \<xi> T"
unfolding int_transE_proj[OF wt] apply(rule proj_id)
using Ik_intT_int[OF wt \<xi> nv2T] .

lemma isGuard_not_satL_intT:
assumes wtL: "Ik.wtL l"
and (* crucial hypothesis--the essence of guarding:*) ns: "\<not> I.satL \<xi> l"
and g: "isGuard x l" and \<xi>: "I.wtE \<xi>"
shows "Ik_intT (tpOfV x) (\<xi> x)" (is "Ik_intT ?\<sigma> (\<xi> x)")
(* "proj \<sigma> (\<xi> \<sigma> x) = \<xi> \<sigma> x" *)
(* "Ik.int (transE \<xi>) (Var \<sigma> x) = I.int \<xi> (Var \<sigma> x)" *)
proof(cases l)
  case (Pos at)  show ?thesis proof(cases at)
    case (Pr p Tl)
    then obtain T where Tin: "T \<in> set Tl" and x: "x \<in> nv2T T" and pol: "polC p = Text"
    using g unfolding Pos Pr by auto
    hence T: "T = Var x" by (simp add: in_nv2T)
    obtain i where i: "i < length Tl" and Ti: "T = Tl!i" using Tin
    by (metis in_set_conv_nth)
    hence 0 : "wt T" "parOf p ! i = ?\<sigma>" using wtL unfolding Pos Pr T
    apply (simp_all add: list_all_iff) by (metis T x in_nv2T tpOf.simps)
    have "list_all2 Ik_intT (parOf p) (map (I.int \<xi>) Tl)" (is ?phi)
    using ns unfolding Pos Pr using pol by (cases ?phi, auto)
    hence "Ik_intT ?\<sigma> (I.int \<xi> T)"
    using ns 0 i Ti unfolding Pos Pr by (auto simp add: list_all2_length nth_map)
    thus ?thesis unfolding T by simp
  qed(insert g, unfold Pos, simp)
next
  case (Neg at)  show ?thesis proof(cases at)
    case (Eq T1 T2)
    hence 0: "T1 = Var x \<or> T2 = Var x" using g unfolding Neg by auto
    hence wt1: "Ik.wt T1" "Ik.tpOf T1 = tpOfV x"
    and wt2: "Ik.wt T2" "Ik.tpOf T2 = tpOfV x"
    using wtL unfolding Neg Eq by auto
    have eq: "I.int \<xi> T1 = I.int \<xi> T2" using ns unfolding Neg Eq by simp
    show ?thesis proof(cases "T1 = Var x")
      case True note T1 = True obtain f Tl where "T2 = Fn f Tl"
      using g T1 Eq unfolding Neg by auto
      hence "\<And> \<sigma>. infTp \<sigma> \<or> (\<forall> x \<in> nv2T T2. tpOfV x \<noteq> \<sigma>)" by auto
      hence 1: "I.int \<xi> T2 = Ik.int (transE \<xi>) T2" using int_transE_nv2T wt2 \<xi> by auto
      have "Ik_intT ?\<sigma> (I.int \<xi> T1)" unfolding eq 1 using wt2 \<xi> Ik.wt_int by force
      thus ?thesis unfolding T1 by simp
    next
      case False then obtain f Tl where T2: "T2 = Var x" and "T1 = Fn f Tl"
      using Eq Neg g by auto
      hence "\<And> \<sigma>. infTp \<sigma> \<or> (\<forall> x \<in> nv2T T1. tpOfV x \<noteq> \<sigma>)" by simp
      hence 1: "I.int \<xi> T1 = Ik.int (transE \<xi>) T1" using int_transE_nv2T wt1 \<xi> by auto
      have "Ik_intT ?\<sigma> (I.int \<xi> T2)" unfolding eq[symmetric] 1
      using wt1 \<xi> Ik.wt_int by force
      thus ?thesis unfolding T2 by simp
    qed
  next
    case (Pr p Tl)
    then obtain T where Tin: "T \<in> set Tl" and x: "x \<in> nv2T T" and pol: "polC p = Fext"
    using g unfolding Neg Pr by auto
    hence T: "T = Var x" by (simp add: in_nv2T)
    obtain i where i: "i < length Tl" and Ti: "T = Tl!i" using Tin
    by (metis in_set_conv_nth)
    hence 0 : "wt T" "parOf p ! i = ?\<sigma>" using wtL unfolding Neg Pr T
    apply (simp_all add: list_all_iff) by (metis T x in_nv2T tpOf.simps)
    have "list_all2 Ik_intT (parOf p) (map (I.int \<xi>) Tl)" (is ?phi)
    using ns unfolding Neg Pr using pol by (cases ?phi, auto)
    hence "Ik_intT ?\<sigma> (I.int \<xi> T)"
    using ns 0 i Ti unfolding Neg Pr by (auto simp add: list_all2_length nth_map)
    thus ?thesis unfolding T by simp
  qed
qed

lemma int_transE[simp]:
assumes wt: "Ik.wt T" and \<xi>: "I.wtE \<xi>" and
nv2T: "\<And> x. \<lbrakk>\<not> infTp (tpOfV x); x \<in> nv2T T\<rbrakk> \<Longrightarrow>
           \<exists> l. Ik.wtL l \<and> \<not> I.satL \<xi> l \<and> isGuard x l"
shows "Ik.int (transE \<xi>) T = I.int \<xi> T"
proof(cases "infTp (Ik.tpOf T) \<or> (\<forall> x \<in> nv2T T. tpOfV x \<noteq> Ik.tpOf T)")
  case True
  thus ?thesis using int_transE_nv2T[OF wt \<xi>] by auto
next
  define \<sigma> where "\<sigma> = Ik.tpOf T"
  case False then obtain x where i: "\<not> infTp \<sigma>" and x: "x \<in> nv2T T"
  unfolding \<sigma>_def by auto
  hence T: "T = Var x" by (simp add: in_nv2T)
  hence \<sigma>: "\<sigma> = tpOfV x" unfolding \<sigma>_def by simp
  obtain l where 0: "Ik.wtL l" "\<not> I.satL \<xi> l" "isGuard x l"
  using nv2T[OF i[unfolded \<sigma>] x] by auto
  show ?thesis unfolding T using isGuard_not_satL_intT[OF 0 \<xi>] by simp
qed

lemma intT_int_transE[simp]:
assumes wt: "Ik.wt T" and \<xi>: "I.wtE \<xi>" and
nv2T: "\<And> x. \<lbrakk>\<not> infTp (tpOfV x); x \<in> nv2T T\<rbrakk> \<Longrightarrow>
           \<exists> l. Ik.wtL l \<and> \<not> I.satL \<xi> l \<and> isGuard x l"
shows "Ik_intT (Ik.tpOf T) (I.int \<xi> T)"
proof-
  have 0: "I.int \<xi> T = Ik.int (transE \<xi>) T" using int_transE[OF assms] by simp
  show ?thesis unfolding 0 using Ik.wt_int[OF wtE_transE[OF \<xi>] wt] .
qed

lemma map_int_transE_nv2T[simp]:
assumes wt: "list_all Ik.wt Tl" and \<xi>: "I.wtE \<xi>" and
nv2T: "\<And> x. \<lbrakk>\<not> infTp (tpOfV x); \<exists>T\<in>set Tl. x \<in> nv2T T\<rbrakk> \<Longrightarrow>
           \<exists> l. Ik.wtL l \<and> \<not> I.satL \<xi> l \<and> isGuard x l"
shows "map (Ik.int (transE \<xi>)) Tl = map (I.int \<xi>) Tl"
apply(rule nth_equalityI) using assms by (force simp: list_all_iff intro: int_transE)+

lemma list_all2_intT_int_transE_nv2T[simp]:
assumes wt: "list_all Ik.wt Tl" and \<xi>: "I.wtE \<xi>" and
nv2T: "\<And> x. \<lbrakk>\<not> infTp (tpOfV x); \<exists>T\<in>set Tl. x \<in> nv2T T\<rbrakk> \<Longrightarrow>
           \<exists> l. Ik.wtL l \<and> \<not> I.satL \<xi> l \<and> isGuard x l"
shows "list_all2 Ik_intT (map Ik.tpOf Tl) (map (I.int \<xi>) Tl)"
unfolding list_all2_length using assms
unfolding list_all_iff apply simp_all by (metis intT_int_transE nth_mem)

lemma map_proj_transE[simp]:
assumes wt: "list_all wt Tl"
shows "map (Ik.int (transE \<xi>)) Tl =
       map2 proj (map tpOf Tl) (map (I.int \<xi>) Tl)"
apply(rule nth_equalityI) using assms
using int_transE_proj unfolding list_all_length by auto

lemma satL_transE[simp]:
assumes wtL: "Ik.wtL l" and \<xi>: "I.wtE \<xi>" and
nv2T:  "\<And> x. \<lbrakk>\<not> infTp (tpOfV x); x \<in> nv2L l\<rbrakk> \<Longrightarrow>
             \<exists> l'. Ik.wtL l' \<and> \<not> I.satL \<xi> l' \<and> isGuard x l'"
and "Ik.satL (transE \<xi>) l"
shows "I.satL \<xi> l"
proof(cases l)
  case (Pos at) show ?thesis proof (cases at)
    case (Pr p Tl) show ?thesis using assms unfolding Pos Pr
    apply(cases "polC p")
      apply force
      apply(cases "list_all2 intT (map Ik.tpOf Tl) (map (I.int \<xi>) Tl)", force, force)
      by simp
  qed(insert assms, unfold Pos, simp)
next
  case (Neg at) show ?thesis proof (cases at)
    case (Pr p Tl) show ?thesis using assms unfolding Neg Pr
    apply(cases "polC p")
      apply force apply force
      by (cases "list_all2 intT (map Ik.tpOf Tl) (map (I.int \<xi>) Tl)", force, force)
  qed(insert assms int_transE_proj, unfold Neg, auto)
qed

lemma satPB_transE[simp]:
assumes \<xi>: "I.wtE \<xi>"  shows "I.satPB \<xi> \<Phi>"
unfolding I.satPB_def proof safe
  fix c assume cin: "c \<in> \<Phi>"  let ?thesis = "I.satC \<xi> c"
  have mc: "\<And> \<sigma>. \<sigma> \<turnstile>2 c" using mcalc2[OF cin] .
  have c: "Ik.satC (transE \<xi>) c"
  using sat_\<Phi> wtE_transE[OF \<xi>] cin unfolding Ik.satPB_def by auto
  have wtC: "Ik.wtC c" using wt_\<Phi> cin unfolding wtPB_def by auto
  obtain l where lin: "l \<in> set c" and l: "Ik.satL (transE \<xi>) l"
  using c unfolding Ik.satC_iff_set by auto
  have wtL: "Ik.wtL l" using wtC unfolding wtC_def
  by (metis (lifting) lin list_all_iff)
  {assume "\<not> ?thesis"
   hence 0: "\<And> l'. l' \<in> set c \<Longrightarrow> \<not> I.satL \<xi> l'" unfolding I.satC_iff_set by auto
   have "I.satL \<xi> l"
   proof (rule satL_transE[OF wtL \<xi> _ l])
     fix x let ?\<sigma> = "tpOfV x"
     assume \<sigma>: "\<not> infTp ?\<sigma>" and x: "x \<in> nv2L l"
     hence g: "isGuard x (grdOf c l x)" using mc[of ?\<sigma>] lin unfolding mcalc2_iff by simp
     show "\<exists> l'. Ik.wtL l' \<and> \<not> I.satL \<xi> l' \<and> isGuard x l'"
     apply(rule exI[of _ "grdOf c l x"]) apply safe
     using g \<sigma> cin lin wtL_grdOf x 0 grdOf x by auto
   qed
   hence False using 0 lin by auto
   hence ?thesis by simp
  }
  thus ?thesis by auto
qed

lemma I_SAT: "I.SAT \<Phi>"
unfolding I.SAT_def by simp

lemma InfModel: "IInfModel I_intT I_intF I_intP"
  by standard (rule I_SAT)

end (* context ModelIkPolMcalc2C *)

sublocale ModelIkPolMcalc2C < inf?: InfModel where
intT = I_intT and intF = I_intF and intP = I_intP
using InfModel .

context ProblemIkPolMcalc2C begin

abbreviation
"MModelIkPolMcalc2C \<equiv> ModelIkPolMcalc2C wtFsym wtPsym arOf resOf parOf \<Phi> infTp pol grdOf"

theorem monot: monot
unfolding monot_def proof safe
  fix intT intF intP assume "MModel intT intF intP"
  hence M: "MModelIkPolMcalc2C intT intF intP"
  unfolding ModelIkPolMcalc2C_def ModelIk_def apply safe ..
  show "\<exists> intTI intFI intPI. IInfModel intTI intFI intPI"
  using ModelIkPolMcalc2C.InfModel[OF M] by auto
qed

end (* context ProblemIkPolMcalc2 *)

text\<open>Final theorem in sublocale form: Any problem that passes the
  monotonicity calculus is monotonic:\<close>
sublocale ProblemIkPolMcalc2C < MonotProblem
by standard (rule monot)

end
