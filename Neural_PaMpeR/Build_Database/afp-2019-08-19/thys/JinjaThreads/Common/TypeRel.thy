(*  Title:      JinjaThreads/Common/TypeRel.thy
    Author:     Tobias Nipkow, Andreas Lochbihler

    Based on the Jinja theory Common/Type.thy by Tobias Nipkow
*)

section \<open>Relations between Jinja Types\<close>

theory TypeRel
imports
  Decl
begin

subsection\<open>The subclass relations\<close>

inductive subcls1 :: "'m prog \<Rightarrow> cname \<Rightarrow> cname \<Rightarrow> bool" ("_ \<turnstile> _ \<prec>\<^sup>1 _" [71, 71, 71] 70)
  for P :: "'m prog"
where subcls1I: "\<lbrakk> class P C = Some (D, rest); C \<noteq> Object \<rbrakk> \<Longrightarrow> P \<turnstile> C \<prec>\<^sup>1 D"

abbreviation subcls :: "'m prog \<Rightarrow> cname \<Rightarrow> cname \<Rightarrow> bool" ("_ \<turnstile> _ \<preceq>\<^sup>* _"  [71,71,71] 70)
where "P \<turnstile> C \<preceq>\<^sup>* D \<equiv> (subcls1 P)\<^sup>*\<^sup>* C D"

lemma subcls1D:
  "P \<turnstile> C \<prec>\<^sup>1 D \<Longrightarrow> C \<noteq> Object \<and> (\<exists>fs ms. class P C = Some (D,fs,ms))"
by(auto elim: subcls1.cases)

lemma Object_subcls1 [iff]: "\<not> P \<turnstile> Object \<prec>\<^sup>1 C"
by(simp add: subcls1.simps)

lemma Object_subcls_conv [iff]: "(P \<turnstile> Object \<preceq>\<^sup>* C) = (C = Object)"
by(auto elim: converse_rtranclpE)

lemma finite_subcls1: "finite {(C, D). P \<turnstile> C \<prec>\<^sup>1 D}"
proof -
  let ?A = "SIGMA C:{C. is_class P C}. {D. C\<noteq>Object \<and> fst (the (class P C))=D}"
  have "finite ?A" by(rule finite_SigmaI [OF finite_is_class]) auto
  also have "?A = {(C, D). P \<turnstile> C \<prec>\<^sup>1 D}"
    by(fastforce simp:is_class_def dest: subcls1D elim: subcls1I)
  finally show ?thesis .
qed

lemma finite_subcls1':
  "finite ({(D, C). P \<turnstile> C \<prec>\<^sup>1 D})"
by(subst finite_converse[symmetric])
  (simp add: converse_unfold finite_subcls1 del: finite_converse)

lemma subcls_is_class: "(subcls1 P)\<^sup>+\<^sup>+ C D \<Longrightarrow> is_class P C"
by(auto elim: converse_tranclpE dest!: subcls1D simp add: is_class_def)

lemma subcls_is_class1: "\<lbrakk> P \<turnstile> C \<preceq>\<^sup>* D; is_class P D \<rbrakk> \<Longrightarrow> is_class P C"
by(auto elim: converse_rtranclpE dest!: subcls1D simp add: is_class_def)

subsection\<open>The subtype relations\<close>

inductive widen :: "'m prog \<Rightarrow> ty \<Rightarrow> ty \<Rightarrow> bool" ("_ \<turnstile> _ \<le> _"   [71,71,71] 70)
  for P :: "'m prog"
where 
  widen_refl[iff]: "P \<turnstile> T \<le> T"
| widen_subcls: "P \<turnstile> C \<preceq>\<^sup>* D  \<Longrightarrow>  P \<turnstile> Class C \<le> Class D"
| widen_null[iff]: "P \<turnstile> NT \<le> Class C"
| widen_null_array[iff]: "P \<turnstile> NT \<le> Array A"
| widen_array_object: "P \<turnstile> Array A \<le> Class Object"
| widen_array_array: "P \<turnstile> A \<le> B \<Longrightarrow> P \<turnstile> Array A \<le> Array B"

abbreviation
  widens :: "'m prog \<Rightarrow> ty list \<Rightarrow> ty list \<Rightarrow> bool" ("_ \<turnstile> _ [\<le>] _" [71,71,71] 70)
where
  "P \<turnstile> Ts [\<le>] Ts' == list_all2 (widen P) Ts Ts'"

lemma [iff]: "(P \<turnstile> T \<le> Void) = (T = Void)"
(*<*)by (auto elim: widen.cases)(*>*)

lemma [iff]: "(P \<turnstile> T \<le> Boolean) = (T = Boolean)"
(*<*)by (auto elim: widen.cases)(*>*)

lemma [iff]: "(P \<turnstile> T \<le> Integer) = (T = Integer)"
(*<*)by (auto elim: widen.cases)(*>*)

lemma [iff]: "(P \<turnstile> Void \<le> T) = (T = Void)"
(*<*)by (auto elim: widen.cases)(*>*)

lemma [iff]: "(P \<turnstile> Boolean \<le> T) = (T = Boolean)"
(*<*)by (auto elim: widen.cases)(*>*)

lemma [iff]: "(P \<turnstile> Integer \<le> T) = (T = Integer)"
(*<*)by (auto elim: widen.cases)(*>*)

lemma Class_widen: "P \<turnstile> Class C \<le> T  \<Longrightarrow>  \<exists>D. T = Class D"
by(erule widen.cases, auto)

lemma Array_Array_widen:
  "P \<turnstile> Array T \<le> Array U \<Longrightarrow> P \<turnstile> T \<le> U"
by(auto elim: widen.cases)

lemma widen_Array: "(P \<turnstile> T \<le> U\<lfloor>\<rceil>) \<longleftrightarrow> (T = NT \<or> (\<exists>V. T = V\<lfloor>\<rceil> \<and> P \<turnstile> V \<le> U))"
by(induct T)(auto dest: Array_Array_widen elim: widen.cases intro: widen_array_array)

lemma Array_widen: "P \<turnstile> Array A \<le> T \<Longrightarrow> (\<exists>B. T = Array B \<and> P \<turnstile> A \<le> B) \<or> T = Class Object"
by(auto elim: widen.cases)

lemma [iff]: "(P \<turnstile> T \<le> NT) = (T = NT)"
by(induct T)(auto dest:Class_widen Array_widen)

lemma Class_widen_Class [iff]: "(P \<turnstile> Class C \<le> Class D) = (P \<turnstile> C \<preceq>\<^sup>* D)"
by (auto elim: widen_subcls widen.cases)

lemma widen_Class: "(P \<turnstile> T \<le> Class C) = (T = NT \<or> (\<exists>D. T = Class D \<and> P \<turnstile> D \<preceq>\<^sup>* C) \<or> (C = Object \<and> (\<exists>A. T = Array A)))"
by(induct T)(auto dest: Array_widen intro: widen_array_object)

lemma NT_widen:
  "P \<turnstile> NT \<le> T = (T = NT \<or> (\<exists>C. T = Class C) \<or> (\<exists>U. T = U\<lfloor>\<rceil>))"
by(cases T) auto

lemma Class_widen2: "P \<turnstile> Class C \<le> T = (\<exists>D. T = Class D \<and> P \<turnstile> C \<preceq>\<^sup>* D)"
by (cases T, auto elim: widen.cases)

lemma Object_widen: "P \<turnstile> Class Object \<le> T \<Longrightarrow> T = Class Object"
by(cases T, auto elim: widen.cases)

lemma NT_Array_widen_Object:
  "is_NT_Array T \<Longrightarrow>  P \<turnstile> T \<le> Class Object"
by(induct T, auto intro: widen_array_object)

lemma widen_trans[trans]: 
  assumes "P \<turnstile> S \<le> U" "P \<turnstile> U \<le> T"
  shows "P \<turnstile> S \<le> T"
using assms
proof(induct arbitrary: T)
  case (widen_refl T T') thus "P \<turnstile> T \<le> T'" .
next
  case (widen_subcls C D T)
  then obtain E where "T = Class E" by (blast dest: Class_widen)
  with widen_subcls show "P \<turnstile> Class C \<le> T" by (auto elim: rtrancl_trans)
next
  case (widen_null C RT)
  then obtain D where "RT = Class D" by (blast dest: Class_widen)
  thus "P \<turnstile> NT \<le> RT" by auto
next
  case widen_null_array thus ?case by(auto dest: Array_widen)
next
  case (widen_array_object A T)
  hence "T = Class Object" by(rule Object_widen)
  with widen_array_object show "P \<turnstile> A\<lfloor>\<rceil> \<le> T"
    by(auto intro: widen.widen_array_object)
next
  case widen_array_array thus ?case
    by(auto dest!: Array_widen intro: widen.widen_array_array widen_array_object)
qed

lemma widens_trans: "\<lbrakk>P \<turnstile> Ss [\<le>] Ts; P \<turnstile> Ts [\<le>] Us\<rbrakk> \<Longrightarrow> P \<turnstile> Ss [\<le>] Us"
by (rule list_all2_trans)(rule widen_trans)

lemma class_type_of'_widenD:
  "class_type_of' T = \<lfloor>C\<rfloor> \<Longrightarrow> P \<turnstile> T \<le> Class C"
by(cases T)(auto intro: widen_array_object)

lemma widen_is_class_type_of:
  assumes "class_type_of' T = \<lfloor>C\<rfloor>" "P \<turnstile> T' \<le> T" "T' \<noteq> NT"
  obtains C' where "class_type_of' T' = \<lfloor>C'\<rfloor>" "P \<turnstile> C' \<preceq>\<^sup>* C"
using assms by(cases T)(auto simp add: widen_Class widen_Array)

lemma widens_refl: "P \<turnstile> Ts [\<le>] Ts"
by(rule list_all2_refl[OF widen_refl])

lemma widen_append1:
  "P \<turnstile> (xs @ ys) [\<le>] Ts = (\<exists>Ts1 Ts2. Ts = Ts1 @ Ts2 \<and> length xs = length Ts1 \<and> length ys = length Ts2 \<and> P \<turnstile> xs [\<le>] Ts1 \<and> P \<turnstile> ys [\<le>] Ts2)"
unfolding list_all2_append1 by fastforce

lemmas widens_Cons [iff] = list_all2_Cons1 [of "widen P"] for P

lemma widens_lengthD:
  "P \<turnstile> xs [\<le>] ys \<Longrightarrow> length xs = length ys"
by(rule list_all2_lengthD)

lemma widen_refT: "\<lbrakk> is_refT T; P \<turnstile> U \<le> T \<rbrakk> \<Longrightarrow> is_refT U"
by(erule refTE)(auto simp add: widen_Class widen_Array)

lemma refT_widen: "\<lbrakk> is_refT T; P \<turnstile> T \<le> U \<rbrakk> \<Longrightarrow> is_refT U"
by(erule widen.cases) auto

inductive is_lub :: "'m prog \<Rightarrow> ty \<Rightarrow> ty \<Rightarrow> ty \<Rightarrow> bool" ("_ \<turnstile> lub'((_,/ _)') = _" [51,51,51,51] 50)
for P :: "'m prog" and U :: ty and V :: ty and T ::  ty
where 
  "\<lbrakk> P \<turnstile> U \<le> T; P \<turnstile> V \<le> T;
     \<And>T'. \<lbrakk> P \<turnstile> U \<le> T'; P \<turnstile> V \<le> T' \<rbrakk> \<Longrightarrow> P \<turnstile> T \<le> T' \<rbrakk>
  \<Longrightarrow> P \<turnstile> lub(U, V) = T"

lemma is_lub_upper:
  "P \<turnstile> lub(U, V) = T \<Longrightarrow> P \<turnstile> U \<le> T \<and> P \<turnstile> V \<le> T"
by(auto elim: is_lub.cases)

lemma is_lub_least:
  "\<lbrakk> P \<turnstile> lub(U, V) = T; P \<turnstile> U \<le> T'; P \<turnstile> V \<le> T' \<rbrakk> \<Longrightarrow> P \<turnstile> T \<le> T'"
by(auto elim: is_lub.cases)

lemma is_lub_Void [iff]:
  "P \<turnstile> lub(Void, Void) = T \<longleftrightarrow> T = Void"
by(auto intro: is_lub.intros elim: is_lub.cases)

lemma is_lubI [code_pred_intro]:
  "\<lbrakk>P \<turnstile> U \<le> T; P \<turnstile> V \<le> T; \<forall>T'. P \<turnstile> U \<le> T' \<longrightarrow> P \<turnstile> V \<le> T' \<longrightarrow> P \<turnstile> T \<le> T'\<rbrakk> \<Longrightarrow> P \<turnstile> lub(U, V) = T"
by(blast intro: is_lub.intros)

subsection\<open>Method lookup\<close>

inductive Methods :: "'m prog \<Rightarrow> cname \<Rightarrow> (mname \<rightharpoonup> (ty list \<times> ty \<times> 'm option) \<times> cname) \<Rightarrow> bool" 
  ("_ \<turnstile> _ sees'_methods _" [51,51,51] 50)
  for P :: "'m prog"
where 
sees_methods_Object:
 "\<lbrakk> class P Object = Some(D,fs,ms); Mm = map_option (\<lambda>m. (m,Object)) \<circ> map_of ms \<rbrakk>
  \<Longrightarrow> P \<turnstile> Object sees_methods Mm"
| sees_methods_rec:
 "\<lbrakk> class P C = Some(D,fs,ms); C \<noteq> Object; P \<turnstile> D sees_methods Mm;
    Mm' = Mm ++ (map_option (\<lambda>m. (m,C)) \<circ> map_of ms) \<rbrakk>
  \<Longrightarrow> P \<turnstile> C sees_methods Mm'"

lemma sees_methods_fun:
  assumes "P \<turnstile> C sees_methods Mm"
  shows "P \<turnstile> C sees_methods Mm' \<Longrightarrow> Mm' = Mm"
using assms
proof(induction arbitrary: Mm')
  case sees_methods_Object thus ?case by(auto elim: Methods.cases)
next
  case (sees_methods_rec C D fs ms Dres Cres Cres')
  from \<open>P \<turnstile> C sees_methods Cres'\<close> \<open>C \<noteq> Object\<close> \<open>class P C = \<lfloor>(D, fs, ms)\<rfloor>\<close>
  obtain Dres' where Dmethods': "P \<turnstile> D sees_methods Dres'"
    and Cres': "Cres' = Dres' ++ (map_option (\<lambda>m. (m,C)) \<circ> map_of ms)"
    by cases auto
  from sees_methods_rec.IH[OF Dmethods'] \<open>Cres = Dres ++ (map_option (\<lambda>m. (m,C)) \<circ> map_of ms)\<close> Cres'
  show ?case by simp
qed

lemma visible_methods_exist:
  "P \<turnstile> C sees_methods Mm \<Longrightarrow> Mm M = Some(m,D) \<Longrightarrow>
   (\<exists>D' fs ms. class P D = Some(D',fs,ms) \<and> map_of ms M = Some m)"
by(induct rule:Methods.induct) auto

lemma sees_methods_decl_above:
  assumes "P \<turnstile> C sees_methods Mm"
  shows "Mm M = Some(m,D) \<Longrightarrow> P \<turnstile> C \<preceq>\<^sup>* D"
using assms
by induct(auto elim: converse_rtranclp_into_rtranclp[where r = "subcls1 P", OF subcls1I])

lemma sees_methods_idemp:
  assumes "P \<turnstile> C sees_methods Mm" and "Mm M = Some(m,D)"
  shows "\<exists>Mm'. (P \<turnstile> D sees_methods Mm') \<and> Mm' M = Some(m,D)"
using assms
by(induct arbitrary: m D)(fastforce dest: Methods.intros)+

lemma sees_methods_decl_mono:
  assumes sub: "P \<turnstile> C' \<preceq>\<^sup>* C" and "P \<turnstile> C sees_methods Mm"
  shows "\<exists>Mm' Mm\<^sub>2. P \<turnstile> C' sees_methods Mm' \<and> Mm' = Mm ++ Mm\<^sub>2 \<and> (\<forall>M m D. Mm\<^sub>2 M = Some(m,D) \<longrightarrow> P \<turnstile> D \<preceq>\<^sup>* C)"
      (is "\<exists>Mm' Mm2. ?Q C' C Mm' Mm2")
using assms
proof (induction rule: converse_rtranclp_induct)
  case base
  hence "?Q C C Mm Map.empty" by simp
  thus "\<exists>Mm' Mm2. ?Q C C Mm' Mm2" by blast
next
  case (step C'' C')
  note sub1 = \<open>P \<turnstile> C'' \<prec>\<^sup>1 C'\<close> and sub = \<open>P \<turnstile> C' \<preceq>\<^sup>* C\<close>
    and Csees = \<open>P \<turnstile> C sees_methods Mm\<close>
  from step.IH[OF Csees] obtain Mm' Mm2 where C'sees: "P \<turnstile> C' sees_methods Mm'"
    and Mm': "Mm' = Mm ++ Mm2"
    and subC: "\<forall>M m D. Mm2 M = Some(m,D) \<longrightarrow> P \<turnstile> D \<preceq>\<^sup>* C" by blast
  obtain fs ms where "class": "class P C'' = Some(C',fs,ms)" "C'' \<noteq> Object"
    using subcls1D[OF sub1] by blast
  let ?Mm3 = "map_option (\<lambda>m. (m,C'')) \<circ> map_of ms"
  have "P \<turnstile> C'' sees_methods (Mm ++ Mm2) ++ ?Mm3"
    using sees_methods_rec[OF "class" C'sees refl] Mm' by simp
  hence "?Q C'' C ((Mm ++ Mm2) ++ ?Mm3) (Mm2++?Mm3)"
    using converse_rtranclp_into_rtranclp[OF sub1 sub]
    by simp (simp add:map_add_def subC split:option.split)
  thus "\<exists>Mm' Mm2. ?Q C'' C Mm' Mm2" by blast
qed

definition Method :: "'m prog \<Rightarrow> cname \<Rightarrow> mname \<Rightarrow> ty list \<Rightarrow> ty \<Rightarrow> 'm option \<Rightarrow> cname \<Rightarrow> bool"
            ("_ \<turnstile> _ sees _: _\<rightarrow>_ = _ in _" [51,51,51,51,51,51,51] 50)
where
  "P \<turnstile> C sees M: Ts\<rightarrow>T = m in D  \<equiv>
  \<exists>Mm. P \<turnstile> C sees_methods Mm \<and> Mm M = Some((Ts,T,m),D)"

text \<open>
  Output translation to replace @{term "None"} with its notation \<open>Native\<close>
  when used as method body in @{term "Method"}.
\<close>
abbreviation (output)
  Method_native :: "'m prog \<Rightarrow> cname \<Rightarrow> mname \<Rightarrow> ty list \<Rightarrow> ty \<Rightarrow> cname \<Rightarrow> bool"
  ("_ \<turnstile> _ sees _: _\<rightarrow>_ = Native in _" [51,51,51,51,51,51] 50)
where "Method_native P C M Ts T D \<equiv> Method P C M Ts T Native D"

definition has_method :: "'m prog \<Rightarrow> cname \<Rightarrow> mname \<Rightarrow> bool" ("_ \<turnstile> _ has _" [51,0,51] 50)
where
  "P \<turnstile> C has M \<equiv> \<exists>Ts T m D. P \<turnstile> C sees M:Ts\<rightarrow>T = m in D"

lemma has_methodI:
  "P \<turnstile> C sees M:Ts\<rightarrow>T = m in D \<Longrightarrow> P \<turnstile> C has M"
  by (unfold has_method_def) blast

lemma sees_method_fun:
  "\<lbrakk>P \<turnstile> C sees M:TS\<rightarrow>T = m in D; P \<turnstile> C sees M:TS'\<rightarrow>T' = m' in D' \<rbrakk>
   \<Longrightarrow> TS' = TS \<and> T' = T \<and> m' = m \<and> D' = D"
 (*<*)by(fastforce dest: sees_methods_fun simp:Method_def)(*>*)

lemma sees_method_decl_above:
  "P \<turnstile> C sees M:Ts\<rightarrow>T = m in D \<Longrightarrow> P \<turnstile> C \<preceq>\<^sup>* D"
 (*<*)by(clarsimp simp:Method_def sees_methods_decl_above)(*>*)

lemma visible_method_exists:
  "P \<turnstile> C sees M:Ts\<rightarrow>T = m in D \<Longrightarrow>
  \<exists>D' fs ms. class P D = Some(D',fs,ms) \<and> map_of ms M = Some(Ts,T,m)"
(*<*)by(fastforce simp:Method_def dest!: visible_methods_exist)(*>*)


lemma sees_method_idemp:
  "P \<turnstile> C sees M:Ts\<rightarrow>T=m in D \<Longrightarrow> P \<turnstile> D sees M:Ts\<rightarrow>T=m in D"
 (*<*)by(fastforce simp: Method_def intro:sees_methods_idemp)(*>*)

lemma sees_method_decl_mono:
  "\<lbrakk> P \<turnstile> C' \<preceq>\<^sup>* C; P \<turnstile> C sees M:Ts\<rightarrow>T = m in D;
     P \<turnstile> C' sees M:Ts'\<rightarrow>T' = m' in D' \<rbrakk> \<Longrightarrow> P \<turnstile> D' \<preceq>\<^sup>* D"
apply(frule sees_method_decl_above)
apply(unfold Method_def)
apply clarsimp
apply(drule (1) sees_methods_decl_mono)
apply clarsimp
apply(drule (1) sees_methods_fun)
apply clarsimp
apply(blast intro:rtranclp_trans)
done

lemma sees_method_is_class:
  "P \<turnstile> C sees M:Ts\<rightarrow>T = m in D \<Longrightarrow> is_class P C"
by (auto simp add: is_class_def Method_def elim: Methods.cases)

subsection\<open>Field lookup\<close>

inductive Fields :: "'m prog \<Rightarrow> cname \<Rightarrow> ((vname \<times> cname) \<times> (ty \<times> fmod)) list \<Rightarrow> bool"
  ("_ \<turnstile> _ has'_fields _" [51,51,51] 50)
  for P :: "'m prog"
where 
  has_fields_rec:
  "\<lbrakk> class P C = Some(D,fs,ms); C \<noteq> Object; P \<turnstile> D has_fields FDTs;
     FDTs' = map (\<lambda>(F,Tm). ((F,C),Tm)) fs @ FDTs \<rbrakk>
   \<Longrightarrow> P \<turnstile> C has_fields FDTs'"

| has_fields_Object:
  "\<lbrakk> class P Object = Some(D,fs,ms); FDTs = map (\<lambda>(F,T). ((F,Object),T)) fs \<rbrakk>
   \<Longrightarrow> P \<turnstile> Object has_fields FDTs"

lemma has_fields_fun:
  assumes "P \<turnstile> C has_fields FDTs" and "P \<turnstile> C has_fields FDTs'"
  shows "FDTs' = FDTs"
using assms
proof(induction arbitrary: FDTs')
  case has_fields_Object thus ?case by(auto elim: Fields.cases)
next
  case (has_fields_rec C D fs ms Dres Cres Cres')
  from \<open>P \<turnstile> C has_fields Cres'\<close> \<open>C \<noteq> Object\<close> \<open>class P C = Some (D, fs, ms)\<close>
  obtain Dres' where DFields': "P \<turnstile> D has_fields Dres'"
    and Cres': "Cres' = map (\<lambda>(F,Tm). ((F,C),Tm)) fs @ Dres'"
    by cases auto
  from has_fields_rec.IH[OF DFields'] \<open>Cres = map (\<lambda>(F,Tm). ((F,C),Tm)) fs @ Dres\<close> Cres'
  show ?case by simp
qed

lemma all_fields_in_has_fields:
  assumes "P \<turnstile> C has_fields FDTs"
  and "P \<turnstile> C \<preceq>\<^sup>* D" "class P D = Some(D',fs,ms)" "(F,Tm) \<in> set fs"
  shows "((F,D),Tm) \<in> set FDTs"
using assms
by induct (auto 4 3 elim: converse_rtranclpE dest: subcls1D)

lemma has_fields_decl_above:
  assumes "P \<turnstile> C has_fields FDTs" "((F,D),Tm) \<in> set FDTs"
  shows "P \<turnstile> C \<preceq>\<^sup>* D"
using assms
by induct (auto intro: converse_rtranclp_into_rtranclp subcls1I)

lemma subcls_notin_has_fields:
  assumes "P \<turnstile> C has_fields FDTs" "((F,D),Tm) \<in> set FDTs"
  shows "\<not> (subcls1 P)\<^sup>+\<^sup>+ D C"
using assms apply(induct)
 prefer 2 apply(fastforce dest: tranclpD)
apply clarsimp
apply(erule disjE)
 apply(clarsimp simp add:image_def)
 apply(drule tranclpD)
 apply clarify
 apply(frule subcls1D)
 apply(fastforce dest:tranclpD all_fields_in_has_fields)
apply(blast dest:subcls1I tranclp.trancl_into_trancl)
done

lemma has_fields_mono_lem:
  assumes "P \<turnstile> D \<preceq>\<^sup>* C" "P \<turnstile> C has_fields FDTs"
  shows "\<exists>pre. P \<turnstile> D has_fields pre@FDTs \<and> dom(map_of pre) \<inter> dom(map_of FDTs) = {}"
using assms
apply(induct rule:converse_rtranclp_induct)
 apply(rule_tac x = "[]" in exI)
 apply simp
apply clarsimp
apply(rename_tac D' D pre)
apply(subgoal_tac "(subcls1 P)^++ D' C")
 prefer 2 apply(erule (1) rtranclp_into_tranclp2)
apply(drule subcls1D)
apply clarsimp
apply(rename_tac fs ms)
apply(drule (2) has_fields_rec)
 apply(rule refl)
apply(rule_tac x = "map (\<lambda>(F,Tm). ((F,D'),Tm)) fs @ pre" in exI)
apply simp
apply(simp add:Int_Un_distrib2)
apply(rule equals0I)
apply(auto dest: subcls_notin_has_fields simp:dom_map_of_conv_image_fst image_def)
done

lemma has_fields_is_class:
  "P \<turnstile> C has_fields FDTs \<Longrightarrow> is_class P C"
by (auto simp add: is_class_def elim: Fields.cases)

lemma Object_has_fields_Object:
  assumes "P \<turnstile> Object has_fields FDTs"
  shows "snd ` fst ` set FDTs \<subseteq> {Object}"
using assms by cases auto

definition
  has_field :: "'m prog \<Rightarrow> cname \<Rightarrow> vname \<Rightarrow> ty \<Rightarrow> fmod \<Rightarrow> cname \<Rightarrow> bool"
                   ("_ \<turnstile> _ has _:_ '(_') in _" [51,51,51,51,51,51] 50)
where
  "P \<turnstile> C has F:T (fm) in D  \<equiv>
  \<exists>FDTs. P \<turnstile> C has_fields FDTs \<and> map_of FDTs (F,D) = Some (T, fm)"

lemma has_field_mono:
  "\<lbrakk> P \<turnstile> C has F:T (fm) in D; P \<turnstile> C' \<preceq>\<^sup>* C \<rbrakk> \<Longrightarrow> P \<turnstile> C' has F:T (fm) in D"
by(fastforce simp:has_field_def map_add_def dest: has_fields_mono_lem)

lemma has_field_is_class:
  "P \<turnstile> C has M:T (fm) in D \<Longrightarrow> is_class P C"
by (auto simp add: is_class_def has_field_def elim: Fields.cases)

lemma has_field_decl_above:
  "P \<turnstile> C has F:T (fm) in D \<Longrightarrow> P \<turnstile> C \<preceq>\<^sup>* D"
unfolding has_field_def
by(auto dest: map_of_SomeD has_fields_decl_above)

lemma has_field_fun:
  "\<lbrakk>P \<turnstile> C has F:T (fm) in D; P \<turnstile> C has F:T' (fm') in D\<rbrakk> \<Longrightarrow> T' = T \<and> fm = fm'"
by(auto simp:has_field_def dest:has_fields_fun)

definition
  sees_field :: "'m prog \<Rightarrow> cname \<Rightarrow> vname \<Rightarrow> ty \<Rightarrow> fmod \<Rightarrow> cname \<Rightarrow> bool"
                  ("_ \<turnstile> _ sees _:_ '(_') in _" [51,51,51,51,51,51] 50)
where
  "P \<turnstile> C sees F:T (fm) in D  \<equiv>
  \<exists>FDTs. P \<turnstile> C has_fields FDTs \<and>
            map_of (map (\<lambda>((F,D),Tm). (F,(D,Tm))) FDTs) F = Some(D,T,fm)"

lemma map_of_remap_SomeD:
  "map_of (map (\<lambda>((k,k'),x). (k,(k',x))) t) k = Some (k',x) \<Longrightarrow> map_of t (k, k') = Some x"
by (induct t) (auto simp:fun_upd_apply split: if_split_asm)

lemma has_visible_field:
  "P \<turnstile> C sees F:T (fm) in D \<Longrightarrow> P \<turnstile> C has F:T (fm) in D"
by(auto simp add:has_field_def sees_field_def map_of_remap_SomeD)

lemma sees_field_fun:
  "\<lbrakk>P \<turnstile> C sees F:T (fm) in D; P \<turnstile> C sees F:T' (fm') in D'\<rbrakk> \<Longrightarrow> T' = T \<and> D' = D \<and> fm = fm'"
by(fastforce simp:sees_field_def dest:has_fields_fun)


lemma sees_field_decl_above:
  "P \<turnstile> C sees F:T (fm) in D \<Longrightarrow> P \<turnstile> C \<preceq>\<^sup>* D"
by(clarsimp simp add: sees_field_def)
  (blast intro: has_fields_decl_above map_of_SomeD map_of_remap_SomeD)

lemma sees_field_idemp:
  assumes "P \<turnstile> C sees F:T (fm) in D"
  shows "P \<turnstile> D sees F:T (fm) in D"
proof -
  from assms obtain FDTs where has: "P \<turnstile> C has_fields FDTs"
    and F: "map_of (map (\<lambda>((F, D), Tm). (F, D, Tm)) FDTs) F = \<lfloor>(D, T, fm)\<rfloor>"
    unfolding sees_field_def by blast
  thus ?thesis
  proof induct
    case has_fields_rec thus ?case unfolding sees_field_def
      by(auto)(fastforce dest: map_of_SomeD intro!: exI intro: Fields.has_fields_rec)
  next
    case has_fields_Object thus ?case unfolding sees_field_def
      by(fastforce dest: map_of_SomeD intro: Fields.has_fields_Object intro!: exI)
  qed
qed

subsection "Functional lookup"

definition "method" :: "'m prog \<Rightarrow> cname \<Rightarrow> mname \<Rightarrow> cname \<times> ty list \<times> ty \<times> 'm option"
where "method P C M  \<equiv>  THE (D,Ts,T,m). P \<turnstile> C sees M:Ts \<rightarrow> T = m in D"

definition field  :: "'m prog \<Rightarrow> cname \<Rightarrow> vname \<Rightarrow> cname \<times> ty \<times> fmod"
where "field P C F  \<equiv>  THE (D,T,fm). P \<turnstile> C sees F:T (fm) in D"
                                                        
definition fields :: "'m prog \<Rightarrow> cname \<Rightarrow> ((vname \<times> cname) \<times> (ty \<times> fmod)) list" 
where "fields P C  \<equiv>  THE FDTs. P \<turnstile> C has_fields FDTs"                

lemma [simp]: "P \<turnstile> C has_fields FDTs \<Longrightarrow> fields P C = FDTs"
(*<*)by (unfold fields_def) (auto dest: has_fields_fun)(*>*)

lemma field_def2 [simp]: "P \<turnstile> C sees F:T (fm) in D \<Longrightarrow> field P C F = (D,T,fm)"
(*<*)by (unfold field_def) (auto dest: sees_field_fun)(*>*)

lemma method_def2 [simp]: "P \<turnstile> C sees M: Ts\<rightarrow>T = m in D \<Longrightarrow> method P C M = (D,Ts,T,m)"
(*<*)by (unfold method_def) (auto dest: sees_method_fun)(*>*)

lemma has_fields_b_fields: 
  "P \<turnstile> C has_fields FDTs \<Longrightarrow> fields P C = FDTs"
unfolding fields_def
by (blast intro: the_equality has_fields_fun)

lemma has_field_map_of_fields [simp]:
  "P \<turnstile> C has F:T (fm) in D \<Longrightarrow> map_of (fields P C) (F, D) = \<lfloor>(T, fm)\<rfloor>"
by(auto simp add: has_field_def)

subsection \<open>Code generation\<close>

text \<open>New introduction rules for subcls1\<close>

code_pred
  \<comment> \<open>Disallow mode @{text "i_o_o"} to force @{text code_pred} in subsequent predicates not to use this inefficient mode\<close>
  (modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool, i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool) 
  subcls1
.

text \<open>
  Introduce proper constant \<open>subcls'\<close> for @{term "subcls"}
  and generate executable equation for \<open>subcls'\<close> 
\<close>

definition subcls' where "subcls' = subcls"

code_pred
  (modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool, i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool)
  [inductify]
  subcls'
.

lemma subcls_conv_subcls' [code_unfold]:
  "(subcls1 P)^** = subcls' P"
by(simp add: subcls'_def)

text \<open>
  Change rule @{thm widen_array_object} such that predicate compiler
  tests on class @{term Object} first. Otherwise \<open>widen_i_o_i\<close> never terminates.
\<close>

lemma widen_array_object_code:
  "C = Object \<Longrightarrow> P \<turnstile> Array A \<le> Class C"
by(auto intro: widen.intros)

lemmas [code_pred_intro] =
  widen_refl widen_subcls widen_null widen_null_array widen_array_object_code widen_array_array
code_pred 
  (modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool)
  widen 
by(erule widen.cases) auto

text \<open>
  Readjust the code equations for @{term widen} such that @{term widen_i_i_i} is guaranteed to
  contain @{term "()"} at most once (even in the code representation!). This is important
  for the scheduler and the small-step semantics because of the weaker code equations
  for @{term "the"}.

  A similar problem cannot hit the subclass relation because, for acyclic subclass hierarchies, 
  the paths in the hieararchy are unique and cycle-free.
\<close>

definition widen_i_i_i' where "widen_i_i_i' = widen_i_i_i"

declare widen.equation [code del]
lemmas widen_i_i_i'_equation [code] = widen.equation[folded widen_i_i_i'_def]

lemma widen_i_i_i_code [code]:
  "widen_i_i_i P T T' = (if P \<turnstile> T \<le> T' then Predicate.single () else bot)"
by(auto intro!: pred_eqI intro: widen_i_i_iI elim: widen_i_i_iE)

code_pred 
  (modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool, i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool)
  Methods 
.

code_pred 
  (modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> o \<Rightarrow> o \<Rightarrow> bool, i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> o \<Rightarrow> i \<Rightarrow> bool)
  [inductify]
  Method
.

code_pred 
  (modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool)
  [inductify]
  has_method 
.

(* FIXME: Necessary only because of bug in code_pred *)
declare fun_upd_def [code_pred_inline]

code_pred 
  (modes: i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool)
  Fields 
.

code_pred
  (modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> i \<Rightarrow> bool)
  [inductify, skip_proof]
  has_field
.

code_pred
  (modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> o \<Rightarrow> bool, i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> i \<Rightarrow> bool)
  [inductify, skip_proof]
  sees_field
.

lemma eval_Method_i_i_i_o_o_o_o_conv:
  "Predicate.eval (Method_i_i_i_o_o_o_o P C M) = (\<lambda>(Ts, T, m, D). P \<turnstile> C sees M:Ts\<rightarrow>T=m in D)"
by(auto intro: Method_i_i_i_o_o_o_oI elim: Method_i_i_i_o_o_o_oE intro!: ext)

lemma method_code [code]:
  "method P C M = 
  Predicate.the (Predicate.bind (Method_i_i_i_o_o_o_o P C M) (\<lambda>(Ts, T, m, D). Predicate.single (D, Ts, T, m)))"
apply (rule sym, rule the_eqI)
apply (simp add: method_def eval_Method_i_i_i_o_o_o_o_conv)
apply (rule arg_cong [where f=The])
apply (auto simp add: Sup_fun_def Sup_bool_def fun_eq_iff)
done

lemma eval_sees_field_i_i_i_o_o_o_conv:
  "Predicate.eval (sees_field_i_i_i_o_o_o P C F) = (\<lambda>(T, fm, D). P \<turnstile> C sees F:T (fm) in D)"
by(auto intro!: ext intro: sees_field_i_i_i_o_o_oI elim: sees_field_i_i_i_o_o_oE)

lemma eval_sees_field_i_i_i_o_i_conv:
  "Predicate.eval (sees_field_i_i_i_o_o_i P C F D) = (\<lambda>(T, fm). P \<turnstile> C sees F:T (fm) in D)"
by(auto intro!: ext intro: sees_field_i_i_i_o_o_iI elim: sees_field_i_i_i_o_o_iE)

lemma field_code [code]:
  "field P C F = Predicate.the (Predicate.bind (sees_field_i_i_i_o_o_o P C F) (\<lambda>(T, fm, D). Predicate.single (D, T, fm)))"
apply (rule sym, rule the_eqI)
apply (simp add: field_def eval_sees_field_i_i_i_o_o_o_conv)
apply (rule arg_cong [where f=The])
apply (auto simp add: Sup_fun_def Sup_bool_def fun_eq_iff)
done

lemma eval_Fields_conv:
  "Predicate.eval (Fields_i_i_o P C) = (\<lambda>FDTs. P \<turnstile> C has_fields FDTs)"
by(auto intro: Fields_i_i_oI elim: Fields_i_i_oE intro!: ext)

lemma fields_code [code]:
  "fields P C = Predicate.the (Fields_i_i_o P C)"
by(simp add: fields_def Predicate.the_def eval_Fields_conv)

code_identifier
  code_module TypeRel \<rightharpoonup>
    (SML) TypeRel and (Haskell) TypeRel and (OCaml) TypeRel
| code_module Decl \<rightharpoonup>
    (SML) TypeRel and (Haskell) TypeRel and (OCaml) TypeRel

end
