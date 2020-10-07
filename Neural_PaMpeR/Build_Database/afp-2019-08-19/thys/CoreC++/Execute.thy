(*  Title:       CoreC++
    Author:      Daniel Wasserrab, Stefan Berghofer
    Maintainer:  Daniel Wasserrab <wasserra at fmi.uni-passau.de>
*)

section \<open>Code generation for Semantics and Type System\<close>

theory Execute
imports BigStep WellType
  "HOL-Library.AList_Mapping"
  "HOL-Library.Code_Target_Numeral"
begin

subsection\<open>General redefinitions\<close>

inductive app :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> bool"
where
  "app [] ys ys"
| "app xs ys zs \<Longrightarrow> app (x # xs) ys (x # zs)"

theorem app_eq1: "\<And>ys zs. zs = xs @ ys \<Longrightarrow> app xs ys zs"
  apply (induct xs)
   apply simp
   apply (rule app.intros)
  apply simp
  apply (iprover intro: app.intros)
  done

theorem app_eq2: "app xs ys zs \<Longrightarrow> zs = xs @ ys"
  by (erule app.induct) simp_all

theorem app_eq: "app xs ys zs = (zs = xs @ ys)"
  apply (rule iffI)
   apply (erule app_eq2)
  apply (erule app_eq1)
  done

code_pred
  (modes:
    i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool, i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool, i \<Rightarrow> o \<Rightarrow> i \<Rightarrow> bool,
    o \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool, o \<Rightarrow> o \<Rightarrow> i \<Rightarrow> bool as reverse_app)
  app
.

declare rtranclp_rtrancl_eq[code del]

lemmas [code_pred_intro] = rtranclp.rtrancl_refl converse_rtranclp_into_rtranclp

code_pred 
  (modes: 
   (i => o => bool) => i => i => bool,
   (i => o => bool) => i => o => bool)
  rtranclp
by(erule converse_rtranclpE) blast+

definition Set_project :: "('a \<times> 'b) set => 'a => 'b set"
where "Set_project A a = {b. (a, b) \<in> A}"

lemma Set_project_set [code]:
  "Set_project (set xs) a = set (List.map_filter (\<lambda>(a', b). if a = a' then Some b else None) xs)"
by(auto simp add: Set_project_def map_filter_def intro: rev_image_eqI split: if_split_asm)


text\<open>Redefine map Val vs\<close>

inductive map_val :: "expr list \<Rightarrow> val list \<Rightarrow> bool"
where
  Nil: "map_val [] []"
| Cons: "map_val xs ys \<Longrightarrow> map_val (Val y # xs) (y # ys)"

code_pred 
  (modes: i \<Rightarrow> i \<Rightarrow> bool, i \<Rightarrow> o \<Rightarrow> bool)
  map_val
.

inductive map_val2 :: "expr list \<Rightarrow> val list \<Rightarrow> expr list \<Rightarrow> bool"
where
  Nil: "map_val2 [] [] []"
| Cons: "map_val2 xs ys zs \<Longrightarrow> map_val2 (Val y # xs) (y # ys) zs"
| Throw: "map_val2 (throw e # xs) [] (throw e # xs)"

code_pred
  (modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool, i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> bool)
  map_val2
.

theorem map_val_conv: "(xs = map Val ys) = map_val xs ys"
(*<*)
proof -
  have "\<And>ys. xs = map Val ys \<Longrightarrow> map_val xs ys"
    apply (induct xs type:list)
     apply (case_tac ys)
      apply simp
      apply (rule map_val.Nil)
     apply simp
    apply (case_tac ys)
     apply simp
    apply simp
    apply (erule conjE)
    apply (rule map_val.Cons)
    apply simp
    done
  moreover have "map_val xs ys \<Longrightarrow> xs = map Val ys"
    by (erule map_val.induct) simp+
  ultimately show ?thesis ..
qed
(*>*)

theorem map_val2_conv:
 "(xs = map Val ys @ throw e # zs) = map_val2 xs ys (throw e # zs)"
(*<*)
proof -
  have "\<And>ys. xs = map Val ys @ throw e # zs \<Longrightarrow> map_val2 xs ys (throw e # zs)"
    apply (induct xs type:list)
     apply (case_tac ys)
      apply simp
     apply simp
    apply simp
    apply (case_tac ys)
     apply simp
     apply (rule map_val2.Throw)
    apply simp
    apply (rule map_val2.Cons)
    apply simp
    done
  moreover have "map_val2 xs ys (throw e # zs) \<Longrightarrow> xs = map Val ys @ throw e # zs"
    by (erule map_val2.induct) simp+
  ultimately show ?thesis ..
qed
(*>*)


subsection\<open>Code generation\<close>

lemma subclsRp_code [code_pred_intro]:
  "\<lbrakk> class P C = \<lfloor>(Bs, rest)\<rfloor>; Predicate_Compile.contains (set Bs) (Repeats D) \<rbrakk> \<Longrightarrow> subclsRp P C D"
by(auto intro: subclsRp.intros simp add: contains_def)

code_pred
  (modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool, i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool)
  subclsRp
by(erule subclsRp.cases)(fastforce simp add: Predicate_Compile.contains_def)

lemma subclsR_code [code_pred_inline]:
  "P \<turnstile> C \<prec>\<^sub>R D \<longleftrightarrow> subclsRp P C D"
by(simp add: subclsR_def)

lemma subclsSp_code [code_pred_intro]:
  "\<lbrakk> class P C = \<lfloor>(Bs, rest)\<rfloor>; Predicate_Compile.contains (set Bs) (Shares D) \<rbrakk> \<Longrightarrow> subclsSp P C D"
by(auto intro: subclsSp.intros simp add: Predicate_Compile.contains_def)

code_pred
  (modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool, i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool)
  subclsSp
by(erule subclsSp.cases)(fastforce simp add: Predicate_Compile.contains_def)

declare SubobjsR_Base [code_pred_intro]
lemma SubobjsR_Rep_code [code_pred_intro]:
  "\<lbrakk>subclsRp P C D; Subobjs\<^sub>R P D Cs\<rbrakk> \<Longrightarrow> Subobjs\<^sub>R P C (C # Cs)"
by(simp add: SubobjsR_Rep subclsR_def)

code_pred
  (modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool, i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool)
  Subobjs\<^sub>R
by(erule Subobjs\<^sub>R.cases)(auto simp add: subclsR_code)

lemma subcls1p_code [code_pred_intro]:
  "\<lbrakk>class P C = Some (Bs,rest); Predicate_Compile.contains (baseClasses Bs) D \<rbrakk> \<Longrightarrow> subcls1p P C D"
by(auto intro: subcls1p.intros simp add: Predicate_Compile.contains_def)

code_pred (modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool, i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool)
  subcls1p
by(fastforce elim!: subcls1p.cases simp add: Predicate_Compile.contains_def) 

declare Subobjs_Rep [code_pred_intro]
lemma Subobjs_Sh_code [code_pred_intro]:
  "\<lbrakk> (subcls1p P)^** C C'; subclsSp P C' D; Subobjs\<^sub>R P D Cs\<rbrakk>
  \<Longrightarrow> Subobjs P C Cs"
by(rule Subobjs_Sh)(simp_all add: rtrancl_def subcls1_def subclsS_def)

code_pred
  (modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool, i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool)
  Subobjs
by(erule Subobjs.cases)(auto simp add: rtrancl_def subcls1_def subclsS_def)

definition widen_unique :: "prog \<Rightarrow> cname \<Rightarrow> cname \<Rightarrow> path \<Rightarrow> bool"
where "widen_unique P C D Cs \<longleftrightarrow> (\<forall>Cs'. Subobjs P C Cs' \<longrightarrow> last Cs' = D \<longrightarrow> Cs = Cs')"

code_pred [inductify, skip_proof] widen_unique .

lemma widen_subcls':
  "\<lbrakk>Subobjs P C Cs'; last Cs' = D; widen_unique P C D Cs' \<rbrakk>
\<Longrightarrow> P \<turnstile> Class C \<le> Class D"
by(rule widen_subcls,auto simp:path_unique_def widen_unique_def)

declare 
  widen_refl [code_pred_intro]
  widen_subcls' [code_pred_intro widen_subcls]
  widen_null [code_pred_intro]

code_pred
  (modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool)
  widen
by(erule widen.cases)(auto simp add: path_unique_def widen_unique_def)

code_pred 
  (modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool, i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool, i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> i \<Rightarrow> bool, i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> bool)
  leq_path1p 
.

lemma leq_path_unfold: "P,C \<turnstile> Cs \<sqsubseteq> Ds \<longleftrightarrow> (leq_path1p P C)^** Cs Ds"
by(simp add: leq_path1_def rtrancl_def)

code_pred
   (modes: i => i => i => o => bool, i => i => i => i =>  bool)
   [inductify,skip_proof] 
   path_via 
.


lemma path_unique_eq [code_pred_def]: "P \<turnstile> Path C to D unique \<longleftrightarrow>
  (\<exists>Cs. Subobjs P C Cs \<and> last Cs = D \<and> (\<forall>Cs'. Subobjs P C Cs' \<longrightarrow> last Cs' = D \<longrightarrow> Cs = Cs'))"
by(auto simp add: path_unique_def)

code_pred
   (modes: i => i => o => bool, i => i => i => bool) 
   [inductify, skip_proof]
   path_unique .

text \<open>Redefine MethodDefs and FieldDecls\<close>

(* FIXME: These predicates should be defined inductively in the first place! *)

definition MethodDefs' :: "prog \<Rightarrow> cname \<Rightarrow> mname \<Rightarrow> path \<Rightarrow> method \<Rightarrow> bool" where
  "MethodDefs' P C M Cs mthd \<equiv> (Cs, mthd) \<in> MethodDefs P C M"

lemma [code_pred_intro]:
  "Subobjs P C Cs \<Longrightarrow> class P (last Cs) = \<lfloor>(Bs,fs,ms)\<rfloor> \<Longrightarrow> map_of ms M =  \<lfloor>mthd\<rfloor> \<Longrightarrow>
   MethodDefs' P C M Cs mthd"
 by (simp add: MethodDefs_def MethodDefs'_def)

code_pred
  (modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> bool, i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool)
  MethodDefs'
by(fastforce simp add: MethodDefs_def MethodDefs'_def)


definition FieldDecls' :: "prog \<Rightarrow> cname \<Rightarrow> vname \<Rightarrow> path \<Rightarrow> ty \<Rightarrow> bool" where
  "FieldDecls' P C F Cs T \<equiv> (Cs, T) \<in> FieldDecls P C F"

lemma [code_pred_intro]:
  "Subobjs P C Cs \<Longrightarrow> class P (last Cs) = \<lfloor>(Bs,fs,ms)\<rfloor> \<Longrightarrow> map_of fs F =  \<lfloor>T\<rfloor> \<Longrightarrow>
   FieldDecls' P C F Cs T"
by (simp add: FieldDecls_def FieldDecls'_def)

code_pred
  (modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> bool, i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool)
  FieldDecls'
by(fastforce simp add: FieldDecls_def FieldDecls'_def)



definition MinimalMethodDefs' :: "prog \<Rightarrow> cname \<Rightarrow> mname \<Rightarrow> path \<Rightarrow> method \<Rightarrow> bool" where
  "MinimalMethodDefs' P C M Cs mthd \<equiv> (Cs, mthd) \<in> MinimalMethodDefs P C M"

definition MinimalMethodDefs_unique :: "prog \<Rightarrow> cname \<Rightarrow> mname \<Rightarrow> path \<Rightarrow> bool"
where
  "MinimalMethodDefs_unique P C M Cs \<longleftrightarrow> 
  (\<forall>Cs' mthd. MethodDefs' P C M Cs' mthd \<longrightarrow> (leq_path1p P C)^** Cs' Cs \<longrightarrow> Cs' = Cs)"

code_pred [inductify, skip_proof] MinimalMethodDefs_unique .

lemma [code_pred_intro]:
  "MethodDefs' P C M Cs mthd \<Longrightarrow> MinimalMethodDefs_unique P C M Cs \<Longrightarrow>
   MinimalMethodDefs' P C M Cs mthd"
by (fastforce simp add:MinimalMethodDefs_def MinimalMethodDefs'_def MethodDefs'_def MinimalMethodDefs_unique_def leq_path_unfold)

code_pred
  (modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> bool)
  MinimalMethodDefs' 
by(fastforce simp add:MinimalMethodDefs_def MinimalMethodDefs'_def MethodDefs'_def MinimalMethodDefs_unique_def leq_path_unfold)



definition LeastMethodDef_unique :: "prog \<Rightarrow> cname \<Rightarrow> mname \<Rightarrow> path \<Rightarrow> bool"
where
  "LeastMethodDef_unique P C M Cs \<longleftrightarrow>
  (\<forall>Cs' mthd'. MethodDefs' P C M Cs' mthd' \<longrightarrow> (leq_path1p P C)^** Cs Cs')"

code_pred [inductify, skip_proof] LeastMethodDef_unique .

lemma LeastMethodDef_unfold:
  "P \<turnstile> C has least M = mthd via Cs \<longleftrightarrow>
   MethodDefs' P C M Cs mthd \<and> LeastMethodDef_unique P C M Cs"
by(fastforce simp add: LeastMethodDef_def MethodDefs'_def leq_path_unfold LeastMethodDef_unique_def)

lemma LeastMethodDef_intro [code_pred_intro]:
  "\<lbrakk> MethodDefs' P C M Cs mthd; LeastMethodDef_unique P C M Cs \<rbrakk>
  \<Longrightarrow> P \<turnstile> C has least M = mthd via Cs"
by(simp add: LeastMethodDef_unfold LeastMethodDef_unique_def)

code_pred (modes: i => i => i => o => o => bool)
  LeastMethodDef
by(simp add: LeastMethodDef_unfold LeastMethodDef_unique_def)


definition OverriderMethodDefs' :: "prog \<Rightarrow> subobj \<Rightarrow> mname \<Rightarrow> path \<Rightarrow> method \<Rightarrow> bool" where
  "OverriderMethodDefs' P R M Cs mthd \<equiv> (Cs, mthd) \<in> OverriderMethodDefs P R M"

lemma Overrider1 [code_pred_intro]:
  "P \<turnstile> (ldc R) has least M = mthd' via Cs' \<Longrightarrow> 
   MinimalMethodDefs' P (mdc R) M Cs mthd \<Longrightarrow>
   last (snd R) = hd Cs' \<Longrightarrow> (leq_path1p P (mdc R))^** Cs (snd R @ tl Cs') \<Longrightarrow>
   OverriderMethodDefs' P R M Cs mthd"
apply(simp add:OverriderMethodDefs_def OverriderMethodDefs'_def MinimalMethodDefs'_def appendPath_def leq_path_unfold)
apply(rule_tac x="Cs'" in exI)
apply clarsimp
apply(cases mthd')
apply blast
done

lemma Overrider2 [code_pred_intro]:
  "P \<turnstile> (ldc R) has least M = mthd' via Cs' \<Longrightarrow> 
   MinimalMethodDefs' P (mdc R) M Cs mthd \<Longrightarrow>
   last (snd R) \<noteq> hd Cs' \<Longrightarrow> (leq_path1p P (mdc R))^** Cs Cs' \<Longrightarrow>
   OverriderMethodDefs' P R M Cs mthd"
by(auto simp add:OverriderMethodDefs_def OverriderMethodDefs'_def MinimalMethodDefs'_def appendPath_def leq_path_unfold simp del: split_paired_Ex)


code_pred
  (modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> bool, i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool, i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> i \<Rightarrow> bool, i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool)
  OverriderMethodDefs'
apply(clarsimp simp add: OverriderMethodDefs'_def MinimalMethodDefs'_def MethodDefs'_def OverriderMethodDefs_def appendPath_def leq_path_unfold)
apply(case_tac "last xb = hd Cs'")
 apply(simp)

apply(thin_tac "PROP _")
apply(simp add: leq_path1_def)
done


definition WTDynCast_ex :: "prog \<Rightarrow> cname \<Rightarrow> cname \<Rightarrow> bool"
where "WTDynCast_ex P D C \<longleftrightarrow> (\<exists>Cs. P \<turnstile> Path D to C via Cs)"

code_pred [inductify, skip_proof] WTDynCast_ex .

lemma WTDynCast_new:
  "\<lbrakk>P,E \<turnstile> e :: Class D; is_class P C;
    P \<turnstile> Path D to C unique \<or> \<not> WTDynCast_ex P D C\<rbrakk> 
  \<Longrightarrow> P,E \<turnstile> Cast C e :: Class C"
by(rule WTDynCast)(auto simp add: WTDynCast_ex_def)

definition WTStaticCast_sub :: "prog \<Rightarrow> cname \<Rightarrow> cname \<Rightarrow> bool"
where "WTStaticCast_sub P C D \<longleftrightarrow> 
  P \<turnstile> Path D to C unique \<or> 
  ((subcls1p P)^** C D \<and> (\<forall>Cs. P \<turnstile> Path C to D via Cs \<longrightarrow> Subobjs\<^sub>R P C Cs))"

code_pred [inductify, skip_proof] WTStaticCast_sub .

lemma WTStaticCast_new:
  "\<lbrakk>P,E \<turnstile> e :: Class D; is_class P C; WTStaticCast_sub P C D \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> \<lparr>C\<rparr>e :: Class C"
by (rule WTStaticCast)(auto simp add: WTStaticCast_sub_def subcls1_def rtrancl_def)

lemma WTBinOp1: "\<lbrakk> P,E \<turnstile> e\<^sub>1 :: T;  P,E \<turnstile> e\<^sub>2 :: T\<rbrakk>
  \<Longrightarrow> P,E \<turnstile> e\<^sub>1 \<guillemotleft>Eq\<guillemotright> e\<^sub>2 :: Boolean"
  apply (rule WTBinOp)
  apply assumption+
  apply simp
  done

lemma WTBinOp2: "\<lbrakk> P,E \<turnstile> e\<^sub>1 :: Integer;  P,E \<turnstile> e\<^sub>2 :: Integer \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> e\<^sub>1 \<guillemotleft>Add\<guillemotright> e\<^sub>2 :: Integer"
  apply (rule WTBinOp)
  apply assumption+
  apply simp
  done


lemma LeastFieldDecl_unfold [code_pred_def]: 
  "P \<turnstile> C has least F:T via Cs \<longleftrightarrow>
   FieldDecls' P C F Cs T \<and> (\<forall>Cs' T'. FieldDecls' P C F Cs' T' \<longrightarrow> (leq_path1p P C)^** Cs Cs')"
by(auto simp add: LeastFieldDecl_def FieldDecls'_def leq_path_unfold)

code_pred [inductify, skip_proof] LeastFieldDecl .


lemmas [code_pred_intro] = WT_WTs.WTNew
declare
  WTDynCast_new[code_pred_intro WTDynCast_new]
  WTStaticCast_new[code_pred_intro WTStaticCast_new]
lemmas [code_pred_intro] = WT_WTs.WTVal WT_WTs.WTVar 
declare
  WTBinOp1[code_pred_intro WTBinOp1]
  WTBinOp2 [code_pred_intro WTBinOp2]
lemmas [code_pred_intro] =
  WT_WTs.WTLAss WT_WTs.WTFAcc WT_WTs.WTFAss WT_WTs.WTCall WTStaticCall
  WT_WTs.WTBlock WT_WTs.WTSeq WT_WTs.WTCond WT_WTs.WTWhile WT_WTs.WTThrow
lemmas [code_pred_intro] = WT_WTs.WTNil WT_WTs.WTCons

code_pred
  (modes: WT: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool, i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool
   and WTs: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool, i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool)
  WT
proof -
  case WT
  from WT.prems show thesis
  proof(cases (no_simp) rule: WT.cases)
    case WTDynCast thus thesis
      by(rule WT.WTDynCast_new[OF refl, unfolded WTDynCast_ex_def, simplified])
  next
    case WTStaticCast thus ?thesis
      unfolding subcls1_def rtrancl_def mem_Collect_eq prod.case
      by(rule WT.WTStaticCast_new[OF refl, unfolded WTStaticCast_sub_def])
  next
    case WTBinOp thus ?thesis
      by(split bop.split_asm)(simp_all, (erule (4) WT.WTBinOp1[OF refl] WT.WTBinOp2[OF refl])+)
  qed(assumption|erule (2) WT.that[OF refl])+
next
  case WTs
  from WTs.prems show thesis
    by(cases (no_simp) rule: WTs.cases)(assumption|erule (2) WTs.that[OF refl])+
qed

lemma casts_to_code [code_pred_intro]:
  "(case T of Class C \<Rightarrow> False | _ \<Rightarrow> True) \<Longrightarrow> P \<turnstile> T casts v to v"
  "P \<turnstile> Class C casts Null to Null"
  "\<lbrakk>Subobjs P (last Cs) Cs'; last Cs' = C;
    last Cs = hd Cs'; Cs @ tl Cs' = Ds\<rbrakk> 
  \<Longrightarrow> P \<turnstile> Class C casts Ref(a,Cs) to Ref(a,Ds)"
  "\<lbrakk>Subobjs P (last Cs) Cs'; last Cs' = C; last Cs \<noteq> hd Cs'\<rbrakk>
  \<Longrightarrow> P \<turnstile> Class C casts Ref(a,Cs) to Ref(a,Cs')"
by(auto intro: casts_to.intros simp add: path_via_def appendPath_def)

code_pred (modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool, i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool)
  casts_to
apply(erule casts_to.cases)
  apply(fastforce split: ty.splits)
 apply simp
apply(fastforce simp add: appendPath_def path_via_def split: if_split_asm)
done

code_pred 
  (modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool, i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool)
  Casts_to
.


lemma card_eq_1_iff_ex1: "x \<in> A \<Longrightarrow> card A = 1 \<longleftrightarrow> A = {x}"
apply(rule iffI)
 apply(rule equalityI)
  apply(rule subsetI)
  apply(subgoal_tac "card {x, xa} \<le> card A")
   apply(auto intro: ccontr)[1]
  apply(rule card_mono)
   apply simp_all
apply(metis Suc_n_not_n card_infinite)
done

lemma FinalOverriderMethodDef_unfold [code_pred_def]:
  "P \<turnstile> R has overrider M = mthd via Cs \<longleftrightarrow>
   OverriderMethodDefs' P R M Cs mthd \<and> 
   (\<forall>Cs' mthd'. OverriderMethodDefs' P R M Cs' mthd' \<longrightarrow> Cs = Cs' \<and> mthd = mthd')"
by(auto simp add: FinalOverriderMethodDef_def OverriderMethodDefs'_def card_eq_1_iff_ex1 simp del: One_nat_def)

code_pred
  (modes: i => i => i => o => o => bool)
  [inductify, skip_proof]
  FinalOverriderMethodDef
.

code_pred
  (modes: i => i => i => i => o => o => bool, i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool)
  [inductify]
  SelectMethodDef 
.

text \<open>Isomorphic subo with mapping instead of a map\<close>

type_synonym subo' = "(path \<times> (vname, val) mapping)"
type_synonym obj'  = "cname \<times> subo' set"

lift_definition init_class_fieldmap' :: "prog \<Rightarrow> cname \<Rightarrow> (vname, val) mapping" is "init_class_fieldmap" .

lemma init_class_fieldmap'_code [code]:
  "init_class_fieldmap' P C =
     Mapping (map (\<lambda>(F,T).(F,default_val T)) (fst(snd(the(class P C)))) )"
by transfer(simp add: init_class_fieldmap_def)

lift_definition init_obj' :: "prog \<Rightarrow> cname \<Rightarrow> subo' \<Rightarrow> bool" is init_obj .

lemma init_obj'_intros [code_pred_intro]: 
  "Subobjs P C Cs \<Longrightarrow> init_obj' P C (Cs, init_class_fieldmap' P (last Cs))"
by(transfer)(rule init_obj.intros)

code_pred
  (modes: i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool as init_obj_pred)
  init_obj'
by transfer(erule init_obj.cases, blast)


lemma init_obj_pred_conv: "set_of_pred (init_obj_pred P C) = Collect (init_obj' P C)"
by(auto elim: init_obj_predE intro: init_obj_predI)

lift_definition blank' :: "prog \<Rightarrow> cname \<Rightarrow> obj'" is "blank" .

lemma blank'_code [code]:
  "blank' P C = (C, set_of_pred (init_obj_pred P C))"
unfolding init_obj_pred_conv by transfer(simp add: blank_def)

type_synonym heap'  = "addr \<rightharpoonup> obj'"

abbreviation
  cname_of' :: "heap' \<Rightarrow> addr \<Rightarrow> cname" where
  "\<And>hp. cname_of' hp a == fst (the (hp a))"

lift_definition new_Addr' :: "heap' \<Rightarrow> addr option" is "new_Addr" .

lift_definition start_heap' :: "prog \<Rightarrow> heap'" is "start_heap" .

lemma start_heap'_code [code]:
  "start_heap' P = Map.empty (addr_of_sys_xcpt NullPointer \<mapsto> blank' P NullPointer)
                        (addr_of_sys_xcpt ClassCast \<mapsto> blank' P ClassCast)
                        (addr_of_sys_xcpt OutOfMemory \<mapsto> blank' P OutOfMemory)"
by transfer(simp add: start_heap_def)

type_synonym
  state'  = "heap' \<times> locals"

lift_definition hp' :: "state' \<Rightarrow> heap'" is hp .

lemma hp'_code [code]: "hp' = fst"
by transfer simp

lift_definition lcl' :: "state' \<Rightarrow> locals" is lcl .

lemma lcl_code [code]: "lcl' = snd"
by transfer simp


lift_definition eval' :: "prog \<Rightarrow> env \<Rightarrow> expr \<Rightarrow> state' \<Rightarrow> expr \<Rightarrow> state' \<Rightarrow> bool"
          ("_,_ \<turnstile> ((1\<langle>_,/_\<rangle>) \<Rightarrow>''/ (1\<langle>_,/_\<rangle>))" [51,0,0,0,0] 81)
  is eval .
lift_definition evals' :: "prog \<Rightarrow> env \<Rightarrow> expr list \<Rightarrow> state' \<Rightarrow> expr list \<Rightarrow> state' \<Rightarrow> bool"
           ("_,_ \<turnstile> ((1\<langle>_,/_\<rangle>) [\<Rightarrow>'']/ (1\<langle>_,/_\<rangle>))" [51,0,0,0,0] 81)
  is evals .

lemma New':
  "\<lbrakk> new_Addr' h = Some a; h' = h(a\<mapsto>(blank' P C)) \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> \<langle>new C,(h,l)\<rangle> \<Rightarrow>' \<langle>ref (a,[C]),(h',l)\<rangle>"
by transfer(unfold blank_def, rule New)

lemma NewFail':
  "new_Addr' h = None \<Longrightarrow>
  P,E \<turnstile> \<langle>new C, (h,l)\<rangle> \<Rightarrow>' \<langle>THROW OutOfMemory,(h,l)\<rangle>"
by transfer(rule NewFail)

lemma StaticUpCast':
  "\<lbrakk> P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow>' \<langle>ref (a,Cs),s\<^sub>1\<rangle>; P \<turnstile> Path last Cs to C via Cs'; Ds = Cs@\<^sub>pCs' \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> \<langle>\<lparr>C\<rparr>e,s\<^sub>0\<rangle> \<Rightarrow>' \<langle>ref (a,Ds),s\<^sub>1\<rangle>"
by transfer(rule StaticUpCast)

lemma StaticDownCast'_new:  (* requires reverse append *)
  "\<lbrakk>P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow>' \<langle>ref (a,Ds),s\<^sub>1\<rangle>; app Cs [C] Ds'; app Ds' Cs' Ds\<rbrakk>
  \<Longrightarrow> P,E \<turnstile> \<langle>\<lparr>C\<rparr>e,s\<^sub>0\<rangle> \<Rightarrow>' \<langle>ref(a,Cs@[C]),s\<^sub>1\<rangle>"
apply transfer
apply (rule StaticDownCast)
apply (simp add: app_eq)
done

lemma StaticCastNull':
  "P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow>' \<langle>null,s\<^sub>1\<rangle> \<Longrightarrow>
  P,E \<turnstile> \<langle>\<lparr>C\<rparr>e,s\<^sub>0\<rangle> \<Rightarrow>' \<langle>null,s\<^sub>1\<rangle>"
by transfer(rule StaticCastNull)

lemma StaticCastFail'_new: (* manual unfolding of subcls *)
"\<lbrakk> P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle>\<Rightarrow>' \<langle>ref (a,Cs),s\<^sub>1\<rangle>;  \<not> (subcls1p P)^** (last Cs) C; C \<notin> set Cs\<rbrakk>
  \<Longrightarrow> P,E \<turnstile> \<langle>\<lparr>C\<rparr>e,s\<^sub>0\<rangle> \<Rightarrow>' \<langle>THROW ClassCast,s\<^sub>1\<rangle>"
apply transfer
by (fastforce intro:StaticCastFail simp add: rtrancl_def subcls1_def)

lemma StaticCastThrow':
  "P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow>' \<langle>throw e',s\<^sub>1\<rangle> \<Longrightarrow>
  P,E \<turnstile> \<langle>\<lparr>C\<rparr>e,s\<^sub>0\<rangle> \<Rightarrow>' \<langle>throw e',s\<^sub>1\<rangle>"
by transfer(rule StaticCastThrow)

lemma StaticUpDynCast':
  "\<lbrakk>P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow>' \<langle>ref(a,Cs),s\<^sub>1\<rangle>; P \<turnstile> Path last Cs to C unique;
    P \<turnstile> Path last Cs to C via Cs'; Ds = Cs@\<^sub>pCs' \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> \<langle>Cast C e,s\<^sub>0\<rangle> \<Rightarrow>' \<langle>ref(a,Ds),s\<^sub>1\<rangle>"
by transfer(rule StaticUpDynCast)

lemma StaticDownDynCast'_new: (* requires reverse append *)
  "\<lbrakk>P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow>' \<langle>ref (a,Ds),s\<^sub>1\<rangle>; app Cs [C] Ds'; app Ds' Cs' Ds\<rbrakk>
  \<Longrightarrow> P,E \<turnstile> \<langle>Cast C e,s\<^sub>0\<rangle> \<Rightarrow>' \<langle>ref(a,Cs@[C]),s\<^sub>1\<rangle>"
apply transfer
apply (rule StaticDownDynCast)
apply (simp add: app_eq)
done

lemma DynCast':
  "\<lbrakk> P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow>' \<langle>ref (a,Cs),(h,l)\<rangle>; h a = Some(D,S);
    P \<turnstile> Path D to C via Cs'; P \<turnstile> Path D to C unique \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> \<langle>Cast C e,s\<^sub>0\<rangle> \<Rightarrow>' \<langle>ref (a,Cs'),(h,l)\<rangle>"
by transfer(rule DynCast)

lemma DynCastNull':
  "P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow>' \<langle>null,s\<^sub>1\<rangle> \<Longrightarrow>
  P,E \<turnstile> \<langle>Cast C e,s\<^sub>0\<rangle> \<Rightarrow>' \<langle>null,s\<^sub>1\<rangle>"
by transfer(rule DynCastNull)

lemma DynCastFail':
  "\<lbrakk> P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle>\<Rightarrow>' \<langle>ref (a,Cs),(h,l)\<rangle>; h a = Some(D,S); \<not> P \<turnstile> Path D to C unique;
    \<not> P \<turnstile> Path last Cs to C unique; C \<notin> set Cs \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> \<langle>Cast C e,s\<^sub>0\<rangle> \<Rightarrow>' \<langle>null,(h,l)\<rangle>"
by transfer(rule DynCastFail)

lemma DynCastThrow':
  "P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow>' \<langle>throw e',s\<^sub>1\<rangle> \<Longrightarrow>
  P,E \<turnstile> \<langle>Cast C e,s\<^sub>0\<rangle> \<Rightarrow>' \<langle>throw e',s\<^sub>1\<rangle>"
by transfer(rule DynCastThrow)

lemma Val':
  "P,E \<turnstile> \<langle>Val v,s\<rangle> \<Rightarrow>' \<langle>Val v,s\<rangle>"
by transfer(rule Val)

lemma BinOp':
  "\<lbrakk> P,E \<turnstile> \<langle>e\<^sub>1,s\<^sub>0\<rangle> \<Rightarrow>' \<langle>Val v\<^sub>1,s\<^sub>1\<rangle>; P,E \<turnstile> \<langle>e\<^sub>2,s\<^sub>1\<rangle> \<Rightarrow>' \<langle>Val v\<^sub>2,s\<^sub>2\<rangle>; 
    binop(bop,v\<^sub>1,v\<^sub>2) = Some v \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> \<langle>e\<^sub>1 \<guillemotleft>bop\<guillemotright> e\<^sub>2,s\<^sub>0\<rangle>\<Rightarrow>'\<langle>Val v,s\<^sub>2\<rangle>"
by transfer(rule BinOp)

lemma BinOpThrow1':
  "P,E \<turnstile> \<langle>e\<^sub>1,s\<^sub>0\<rangle> \<Rightarrow>' \<langle>throw e,s\<^sub>1\<rangle> \<Longrightarrow>
  P,E \<turnstile> \<langle>e\<^sub>1 \<guillemotleft>bop\<guillemotright> e\<^sub>2, s\<^sub>0\<rangle> \<Rightarrow>' \<langle>throw e,s\<^sub>1\<rangle>"
by transfer(rule BinOpThrow1)

lemma BinOpThrow2':
  "\<lbrakk> P,E \<turnstile> \<langle>e\<^sub>1,s\<^sub>0\<rangle> \<Rightarrow>' \<langle>Val v\<^sub>1,s\<^sub>1\<rangle>; P,E \<turnstile> \<langle>e\<^sub>2,s\<^sub>1\<rangle> \<Rightarrow>' \<langle>throw e,s\<^sub>2\<rangle> \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> \<langle>e\<^sub>1 \<guillemotleft>bop\<guillemotright> e\<^sub>2,s\<^sub>0\<rangle> \<Rightarrow>' \<langle>throw e,s\<^sub>2\<rangle>"
by transfer(rule BinOpThrow2)

lemma Var':
  "l V = Some v \<Longrightarrow>
  P,E \<turnstile> \<langle>Var V,(h,l)\<rangle> \<Rightarrow>' \<langle>Val v,(h,l)\<rangle>"
by transfer(rule Var)

lemma LAss':
  "\<lbrakk> P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow>' \<langle>Val v,(h,l)\<rangle>; E V = Some T;
     P \<turnstile> T casts v to v'; l' = l(V\<mapsto>v') \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> \<langle>V:=e,s\<^sub>0\<rangle> \<Rightarrow>' \<langle>Val v',(h,l')\<rangle>"
by (transfer) (erule (3) LAss)

lemma LAssThrow':
  "P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow>' \<langle>throw e',s\<^sub>1\<rangle> \<Longrightarrow>
  P,E \<turnstile> \<langle>V:=e,s\<^sub>0\<rangle> \<Rightarrow>' \<langle>throw e',s\<^sub>1\<rangle>"
by transfer(rule LAssThrow)

lemma FAcc'_new: (* iteration over set *)
  "\<lbrakk> P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow>' \<langle>ref (a,Cs'),(h,l)\<rangle>; h a = Some(D,S);
     Ds = Cs'@\<^sub>pCs; Predicate_Compile.contains (Set_project S Ds) fs; Mapping.lookup fs F = Some v \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> \<langle>e\<bullet>F{Cs},s\<^sub>0\<rangle> \<Rightarrow>' \<langle>Val v,(h,l)\<rangle>"
unfolding Set_project_def mem_Collect_eq Predicate_Compile.contains_def
by transfer(rule FAcc)

lemma FAccNull':
  "P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow>' \<langle>null,s\<^sub>1\<rangle> \<Longrightarrow>
  P,E \<turnstile> \<langle>e\<bullet>F{Cs},s\<^sub>0\<rangle> \<Rightarrow>' \<langle>THROW NullPointer,s\<^sub>1\<rangle>" 
by transfer(rule FAccNull)

lemma FAccThrow':
  "P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow>' \<langle>throw e',s\<^sub>1\<rangle> \<Longrightarrow>
  P,E \<turnstile> \<langle>e\<bullet>F{Cs},s\<^sub>0\<rangle> \<Rightarrow>' \<langle>throw e',s\<^sub>1\<rangle>"
by transfer(rule FAccThrow)

lemma FAss'_new: (* iteration over set *)
  "\<lbrakk> P,E \<turnstile> \<langle>e\<^sub>1,s\<^sub>0\<rangle> \<Rightarrow>' \<langle>ref (a,Cs'),s\<^sub>1\<rangle>; P,E \<turnstile> \<langle>e\<^sub>2,s\<^sub>1\<rangle> \<Rightarrow>' \<langle>Val v,(h\<^sub>2,l\<^sub>2)\<rangle>;
     h\<^sub>2 a = Some(D,S); P \<turnstile> (last Cs') has least F:T via Cs; P \<turnstile> T casts v to v';
     Ds = Cs'@\<^sub>pCs;  Predicate_Compile.contains (Set_project S Ds) fs; fs' = Mapping.update F v' fs;
     S' = S - {(Ds,fs)} \<union> {(Ds,fs')}; h\<^sub>2' = h\<^sub>2(a\<mapsto>(D,S'))\<rbrakk>
  \<Longrightarrow> P,E \<turnstile> \<langle>e\<^sub>1\<bullet>F{Cs}:=e\<^sub>2,s\<^sub>0\<rangle> \<Rightarrow>' \<langle>Val v',(h\<^sub>2',l\<^sub>2)\<rangle>"
unfolding Predicate_Compile.contains_def Set_project_def mem_Collect_eq
by transfer(rule FAss)

lemma FAssNull':
  "\<lbrakk> P,E \<turnstile> \<langle>e\<^sub>1,s\<^sub>0\<rangle> \<Rightarrow>' \<langle>null,s\<^sub>1\<rangle>;  P,E \<turnstile> \<langle>e\<^sub>2,s\<^sub>1\<rangle> \<Rightarrow>' \<langle>Val v,s\<^sub>2\<rangle> \<rbrakk> \<Longrightarrow>
  P,E \<turnstile> \<langle>e\<^sub>1\<bullet>F{Cs}:=e\<^sub>2,s\<^sub>0\<rangle> \<Rightarrow>' \<langle>THROW NullPointer,s\<^sub>2\<rangle>" 
by transfer(rule FAssNull)

lemma FAssThrow1':
  "P,E \<turnstile> \<langle>e\<^sub>1,s\<^sub>0\<rangle> \<Rightarrow>' \<langle>throw e',s\<^sub>1\<rangle> \<Longrightarrow>
  P,E \<turnstile> \<langle>e\<^sub>1\<bullet>F{Cs}:=e\<^sub>2,s\<^sub>0\<rangle> \<Rightarrow>' \<langle>throw e',s\<^sub>1\<rangle>"
by transfer(rule FAssThrow1)

lemma FAssThrow2':
  "\<lbrakk> P,E \<turnstile> \<langle>e\<^sub>1,s\<^sub>0\<rangle> \<Rightarrow>' \<langle>Val v,s\<^sub>1\<rangle>; P,E \<turnstile> \<langle>e\<^sub>2,s\<^sub>1\<rangle> \<Rightarrow>' \<langle>throw e',s\<^sub>2\<rangle> \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> \<langle>e\<^sub>1\<bullet>F{Cs}:=e\<^sub>2,s\<^sub>0\<rangle> \<Rightarrow>' \<langle>throw e',s\<^sub>2\<rangle>"
by transfer(rule FAssThrow2)

lemma CallObjThrow':
  "P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow>' \<langle>throw e',s\<^sub>1\<rangle> \<Longrightarrow>
  P,E \<turnstile> \<langle>Call e Copt M es,s\<^sub>0\<rangle> \<Rightarrow>' \<langle>throw e',s\<^sub>1\<rangle>"
by transfer(rule CallObjThrow)

lemma CallParamsThrow'_new: (* requires inverse map Val and append *)
  "\<lbrakk> P,E \<turnstile> \<langle>e,s0\<rangle> \<Rightarrow>' \<langle>Val v,s1\<rangle>; P,E \<turnstile> \<langle>es,s1\<rangle> [\<Rightarrow>'] \<langle>evs,s2\<rangle>;
     map_val2 evs vs (throw ex # es') \<rbrakk>
   \<Longrightarrow> P,E \<turnstile> \<langle>Call e Copt M es,s0\<rangle> \<Rightarrow>' \<langle>throw ex,s2\<rangle>"
apply transfer
apply(rule eval_evals.CallParamsThrow, assumption+)
apply(simp add: map_val2_conv[symmetric])
done

lemma Call'_new: (* requires inverse map Val *)
  "\<lbrakk> P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow>' \<langle>ref (a,Cs),s\<^sub>1\<rangle>;  P,E \<turnstile> \<langle>ps,s\<^sub>1\<rangle> [\<Rightarrow>'] \<langle>evs,(h\<^sub>2,l\<^sub>2)\<rangle>;
     map_val evs vs;
     h\<^sub>2 a = Some(C,S);  P \<turnstile> last Cs has least M = (Ts',T',pns',body') via Ds;
     P \<turnstile> (C,Cs@\<^sub>pDs) selects M = (Ts,T,pns,body) via Cs'; length vs = length pns; 
     P \<turnstile> Ts Casts vs to vs'; l\<^sub>2' = [this\<mapsto>Ref (a,Cs'), pns[\<mapsto>]vs'];
     new_body = (case T' of Class D \<Rightarrow> \<lparr>D\<rparr>body   | _  \<Rightarrow> body);  
     P,E(this\<mapsto>Class(last Cs'), pns[\<mapsto>]Ts) \<turnstile> \<langle>new_body,(h\<^sub>2,l\<^sub>2')\<rangle> \<Rightarrow>' \<langle>e',(h\<^sub>3,l\<^sub>3)\<rangle> \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> \<langle>e\<bullet>M(ps),s\<^sub>0\<rangle> \<Rightarrow>' \<langle>e',(h\<^sub>3,l\<^sub>2)\<rangle>"
apply transfer
apply(rule Call)
apply assumption+
apply(simp add: map_val_conv[symmetric])
apply assumption+
done

lemma StaticCall'_new: (* requires inverse map Val *)
  "\<lbrakk> P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow>' \<langle>ref (a,Cs),s\<^sub>1\<rangle>;  P,E \<turnstile> \<langle>ps,s\<^sub>1\<rangle> [\<Rightarrow>'] \<langle>evs,(h\<^sub>2,l\<^sub>2)\<rangle>;
     map_val evs vs;
     P \<turnstile> Path (last Cs) to C unique; P \<turnstile> Path (last Cs) to C via Cs'';
     P \<turnstile> C has least M = (Ts,T,pns,body) via Cs'; Ds = (Cs@\<^sub>pCs'')@\<^sub>pCs';
     length vs = length pns; P \<turnstile> Ts Casts vs to vs'; 
     l\<^sub>2' = [this\<mapsto>Ref (a,Ds), pns[\<mapsto>]vs'];
     P,E(this\<mapsto>Class(last Ds), pns[\<mapsto>]Ts) \<turnstile> \<langle>body,(h\<^sub>2,l\<^sub>2')\<rangle> \<Rightarrow>' \<langle>e',(h\<^sub>3,l\<^sub>3)\<rangle> \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> \<langle>e\<bullet>(C::)M(ps),s\<^sub>0\<rangle> \<Rightarrow>' \<langle>e',(h\<^sub>3,l\<^sub>2)\<rangle>"
apply transfer
apply(rule StaticCall)
apply(assumption)+
apply(simp add: map_val_conv[symmetric])
apply assumption+
done

lemma CallNull'_new: (* requires inverse map Val *)
  "\<lbrakk> P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow>' \<langle>null,s\<^sub>1\<rangle>;  P,E \<turnstile> \<langle>es,s\<^sub>1\<rangle> [\<Rightarrow>'] \<langle>evs,s\<^sub>2\<rangle>; map_val evs vs \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> \<langle>Call e Copt M es,s\<^sub>0\<rangle> \<Rightarrow>' \<langle>THROW NullPointer,s\<^sub>2\<rangle>"
apply transfer
apply(rule CallNull, assumption+)
apply(simp add: map_val_conv[symmetric])
done

lemma Block':
  "\<lbrakk>P,E(V \<mapsto> T) \<turnstile> \<langle>e\<^sub>0,(h\<^sub>0,l\<^sub>0(V:=None))\<rangle> \<Rightarrow>' \<langle>e\<^sub>1,(h\<^sub>1,l\<^sub>1)\<rangle> \<rbrakk> \<Longrightarrow>
  P,E \<turnstile> \<langle>{V:T; e\<^sub>0},(h\<^sub>0,l\<^sub>0)\<rangle> \<Rightarrow>' \<langle>e\<^sub>1,(h\<^sub>1,l\<^sub>1(V:=l\<^sub>0 V))\<rangle>"
by transfer(rule Block)

lemma Seq':
  "\<lbrakk> P,E \<turnstile> \<langle>e\<^sub>0,s\<^sub>0\<rangle> \<Rightarrow>' \<langle>Val v,s\<^sub>1\<rangle>; P,E \<turnstile> \<langle>e\<^sub>1,s\<^sub>1\<rangle> \<Rightarrow>' \<langle>e\<^sub>2,s\<^sub>2\<rangle> \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> \<langle>e\<^sub>0;;e\<^sub>1,s\<^sub>0\<rangle> \<Rightarrow>' \<langle>e\<^sub>2,s\<^sub>2\<rangle>"
by transfer(rule Seq)

lemma SeqThrow':
  "P,E \<turnstile> \<langle>e\<^sub>0,s\<^sub>0\<rangle> \<Rightarrow>' \<langle>throw e,s\<^sub>1\<rangle> \<Longrightarrow>
  P,E \<turnstile> \<langle>e\<^sub>0;;e\<^sub>1,s\<^sub>0\<rangle>\<Rightarrow>'\<langle>throw e,s\<^sub>1\<rangle>"
by transfer(rule SeqThrow)

lemma CondT':
  "\<lbrakk> P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow>' \<langle>true,s\<^sub>1\<rangle>; P,E \<turnstile> \<langle>e\<^sub>1,s\<^sub>1\<rangle> \<Rightarrow>' \<langle>e',s\<^sub>2\<rangle> \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> \<langle>if (e) e\<^sub>1 else e\<^sub>2,s\<^sub>0\<rangle> \<Rightarrow>' \<langle>e',s\<^sub>2\<rangle>"
by transfer(rule CondT)

lemma CondF':
  "\<lbrakk> P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow>' \<langle>false,s\<^sub>1\<rangle>; P,E \<turnstile> \<langle>e\<^sub>2,s\<^sub>1\<rangle> \<Rightarrow>' \<langle>e',s\<^sub>2\<rangle> \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> \<langle>if (e) e\<^sub>1 else e\<^sub>2,s\<^sub>0\<rangle> \<Rightarrow>' \<langle>e',s\<^sub>2\<rangle>"
by transfer(rule CondF)

lemma CondThrow':
  "P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow>' \<langle>throw e',s\<^sub>1\<rangle> \<Longrightarrow>
  P,E \<turnstile> \<langle>if (e) e\<^sub>1 else e\<^sub>2, s\<^sub>0\<rangle> \<Rightarrow>' \<langle>throw e',s\<^sub>1\<rangle>"
by transfer(rule CondThrow)

lemma WhileF':
  "P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow>' \<langle>false,s\<^sub>1\<rangle> \<Longrightarrow>
  P,E \<turnstile> \<langle>while (e) c,s\<^sub>0\<rangle> \<Rightarrow>' \<langle>unit,s\<^sub>1\<rangle>"
by transfer(rule WhileF)

lemma WhileT':
  "\<lbrakk> P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow>' \<langle>true,s\<^sub>1\<rangle>; P,E \<turnstile> \<langle>c,s\<^sub>1\<rangle> \<Rightarrow>' \<langle>Val v\<^sub>1,s\<^sub>2\<rangle>; 
     P,E \<turnstile> \<langle>while (e) c,s\<^sub>2\<rangle> \<Rightarrow>' \<langle>e\<^sub>3,s\<^sub>3\<rangle> \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> \<langle>while (e) c,s\<^sub>0\<rangle> \<Rightarrow>' \<langle>e\<^sub>3,s\<^sub>3\<rangle>"
by transfer(rule WhileT)

lemma WhileCondThrow':
  "P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow>' \<langle> throw e',s\<^sub>1\<rangle> \<Longrightarrow>
  P,E \<turnstile> \<langle>while (e) c,s\<^sub>0\<rangle> \<Rightarrow>' \<langle>throw e',s\<^sub>1\<rangle>"
by transfer(rule WhileCondThrow)

lemma WhileBodyThrow':
  "\<lbrakk> P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow>' \<langle>true,s\<^sub>1\<rangle>; P,E \<turnstile> \<langle>c,s\<^sub>1\<rangle> \<Rightarrow>' \<langle>throw e',s\<^sub>2\<rangle>\<rbrakk>
  \<Longrightarrow> P,E \<turnstile> \<langle>while (e) c,s\<^sub>0\<rangle> \<Rightarrow>' \<langle>throw e',s\<^sub>2\<rangle>"
by transfer(rule WhileBodyThrow)

lemma Throw':
  "P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow>' \<langle>ref r,s\<^sub>1\<rangle> \<Longrightarrow>
  P,E \<turnstile> \<langle>throw e,s\<^sub>0\<rangle> \<Rightarrow>' \<langle>Throw r,s\<^sub>1\<rangle>"
by transfer(rule eval_evals.Throw)

lemma ThrowNull':
  "P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow>' \<langle>null,s\<^sub>1\<rangle> \<Longrightarrow>
  P,E \<turnstile> \<langle>throw e,s\<^sub>0\<rangle> \<Rightarrow>' \<langle>THROW NullPointer,s\<^sub>1\<rangle>"
by transfer(rule ThrowNull)

lemma ThrowThrow':
  "P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow>' \<langle>throw e',s\<^sub>1\<rangle> \<Longrightarrow>
  P,E \<turnstile> \<langle>throw e,s\<^sub>0\<rangle> \<Rightarrow>' \<langle>throw e',s\<^sub>1\<rangle>"
by transfer(rule ThrowThrow)

lemma Nil':
  "P,E \<turnstile> \<langle>[],s\<rangle> [\<Rightarrow>'] \<langle>[],s\<rangle>"
by transfer(rule eval_evals.Nil)

lemma Cons':
  "\<lbrakk> P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow>' \<langle>Val v,s\<^sub>1\<rangle>; P,E \<turnstile> \<langle>es,s\<^sub>1\<rangle> [\<Rightarrow>'] \<langle>es',s\<^sub>2\<rangle> \<rbrakk>
  \<Longrightarrow> P,E \<turnstile> \<langle>e#es,s\<^sub>0\<rangle> [\<Rightarrow>'] \<langle>Val v # es',s\<^sub>2\<rangle>"
by transfer(rule eval_evals.Cons)

lemma ConsThrow':
  "P,E \<turnstile> \<langle>e, s\<^sub>0\<rangle> \<Rightarrow>' \<langle>throw e', s\<^sub>1\<rangle> \<Longrightarrow>
  P,E \<turnstile> \<langle>e#es, s\<^sub>0\<rangle> [\<Rightarrow>'] \<langle>throw e' # es, s\<^sub>1\<rangle>"
by transfer(rule ConsThrow)

text \<open>Axiomatic heap address model refinement\<close>

partial_function (option) lowest :: "(nat \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> nat option"
where
  [code]: "lowest P n = (if P n then Some n else lowest P (Suc n))"

axiomatization
where
  new_Addr'_code [code]: "new_Addr' h = lowest (Option.is_none \<circ> h) 0"
    \<comment> \<open>admissible: a tightening of the specification of @{const new_Addr'}\<close>

lemma eval'_cases
  [consumes 1,
   case_names New NewFail StaticUpCast StaticDownCast StaticCastNull StaticCastFail
    StaticCastThrow StaticUpDynCast StaticDownDynCast DynCast DynCastNull DynCastFail
    DynCastThrow Val BinOp BinOpThrow1 BinOpThrow2 Var LAss LAssThrow FAcc FAccNull FAccThrow
    FAss FAssNull FAssThrow1 FAssThrow2 CallObjThrow CallParamsThrow Call StaticCall CallNull
    Block Seq SeqThrow CondT CondF CondThrow WhileF WhileT WhileCondThrow WhileBodyThrow
    Throw ThrowNull ThrowThrow]:
  assumes "P,x \<turnstile> \<langle>y,z\<rangle> \<Rightarrow>' \<langle>u,v\<rangle>"
  and "\<And>h a h' C E l. x = E \<Longrightarrow> y = new C \<Longrightarrow> z = (h, l) \<Longrightarrow> u = ref (a, [C]) \<Longrightarrow>
    v = (h', l) \<Longrightarrow> new_Addr' h = \<lfloor>a\<rfloor> \<Longrightarrow> h' = h(a \<mapsto> blank' P C) \<Longrightarrow> thesis"
  and "\<And>h E C l. x = E \<Longrightarrow> y = new C \<Longrightarrow> z = (h, l) \<Longrightarrow>
    u = Throw (addr_of_sys_xcpt OutOfMemory, [OutOfMemory]) \<Longrightarrow>
    v = (h, l) \<Longrightarrow> new_Addr' h = None \<Longrightarrow> thesis"
  and "\<And>E e s\<^sub>0 a Cs s\<^sub>1 C Cs' Ds. x = E \<Longrightarrow> y = \<lparr>C\<rparr>e \<Longrightarrow> z = s\<^sub>0 \<Longrightarrow>
    u = ref (a, Ds) \<Longrightarrow> v = s\<^sub>1 \<Longrightarrow> P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow>' \<langle>ref (a, Cs),s\<^sub>1\<rangle> \<Longrightarrow>
    P \<turnstile> Path last Cs to C via Cs'  \<Longrightarrow> Ds = Cs @\<^sub>p Cs' \<Longrightarrow> thesis"
  and "\<And>E e s\<^sub>0 a Cs C Cs' s\<^sub>1. x = E \<Longrightarrow> y = \<lparr>C\<rparr>e \<Longrightarrow> z = s\<^sub>0 \<Longrightarrow> u = ref (a, Cs @ [C]) \<Longrightarrow>
    v = s\<^sub>1 \<Longrightarrow> P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow>' \<langle>ref (a, Cs @ [C] @ Cs'),s\<^sub>1\<rangle> \<Longrightarrow> thesis"
  and "\<And>E e s\<^sub>0 s\<^sub>1 C. x = E \<Longrightarrow> y = \<lparr>C\<rparr>e \<Longrightarrow> z = s\<^sub>0 \<Longrightarrow> u = null \<Longrightarrow> v = s\<^sub>1 \<Longrightarrow>
   P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow>' \<langle>null,s\<^sub>1\<rangle> \<Longrightarrow> thesis"
  and "\<And>E e s\<^sub>0 a Cs s\<^sub>1 C. x = E \<Longrightarrow> y = \<lparr>C\<rparr>e \<Longrightarrow> z = s\<^sub>0 \<Longrightarrow>
    u = Throw (addr_of_sys_xcpt ClassCast, [ClassCast]) \<Longrightarrow>  v = s\<^sub>1 \<Longrightarrow>
    P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow>' \<langle>ref (a, Cs),s\<^sub>1\<rangle> \<Longrightarrow> (last Cs, C) \<notin> (subcls1 P)\<^sup>* \<Longrightarrow> C \<notin> set Cs \<Longrightarrow> thesis"
  and "\<And>E e s\<^sub>0 e' s\<^sub>1 C. x = E \<Longrightarrow> y = \<lparr>C\<rparr>e \<Longrightarrow> z = s\<^sub>0 \<Longrightarrow> u = throw e' \<Longrightarrow> v = s\<^sub>1 \<Longrightarrow>
    P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow>' \<langle>throw e',s\<^sub>1\<rangle> \<Longrightarrow> thesis"
  and "\<And>E e s\<^sub>0 a Cs s\<^sub>1 C Cs' Ds. x = E \<Longrightarrow> y = Cast C e \<Longrightarrow> z = s\<^sub>0 \<Longrightarrow> u = ref (a, Ds) \<Longrightarrow>
    v = s\<^sub>1 \<Longrightarrow> P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow>' \<langle>ref (a, Cs),s\<^sub>1\<rangle> \<Longrightarrow> P \<turnstile> Path last Cs to C unique \<Longrightarrow>
    P \<turnstile> Path last Cs to C via Cs'  \<Longrightarrow> Ds = Cs @\<^sub>p Cs' \<Longrightarrow> thesis"
  and "\<And>E e s\<^sub>0 a Cs C Cs' s\<^sub>1. x = E \<Longrightarrow> y = Cast C e \<Longrightarrow> z = s\<^sub>0 \<Longrightarrow>
    u = ref (a, Cs @ [C]) \<Longrightarrow> v = s\<^sub>1 \<Longrightarrow> P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow>' \<langle>ref (a, Cs @ [C] @ Cs'),s\<^sub>1\<rangle> \<Longrightarrow> thesis"
  and "\<And>E e s\<^sub>0 a Cs h l D S C Cs'. x = E \<Longrightarrow> y = Cast C e \<Longrightarrow> z = s\<^sub>0 \<Longrightarrow>
    u = ref (a, Cs') \<Longrightarrow> v = (h, l) \<Longrightarrow> P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow>' \<langle>ref (a, Cs),(h, l)\<rangle> \<Longrightarrow>
    h a = \<lfloor>(D, S)\<rfloor> \<Longrightarrow> P \<turnstile> Path D to C via Cs'  \<Longrightarrow> P \<turnstile> Path D to C unique \<Longrightarrow> thesis"
  and "\<And>E e s\<^sub>0 s\<^sub>1 C. x = E \<Longrightarrow> y = Cast C e \<Longrightarrow> z = s\<^sub>0 \<Longrightarrow> u = null \<Longrightarrow> v = s\<^sub>1 \<Longrightarrow> 
    P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow>' \<langle>null,s\<^sub>1\<rangle> \<Longrightarrow> thesis" 
  and "\<And>E e s\<^sub>0 a Cs h l D S C. x = E \<Longrightarrow> y = Cast C e \<Longrightarrow> z = s\<^sub>0 \<Longrightarrow> u = null \<Longrightarrow>
    v = (h, l) \<Longrightarrow> P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow>' \<langle>ref (a, Cs),(h, l)\<rangle> \<Longrightarrow> h a = \<lfloor>(D, S)\<rfloor> \<Longrightarrow>
    \<not> P \<turnstile> Path D to C unique \<Longrightarrow> \<not> P \<turnstile> Path last Cs to C unique \<Longrightarrow> C \<notin> set Cs \<Longrightarrow> thesis"
  and "\<And>E e s\<^sub>0 e' s\<^sub>1 C. x = E \<Longrightarrow> y = Cast C e \<Longrightarrow> z = s\<^sub>0 \<Longrightarrow> u = throw e' \<Longrightarrow> v = s\<^sub>1
    \<Longrightarrow> P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow>' \<langle>throw e',s\<^sub>1\<rangle> \<Longrightarrow> thesis"
  and "\<And>E va s. x = E \<Longrightarrow> y = Val va \<Longrightarrow> z = s \<Longrightarrow> u = Val va \<Longrightarrow> v = s \<Longrightarrow> thesis"
  and "\<And>E e\<^sub>1 s\<^sub>0 v\<^sub>1 s\<^sub>1 e\<^sub>2 v\<^sub>2 s\<^sub>2 bop va. x = E \<Longrightarrow> y = e\<^sub>1 \<guillemotleft>bop\<guillemotright> e\<^sub>2 \<Longrightarrow> z = s\<^sub>0 \<Longrightarrow>
    u = Val va \<Longrightarrow> v = s\<^sub>2 \<Longrightarrow> P,E \<turnstile> \<langle>e\<^sub>1,s\<^sub>0\<rangle> \<Rightarrow>' \<langle>Val v\<^sub>1,s\<^sub>1\<rangle> \<Longrightarrow>
    P,E \<turnstile> \<langle>e\<^sub>2,s\<^sub>1\<rangle> \<Rightarrow>' \<langle>Val v\<^sub>2,s\<^sub>2\<rangle> \<Longrightarrow> binop (bop, v\<^sub>1, v\<^sub>2) = \<lfloor>va\<rfloor> \<Longrightarrow> thesis"
  and "\<And>E e\<^sub>1 s\<^sub>0 e s\<^sub>1 bop e\<^sub>2. x = E \<Longrightarrow> y = e\<^sub>1 \<guillemotleft>bop\<guillemotright> e\<^sub>2 \<Longrightarrow> z = s\<^sub>0 \<Longrightarrow> u = throw e \<Longrightarrow> v = s\<^sub>1  \<Longrightarrow>
    P,E \<turnstile> \<langle>e\<^sub>1,s\<^sub>0\<rangle> \<Rightarrow>' \<langle>throw e,s\<^sub>1\<rangle> \<Longrightarrow> thesis"
  and "\<And>E e\<^sub>1 s\<^sub>0 v\<^sub>1 s\<^sub>1 e\<^sub>2 e s\<^sub>2 bop. x = E \<Longrightarrow> y = e\<^sub>1 \<guillemotleft>bop\<guillemotright> e\<^sub>2 \<Longrightarrow> z = s\<^sub>0 \<Longrightarrow> u = throw e \<Longrightarrow>
    v = s\<^sub>2 \<Longrightarrow> P,E \<turnstile> \<langle>e\<^sub>1,s\<^sub>0\<rangle> \<Rightarrow>' \<langle>Val v\<^sub>1,s\<^sub>1\<rangle> \<Longrightarrow> P,E \<turnstile> \<langle>e\<^sub>2,s\<^sub>1\<rangle> \<Rightarrow>' \<langle>throw e,s\<^sub>2\<rangle> \<Longrightarrow> thesis"
  and "\<And>l V va E h. x = E \<Longrightarrow> y = Var V \<Longrightarrow> z = (h, l) \<Longrightarrow> u = Val va \<Longrightarrow> v = (h, l) \<Longrightarrow>
    l V = \<lfloor>va\<rfloor> \<Longrightarrow> thesis"
  and "\<And>E e s\<^sub>0 va h l V T v' l'. x = E \<Longrightarrow> y = V:=e \<Longrightarrow> z = s\<^sub>0 \<Longrightarrow> u = Val v' \<Longrightarrow>
    v = (h, l') \<Longrightarrow> P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow>' \<langle>Val va,(h, l)\<rangle> \<Longrightarrow>
    E V = \<lfloor>T\<rfloor> \<Longrightarrow> P \<turnstile> T casts va to v'  \<Longrightarrow> l' = l(V \<mapsto> v') \<Longrightarrow> thesis"
  and "\<And>E e s\<^sub>0 e' s\<^sub>1 V. x = E \<Longrightarrow> y = V:=e \<Longrightarrow> z = s\<^sub>0 \<Longrightarrow> u = throw e' \<Longrightarrow> v = s\<^sub>1 \<Longrightarrow>
    P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow>' \<langle>throw e',s\<^sub>1\<rangle> \<Longrightarrow> thesis"
  and "\<And>E e s\<^sub>0 a Cs' h l D S Ds Cs fs F va. x = E \<Longrightarrow> y = e\<bullet>F{Cs} \<Longrightarrow> z = s\<^sub>0 \<Longrightarrow>
    u = Val va \<Longrightarrow> v = (h, l) \<Longrightarrow> P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow>' \<langle>ref (a, Cs'),(h, l)\<rangle> \<Longrightarrow>
    h a = \<lfloor>(D, S)\<rfloor> \<Longrightarrow> Ds = Cs' @\<^sub>p Cs \<Longrightarrow> (Ds, fs) \<in> S \<Longrightarrow> Mapping.lookup fs F = \<lfloor>va\<rfloor> \<Longrightarrow> thesis"
  and "\<And>E e s\<^sub>0 s\<^sub>1 F Cs. x = E \<Longrightarrow> y = e\<bullet>F{Cs} \<Longrightarrow> z = s\<^sub>0 \<Longrightarrow>
    u = Throw (addr_of_sys_xcpt NullPointer, [NullPointer]) \<Longrightarrow>
    v = s\<^sub>1 \<Longrightarrow> P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow>' \<langle>null,s\<^sub>1\<rangle> \<Longrightarrow> thesis"
  and "\<And>E e s\<^sub>0 e' s\<^sub>1 F Cs. x = E \<Longrightarrow> y = e\<bullet>F{Cs} \<Longrightarrow> z = s\<^sub>0 \<Longrightarrow> u = throw e' \<Longrightarrow> v = s\<^sub>1 \<Longrightarrow>
    P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow>' \<langle>throw e',s\<^sub>1\<rangle> \<Longrightarrow> thesis"
  and "\<And>E e\<^sub>1 s\<^sub>0 a Cs' s\<^sub>1 e\<^sub>2 va h\<^sub>2 l\<^sub>2 D S F T Cs v' Ds fs fs' S' h\<^sub>2'.
    x = E \<Longrightarrow> y = e\<^sub>1\<bullet>F{Cs} := e\<^sub>2 \<Longrightarrow> z = s\<^sub>0 \<Longrightarrow> u = Val v' \<Longrightarrow> v = (h\<^sub>2', l\<^sub>2) \<Longrightarrow>
    P,E \<turnstile> \<langle>e\<^sub>1,s\<^sub>0\<rangle> \<Rightarrow>' \<langle>ref (a, Cs'),s\<^sub>1\<rangle> \<Longrightarrow> P,E \<turnstile> \<langle>e\<^sub>2,s\<^sub>1\<rangle> \<Rightarrow>' \<langle>Val va,(h\<^sub>2, l\<^sub>2)\<rangle> \<Longrightarrow>
    h\<^sub>2 a = \<lfloor>(D, S)\<rfloor> \<Longrightarrow> P \<turnstile> last Cs' has least F:T via Cs \<Longrightarrow>
    P \<turnstile> T casts va to v'  \<Longrightarrow> Ds = Cs' @\<^sub>p Cs \<Longrightarrow> (Ds, fs) \<in> S \<Longrightarrow> fs' = Mapping.update F v' fs \<Longrightarrow>
    S' = S - {(Ds, fs)} \<union> {(Ds, fs')} \<Longrightarrow> h\<^sub>2' = h\<^sub>2(a \<mapsto> (D, S')) \<Longrightarrow> thesis"
  and "\<And>E e\<^sub>1 s\<^sub>0 s\<^sub>1 e\<^sub>2 va s\<^sub>2 F Cs. x = E \<Longrightarrow> y = e\<^sub>1\<bullet>F{Cs} := e\<^sub>2 \<Longrightarrow> z = s\<^sub>0 \<Longrightarrow>
    u = Throw (addr_of_sys_xcpt NullPointer, [NullPointer]) \<Longrightarrow>
    v = s\<^sub>2 \<Longrightarrow> P,E \<turnstile> \<langle>e\<^sub>1,s\<^sub>0\<rangle> \<Rightarrow>' \<langle>null,s\<^sub>1\<rangle> \<Longrightarrow> P,E \<turnstile> \<langle>e\<^sub>2,s\<^sub>1\<rangle> \<Rightarrow>' \<langle>Val va,s\<^sub>2\<rangle> \<Longrightarrow> thesis"
  and "\<And>E e\<^sub>1 s\<^sub>0 e' s\<^sub>1 F Cs e\<^sub>2. x = E \<Longrightarrow> y = e\<^sub>1\<bullet>F{Cs} := e\<^sub>2 \<Longrightarrow>
    z = s\<^sub>0 \<Longrightarrow> u = throw e' \<Longrightarrow> v = s\<^sub>1 \<Longrightarrow> P,E \<turnstile> \<langle>e\<^sub>1,s\<^sub>0\<rangle> \<Rightarrow>' \<langle>throw e',s\<^sub>1\<rangle> \<Longrightarrow> thesis"
  and "\<And>E e\<^sub>1 s\<^sub>0 va s\<^sub>1 e\<^sub>2 e' s\<^sub>2 F Cs. x = E \<Longrightarrow> y = e\<^sub>1\<bullet>F{Cs} := e\<^sub>2 \<Longrightarrow> z = s\<^sub>0 \<Longrightarrow>
    u = throw e' \<Longrightarrow> v = s\<^sub>2 \<Longrightarrow> P,E \<turnstile> \<langle>e\<^sub>1,s\<^sub>0\<rangle> \<Rightarrow>' \<langle>Val va,s\<^sub>1\<rangle> \<Longrightarrow> P,E \<turnstile> \<langle>e\<^sub>2,s\<^sub>1\<rangle> \<Rightarrow>' \<langle>throw e',s\<^sub>2\<rangle> \<Longrightarrow> 
    thesis"
  and "\<And>E e s\<^sub>0 e' s\<^sub>1 Copt M es. x = E \<Longrightarrow> y = Call e Copt M es \<Longrightarrow>
    z = s\<^sub>0 \<Longrightarrow> u = throw e' \<Longrightarrow> v = s\<^sub>1 \<Longrightarrow> P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow>' \<langle>throw e',s\<^sub>1\<rangle> \<Longrightarrow> thesis"
  and "\<And>E e s\<^sub>0 va s\<^sub>1 es vs ex es' s\<^sub>2 Copt M. x = E \<Longrightarrow> y = Call e Copt M es \<Longrightarrow>
    z = s\<^sub>0 \<Longrightarrow> u = throw ex \<Longrightarrow> v = s\<^sub>2 \<Longrightarrow> P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow>' \<langle>Val va,s\<^sub>1\<rangle> \<Longrightarrow>
    P,E \<turnstile> \<langle>es,s\<^sub>1\<rangle> [\<Rightarrow>'] \<langle>map Val vs @ throw ex # es',s\<^sub>2\<rangle> \<Longrightarrow> thesis"
  and "\<And>E e s\<^sub>0 a Cs s\<^sub>1 ps vs h\<^sub>2 l\<^sub>2 C S M Ts' T' pns' body' Ds Ts T pns body Cs' vs' l\<^sub>2' new_body e'
    h\<^sub>3 l\<^sub>3. x = E \<Longrightarrow> y = Call e None M ps \<Longrightarrow> z = s\<^sub>0 \<Longrightarrow> u = e' \<Longrightarrow> v = (h\<^sub>3, l\<^sub>2) \<Longrightarrow>
    P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow>' \<langle>ref (a, Cs),s\<^sub>1\<rangle> \<Longrightarrow> P,E \<turnstile> \<langle>ps,s\<^sub>1\<rangle> [\<Rightarrow>'] \<langle>map Val vs,(h\<^sub>2, l\<^sub>2)\<rangle> \<Longrightarrow>
    h\<^sub>2 a = \<lfloor>(C, S)\<rfloor> \<Longrightarrow> P \<turnstile> last Cs has least M = (Ts', T', pns', body') via Ds \<Longrightarrow>
    P \<turnstile> (C,Cs @\<^sub>p Ds) selects M = (Ts, T, pns, body) via Cs' \<Longrightarrow> length vs = length pns \<Longrightarrow>
    P \<turnstile> Ts Casts vs to vs'  \<Longrightarrow> l\<^sub>2' = [this \<mapsto> Ref (a, Cs'), pns [\<mapsto>] vs'] \<Longrightarrow>
    new_body = (case T' of Class D \<Rightarrow> \<lparr>D\<rparr>body | _ \<Rightarrow> body) \<Longrightarrow>
    P,E(this \<mapsto> Class (last Cs'), pns [\<mapsto>] Ts) \<turnstile> \<langle>new_body,(h\<^sub>2, l\<^sub>2')\<rangle> \<Rightarrow>' \<langle>e',(h\<^sub>3, l\<^sub>3)\<rangle> \<Longrightarrow>
    thesis"
  and "\<And>E e s\<^sub>0 a Cs s\<^sub>1 ps vs h\<^sub>2 l\<^sub>2 C Cs'' M Ts T pns body Cs' Ds vs' l\<^sub>2' e' h\<^sub>3 l\<^sub>3.
    x = E \<Longrightarrow> y = Call e \<lfloor>C\<rfloor> M ps \<Longrightarrow> z = s\<^sub>0 \<Longrightarrow> u = e' \<Longrightarrow> v = (h\<^sub>3, l\<^sub>2) \<Longrightarrow>
    P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow>' \<langle>ref (a, Cs),s\<^sub>1\<rangle> \<Longrightarrow> P,E \<turnstile> \<langle>ps,s\<^sub>1\<rangle> [\<Rightarrow>'] \<langle>map Val vs,(h\<^sub>2, l\<^sub>2)\<rangle> \<Longrightarrow>
    P \<turnstile> Path last Cs to C unique \<Longrightarrow> P \<turnstile> Path last Cs to C via Cs''  \<Longrightarrow>
    P \<turnstile> C has least M = (Ts, T, pns, body) via Cs' \<Longrightarrow> Ds = (Cs @\<^sub>p Cs'') @\<^sub>p Cs' \<Longrightarrow>
    length vs = length pns \<Longrightarrow> P \<turnstile> Ts Casts vs to vs'  \<Longrightarrow>
    l\<^sub>2' = [this \<mapsto> Ref (a, Ds), pns [\<mapsto>] vs'] \<Longrightarrow>
    P,E(this \<mapsto> Class (last Ds), pns [\<mapsto>] Ts) \<turnstile> \<langle>body,(h\<^sub>2, l\<^sub>2')\<rangle> \<Rightarrow>' \<langle>e',(h\<^sub>3, l\<^sub>3)\<rangle> \<Longrightarrow>
    thesis"
  and "\<And>E e s\<^sub>0 s\<^sub>1 es vs s\<^sub>2 Copt M. x = E \<Longrightarrow> y = Call e Copt M es \<Longrightarrow> z = s\<^sub>0 \<Longrightarrow>
    u = Throw (addr_of_sys_xcpt NullPointer, [NullPointer]) \<Longrightarrow>
    v = s\<^sub>2 \<Longrightarrow> P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow>' \<langle>null,s\<^sub>1\<rangle> \<Longrightarrow> P,E \<turnstile> \<langle>es,s\<^sub>1\<rangle> [\<Rightarrow>'] \<langle>map Val vs,s\<^sub>2\<rangle> \<Longrightarrow> thesis"
  and "\<And>E V T e\<^sub>0 h\<^sub>0 l\<^sub>0 e\<^sub>1 h\<^sub>1 l\<^sub>1.
    x = E \<Longrightarrow> y = {V:T; e\<^sub>0} \<Longrightarrow> z = (h\<^sub>0, l\<^sub>0) \<Longrightarrow> u = e\<^sub>1 \<Longrightarrow>
    v = (h\<^sub>1, l\<^sub>1(V := l\<^sub>0 V)) \<Longrightarrow> P,E(V \<mapsto> T) \<turnstile> \<langle>e\<^sub>0,(h\<^sub>0, l\<^sub>0(V := None))\<rangle> \<Rightarrow>' \<langle>e\<^sub>1,(h\<^sub>1, l\<^sub>1)\<rangle> \<Longrightarrow> thesis"
  and "\<And>E e\<^sub>0 s\<^sub>0 va s\<^sub>1 e\<^sub>1 e\<^sub>2 s\<^sub>2. x = E \<Longrightarrow> y = e\<^sub>0;; e\<^sub>1 \<Longrightarrow> z = s\<^sub>0 \<Longrightarrow> u = e\<^sub>2 \<Longrightarrow>
    v = s\<^sub>2 \<Longrightarrow> P,E \<turnstile> \<langle>e\<^sub>0,s\<^sub>0\<rangle> \<Rightarrow>' \<langle>Val va,s\<^sub>1\<rangle> \<Longrightarrow> P,E \<turnstile> \<langle>e\<^sub>1,s\<^sub>1\<rangle> \<Rightarrow>' \<langle>e\<^sub>2,s\<^sub>2\<rangle> \<Longrightarrow> thesis"
  and "\<And>E e\<^sub>0 s\<^sub>0 e s\<^sub>1 e\<^sub>1. x = E \<Longrightarrow> y = e\<^sub>0;; e\<^sub>1 \<Longrightarrow> z = s\<^sub>0 \<Longrightarrow> u = throw e \<Longrightarrow> v = s\<^sub>1 \<Longrightarrow>
    P,E \<turnstile> \<langle>e\<^sub>0,s\<^sub>0\<rangle> \<Rightarrow>' \<langle>throw e,s\<^sub>1\<rangle> \<Longrightarrow> thesis"
  and "\<And>E e s\<^sub>0 s\<^sub>1 e\<^sub>1 e' s\<^sub>2 e\<^sub>2. x = E \<Longrightarrow> y = if (e) e\<^sub>1 else e\<^sub>2 \<Longrightarrow> z = s\<^sub>0 \<Longrightarrow> u = e' \<Longrightarrow>
    v = s\<^sub>2 \<Longrightarrow> P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow>' \<langle>true,s\<^sub>1\<rangle> \<Longrightarrow> P,E \<turnstile> \<langle>e\<^sub>1,s\<^sub>1\<rangle> \<Rightarrow>' \<langle>e',s\<^sub>2\<rangle> \<Longrightarrow> thesis"
  and "\<And>E e s\<^sub>0 s\<^sub>1 e\<^sub>2 e' s\<^sub>2 e\<^sub>1. x = E \<Longrightarrow> y = if (e) e\<^sub>1 else e\<^sub>2 \<Longrightarrow> z = s\<^sub>0 \<Longrightarrow>
    u = e' \<Longrightarrow> v = s\<^sub>2 \<Longrightarrow> P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow>' \<langle>false,s\<^sub>1\<rangle> \<Longrightarrow> P,E \<turnstile> \<langle>e\<^sub>2,s\<^sub>1\<rangle> \<Rightarrow>' \<langle>e',s\<^sub>2\<rangle> \<Longrightarrow> thesis"
  and "\<And>E e s\<^sub>0 e' s\<^sub>1 e\<^sub>1 e\<^sub>2. x = E \<Longrightarrow> y = if (e) e\<^sub>1 else e\<^sub>2 \<Longrightarrow>
    z = s\<^sub>0 \<Longrightarrow> u = throw e' \<Longrightarrow> v = s\<^sub>1 \<Longrightarrow> P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow>' \<langle>throw e',s\<^sub>1\<rangle> \<Longrightarrow> thesis"
  and "\<And>E e s\<^sub>0 s\<^sub>1 c. x = E \<Longrightarrow> y = while (e) c \<Longrightarrow> z = s\<^sub>0 \<Longrightarrow> u = unit \<Longrightarrow> v = s\<^sub>1 \<Longrightarrow>
    P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow>' \<langle>false,s\<^sub>1\<rangle> \<Longrightarrow> thesis"
  and "\<And>E e s\<^sub>0 s\<^sub>1 c v\<^sub>1 s\<^sub>2 e\<^sub>3 s\<^sub>3. x = E \<Longrightarrow> y = while (e) c \<Longrightarrow> z = s\<^sub>0 \<Longrightarrow> u = e\<^sub>3 \<Longrightarrow>
    v = s\<^sub>3 \<Longrightarrow> P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow>' \<langle>true,s\<^sub>1\<rangle> \<Longrightarrow> P,E \<turnstile> \<langle>c,s\<^sub>1\<rangle> \<Rightarrow>' \<langle>Val v\<^sub>1,s\<^sub>2\<rangle> \<Longrightarrow>
    P,E \<turnstile> \<langle>while (e) c,s\<^sub>2\<rangle> \<Rightarrow>' \<langle>e\<^sub>3,s\<^sub>3\<rangle> \<Longrightarrow> thesis"
  and "\<And>E e s\<^sub>0 e' s\<^sub>1 c. x = E \<Longrightarrow> y = while (e) c \<Longrightarrow> z = s\<^sub>0 \<Longrightarrow> u = throw e' \<Longrightarrow> v = s\<^sub>1 \<Longrightarrow> 
    P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow>' \<langle>throw e',s\<^sub>1\<rangle> \<Longrightarrow> thesis"
  and "\<And>E e s\<^sub>0 s\<^sub>1 c e' s\<^sub>2. x = E \<Longrightarrow> y = while (e) c \<Longrightarrow> z = s\<^sub>0 \<Longrightarrow> u = throw e' \<Longrightarrow>
    v = s\<^sub>2 \<Longrightarrow> P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow>' \<langle>true,s\<^sub>1\<rangle> \<Longrightarrow> P,E \<turnstile> \<langle>c,s\<^sub>1\<rangle> \<Rightarrow>' \<langle>throw e',s\<^sub>2\<rangle> \<Longrightarrow> thesis"
  and "\<And>E e s\<^sub>0 r s\<^sub>1. x = E \<Longrightarrow> y = throw e \<Longrightarrow>
    z = s\<^sub>0 \<Longrightarrow> u = Throw r \<Longrightarrow> v = s\<^sub>1 \<Longrightarrow> P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow>' \<langle>ref r,s\<^sub>1\<rangle> \<Longrightarrow> thesis"
  and "\<And>E e s\<^sub>0 s\<^sub>1. x = E \<Longrightarrow> y = throw e \<Longrightarrow> z = s\<^sub>0 \<Longrightarrow>
    u = Throw (addr_of_sys_xcpt NullPointer, [NullPointer]) \<Longrightarrow>
    v = s\<^sub>1 \<Longrightarrow> P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow>' \<langle>null,s\<^sub>1\<rangle> \<Longrightarrow> thesis"
  and "\<And>E e s\<^sub>0 e' s\<^sub>1. x = E \<Longrightarrow> y = throw e \<Longrightarrow>
    z = s\<^sub>0 \<Longrightarrow> u = throw e' \<Longrightarrow> v = s\<^sub>1 \<Longrightarrow> P,E \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow>' \<langle>throw e',s\<^sub>1\<rangle> \<Longrightarrow> thesis"
  shows thesis
using assms
by(transfer)(erule eval.cases, unfold blank_def, assumption+)

lemmas [code_pred_intro] = New' NewFail' StaticUpCast'
declare StaticDownCast'_new[code_pred_intro StaticDownCast']
lemmas [code_pred_intro] = StaticCastNull'
declare StaticCastFail'_new[code_pred_intro StaticCastFail']
lemmas [code_pred_intro] = StaticCastThrow' StaticUpDynCast'
declare
  StaticDownDynCast'_new[code_pred_intro StaticDownDynCast']
  DynCast'[code_pred_intro DynCast']
lemmas [code_pred_intro] = DynCastNull'
declare DynCastFail'[code_pred_intro DynCastFail']
lemmas [code_pred_intro] = DynCastThrow' Val' BinOp' BinOpThrow1'
declare BinOpThrow2'[code_pred_intro BinOpThrow2']
lemmas [code_pred_intro] = Var' LAss' LAssThrow'
declare FAcc'_new[code_pred_intro FAcc']
lemmas [code_pred_intro] = FAccNull' FAccThrow'
declare FAss'_new[code_pred_intro FAss']
lemmas [code_pred_intro] = FAssNull' FAssThrow1'
declare FAssThrow2'[code_pred_intro FAssThrow2']
lemmas [code_pred_intro] = CallObjThrow'
declare
  CallParamsThrow'_new[code_pred_intro CallParamsThrow']
  Call'_new[code_pred_intro Call']
  StaticCall'_new[code_pred_intro StaticCall']
  CallNull'_new[code_pred_intro CallNull']
lemmas [code_pred_intro] = Block' Seq'
declare SeqThrow'[code_pred_intro SeqThrow']
lemmas [code_pred_intro] = CondT'
declare 
  CondF'[code_pred_intro CondF']
  CondThrow'[code_pred_intro CondThrow']
lemmas [code_pred_intro] = WhileF' WhileT'
declare
  WhileCondThrow'[code_pred_intro WhileCondThrow']
  WhileBodyThrow'[code_pred_intro WhileBodyThrow']
lemmas [code_pred_intro] = Throw'
declare ThrowNull'[code_pred_intro ThrowNull']
lemmas [code_pred_intro] = ThrowThrow'
lemmas [code_pred_intro] = Nil' Cons' ConsThrow'

code_pred 
  (modes: eval': i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> bool as big_step
   and evals': i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> bool as big_steps)
  eval'
proof -
  case eval'
  from eval'.prems show thesis
  proof(cases (no_simp) rule: eval'_cases)
    case (StaticDownCast E C e s\<^sub>0 a Cs Cs' s\<^sub>1)
    moreover
    have "app a [Cs] (a @ [Cs])" "app (a @ [Cs]) Cs' (a @ [Cs] @ Cs')"
      by(simp_all add: app_eq)
    ultimately show ?thesis by(rule eval'.StaticDownCast'[OF refl])
  next
    case StaticCastFail thus ?thesis
      unfolding rtrancl_def subcls1_def mem_Collect_eq prod.case
      by(rule eval'.StaticCastFail'[OF refl])
  next
    case (StaticDownDynCast E e s\<^sub>0 a Cs C Cs' s\<^sub>1)
    moreover have "app Cs [C] (Cs @ [C])" "app (Cs @ [C]) Cs' (Cs @ [C] @ Cs')"
      by(simp_all add: app_eq)
    ultimately show thesis by(rule eval'.StaticDownDynCast'[OF refl])
  next
    case DynCast thus ?thesis by(rule eval'.DynCast'[OF refl])
  next
    case DynCastFail thus ?thesis by(rule eval'.DynCastFail'[OF refl])
  next
    case BinOpThrow2 thus ?thesis by(rule eval'.BinOpThrow2'[OF refl])
  next
    case FAcc thus ?thesis
      by(rule eval'.FAcc'[OF refl, unfolded Predicate_Compile.contains_def Set_project_def mem_Collect_eq])
  next
    case FAss thus ?thesis
      by(rule eval'.FAss'[OF refl, unfolded Predicate_Compile.contains_def Set_project_def mem_Collect_eq])
  next
    case FAssThrow2 thus ?thesis by(rule eval'.FAssThrow2'[OF refl])
  next
    case (CallParamsThrow E e s\<^sub>0 v s\<^sub>1 es vs ex es' s\<^sub>2 Copt M)
    moreover have "map_val2 (map Val vs @ throw ex # es') vs (throw ex # es')"
      by(simp add: map_val2_conv[symmetric])
    ultimately show ?thesis by(rule eval'.CallParamsThrow'[OF refl])
  next
    case (Call E e s\<^sub>0 a Cs s\<^sub>1 ps vs)
    moreover have "map_val (map Val vs) vs" by(simp add: map_val_conv[symmetric])
    ultimately show ?thesis by-(rule eval'.Call'[OF refl])
  next
    case (StaticCall E e s\<^sub>0 a Cs s\<^sub>1 ps vs)
    moreover have "map_val (map Val vs) vs" by(simp add: map_val_conv[symmetric])
    ultimately show ?thesis by-(rule eval'.StaticCall'[OF refl])
  next
    case (CallNull E e s\<^sub>0 s\<^sub>1 es vs)
    moreover have "map_val (map Val vs) vs" by(simp add: map_val_conv[symmetric])
    ultimately show ?thesis by-(rule eval'.CallNull'[OF refl])
  next
    case SeqThrow thus ?thesis by(rule eval'.SeqThrow'[OF refl])
  next
    case CondF thus ?thesis by(rule eval'.CondF'[OF refl])
  next
    case CondThrow thus ?thesis by(rule eval'.CondThrow'[OF refl])
  next
    case WhileCondThrow thus ?thesis by(rule eval'.WhileCondThrow'[OF refl])
  next
    case WhileBodyThrow thus ?thesis by(rule eval'.WhileBodyThrow'[OF refl])
  next
    case ThrowNull thus ?thesis by(rule eval'.ThrowNull'[OF refl])
  qed(assumption|erule (4) eval'.that[OF refl])+
next
  case evals'
  from evals'.prems evals'.that[OF refl]
  show thesis by transfer(erule evals.cases)
qed

subsection \<open>Examples\<close>

declare [[values_timeout = 180]]

values [expected "{Val (Intg 5)}"]
  "{fst (e', s') | e' s'. 
    [],Map.empty \<turnstile> \<langle>{''V'':Integer; ''V'' :=  Val(Intg 5);; Var ''V''},(Map.empty,Map.empty)\<rangle> \<Rightarrow>' \<langle>e', s'\<rangle>}"

values [expected "{Val (Intg 11)}"]
  "{fst (e', s') | e' s'. 
    [],Map.empty \<turnstile> \<langle>(Val(Intg 5)) \<guillemotleft>Add\<guillemotright> (Val(Intg 6)),(Map.empty,Map.empty)\<rangle> \<Rightarrow>' \<langle>e', s'\<rangle>}"

values [expected "{Val (Intg 83)}"]
  "{fst (e', s') | e' s'. 
    [],[''V''\<mapsto>Integer] \<turnstile> \<langle>(Var ''V'') \<guillemotleft>Add\<guillemotright> (Val(Intg 6)),
                                       (Map.empty,[''V''\<mapsto>Intg 77])\<rangle> \<Rightarrow>' \<langle>e', s'\<rangle>}"

values [expected "{Some (Intg 6)}"]
  "{lcl' (snd (e', s')) ''V''  | e' s'. 
    [],[''V''\<mapsto>Integer] \<turnstile> \<langle>''V'' := Val(Intg 6),(Map.empty,Map.empty)\<rangle> \<Rightarrow>' \<langle>e', s'\<rangle>}"

values [expected "{Some (Intg 12)}"]
  "{lcl' (snd (e', s')) ''mult''  | e' s'. 
    [],[''V''\<mapsto>Integer,''a''\<mapsto>Integer,''b''\<mapsto>Integer,''mult''\<mapsto>Integer]
    \<turnstile> \<langle>(''a'' := Val(Intg 3));;(''b'' := Val(Intg 4));;(''mult'' := Val(Intg 0));;
       (''V'' := Val(Intg 1));;
       while (Var ''V'' \<guillemotleft>Eq\<guillemotright> Val(Intg 1))((''mult'' := Var ''mult'' \<guillemotleft>Add\<guillemotright> Var ''b'');;
         (''a'' := Var ''a'' \<guillemotleft>Add\<guillemotright> Val(Intg (- 1)));;
         (''V'' := (if(Var ''a'' \<guillemotleft>Eq\<guillemotright> Val(Intg 0)) Val(Intg 0) else Val(Intg 1)))),
       (Map.empty,Map.empty)\<rangle> \<Rightarrow>' \<langle>e', s'\<rangle>}"

values [expected "{Val (Intg 30)}"]
  "{fst (e', s') | e' s'. 
    [],[''a''\<mapsto>Integer, ''b''\<mapsto>Integer, ''c''\<mapsto> Integer, ''cond''\<mapsto>Boolean]
    \<turnstile> \<langle>''a'' := Val(Intg 17);; ''b'' := Val(Intg 13);; 
       ''c'' := Val(Intg 42);; ''cond'' := true;; 
       if (Var ''cond'') (Var ''a'' \<guillemotleft>Add\<guillemotright> Var ''b'') else (Var ''a'' \<guillemotleft>Add\<guillemotright> Var ''c''),
       (Map.empty,Map.empty)\<rangle> \<Rightarrow>' \<langle>e',s'\<rangle>}"


text \<open>progOverrider examples\<close>

definition
  classBottom :: "cdecl" where
  "classBottom = (''Bottom'', [Repeats ''Left'', Repeats ''Right''],
                   [(''x'',Integer)],[])" 

definition
  classLeft :: "cdecl" where
  "classLeft = (''Left'', [Repeats ''Top''],[],[(''f'', [Class ''Top'', Integer],Integer, [''V'',''W''],Var this \<bullet> ''x'' {[''Left'',''Top'']} \<guillemotleft>Add\<guillemotright> Val (Intg 5))])"

definition
  classRight :: "cdecl" where
  "classRight = (''Right'', [Shares ''Right2''],[],
    [(''f'', [Class ''Top'', Integer], Integer,[''V'',''W''],Var this \<bullet> ''x'' {[''Right2'',''Top'']} \<guillemotleft>Add\<guillemotright> Val (Intg 7)),(''g'',[],Class ''Left'',[],new ''Left'')])"

definition
  classRight2 :: "cdecl" where
  "classRight2 = (''Right2'', [Repeats ''Top''],[],
    [(''f'', [Class ''Top'', Integer], Integer,[''V'',''W''],Var this \<bullet> ''x'' {[''Right2'',''Top'']} \<guillemotleft>Add\<guillemotright> Val (Intg 9)),(''g'',[],Class ''Top'',[],new ''Top'')])"

definition
  classTop :: "cdecl" where
  "classTop = (''Top'', [], [(''x'',Integer)],[])"

definition
  progOverrider :: "cdecl list" where
  "progOverrider = [classBottom, classLeft, classRight, classRight2, classTop]"

values [expected "{Val(Ref(0,[''Bottom'',''Left'']))}"] \<comment> \<open>dynCastSide\<close>
  "{fst (e', s') | e' s'. 
    progOverrider,[''V''\<mapsto>Class ''Right''] \<turnstile>
    \<langle>''V'' := new ''Bottom'' ;; Cast ''Left'' (Var ''V''),(Map.empty,Map.empty)\<rangle> \<Rightarrow>' \<langle>e', s'\<rangle>}"

values [expected "{Val(Ref(0,[''Right'']))}"] \<comment> \<open>dynCastViaSh\<close>
  "{fst (e', s') | e' s'. 
    progOverrider,[''V''\<mapsto>Class ''Right2''] \<turnstile> 
    \<langle>''V'' := new ''Right'' ;; Cast ''Right'' (Var ''V''),(Map.empty,Map.empty)\<rangle> \<Rightarrow>' \<langle>e', s'\<rangle>}"

values [expected "{Val (Intg 42)}"] \<comment> \<open>block\<close>
  "{fst (e', s') | e' s'. 
    progOverrider,[''V''\<mapsto>Integer] 
    \<turnstile> \<langle>''V'' := Val(Intg 42) ;; {''V'':Class ''Left''; ''V'' := new ''Bottom''} ;; Var ''V'',
      (Map.empty,Map.empty)\<rangle> \<Rightarrow>' \<langle>e', s'\<rangle>}"

values [expected "{Val (Intg 8)}"] \<comment> \<open>staticCall\<close>
  "{fst (e', s') | e' s'. 
    progOverrider,[''V''\<mapsto>Class ''Right'',''W''\<mapsto>Class ''Bottom''] 
    \<turnstile> \<langle>''V'' := new ''Bottom'' ;; ''W'' := new ''Bottom'' ;; 
       ((Cast ''Left'' (Var ''W''))\<bullet>''x''{[''Left'',''Top'']} := Val(Intg 3));;
       (Var ''W''\<bullet>(''Left''::)''f''([Var ''V'',Val(Intg 2)])),(Map.empty,Map.empty)\<rangle> \<Rightarrow>' \<langle>e', s'\<rangle>}"

values [expected "{Val (Intg 12)}"] \<comment> \<open>call\<close>
  "{fst (e', s') | e' s'. 
    progOverrider,[''V''\<mapsto>Class ''Right2'',''W''\<mapsto>Class ''Left''] 
    \<turnstile> \<langle>''V'' := new ''Right'' ;; ''W'' := new ''Left'' ;; 
       (Var ''V''\<bullet>''f''([Var ''W'',Val(Intg 42)])) \<guillemotleft>Add\<guillemotright> (Var ''W''\<bullet>''f''([Var ''V'',Val(Intg 13)])),
       (Map.empty,Map.empty)\<rangle> \<Rightarrow>' \<langle>e', s'\<rangle>}"

values [expected "{Val(Intg 13)}"] \<comment> \<open>callOverrider\<close>
  "{fst (e', s') | e' s'. 
    progOverrider,[''V''\<mapsto>Class ''Right2'',''W''\<mapsto>Class ''Left''] 
    \<turnstile> \<langle>''V'' := new ''Bottom'';; (Var ''V'' \<bullet> ''x'' {[''Right2'',''Top'']} := Val(Intg 6));; 
       ''W'' := new ''Left'' ;; Var ''V''\<bullet>''f''([Var ''W'',Val(Intg 42)]),
       (Map.empty,Map.empty)\<rangle> \<Rightarrow>' \<langle>e', s'\<rangle>}"

values [expected "{Val(Ref(1,[''Left'',''Top'']))}"] \<comment> \<open>callClass\<close>
  "{fst (e', s') | e' s'. 
    progOverrider,[''V''\<mapsto>Class ''Right2''] 
    \<turnstile> \<langle>''V'' := new ''Right'' ;; Var ''V''\<bullet>''g''([]),(Map.empty,Map.empty)\<rangle> \<Rightarrow>' \<langle>e', s'\<rangle>}"

values [expected "{Val(Intg 42)}"] \<comment> \<open>fieldAss\<close>
  "{fst (e', s') | e' s'. 
    progOverrider,[''V''\<mapsto>Class ''Right2''] 
    \<turnstile> \<langle>''V'' := new ''Right'' ;; 
       (Var ''V''\<bullet>''x''{[''Right2'',''Top'']} := (Val(Intg 42))) ;; 
       (Var ''V''\<bullet>''x''{[''Right2'',''Top'']}),(Map.empty,Map.empty)\<rangle> \<Rightarrow>' \<langle>e', s'\<rangle>}"


text \<open>typing rules\<close>

values [expected "{Class ''Bottom''}"] \<comment> \<open>typeNew\<close>
  "{T. progOverrider,Map.empty \<turnstile> new ''Bottom'' :: T}"

values [expected "{Class ''Left''}"] \<comment> \<open>typeDynCast\<close>
  "{T. progOverrider,Map.empty \<turnstile> Cast ''Left'' (new ''Bottom'') :: T}"

values [expected "{Class ''Left''}"] \<comment> \<open>typeStaticCast\<close>
  "{T. progOverrider,Map.empty \<turnstile> \<lparr>''Left''\<rparr> (new ''Bottom'') :: T}"

values [expected "{Integer}"] \<comment> \<open>typeVal\<close>
  "{T. [],Map.empty \<turnstile> Val(Intg 17) :: T}"

values [expected "{Integer}"] \<comment> \<open>typeVar\<close>
  "{T. [],[''V'' \<mapsto> Integer] \<turnstile> Var ''V'' :: T}"

values [expected "{Boolean}"] \<comment> \<open>typeBinOp\<close>
  "{T. [],Map.empty \<turnstile> (Val(Intg 5)) \<guillemotleft>Eq\<guillemotright> (Val(Intg 6)) :: T}"

values [expected "{Class ''Top''}"] \<comment> \<open>typeLAss\<close>
  "{T. progOverrider,[''V'' \<mapsto> Class ''Top''] \<turnstile> ''V'' := (new ''Left'') :: T}"

values [expected "{Integer}"] \<comment> \<open>typeFAcc\<close>
  "{T. progOverrider,Map.empty \<turnstile> (new ''Right'')\<bullet>''x''{[''Right2'',''Top'']} :: T}"

values [expected "{Integer}"] \<comment> \<open>typeFAss\<close>
  "{T. progOverrider,Map.empty \<turnstile> (new ''Right'')\<bullet>''x''{[''Right2'',''Top'']} :: T}"

values [expected "{Integer}"] \<comment> \<open>typeStaticCall\<close>
  "{T. progOverrider,[''V''\<mapsto>Class ''Left''] 
       \<turnstile> ''V'' := new ''Left'' ;; Var ''V''\<bullet>(''Left''::)''f''([new ''Top'', Val(Intg 13)]) :: T}"

values [expected "{Class ''Top''}"] \<comment> \<open>typeCall\<close>
  "{T. progOverrider,[''V''\<mapsto>Class ''Right2''] 
       \<turnstile> ''V'' := new ''Right'' ;; Var ''V''\<bullet>''g''([]) :: T}"

values [expected "{Class ''Top''}"] \<comment> \<open>typeBlock\<close>
  "{T. progOverrider,Map.empty \<turnstile> {''V'':Class ''Top''; ''V'' := new ''Left''} :: T}"

values [expected "{Integer}"] \<comment> \<open>typeCond\<close>
  "{T. [],Map.empty \<turnstile> if (true) Val(Intg 6) else Val(Intg 9) :: T}"

values [expected "{Void}"] \<comment> \<open>typeWhile\<close>
  "{T. [],Map.empty \<turnstile> while (false) Val(Intg 17) :: T}"

values [expected "{Void}"] \<comment> \<open>typeThrow\<close>
  "{T. progOverrider,Map.empty \<turnstile> throw (new ''Bottom'') :: T}"

values [expected "{Integer}"] \<comment> \<open>typeBig\<close>
  "{T. progOverrider,[''V''\<mapsto>Class ''Right2'',''W''\<mapsto>Class ''Left''] 
       \<turnstile> ''V'' := new ''Right'' ;; ''W'' := new ''Left'' ;; 
         (Var ''V''\<bullet>''f''([Var ''W'', Val(Intg 7)])) \<guillemotleft>Add\<guillemotright> (Var ''W''\<bullet>''f''([Var ''V'', Val(Intg 13)])) 
       :: T}"


text \<open>progDiamond examples\<close>

definition
  classDiamondBottom :: "cdecl" where
  "classDiamondBottom = (''Bottom'', [Repeats ''Left'', Repeats ''Right''],[(''x'',Integer)],
    [(''g'', [],Integer, [],Var this \<bullet> ''x'' {[''Bottom'']} \<guillemotleft>Add\<guillemotright> Val (Intg 5))])" 

definition
  classDiamondLeft :: "cdecl" where
  "classDiamondLeft = (''Left'', [Repeats ''TopRep'',Shares ''TopSh''],[],[])"

definition
  classDiamondRight :: "cdecl" where
  "classDiamondRight = (''Right'', [Repeats ''TopRep'',Shares ''TopSh''],[],
    [(''f'', [Integer], Boolean,[''i''], Var ''i'' \<guillemotleft>Eq\<guillemotright> Val (Intg 7))])"

definition
  classDiamondTopRep :: "cdecl" where
  "classDiamondTopRep = (''TopRep'', [], [(''x'',Integer)],
    [(''g'', [],Integer, [], Var this \<bullet> ''x'' {[''TopRep'']} \<guillemotleft>Add\<guillemotright> Val (Intg 10))])"

definition
  classDiamondTopSh :: "cdecl" where
  "classDiamondTopSh = (''TopSh'', [], [], 
    [(''f'', [Integer], Boolean,[''i''], Var ''i'' \<guillemotleft>Eq\<guillemotright> Val (Intg 3))])"

definition
  progDiamond :: "cdecl list" where
  "progDiamond = [classDiamondBottom, classDiamondLeft, classDiamondRight, classDiamondTopRep, classDiamondTopSh]"

values [expected "{Val(Ref(0,[''Bottom'',''Left'']))}"] \<comment> \<open>cast1\<close>
  "{fst (e', s') | e' s'. 
    progDiamond,[''V''\<mapsto>Class ''Left''] \<turnstile> \<langle>''V'' := new ''Bottom'',
                                                      (Map.empty,Map.empty)\<rangle> \<Rightarrow>' \<langle>e', s'\<rangle>}"

values [expected "{Val(Ref(0,[''TopSh'']))}"] \<comment> \<open>cast2\<close>
  "{fst (e', s') | e' s'. 
    progDiamond,[''V''\<mapsto>Class ''TopSh''] \<turnstile> \<langle>''V'' := new ''Bottom'',
                                                      (Map.empty,Map.empty)\<rangle> \<Rightarrow>' \<langle>e', s'\<rangle>}"

values [expected "{}"] \<comment> \<open>typeCast3 not typeable\<close>
  "{T. progDiamond,[''V''\<mapsto>Class ''TopRep''] \<turnstile> ''V'' := new ''Bottom'' :: T}"

values [expected "{
   Val(Ref(0,[''Bottom'', ''Left'', ''TopRep''])), 
   Val(Ref(0,[''Bottom'', ''Right'', ''TopRep'']))
  }"] \<comment> \<open>cast3\<close>
  "{fst (e', s') | e' s'. 
    progDiamond,[''V''\<mapsto>Class ''TopRep''] \<turnstile> \<langle>''V'' := new ''Bottom'', 
                                                      (Map.empty,Map.empty)\<rangle> \<Rightarrow>' \<langle>e', s'\<rangle>}"

values [expected "{Val(Intg 17)}"] \<comment> \<open>fieldAss\<close>
  "{fst (e', s') | e' s'. 
    progDiamond,[''V''\<mapsto>Class ''Bottom''] 
    \<turnstile> \<langle>''V'' := new ''Bottom'' ;; 
       ((Var ''V'')\<bullet>''x''{[''Bottom'']} := (Val(Intg 17))) ;; 
       ((Var ''V'')\<bullet>''x''{[''Bottom'']}),(Map.empty,Map.empty)\<rangle> \<Rightarrow>' \<langle>e',s'\<rangle>}"

values [expected "{Val Null}"] \<comment> \<open>dynCastNull\<close>
  "{fst (e', s') | e' s'. 
    progDiamond,Map.empty \<turnstile> \<langle>Cast ''Right'' null,(Map.empty,Map.empty)\<rangle> \<Rightarrow>' \<langle>e',s'\<rangle>}"

values [expected "{Val (Ref(0, [''Right'']))}"] \<comment> \<open>dynCastViaSh\<close>
  "{fst (e', s') | e' s'. 
    progDiamond,[''V''\<mapsto>Class ''TopSh''] 
    \<turnstile> \<langle>''V'' := new ''Right'' ;; Cast ''Right'' (Var ''V''),(Map.empty,Map.empty)\<rangle> \<Rightarrow>' \<langle>e',s'\<rangle>}"

values [expected "{Val Null}"] \<comment> \<open>dynCastFail\<close>
  "{fst (e', s') | e' s'. 
    progDiamond,[''V''\<mapsto>Class ''TopRep''] 
    \<turnstile> \<langle>''V'' := new ''Right'' ;; Cast ''Bottom'' (Var ''V''),(Map.empty,Map.empty)\<rangle> \<Rightarrow>' \<langle>e',s'\<rangle>}"

values [expected "{Val (Ref(0, [''Bottom'', ''Left'']))}"] \<comment> \<open>dynCastSide\<close>
  "{fst (e', s') | e' s'. 
    progDiamond,[''V''\<mapsto>Class ''Right'']
    \<turnstile> \<langle>''V'' := new ''Bottom'' ;; Cast ''Left'' (Var ''V''),(Map.empty,Map.empty)\<rangle> \<Rightarrow>' \<langle>e',s'\<rangle>}"

text \<open>failing g++ example\<close>

definition
  classD :: "cdecl" where
  "classD = (''D'', [Shares ''A'', Shares ''B'', Repeats ''C''],[],[])"

definition
  classC :: "cdecl" where
  "classC = (''C'', [Shares ''A'', Shares ''B''],[],
              [(''f'',[],Integer,[],Val(Intg 42))])"

definition
  classB :: "cdecl" where
  "classB = (''B'', [],[],
              [(''f'',[],Integer,[],Val(Intg 17))])"

definition
  classA :: "cdecl" where
  "classA = (''A'', [],[],
              [(''f'',[],Integer,[],Val(Intg 13))])"

definition
  ProgFailing :: "cdecl list" where
  "ProgFailing = [classA,classB,classC,classD]"

values [expected "{Val (Intg 42)}"] \<comment> \<open>callFailGplusplus\<close>
  "{fst (e', s') | e' s'. 
    ProgFailing,Map.empty 
    \<turnstile> \<langle>{''V'':Class ''D''; ''V'' := new ''D'';; Var ''V''\<bullet>''f''([])},
       (Map.empty,Map.empty)\<rangle> \<Rightarrow>' \<langle>e', s'\<rangle>}"

end

