(*  Title:      Jinja/J/WellTypeRT.thy

    Author:     Tobias Nipkow
    Copyright   2003 Technische Universitaet Muenchen
*)

section \<open>Runtime Well-typedness\<close>

theory WellTypeRT
imports WellType
begin

inductive
  WTrt :: "J_prog \<Rightarrow> heap \<Rightarrow> env \<Rightarrow> expr \<Rightarrow> ty \<Rightarrow> bool"
  and WTrts :: "J_prog \<Rightarrow> heap \<Rightarrow> env \<Rightarrow> expr list \<Rightarrow> ty list \<Rightarrow> bool"
  and WTrt2 :: "[J_prog,env,heap,expr,ty] \<Rightarrow> bool"
        ("_,_,_ \<turnstile> _ : _"   [51,51,51]50)
  and WTrts2 :: "[J_prog,env,heap,expr list, ty list] \<Rightarrow> bool"
        ("_,_,_ \<turnstile> _ [:] _" [51,51,51]50)
  for P :: J_prog and h :: heap
where
  
  "P,E,h \<turnstile> e : T \<equiv> WTrt P h E e T"
| "P,E,h \<turnstile> es[:]Ts \<equiv> WTrts P h E es Ts"

| WTrtNew:
  "is_class P C  \<Longrightarrow>
  P,E,h \<turnstile> new C : Class C"

| WTrtCast:
  "\<lbrakk> P,E,h \<turnstile> e : T; is_refT T; is_class P C \<rbrakk>
  \<Longrightarrow> P,E,h \<turnstile> Cast C e : Class C"

| WTrtVal:
  "typeof\<^bsub>h\<^esub> v = Some T \<Longrightarrow>
  P,E,h \<turnstile> Val v : T"

| WTrtVar:
  "E V = Some T  \<Longrightarrow>
  P,E,h \<turnstile> Var V : T"
(*
WTrtBinOp:
  "\<lbrakk> P,E,h \<turnstile> e\<^sub>1 : T\<^sub>1;  P,E,h \<turnstile> e\<^sub>2 : T\<^sub>2;
    case bop of Eq \<Rightarrow> T = Boolean
              | Add \<Rightarrow> T\<^sub>1 = Integer \<and> T\<^sub>2 = Integer \<and> T = Integer \<rbrakk>
   \<Longrightarrow> P,E,h \<turnstile> e\<^sub>1 \<guillemotleft>bop\<guillemotright> e\<^sub>2 : T"
*)
| WTrtBinOpEq:
  "\<lbrakk> P,E,h \<turnstile> e\<^sub>1 : T\<^sub>1;  P,E,h \<turnstile> e\<^sub>2 : T\<^sub>2 \<rbrakk>
  \<Longrightarrow> P,E,h \<turnstile> e\<^sub>1 \<guillemotleft>Eq\<guillemotright> e\<^sub>2 : Boolean"

| WTrtBinOpAdd:
  "\<lbrakk> P,E,h \<turnstile> e\<^sub>1 : Integer;  P,E,h \<turnstile> e\<^sub>2 : Integer \<rbrakk>
  \<Longrightarrow> P,E,h \<turnstile> e\<^sub>1 \<guillemotleft>Add\<guillemotright> e\<^sub>2 : Integer"

| WTrtLAss:
  "\<lbrakk> E V = Some T;  P,E,h \<turnstile> e : T';  P \<turnstile> T' \<le> T \<rbrakk>
   \<Longrightarrow> P,E,h \<turnstile> V:=e : Void"

| WTrtFAcc:
  "\<lbrakk> P,E,h \<turnstile> e : Class C; P \<turnstile> C has F:T in D \<rbrakk> \<Longrightarrow>
  P,E,h \<turnstile> e\<bullet>F{D} : T"

| WTrtFAccNT:
  "P,E,h \<turnstile> e : NT \<Longrightarrow>
  P,E,h \<turnstile> e\<bullet>F{D} : T"

| WTrtFAss:
  "\<lbrakk> P,E,h \<turnstile> e\<^sub>1 : Class C;  P \<turnstile> C has F:T in D; P,E,h \<turnstile> e\<^sub>2 : T\<^sub>2;  P \<turnstile> T\<^sub>2 \<le> T \<rbrakk>
  \<Longrightarrow> P,E,h \<turnstile> e\<^sub>1\<bullet>F{D}:=e\<^sub>2 : Void"

| WTrtFAssNT:
  "\<lbrakk> P,E,h \<turnstile> e\<^sub>1:NT; P,E,h \<turnstile> e\<^sub>2 : T\<^sub>2 \<rbrakk>
  \<Longrightarrow> P,E,h \<turnstile> e\<^sub>1\<bullet>F{D}:=e\<^sub>2 : Void"

| WTrtCall:
  "\<lbrakk> P,E,h \<turnstile> e : Class C; P \<turnstile> C sees M:Ts \<rightarrow> T = (pns,body) in D;
     P,E,h \<turnstile> es [:] Ts'; P \<turnstile> Ts' [\<le>] Ts \<rbrakk>
  \<Longrightarrow> P,E,h \<turnstile> e\<bullet>M(es) : T"

| WTrtCallNT:
  "\<lbrakk> P,E,h \<turnstile> e : NT; P,E,h \<turnstile> es [:] Ts \<rbrakk>
  \<Longrightarrow> P,E,h \<turnstile> e\<bullet>M(es) : T"

| WTrtBlock:
  "P,E(V\<mapsto>T),h \<turnstile> e : T'  \<Longrightarrow>
  P,E,h \<turnstile> {V:T; e} : T'"

| WTrtSeq:
  "\<lbrakk> P,E,h \<turnstile> e\<^sub>1:T\<^sub>1;  P,E,h \<turnstile> e\<^sub>2:T\<^sub>2 \<rbrakk>
  \<Longrightarrow> P,E,h \<turnstile> e\<^sub>1;;e\<^sub>2 : T\<^sub>2"

| WTrtCond:
  "\<lbrakk> P,E,h \<turnstile> e : Boolean;  P,E,h \<turnstile> e\<^sub>1:T\<^sub>1;  P,E,h \<turnstile> e\<^sub>2:T\<^sub>2;
     P \<turnstile> T\<^sub>1 \<le> T\<^sub>2 \<or> P \<turnstile> T\<^sub>2 \<le> T\<^sub>1; P \<turnstile> T\<^sub>1 \<le> T\<^sub>2 \<longrightarrow> T = T\<^sub>2; P \<turnstile> T\<^sub>2 \<le> T\<^sub>1 \<longrightarrow> T = T\<^sub>1 \<rbrakk>
  \<Longrightarrow> P,E,h \<turnstile> if (e) e\<^sub>1 else e\<^sub>2 : T"

| WTrtWhile:
  "\<lbrakk> P,E,h \<turnstile> e : Boolean;  P,E,h \<turnstile> c:T \<rbrakk>
  \<Longrightarrow>  P,E,h \<turnstile> while(e) c : Void"

| WTrtThrow:
  "\<lbrakk> P,E,h \<turnstile> e : T\<^sub>r; is_refT T\<^sub>r \<rbrakk> \<Longrightarrow>
  P,E,h \<turnstile> throw e : T"

| WTrtTry:
  "\<lbrakk> P,E,h \<turnstile> e\<^sub>1 : T\<^sub>1;  P,E(V \<mapsto> Class C),h \<turnstile> e\<^sub>2 : T\<^sub>2; P \<turnstile> T\<^sub>1 \<le> T\<^sub>2 \<rbrakk>
  \<Longrightarrow> P,E,h \<turnstile> try e\<^sub>1 catch(C V) e\<^sub>2 : T\<^sub>2"

\<comment> \<open>well-typed expression lists\<close>

| WTrtNil:
  "P,E,h \<turnstile> [] [:] []"

| WTrtCons:
  "\<lbrakk> P,E,h \<turnstile> e : T;  P,E,h \<turnstile> es [:] Ts \<rbrakk>
  \<Longrightarrow>  P,E,h \<turnstile> e#es [:] T#Ts"

(*<*)
declare WTrt_WTrts.intros[intro!] WTrtNil[iff]
declare
  WTrtFAcc[rule del] WTrtFAccNT[rule del]
  WTrtFAss[rule del] WTrtFAssNT[rule del]
  WTrtCall[rule del] WTrtCallNT[rule del]

lemmas WTrt_induct = WTrt_WTrts.induct [split_format (complete)]
  and WTrt_inducts = WTrt_WTrts.inducts [split_format (complete)]
(*>*)


subsection\<open>Easy consequences\<close>

lemma [iff]: "(P,E,h \<turnstile> [] [:] Ts) = (Ts = [])"
(*<*)
apply(rule iffI)
apply (auto elim: WTrts.cases)
done
(*>*)

lemma [iff]: "(P,E,h \<turnstile> e#es [:] T#Ts) = (P,E,h \<turnstile> e : T \<and> P,E,h \<turnstile> es [:] Ts)"
(*<*)
apply(rule iffI)
apply (auto elim: WTrts.cases)
done
(*>*)

lemma [iff]: "(P,E,h \<turnstile> (e#es) [:] Ts) =
  (\<exists>U Us. Ts = U#Us \<and> P,E,h \<turnstile> e : U \<and> P,E,h \<turnstile> es [:] Us)"
(*<*)
apply(rule iffI)
apply (auto elim: WTrts.cases)
done
(*>*)

lemma [simp]: "\<forall>Ts. (P,E,h \<turnstile> es\<^sub>1 @ es\<^sub>2 [:] Ts) =
  (\<exists>Ts\<^sub>1 Ts\<^sub>2. Ts = Ts\<^sub>1 @ Ts\<^sub>2 \<and> P,E,h \<turnstile> es\<^sub>1 [:] Ts\<^sub>1 & P,E,h \<turnstile> es\<^sub>2[:]Ts\<^sub>2)"
(*<*)
apply(induct_tac es\<^sub>1)
 apply simp
apply clarsimp
apply(erule thin_rl)
apply (rule iffI)
 apply clarsimp
 apply(rule exI)+
 apply(rule conjI)
  prefer 2 apply blast
 apply simp
apply fastforce
done
(*>*)

lemma [iff]: "P,E,h \<turnstile> Val v : T = (typeof\<^bsub>h\<^esub> v = Some T)"
(*<*)
apply(rule iffI)
apply (auto elim: WTrt.cases)
done
(*>*)

lemma [iff]: "P,E,h \<turnstile> Var v : T = (E v = Some T)"
(*<*)
apply(rule iffI)
apply (auto elim: WTrt.cases)
done
(*>*)

lemma [iff]: "P,E,h \<turnstile> e\<^sub>1;;e\<^sub>2 : T\<^sub>2 = (\<exists>T\<^sub>1. P,E,h \<turnstile> e\<^sub>1:T\<^sub>1 \<and> P,E,h \<turnstile> e\<^sub>2:T\<^sub>2)"
(*<*)
apply(rule iffI)
apply (auto elim: WTrt.cases)
done
(*>*)

lemma [iff]: "P,E,h \<turnstile> {V:T; e} : T'  =  (P,E(V\<mapsto>T),h \<turnstile> e : T')"
(*<*)
apply(rule iffI)
apply (auto elim: WTrt.cases)
done
(*>*)
(*<*)
inductive_cases WTrt_elim_cases[elim!]:
  "P,E,h \<turnstile> v :=e : T"
  "P,E,h \<turnstile> if (e) e\<^sub>1 else e\<^sub>2 : T"
  "P,E,h \<turnstile> while(e) c : T"
  "P,E,h \<turnstile> throw e : T"
  "P,E,h \<turnstile> try e\<^sub>1 catch(C V) e\<^sub>2 : T"
  "P,E,h \<turnstile> Cast D e : T"
  "P,E,h \<turnstile> e\<bullet>F{D} : T"
  "P,E,h \<turnstile> e\<bullet>F{D} := v : T"
  "P,E,h \<turnstile> e\<^sub>1 \<guillemotleft>bop\<guillemotright> e\<^sub>2 : T"
  "P,E,h \<turnstile> new C : T"
  "P,E,h \<turnstile> e\<bullet>M{D}(es) : T"
(*>*)

subsection\<open>Some interesting lemmas\<close>

lemma WTrts_Val[simp]:
 "\<And>Ts. (P,E,h \<turnstile> map Val vs [:] Ts) = (map (typeof\<^bsub>h\<^esub>) vs = map Some Ts)"
(*<*)
apply(induct vs)
 apply simp
apply(case_tac Ts)
 apply simp
apply simp
done
(*>*)


lemma WTrts_same_length: "\<And>Ts. P,E,h \<turnstile> es [:] Ts \<Longrightarrow> length es = length Ts"
(*<*)by(induct es type:list)auto(*>*)


lemma WTrt_env_mono:
  "P,E,h \<turnstile> e : T \<Longrightarrow> (\<And>E'. E \<subseteq>\<^sub>m E' \<Longrightarrow> P,E',h \<turnstile> e : T)" and
  "P,E,h \<turnstile> es [:] Ts \<Longrightarrow> (\<And>E'. E \<subseteq>\<^sub>m E' \<Longrightarrow> P,E',h \<turnstile> es [:] Ts)"
(*<*)
apply(induct rule: WTrt_inducts)
apply(simp add: WTrtNew)
apply(fastforce simp: WTrtCast)
apply(fastforce simp: WTrtVal)
apply(simp add: WTrtVar map_le_def dom_def)
apply(fastforce simp add: WTrtBinOpEq)
apply(fastforce simp add: WTrtBinOpAdd)
apply(force simp: map_le_def)
apply(fastforce simp: WTrtFAcc)
apply(simp add: WTrtFAccNT)
apply(fastforce simp: WTrtFAss)
apply(fastforce simp: WTrtFAssNT)
apply(fastforce simp: WTrtCall)
apply(fastforce simp: WTrtCallNT)
apply(simp add: WTrtNil)
apply(simp add: WTrtCons)
apply(fastforce simp: map_le_def)
apply(fastforce)
apply(fastforce simp: WTrtSeq)
apply(fastforce simp: WTrtWhile)
apply(fastforce simp: WTrtThrow)
apply(auto simp: WTrtTry map_le_def dom_def)
done
(*>*)


lemma WTrt_hext_mono: "P,E,h \<turnstile> e : T \<Longrightarrow> h \<unlhd> h' \<Longrightarrow> P,E,h' \<turnstile> e : T"
and WTrts_hext_mono: "P,E,h \<turnstile> es [:] Ts \<Longrightarrow> h \<unlhd> h' \<Longrightarrow> P,E,h' \<turnstile> es [:] Ts"
(*<*)
apply(induct rule: WTrt_inducts)
apply(simp add: WTrtNew)
apply(fastforce simp: WTrtCast)
apply(fastforce simp: WTrtVal dest:hext_typeof_mono)
apply(simp add: WTrtVar)
apply(fastforce simp add: WTrtBinOpEq)
apply(fastforce simp add: WTrtBinOpAdd)
apply(fastforce simp add: WTrtLAss)
apply(fast intro: WTrtFAcc)
apply(simp add: WTrtFAccNT)
apply(fastforce simp: WTrtFAss del:WTrt_WTrts.intros WTrt_elim_cases)
apply(fastforce simp: WTrtFAssNT)
apply(fastforce simp: WTrtCall)
apply(fastforce simp: WTrtCallNT)
apply(fastforce)
apply(fastforce simp add: WTrtSeq)
apply(fastforce simp add: WTrtCond)
apply(fastforce simp add: WTrtWhile)
apply(fastforce simp add: WTrtThrow)
apply(fastforce simp: WTrtTry)
apply(simp add: WTrtNil)
apply(simp add: WTrtCons)
done
(*>*)


lemma WT_implies_WTrt: "P,E \<turnstile> e :: T \<Longrightarrow> P,E,h \<turnstile> e : T"
and WTs_implies_WTrts: "P,E \<turnstile> es [::] Ts \<Longrightarrow> P,E,h \<turnstile> es [:] Ts"
(*<*)
apply(induct rule: WT_WTs_inducts)
apply fast
apply (fast)
apply(fastforce dest:typeof_lit_typeof)
apply(simp)
apply(fastforce)
apply(fastforce)
apply(fastforce)
apply(fastforce simp: WTrtFAcc has_visible_field)
apply(fastforce simp: WTrtFAss dest: has_visible_field)
apply(fastforce simp: WTrtCall)
apply(fastforce)
apply(fastforce)
apply(fastforce simp: WTrtCond)
apply(fastforce)
apply(fastforce)
apply(fastforce)
apply(simp)
apply(simp)
done
(*>*)


end
