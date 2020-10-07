(*  Title:      JinjaThreads/J/WellTypeRT.thy
    Author:     Tobias Nipkow, Andreas Lochbihler
*)

section \<open>Runtime Well-typedness\<close>

theory WellTypeRT
imports 
  WellType
  JHeap
begin

context J_heap_base begin

inductive WTrt :: "'addr J_prog \<Rightarrow> 'heap \<Rightarrow> env \<Rightarrow> 'addr expr \<Rightarrow> ty \<Rightarrow> bool"
  and WTrts :: "'addr J_prog \<Rightarrow> 'heap \<Rightarrow> env \<Rightarrow> 'addr expr list \<Rightarrow> ty list \<Rightarrow> bool"
  for P :: "'addr J_prog" and h :: "'heap"
  where

  WTrtNew:
    "is_class P C  \<Longrightarrow> WTrt P h E (new C) (Class C)"

| WTrtNewArray:
    "\<lbrakk> WTrt P h E e Integer; is_type P (T\<lfloor>\<rceil>) \<rbrakk>
    \<Longrightarrow> WTrt P h E (newA T\<lfloor>e\<rceil>) (T\<lfloor>\<rceil>)"

| WTrtCast:
    "\<lbrakk> WTrt P h E e T; is_type P U \<rbrakk> \<Longrightarrow> WTrt P h E (Cast U e) U"

| WTrtInstanceOf:
    "\<lbrakk> WTrt P h E e T; is_type P U \<rbrakk> \<Longrightarrow> WTrt P h E (e instanceof U) Boolean"

| WTrtVal:
    "typeof\<^bsub>h\<^esub> v = Some T \<Longrightarrow> WTrt P h E (Val v) T"

| WTrtVar:
    "E V = Some T  \<Longrightarrow> WTrt P h E (Var V) T"

| WTrtBinOp:
    "\<lbrakk> WTrt P h E e1 T1; WTrt P h E e2 T2; P \<turnstile> T1\<guillemotleft>bop\<guillemotright>T2 : T \<rbrakk>
  \<Longrightarrow> WTrt P h E (e1 \<guillemotleft>bop\<guillemotright> e2) T"

| WTrtLAss:
    "\<lbrakk> E V = Some T; WTrt P h E e T'; P \<turnstile> T' \<le> T \<rbrakk>
     \<Longrightarrow> WTrt P h E (V:=e) Void"

| WTrtAAcc:
    "\<lbrakk> WTrt P h E a (T\<lfloor>\<rceil>); WTrt P h E i Integer \<rbrakk>
    \<Longrightarrow> WTrt P h E (a\<lfloor>i\<rceil>) T"

| WTrtAAccNT:
    "\<lbrakk> WTrt P h E a NT; WTrt P h E i Integer \<rbrakk>
    \<Longrightarrow> WTrt P h E (a\<lfloor>i\<rceil>) T"

| WTrtAAss:
    "\<lbrakk>  WTrt P h E a (T\<lfloor>\<rceil>); WTrt P h E i Integer; WTrt P h E e T' \<rbrakk>
    \<Longrightarrow> WTrt P h E (a\<lfloor>i\<rceil> := e) Void"

| WTrtAAssNT:
    "\<lbrakk>  WTrt P h E a NT; WTrt P h E i Integer; WTrt P h E e T' \<rbrakk>
    \<Longrightarrow> WTrt P h E (a\<lfloor>i\<rceil> := e) Void"

| WTrtALength:
  "WTrt P h E a (T\<lfloor>\<rceil>) \<Longrightarrow> WTrt P h E (a\<bullet>length) Integer"

| WTrtALengthNT:
  "WTrt P h E a NT \<Longrightarrow> WTrt P h E (a\<bullet>length) T"

| WTrtFAcc:
    "\<lbrakk> WTrt P h E e U; class_type_of' U = \<lfloor>C\<rfloor>; P \<turnstile> C has F:T (fm) in D \<rbrakk> \<Longrightarrow>
    WTrt P h E (e\<bullet>F{D}) T"

| WTrtFAccNT:
    "WTrt P h E e NT \<Longrightarrow> WTrt P h E (e\<bullet>F{D}) T"

| WTrtFAss:
    "\<lbrakk> WTrt P h E e1 U; class_type_of' U = \<lfloor>C\<rfloor>;  P \<turnstile> C has F:T (fm) in D; WTrt P h E e2 T2;  P \<turnstile> T2 \<le> T \<rbrakk>
    \<Longrightarrow> WTrt P h E (e1\<bullet>F{D}:=e2) Void"

| WTrtFAssNT:
    "\<lbrakk> WTrt P h E e1 NT; WTrt P h E e2 T2 \<rbrakk>
    \<Longrightarrow> WTrt P h E (e1\<bullet>F{D}:=e2) Void"

| WTrtCAS:
  "\<lbrakk> WTrt P h E e1 U; class_type_of' U = \<lfloor>C\<rfloor>; P \<turnstile> C has F:T (fm) in D; volatile fm;
     WTrt P h E e2 T2; P \<turnstile> T2 \<le> T; WTrt P h E e3 T3; P \<turnstile> T3 \<le> T \<rbrakk>
  \<Longrightarrow> WTrt P h E (e1\<bullet>compareAndSwap(D\<bullet>F, e2, e3)) Boolean"

| WTrtCASNT:
  "\<lbrakk> WTrt P h E e1 NT; WTrt P h E e2 T2; WTrt P h E e3 T3 \<rbrakk>
  \<Longrightarrow> WTrt P h E (e1\<bullet>compareAndSwap(D\<bullet>F, e2, e3)) Boolean"

| WTrtCall:
    "\<lbrakk> WTrt P h E e U; class_type_of' U = \<lfloor>C\<rfloor>; P \<turnstile> C sees M:Ts \<rightarrow> T = meth in D;
       WTrts P h E es Ts'; P \<turnstile> Ts' [\<le>] Ts \<rbrakk>
    \<Longrightarrow> WTrt P h E (e\<bullet>M(es)) T"

| WTrtCallNT:
    "\<lbrakk> WTrt P h E e NT; WTrts P h E es Ts \<rbrakk>
    \<Longrightarrow> WTrt P h E (e\<bullet>M(es)) T"

| WTrtBlock:
    "\<lbrakk> WTrt P h (E(V\<mapsto>T)) e T'; case vo of None \<Rightarrow> True | \<lfloor>v\<rfloor> \<Rightarrow> \<exists>T'. typeof\<^bsub>h\<^esub> v = \<lfloor>T'\<rfloor> \<and> P \<turnstile> T' \<le> T \<rbrakk>
  \<Longrightarrow> WTrt P h E {V:T=vo; e} T'"

| WTrtSynchronized:
    "\<lbrakk> WTrt P h E o' T; is_refT T; WTrt P h E e T' \<rbrakk>
    \<Longrightarrow> WTrt P h E (sync(o') e) T'"

| WTrtInSynchronized:
    "\<lbrakk> WTrt P h E (addr a) T; WTrt P h E e T' \<rbrakk>
    \<Longrightarrow> WTrt P h E (insync(a) e) T'"

| WTrtSeq:
    "\<lbrakk> WTrt P h E e1 T1; WTrt P h E e2 T2 \<rbrakk>
    \<Longrightarrow> WTrt P h E (e1;;e2) T2"

| WTrtCond:
    "\<lbrakk> WTrt P h E e Boolean; WTrt P h E e1 T1; WTrt P h E e2 T2; P \<turnstile> lub(T1, T2) = T \<rbrakk>
    \<Longrightarrow> WTrt P h E (if (e) e1 else e2) T"

| WTrtWhile:
    "\<lbrakk> WTrt P h E e Boolean; WTrt P h E c T \<rbrakk>
    \<Longrightarrow> WTrt P h E (while(e) c) Void"

| WTrtThrow:
    "\<lbrakk> WTrt P h E e T; P \<turnstile> T \<le> Class Throwable \<rbrakk>
    \<Longrightarrow> WTrt P h E (throw e) T'"

| WTrtTry:
    "\<lbrakk> WTrt P h E e1 T1; WTrt P h (E(V \<mapsto> Class C)) e2 T2; P \<turnstile> T1 \<le> T2 \<rbrakk>
    \<Longrightarrow> WTrt P h E (try e1 catch(C V) e2) T2"

| WTrtNil: "WTrts P h E [] []"

| WTrtCons: "\<lbrakk> WTrt P h E e T; WTrts P h E es Ts \<rbrakk> \<Longrightarrow> WTrts P h E (e # es) (T # Ts)"

abbreviation
  WTrt_syntax :: "'addr J_prog \<Rightarrow> env \<Rightarrow> 'heap \<Rightarrow> 'addr expr \<Rightarrow> ty \<Rightarrow> bool" ("_,_,_ \<turnstile> _ : _"   [51,51,51]50)
where
  "P,E,h \<turnstile> e : T \<equiv> WTrt P h E e T"

abbreviation
  WTrts_syntax :: "'addr J_prog \<Rightarrow> env \<Rightarrow> 'heap \<Rightarrow> 'addr expr list \<Rightarrow> ty list \<Rightarrow> bool" ("_,_,_ \<turnstile> _ [:] _"   [51,51,51]50)
where
  "P,E,h \<turnstile> es [:] Ts \<equiv> WTrts P h E es Ts"

lemmas [intro!] =
  WTrtNew WTrtNewArray WTrtCast WTrtInstanceOf WTrtVal WTrtVar WTrtBinOp WTrtLAss
  WTrtBlock WTrtSynchronized WTrtInSynchronized WTrtSeq WTrtCond WTrtWhile
  WTrtThrow WTrtTry WTrtNil WTrtCons

lemmas [intro] =
  WTrtFAcc WTrtFAccNT WTrtFAss WTrtFAssNT WTrtCall WTrtCallNT
  WTrtAAcc WTrtAAccNT WTrtAAss WTrtAAssNT WTrtALength WTrtALengthNT 

subsection\<open>Easy consequences\<close>

inductive_simps WTrts_iffs [iff]:
  "P,E,h \<turnstile> [] [:] Ts"
  "P,E,h \<turnstile> e#es [:] T#Ts"
  "P,E,h \<turnstile> (e#es) [:] Ts"

lemma WTrts_conv_list_all2: "P,E,h \<turnstile> es [:] Ts = list_all2 (WTrt P h E) es Ts"
by(induct es arbitrary: Ts)(auto simp add: list_all2_Cons1 elim: WTrts.cases)

lemma [simp]: "(P,E,h \<turnstile> es\<^sub>1 @ es\<^sub>2 [:] Ts) =
  (\<exists>Ts\<^sub>1 Ts\<^sub>2. Ts = Ts\<^sub>1 @ Ts\<^sub>2 \<and> P,E,h \<turnstile> es\<^sub>1 [:] Ts\<^sub>1 & P,E,h \<turnstile> es\<^sub>2[:]Ts\<^sub>2)"
by(auto simp add: WTrts_conv_list_all2 list_all2_append1 dest: list_all2_lengthD[symmetric])

inductive_simps WTrt_iffs [iff]:
  "P,E,h \<turnstile> Val v : T"
  "P,E,h \<turnstile> Var v : T"
  "P,E,h \<turnstile> e\<^sub>1;;e\<^sub>2 : T\<^sub>2"
  "P,E,h \<turnstile> {V:T=vo; e} : T'"

inductive_cases WTrt_elim_cases[elim!]:
  "P,E,h \<turnstile> newA T\<lfloor>i\<rceil> : U"
  "P,E,h \<turnstile> v :=e : T"
  "P,E,h \<turnstile> if (e) e\<^sub>1 else e\<^sub>2 : T"
  "P,E,h \<turnstile> while(e) c : T"
  "P,E,h \<turnstile> throw e : T"
  "P,E,h \<turnstile> try e\<^sub>1 catch(C V) e\<^sub>2 : T"
  "P,E,h \<turnstile> Cast D e : T"
  "P,E,h \<turnstile> e instanceof U : T"
  "P,E,h \<turnstile> a\<lfloor>i\<rceil> : T"
  "P,E,h \<turnstile> a\<lfloor>i\<rceil> := e : T"
  "P,E,h \<turnstile> a\<bullet>length : T"
  "P,E,h \<turnstile> e\<bullet>F{D} : T"
  "P,E,h \<turnstile> e\<bullet>F{D} := v : T"
  "P,E,h \<turnstile> e\<bullet>compareAndSwap(D\<bullet>F, e2, e3) : T"
  "P,E,h \<turnstile> e\<^sub>1 \<guillemotleft>bop\<guillemotright> e\<^sub>2 : T"
  "P,E,h \<turnstile> new C : T"
  "P,E,h \<turnstile> e\<bullet>M(es) : T"
  "P,E,h \<turnstile> sync(o') e : T"
  "P,E,h \<turnstile> insync(a) e : T"

subsection\<open>Some interesting lemmas\<close>

lemma WTrts_Val[simp]:
 "P,E,h \<turnstile> map Val vs [:] Ts \<longleftrightarrow> map (typeof\<^bsub>h\<^esub>) vs = map Some Ts"
by(induct vs arbitrary: Ts) auto

lemma WTrt_env_mono: "P,E,h \<turnstile> e : T \<Longrightarrow> (\<And>E'. E \<subseteq>\<^sub>m E' \<Longrightarrow> P,E',h \<turnstile> e : T)"
  and WTrts_env_mono: "P,E,h \<turnstile> es [:] Ts \<Longrightarrow> (\<And>E'. E \<subseteq>\<^sub>m E' \<Longrightarrow> P,E',h \<turnstile> es [:] Ts)"
apply(induct rule: WTrt_WTrts.inducts)
apply(simp add: WTrtNew)
apply(fastforce simp: WTrtNewArray)
apply(fastforce simp: WTrtCast)
apply(fastforce simp: WTrtInstanceOf)
apply(fastforce simp: WTrtVal)
apply(simp add: WTrtVar map_le_def dom_def)
apply(fastforce simp add: WTrtBinOp)
apply(force simp: map_le_def)
apply(force simp: WTrtAAcc)
apply(force simp: WTrtAAccNT)
apply(rule WTrtAAss, fastforce, blast, blast)
apply(fastforce)
apply(rule WTrtALength, blast)
apply(blast)
apply(fastforce simp: WTrtFAcc)
apply(simp add: WTrtFAccNT)
apply(fastforce simp: WTrtFAss)
apply(fastforce simp: WTrtFAssNT)
apply(fastforce simp: WTrtCAS)
apply(fastforce simp: WTrtCASNT)
apply(fastforce simp: WTrtCall)
apply(fastforce simp: WTrtCallNT)
apply(fastforce simp: map_le_def)
apply(fastforce)
apply(fastforce)
apply(fastforce)
apply(fastforce)
apply(fastforce simp: WTrtSeq)
apply(fastforce simp: WTrtCond)
apply(fastforce simp: WTrtWhile)
apply(fastforce simp: WTrtThrow)
apply(auto simp: WTrtTry map_le_def dom_def)
done

lemma WT_implies_WTrt: "P,E \<turnstile> e :: T \<Longrightarrow> P,E,h \<turnstile> e : T"
  and WTs_implies_WTrts: "P,E \<turnstile> es [::] Ts \<Longrightarrow> P,E,h \<turnstile> es [:] Ts"
apply(induct rule: WT_WTs.inducts)
apply fast
apply fast
apply fast
apply fast
apply(fastforce dest:typeof_lit_typeof)
apply(simp)
apply(fastforce intro: WT_binop_WTrt_binop)
apply(fastforce)
apply(erule WTrtAAcc)
apply(assumption)
apply(erule WTrtAAss)
apply(assumption)+
apply(erule WTrtALength)
apply(fastforce intro: has_visible_field)
apply(fastforce simp: WTrtFAss dest: has_visible_field)
apply(fastforce simp: WTrtCAS dest: has_visible_field)
apply(fastforce simp: WTrtCall)
apply(clarsimp simp del: fun_upd_apply, blast intro: typeof_lit_typeof)
apply(fastforce)+
done

lemma wt_blocks:
 "\<And>E. \<lbrakk> length Vs = length Ts; length vs = length Ts \<rbrakk> \<Longrightarrow>
       (P,E,h \<turnstile> blocks Vs Ts vs e : T) =
       (P,E(Vs[\<mapsto>]Ts),h \<turnstile> e:T \<and> (\<exists>Ts'. map (typeof\<^bsub>h\<^esub>) vs = map Some Ts' \<and> P \<turnstile> Ts' [\<le>] Ts))"
apply(induct Vs Ts vs e rule:blocks.induct)
apply (force)
apply simp_all
done

end

context J_heap begin

lemma WTrt_hext_mono: "P,E,h \<turnstile> e : T \<Longrightarrow> h \<unlhd> h' \<Longrightarrow> P,E,h' \<turnstile> e : T"
  and WTrts_hext_mono: "P,E,h \<turnstile> es [:] Ts \<Longrightarrow> h \<unlhd> h' \<Longrightarrow> P,E,h' \<turnstile> es [:] Ts"
apply(induct rule: WTrt_WTrts.inducts)
apply(simp add: WTrtNew)
apply(fastforce simp: WTrtNewArray)
apply(fastforce simp: WTrtCast)
apply(fastforce simp: WTrtInstanceOf)
apply(fastforce simp: WTrtVal dest:hext_typeof_mono)
apply(simp add: WTrtVar)
apply(fastforce simp add: WTrtBinOp)
apply(fastforce simp add: WTrtLAss)
apply fastforce
apply fastforce
apply fastforce
apply fastforce
apply fastforce
apply fastforce
apply(fast)
apply(simp add: WTrtFAccNT)
apply(fastforce simp: WTrtFAss del:WTrt_WTrts.intros WTrt_elim_cases)
apply(fastforce simp: WTrtFAssNT)
apply(fastforce simp: WTrtCAS)
apply(fastforce simp: WTrtCASNT)
apply(fastforce simp: WTrtCall)
apply(fastforce simp: WTrtCallNT)
apply(fastforce intro: hext_typeof_mono)
apply fastforce+
done

end

end
