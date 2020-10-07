(*  Title:      JinjaThreads/J/WellType.thy
    Author:     Tobias Nipkow, Andreas Lochbihler
*)

section \<open>Well-typedness of Jinja expressions\<close>

theory WellType
imports
  Expr
  State
  "../Common/ExternalCallWF"
  "../Common/WellForm"
  "../Common/SemiType"
begin

declare Listn.lesub_list_impl_same_size[simp del]
declare listE_length [simp del]

type_synonym 
  env  = "vname \<rightharpoonup> ty"

inductive
  WT :: "(ty \<Rightarrow> ty \<Rightarrow> ty \<Rightarrow> bool) \<Rightarrow> 'addr J_prog \<Rightarrow> env \<Rightarrow> 'addr expr \<Rightarrow> ty \<Rightarrow> bool" ("_,_,_ \<turnstile> _ :: _"   [51,51,51,51]50)
  and WTs :: "(ty \<Rightarrow> ty \<Rightarrow> ty \<Rightarrow> bool) \<Rightarrow> 'addr J_prog \<Rightarrow> env \<Rightarrow> 'addr expr list \<Rightarrow> ty list \<Rightarrow> bool" 
    ("_,_,_ \<turnstile> _ [::] _"   [51,51,51,51]50)
  for is_lub :: "ty \<Rightarrow> ty \<Rightarrow> ty \<Rightarrow> bool" ("\<turnstile> lub'((_,/ _)') = _" [51,51,51] 50)
  and P :: "'addr J_prog"
where

  WTNew:
  "is_class P C  \<Longrightarrow>
  is_lub,P,E \<turnstile> new C :: Class C"

| WTNewArray:
  "\<lbrakk> is_lub,P,E \<turnstile> e :: Integer; is_type P (T\<lfloor>\<rceil>) \<rbrakk> \<Longrightarrow>
  is_lub,P,E \<turnstile> newA T\<lfloor>e\<rceil> :: T\<lfloor>\<rceil>"

| WTCast:
  "\<lbrakk> is_lub,P,E \<turnstile> e :: T; P \<turnstile> U \<le> T \<or> P \<turnstile> T \<le> U; is_type P U \<rbrakk>
  \<Longrightarrow> is_lub,P,E \<turnstile> Cast U e :: U"

| WTInstanceOf:
  "\<lbrakk> is_lub,P,E \<turnstile> e :: T; P \<turnstile> U \<le> T \<or> P \<turnstile> T \<le> U; is_type P U; is_refT U \<rbrakk>
  \<Longrightarrow> is_lub,P,E \<turnstile> e instanceof U :: Boolean"

| WTVal:
  "typeof v = Some T \<Longrightarrow>
  is_lub,P,E \<turnstile> Val v :: T"

| WTVar:
  "E V = Some T \<Longrightarrow>
  is_lub,P,E \<turnstile> Var V :: T"

| WTBinOp:
  "\<lbrakk> is_lub,P,E \<turnstile> e1 :: T1; is_lub,P,E \<turnstile> e2 :: T2; P \<turnstile> T1\<guillemotleft>bop\<guillemotright>T2 :: T \<rbrakk>
  \<Longrightarrow> is_lub,P,E \<turnstile> e1\<guillemotleft>bop\<guillemotright>e2 :: T"

| WTLAss:
  "\<lbrakk> E V = Some T;  is_lub,P,E \<turnstile> e :: T';  P \<turnstile> T' \<le> T;  V \<noteq> this \<rbrakk>
  \<Longrightarrow> is_lub,P,E \<turnstile> V:=e :: Void"

| WTAAcc:
  "\<lbrakk> is_lub,P,E \<turnstile> a :: T\<lfloor>\<rceil>; is_lub,P,E \<turnstile> i :: Integer \<rbrakk>
  \<Longrightarrow> is_lub,P,E \<turnstile> a\<lfloor>i\<rceil> :: T"

| WTAAss:
  "\<lbrakk> is_lub,P,E \<turnstile> a :: T\<lfloor>\<rceil>; is_lub,P,E \<turnstile> i :: Integer; is_lub,P,E \<turnstile> e :: T'; P \<turnstile> T' \<le> T \<rbrakk>
  \<Longrightarrow> is_lub,P,E \<turnstile> a\<lfloor>i\<rceil> := e :: Void"

| WTALength:
  "is_lub,P,E \<turnstile> a :: T\<lfloor>\<rceil> \<Longrightarrow> is_lub,P,E \<turnstile> a\<bullet>length :: Integer"

| WTFAcc:
  "\<lbrakk> is_lub,P,E \<turnstile> e :: U; class_type_of' U = \<lfloor>C\<rfloor>; P \<turnstile> C sees F:T (fm) in D \<rbrakk>
  \<Longrightarrow> is_lub,P,E \<turnstile> e\<bullet>F{D} :: T"

| WTFAss:
  "\<lbrakk> is_lub,P,E \<turnstile> e\<^sub>1 :: U; class_type_of' U = \<lfloor>C\<rfloor>; P \<turnstile> C sees F:T (fm) in D; is_lub,P,E \<turnstile> e\<^sub>2 :: T'; P \<turnstile> T' \<le> T \<rbrakk>
  \<Longrightarrow> is_lub,P,E \<turnstile> e\<^sub>1\<bullet>F{D}:=e\<^sub>2 :: Void"

| WTCAS:
  "\<lbrakk> is_lub,P,E \<turnstile> e1 :: U; class_type_of' U = \<lfloor>C\<rfloor>; P \<turnstile> C sees F:T (fm) in D; volatile fm; 
     is_lub,P,E \<turnstile> e2 :: T'; P \<turnstile> T' \<le> T; is_lub,P,E \<turnstile> e3 :: T''; P \<turnstile> T'' \<le> T \<rbrakk>
  \<Longrightarrow>  is_lub,P,E \<turnstile> e1\<bullet>compareAndSwap(D\<bullet>F, e2, e3) :: Boolean"

| WTCall:
  "\<lbrakk> is_lub,P,E \<turnstile> e :: U; class_type_of' U = \<lfloor>C\<rfloor>; P \<turnstile> C sees M:Ts \<rightarrow> T = meth in D;
     is_lub,P,E \<turnstile> es [::] Ts'; P \<turnstile> Ts' [\<le>] Ts \<rbrakk>
  \<Longrightarrow> is_lub,P,E \<turnstile> e\<bullet>M(es) :: T"

| WTBlock:
  "\<lbrakk> is_type P T;  is_lub,P,E(V \<mapsto> T) \<turnstile> e :: T'; case vo of None \<Rightarrow> True | \<lfloor>v\<rfloor> \<Rightarrow> \<exists>T'. typeof v = \<lfloor>T'\<rfloor> \<and> P \<turnstile> T' \<le> T \<rbrakk>
  \<Longrightarrow>  is_lub,P,E \<turnstile> {V:T=vo; e} :: T'"

| WTSynchronized:
  "\<lbrakk> is_lub,P,E \<turnstile> o' :: T; is_refT T; T \<noteq> NT; is_lub,P,E \<turnstile> e :: T' \<rbrakk>
  \<Longrightarrow> is_lub,P,E \<turnstile> sync(o') e :: T'"

\<comment> \<open>Note that insync is not statically typable.\<close>

| WTSeq:
  "\<lbrakk> is_lub,P,E \<turnstile> e\<^sub>1::T\<^sub>1;  is_lub,P,E \<turnstile> e\<^sub>2::T\<^sub>2 \<rbrakk>
  \<Longrightarrow>  is_lub,P,E \<turnstile> e\<^sub>1;;e\<^sub>2 :: T\<^sub>2"

| WTCond:
  "\<lbrakk> is_lub,P,E \<turnstile> e :: Boolean;  is_lub,P,E \<turnstile> e\<^sub>1::T\<^sub>1;  is_lub,P,E \<turnstile> e\<^sub>2::T\<^sub>2; \<turnstile> lub(T\<^sub>1, T\<^sub>2) = T \<rbrakk>
  \<Longrightarrow> is_lub,P,E \<turnstile> if (e) e\<^sub>1 else e\<^sub>2 :: T"

| WTWhile:
  "\<lbrakk> is_lub,P,E \<turnstile> e :: Boolean;  is_lub,P,E \<turnstile> c::T \<rbrakk>
  \<Longrightarrow> is_lub,P,E \<turnstile> while (e) c :: Void"

| WTThrow:
  "\<lbrakk> is_lub,P,E \<turnstile> e :: Class C; P \<turnstile> C \<preceq>\<^sup>* Throwable \<rbrakk> \<Longrightarrow> 
  is_lub,P,E \<turnstile> throw e :: Void"

| WTTry:
  "\<lbrakk> is_lub,P,E \<turnstile> e\<^sub>1 :: T;  is_lub,P,E(V \<mapsto> Class C) \<turnstile> e\<^sub>2 :: T; P \<turnstile> C \<preceq>\<^sup>* Throwable \<rbrakk>
  \<Longrightarrow> is_lub,P,E \<turnstile> try e\<^sub>1 catch(C V) e\<^sub>2 :: T"

| WTNil: "is_lub,P,E \<turnstile> [] [::] []"

| WTCons: "\<lbrakk> is_lub,P,E \<turnstile> e :: T; is_lub,P,E \<turnstile> es [::] Ts \<rbrakk> \<Longrightarrow> is_lub,P,E \<turnstile> e#es [::] T#Ts"

abbreviation WT' :: "'addr J_prog \<Rightarrow> env \<Rightarrow> 'addr expr \<Rightarrow> ty \<Rightarrow> bool" ("_,_ \<turnstile> _ :: _" [51,51,51] 50)
where "WT' P \<equiv> WT (TypeRel.is_lub P) P"

abbreviation WTs' :: "'addr J_prog \<Rightarrow> env \<Rightarrow> 'addr expr list \<Rightarrow> ty list \<Rightarrow> bool" ("_,_ \<turnstile> _ [::] _" [51,51,51] 50)
where "WTs' P \<equiv> WTs (TypeRel.is_lub P) P"

declare WT_WTs.intros[intro!]

inductive_simps WTs_iffs [iff]:
  "is_lub',P,E \<turnstile> [] [::] Ts"
  "is_lub',P,E \<turnstile> e#es [::] T#Ts"
  "is_lub',P,E \<turnstile> e#es [::] Ts"

lemma WTs_conv_list_all2: 
  fixes is_lub 
  shows "is_lub,P,E \<turnstile> es [::] Ts = list_all2 (WT is_lub P E) es Ts"
by(induct es arbitrary: Ts)(auto simp add: list_all2_Cons1 elim: WTs.cases)

lemma WTs_append [iff]: "\<And>is_lub Ts. (is_lub,P,E \<turnstile> es\<^sub>1 @ es\<^sub>2 [::] Ts) =
  (\<exists>Ts\<^sub>1 Ts\<^sub>2. Ts = Ts\<^sub>1 @ Ts\<^sub>2 \<and> is_lub,P,E \<turnstile> es\<^sub>1 [::] Ts\<^sub>1 \<and> is_lub,P,E \<turnstile> es\<^sub>2[::]Ts\<^sub>2)"
by(auto simp add: WTs_conv_list_all2 list_all2_append1 dest: list_all2_lengthD[symmetric])

inductive_simps WT_iffs [iff]:
  "is_lub',P,E \<turnstile> Val v :: T"
  "is_lub',P,E \<turnstile> Var V :: T"
  "is_lub',P,E \<turnstile> e\<^sub>1;;e\<^sub>2 :: T\<^sub>2"
  "is_lub',P,E \<turnstile> {V:T=vo; e} :: T'"

inductive_cases WT_elim_cases[elim!]:
  "is_lub',P,E \<turnstile> V :=e :: T"
  "is_lub',P,E \<turnstile> sync(o') e :: T"
  "is_lub',P,E \<turnstile> if (e) e\<^sub>1 else e\<^sub>2 :: T"
  "is_lub',P,E \<turnstile> while (e) c :: T"
  "is_lub',P,E \<turnstile> throw e :: T"
  "is_lub',P,E \<turnstile> try e\<^sub>1 catch(C V) e\<^sub>2 :: T"
  "is_lub',P,E \<turnstile> Cast D e :: T"
  "is_lub',P,E \<turnstile> e instanceof U :: T"
  "is_lub',P,E \<turnstile> a\<bullet>F{D} :: T"
  "is_lub',P,E \<turnstile> a\<bullet>F{D} := v :: T"
  "is_lub',P,E \<turnstile> e\<bullet>compareAndSwap(D\<bullet>F, e', e'') :: T"
  "is_lub',P,E \<turnstile> e\<^sub>1 \<guillemotleft>bop\<guillemotright> e\<^sub>2 :: T"
  "is_lub',P,E \<turnstile> new C :: T"
  "is_lub',P,E \<turnstile> newA T\<lfloor>e\<rceil> :: T'"
  "is_lub',P,E \<turnstile> a\<lfloor>i\<rceil> := e :: T"
  "is_lub',P,E \<turnstile> a\<lfloor>i\<rceil> :: T"
  "is_lub',P,E \<turnstile> a\<bullet>length :: T"
  "is_lub',P,E \<turnstile> e\<bullet>M(ps) :: T"
  "is_lub',P,E \<turnstile> sync(o') e :: T"
  "is_lub',P,E \<turnstile> insync(a) e :: T"

lemma fixes is_lub :: "ty \<Rightarrow> ty \<Rightarrow> ty \<Rightarrow> bool" ("\<turnstile> lub'((_,/ _)') = _" [51,51,51] 50)
  assumes is_lub_unique: "\<And>T1 T2 T3 T4. \<lbrakk> \<turnstile> lub(T1, T2) = T3; \<turnstile> lub(T1, T2) = T4 \<rbrakk> \<Longrightarrow> T3 = T4"
  shows WT_unique: "\<lbrakk> is_lub,P,E \<turnstile> e :: T; is_lub,P,E \<turnstile> e :: T' \<rbrakk> \<Longrightarrow> T = T'"
  and WTs_unique: "\<lbrakk> is_lub,P,E \<turnstile> es [::] Ts; is_lub,P,E \<turnstile> es [::] Ts' \<rbrakk> \<Longrightarrow> Ts = Ts'"
apply(induct arbitrary: T' and Ts' rule: WT_WTs.inducts)
apply blast
apply blast
apply blast
apply blast
apply fastforce
apply fastforce
apply(fastforce dest: WT_binop_fun)
apply fastforce
apply fastforce
apply fastforce
apply fastforce
apply(fastforce dest: sees_field_fun)
apply(fastforce dest: sees_field_fun)
apply blast
apply(fastforce dest: sees_method_fun)
apply fastforce
apply fastforce
apply fastforce
apply(blast dest: is_lub_unique)
apply fastforce
apply fastforce
apply blast
apply fastforce
apply fastforce
done

lemma fixes is_lub
  shows wt_env_mono: "is_lub,P,E \<turnstile> e :: T \<Longrightarrow> (\<And>E'. E \<subseteq>\<^sub>m E' \<Longrightarrow> is_lub,P,E' \<turnstile> e :: T)"
  and wts_env_mono: "is_lub,P,E \<turnstile> es [::] Ts \<Longrightarrow> (\<And>E'. E \<subseteq>\<^sub>m E' \<Longrightarrow> is_lub,P,E' \<turnstile> es [::] Ts)"
apply(induct rule: WT_WTs.inducts)
apply(simp add: WTNew)
apply(simp add: WTNewArray)
apply(fastforce simp: WTCast)
apply(fastforce simp: WTInstanceOf)
apply(fastforce simp: WTVal)
apply(simp add: WTVar map_le_def dom_def)
apply(fastforce simp: WTBinOp)
apply(force simp:map_le_def)
apply(simp add: WTAAcc)
apply(simp add: WTAAss, fastforce)
apply(simp add: WTALength, fastforce)
apply(fastforce simp: WTFAcc)
apply(fastforce simp: WTFAss del:WT_WTs.intros WT_elim_cases)
apply blast
apply(fastforce)
apply(fastforce simp: map_le_def WTBlock)
apply(fastforce simp: WTSynchronized)
apply(fastforce simp: WTSeq)
apply(fastforce simp: WTCond)
apply(fastforce simp: WTWhile)
apply(fastforce simp: WTThrow)
apply(fastforce simp: WTTry map_le_def dom_def)
apply(fastforce)+
done

lemma fixes is_lub
  shows WT_fv: "is_lub,P,E \<turnstile> e :: T \<Longrightarrow> fv e \<subseteq> dom E"
  and WT_fvs: "is_lub,P,E \<turnstile> es [::] Ts \<Longrightarrow> fvs es \<subseteq> dom E"
apply(induct rule:WT_WTs.inducts)
apply(simp_all del: fun_upd_apply)
apply fast+
done

lemma fixes is_lub
  shows WT_expr_locks: "is_lub,P,E \<turnstile> e :: T \<Longrightarrow> expr_locks e = (\<lambda>ad. 0)"
  and WTs_expr_lockss: "is_lub,P,E \<turnstile> es [::] Ts \<Longrightarrow> expr_lockss es = (\<lambda>ad. 0)"
by(induct rule: WT_WTs.inducts)(auto)

lemma
  fixes is_lub :: "ty \<Rightarrow> ty \<Rightarrow> ty \<Rightarrow> bool" ("\<turnstile> lub'((_,/ _)') = _" [51,51,51] 50)
  assumes is_lub_is_type: "\<And>T1 T2 T3. \<lbrakk> \<turnstile> lub(T1, T2) = T3; is_type P T1; is_type P T2 \<rbrakk> \<Longrightarrow> is_type P T3"
  and wf: "wf_prog wf_md P"
  shows WT_is_type: "\<lbrakk> is_lub,P,E \<turnstile> e :: T; ran E \<subseteq> types P \<rbrakk> \<Longrightarrow> is_type P T"
  and WTs_is_type: "\<lbrakk> is_lub,P,E \<turnstile> es [::] Ts; ran E \<subseteq> types P \<rbrakk> \<Longrightarrow> set Ts \<subseteq> types P"
apply(induct rule: WT_WTs.inducts)
apply simp
apply simp
apply simp
apply simp
apply (simp add:typeof_lit_is_type)
apply (fastforce intro:nth_mem simp add: ran_def)
apply(simp add: WT_binop_is_type)
apply(simp)
apply(simp del: is_type_array add: is_type_ArrayD)
apply(simp)
apply(simp)
apply(simp add:sees_field_is_type[OF _ wf])
apply(simp)
apply simp
apply(fastforce dest: sees_wf_mdecl[OF wf] simp:wf_mdecl_def)
apply(fastforce simp add: ran_def split: if_split_asm)
apply(simp add: is_class_Object[OF wf])
apply(simp)
apply(simp)
apply(fastforce intro: is_lub_is_type)
apply(simp)
apply(simp)
apply simp
apply simp
apply simp
done

lemma
  fixes is_lub1 :: "ty \<Rightarrow> ty \<Rightarrow> ty \<Rightarrow> bool" ("\<turnstile>1 lub'((_,/ _)') = _" [51,51,51] 50)
  and is_lub2 :: "ty \<Rightarrow> ty \<Rightarrow> ty \<Rightarrow> bool" ("\<turnstile>2 lub'((_,/ _)') = _" [51,51,51] 50)
  assumes wf: "wf_prog wf_md P"
  and is_lub1_into_is_lub2: "\<And>T1 T2 T3. \<lbrakk> \<turnstile>1 lub(T1, T2) = T3; is_type P T1; is_type P T2 \<rbrakk> \<Longrightarrow> \<turnstile>2 lub(T1, T2) = T3"
  and is_lub2_is_type: "\<And>T1 T2 T3. \<lbrakk> \<turnstile>2 lub(T1, T2) = T3; is_type P T1; is_type P T2 \<rbrakk> \<Longrightarrow> is_type P T3"
  shows WT_change_is_lub: "\<lbrakk> is_lub1,P,E \<turnstile> e :: T; ran E \<subseteq> types P \<rbrakk> \<Longrightarrow> is_lub2,P,E \<turnstile> e :: T"
  and WTs_change_is_lub: "\<lbrakk> is_lub1,P,E \<turnstile> es [::] Ts; ran E \<subseteq> types P \<rbrakk> \<Longrightarrow> is_lub2,P,E \<turnstile> es [::] Ts"
proof(induct rule: WT_WTs.inducts)
  case (WTBlock U E V e' T vo)
  from \<open>is_type P U\<close> \<open>ran E \<subseteq> types P\<close>
  have "ran (E(V \<mapsto> U)) \<subseteq> types P" by(auto simp add: ran_def)
  hence "is_lub2,P,E(V \<mapsto> U) \<turnstile> e' :: T" by(rule WTBlock)
  with \<open>is_type P U\<close> show ?case
    using \<open>case vo of None \<Rightarrow> True | \<lfloor>v\<rfloor> \<Rightarrow> \<exists>T'. typeof v = \<lfloor>T'\<rfloor> \<and> P \<turnstile> T' \<le> U\<close> by auto
next
  case (WTCond E e e1 T1 e2 T2 T)
  from \<open>ran E \<subseteq> types P\<close> have "is_lub2,P,E \<turnstile> e :: Boolean" "is_lub2,P,E \<turnstile> e1 :: T1" "is_lub2,P,E \<turnstile> e2 :: T2"
    by(rule WTCond)+
  moreover from is_lub2_is_type wf \<open>is_lub2,P,E \<turnstile> e1 :: T1\<close> \<open>ran E \<subseteq> types P\<close>
  have "is_type P T1" by(rule WT_is_type)
  from is_lub2_is_type wf \<open>is_lub2,P,E \<turnstile> e2 :: T2\<close> \<open>ran E \<subseteq> types P\<close>
  have "is_type P T2" by(rule WT_is_type)
  with \<open>\<turnstile>1 lub(T1, T2) = T\<close> \<open>is_type P T1\<close>
  have "\<turnstile>2 lub(T1, T2) = T" by(rule is_lub1_into_is_lub2)
  ultimately show ?case ..
next
  case (WTTry E e1 T V C e2)
  from \<open>ran E \<subseteq> types P\<close> have "is_lub2,P,E \<turnstile> e1 :: T" by(rule WTTry)
  moreover from \<open>P \<turnstile> C \<preceq>\<^sup>* Throwable\<close> have "is_class P C"
    by(rule is_class_sub_Throwable[OF wf])
  with \<open>ran E \<subseteq> types P\<close> have "ran (E(V \<mapsto> Class C)) \<subseteq> types P"
    by(auto simp add: ran_def)
  hence "is_lub2,P,E(V \<mapsto> Class C) \<turnstile> e2 :: T" by(rule WTTry)
  ultimately show ?case using \<open>P \<turnstile> C \<preceq>\<^sup>* Throwable\<close> ..
qed auto

subsection \<open>Code generator setup\<close>

lemma WTBlock_code:
  "\<And>is_lub. \<lbrakk> is_type P T; is_lub,P,E(V \<mapsto> T) \<turnstile> e :: T'; 
     case vo of None \<Rightarrow> True | \<lfloor>v\<rfloor> \<Rightarrow> case typeof v of None \<Rightarrow> False | Some T' \<Rightarrow> P \<turnstile> T' \<le> T \<rbrakk>
  \<Longrightarrow>  is_lub,P,E \<turnstile> {V:T=vo; e} :: T'"
by(auto)

lemmas [code_pred_intro] =
  WTNew WTNewArray WTCast WTInstanceOf WTVal WTVar WTBinOp WTLAss WTAAcc WTAAss WTALength WTFAcc WTFAss WTCAS WTCall 
declare 
  WTBlock_code [code_pred_intro WTBlock']
lemmas [code_pred_intro] =
  WTSynchronized WTSeq WTCond WTWhile WTThrow WTTry
  WTNil WTCons

code_pred
  (modes:
    (i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool) \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool, 
    (i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool) \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool)
  [detect_switches, skip_proof]
  WT
proof -
  case WT
  from WT.prems show thesis
  proof cases
    case (WTBlock T V e vo)
    thus thesis using WT.WTBlock'[OF refl refl refl, of V T vo e] by(auto)
  qed(assumption|erule WT.that[OF refl refl refl]|rule refl)+
next
  case WTs
  from WTs.prems WTs.that show thesis by cases blast+
qed

inductive is_lub_sup :: "'m prog \<Rightarrow> ty \<Rightarrow> ty \<Rightarrow> ty \<Rightarrow> bool"
for P T1 T2 T3
where
  "sup P T1 T2 = OK T3 \<Longrightarrow> is_lub_sup P T1 T2 T3"

code_pred
  (modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool, i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool)
  is_lub_sup
.

definition WT_code :: "'addr J_prog \<Rightarrow> env \<Rightarrow> 'addr expr \<Rightarrow> ty \<Rightarrow> bool" ("_,_ \<turnstile> _ ::' _" [51,51,51] 50)
where "WT_code P \<equiv> WT (is_lub_sup P) P"

definition WTs_code :: "'addr J_prog \<Rightarrow> env \<Rightarrow> 'addr expr list \<Rightarrow> ty list \<Rightarrow> bool" ("_,_ \<turnstile> _ [::''] _" [51,51,51] 50)
where "WTs_code P \<equiv> WTs (is_lub_sup P) P"

lemma assumes wf: "wf_prog wf_md P"
  shows WT_code_into_WT: 
  "\<lbrakk> P,E \<turnstile> e ::' T; ran E \<subseteq> types P \<rbrakk> \<Longrightarrow> P,E \<turnstile> e :: T"

  and WTs_code_into_WTs:
  "\<lbrakk> P,E \<turnstile> es [::'] Ts; ran E \<subseteq> types P \<rbrakk> \<Longrightarrow> P,E \<turnstile> es [::] Ts"
proof -
  assume ran: "ran E \<subseteq> types P"
  { assume wt: "P,E \<turnstile> e ::' T"
    show "P,E \<turnstile> e :: T"
      by(rule WT_change_is_lub[OF wf _ _ wt[unfolded WT_code_def] ran])(blast elim!: is_lub_sup.cases intro: sup_is_lubI[OF wf] is_lub_is_type[OF wf])+ }
  { assume wts: "P,E \<turnstile> es [::'] Ts"
    show "P,E \<turnstile> es [::] Ts"
      by(rule WTs_change_is_lub[OF wf _ _ wts[unfolded WTs_code_def] ran])(blast elim!: is_lub_sup.cases intro: sup_is_lubI[OF wf] is_lub_is_type[OF wf])+ }
qed

lemma assumes wf: "wf_prog wf_md P"
  shows WT_into_WT_code: 
  "\<lbrakk> P,E \<turnstile> e :: T; ran E \<subseteq> types P \<rbrakk> \<Longrightarrow> P,E \<turnstile> e ::' T"

  and WT_into_WTs_code_OK:
  "\<lbrakk> P,E \<turnstile> es [::] Ts; ran E \<subseteq> types P \<rbrakk> \<Longrightarrow> P,E \<turnstile> es [::'] Ts"
proof -
  assume ran: "ran E \<subseteq> types P"
  { assume wt: "P,E \<turnstile> e :: T"
    show "P,E \<turnstile> e ::' T" unfolding WT_code_def
      by(rule WT_change_is_lub[OF wf _ _ wt ran])(blast intro!: is_lub_sup.intros intro: is_lub_subD[OF wf] sup_is_type[OF wf] elim!: is_lub_sup.cases)+ }
  { assume wts: "P,E \<turnstile> es [::] Ts"
    show "P,E \<turnstile> es [::'] Ts" unfolding WTs_code_def
      by(rule WTs_change_is_lub[OF wf _ _ wts ran])(blast intro!: is_lub_sup.intros intro: is_lub_subD[OF wf] sup_is_type[OF wf] elim!: is_lub_sup.cases)+ }
qed

theorem WT_eq_WT_code:
  assumes "wf_prog wf_md P"
  and "ran E \<subseteq> types P"
  shows "P,E \<turnstile> e :: T \<longleftrightarrow> P,E \<turnstile> e ::' T"
using assms by(blast intro: WT_code_into_WT WT_into_WT_code)

code_pred
  (modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool, i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool)
  [inductify]
  WT_code 
.

code_pred
  (modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool, i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool)
  [inductify]
  WTs_code 
.

end
