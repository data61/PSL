(*  Title:      JinjaThreads/Compiler/J1WellType.thy
    Author:     Gerwin Klein, Andreas Lochbihler
*)

section \<open>Type rules for the intermediate language\<close>

theory J1WellType imports
  J1State
  "../Common/ExternalCallWF"
  "../Common/SemiType"
begin

declare Listn.lesub_list_impl_same_size[simp del] listE_length [simp del]

subsection "Well-Typedness"

type_synonym
  env1  = "ty list"   \<comment> \<open>type environment indexed by variable number\<close>

inductive WT1 :: "'addr J1_prog \<Rightarrow> env1 \<Rightarrow> 'addr expr1 \<Rightarrow> ty \<Rightarrow> bool" ("_,_ \<turnstile>1 _ :: _"   [51,0,0,51] 50)
  and WTs1 :: "'addr J1_prog \<Rightarrow> env1 \<Rightarrow> 'addr expr1 list \<Rightarrow> ty list \<Rightarrow> bool" ("_,_ \<turnstile>1 _ [::] _"   [51,0,0,51]50)
  for P :: "'addr J1_prog"
  where

  WT1New:
  "is_class P C  \<Longrightarrow>
  P,E \<turnstile>1 new C :: Class C"

| WT1NewArray:
  "\<lbrakk> P,E \<turnstile>1 e :: Integer; is_type P (T\<lfloor>\<rceil>) \<rbrakk> \<Longrightarrow>
  P,E \<turnstile>1 newA T\<lfloor>e\<rceil> :: T\<lfloor>\<rceil>"

| WT1Cast:
  "\<lbrakk> P,E \<turnstile>1 e :: T; P \<turnstile> U \<le> T \<or> P \<turnstile> T \<le> U; is_type P U \<rbrakk>
  \<Longrightarrow> P,E \<turnstile>1 Cast U e :: U"

| WT1InstanceOf:
  "\<lbrakk> P,E \<turnstile>1 e :: T; P \<turnstile> U \<le> T \<or> P \<turnstile> T \<le> U; is_type P U; is_refT U \<rbrakk>
  \<Longrightarrow> P,E \<turnstile>1 e instanceof U :: Boolean"

| WT1Val:
  "typeof v = Some T \<Longrightarrow>
  P,E \<turnstile>1 Val v :: T"

| WT1Var:
  "\<lbrakk> E!V = T; V < size E \<rbrakk> \<Longrightarrow>
  P,E \<turnstile>1 Var V :: T"

| WT1BinOp:
  "\<lbrakk> P,E \<turnstile>1 e1 :: T1; P,E \<turnstile>1 e2 :: T2; P \<turnstile> T1\<guillemotleft>bop\<guillemotright>T2 :: T \<rbrakk>
  \<Longrightarrow> P,E \<turnstile>1 e1\<guillemotleft>bop\<guillemotright>e2 :: T"

| WT1LAss:
  "\<lbrakk> E!i = T;  i < size E; P,E \<turnstile>1 e :: T';  P \<turnstile> T' \<le> T \<rbrakk>
  \<Longrightarrow> P,E \<turnstile>1 i:=e :: Void"

| WT1AAcc:
  "\<lbrakk> P,E \<turnstile>1 a :: T\<lfloor>\<rceil>; P,E \<turnstile>1 i :: Integer \<rbrakk>
  \<Longrightarrow> P,E \<turnstile>1 a\<lfloor>i\<rceil> :: T"

| WT1AAss:
  "\<lbrakk> P,E \<turnstile>1 a :: T\<lfloor>\<rceil>; P,E \<turnstile>1 i :: Integer; P,E \<turnstile>1 e :: T'; P \<turnstile> T' \<le> T \<rbrakk>
  \<Longrightarrow> P,E \<turnstile>1 a\<lfloor>i\<rceil> := e :: Void"

| WT1ALength:
  "P,E \<turnstile>1 a :: T\<lfloor>\<rceil> \<Longrightarrow> P,E \<turnstile>1 a\<bullet>length :: Integer"

| WTFAcc1:
  "\<lbrakk> P,E \<turnstile>1 e :: U; class_type_of' U = \<lfloor>C\<rfloor>; P \<turnstile> C sees F:T (fm) in D \<rbrakk>
  \<Longrightarrow> P,E \<turnstile>1 e\<bullet>F{D} :: T"

| WTFAss1:
  "\<lbrakk> P,E \<turnstile>1 e1 :: U; class_type_of' U = \<lfloor>C\<rfloor>; P \<turnstile> C sees F:T (fm) in D;  P,E \<turnstile>1 e2 :: T';  P \<turnstile> T' \<le> T \<rbrakk>
  \<Longrightarrow> P,E \<turnstile>1 e1\<bullet>F{D} := e2 :: Void"

| WTCAS1:
  "\<lbrakk> P,E \<turnstile>1 e1 :: U; class_type_of' U = \<lfloor>C\<rfloor>; P \<turnstile> C sees F:T (fm) in D; volatile fm; 
     P,E \<turnstile>1 e2 :: T'; P \<turnstile> T' \<le> T; P,E \<turnstile>1 e3 :: T''; P \<turnstile> T'' \<le> T \<rbrakk>
  \<Longrightarrow> P,E \<turnstile>1 e1\<bullet>compareAndSwap(D\<bullet>F, e2, e3) :: Boolean"

| WT1Call:
  "\<lbrakk> P,E \<turnstile>1 e :: U; class_type_of' U = \<lfloor>C\<rfloor>; P \<turnstile> C sees M:Ts \<rightarrow> T = m in D;
     P,E \<turnstile>1 es [::] Ts'; P \<turnstile> Ts' [\<le>] Ts \<rbrakk>
  \<Longrightarrow> P,E \<turnstile>1 e\<bullet>M(es) :: T"

| WT1Block:
  "\<lbrakk> is_type P T;  P,E@[T] \<turnstile>1 e :: T'; case vo of None \<Rightarrow> True | \<lfloor>v\<rfloor> \<Rightarrow> \<exists>T'. typeof v = \<lfloor>T'\<rfloor> \<and> P \<turnstile> T' \<le> T \<rbrakk>
  \<Longrightarrow>  P,E \<turnstile>1 {V:T=vo; e} :: T'"

| WT1Synchronized:
  "\<lbrakk> P,E \<turnstile>1 o' :: T; is_refT T; T \<noteq> NT; P,E@[Class Object] \<turnstile>1 e :: T' \<rbrakk>
  \<Longrightarrow> P,E \<turnstile>1 sync\<^bsub>V\<^esub> (o') e :: T'"

| WT1Seq:
  "\<lbrakk> P,E \<turnstile>1 e\<^sub>1::T\<^sub>1;  P,E \<turnstile>1 e\<^sub>2::T\<^sub>2 \<rbrakk>
  \<Longrightarrow>  P,E \<turnstile>1 e\<^sub>1;;e\<^sub>2 :: T\<^sub>2"

| WT1Cond:
  "\<lbrakk> P,E \<turnstile>1 e :: Boolean;  P,E \<turnstile>1 e\<^sub>1::T\<^sub>1;  P,E \<turnstile>1 e\<^sub>2::T\<^sub>2; P \<turnstile> lub(T\<^sub>1,T\<^sub>2) = T \<rbrakk>
  \<Longrightarrow> P,E \<turnstile>1 if (e) e\<^sub>1 else e\<^sub>2 :: T"

| WT1While:
  "\<lbrakk> P,E \<turnstile>1 e :: Boolean;  P,E \<turnstile>1 c::T \<rbrakk>
  \<Longrightarrow> P,E \<turnstile>1 while (e) c :: Void"

| WT1Throw:
  "\<lbrakk> P,E \<turnstile>1 e :: Class C; P \<turnstile> C \<preceq>\<^sup>* Throwable \<rbrakk> \<Longrightarrow> 
  P,E \<turnstile>1 throw e :: Void"

| WT1Try:
  "\<lbrakk> P,E \<turnstile>1 e\<^sub>1 :: T;  P,E@[Class C] \<turnstile>1 e\<^sub>2 :: T; is_class P C \<rbrakk>
  \<Longrightarrow> P,E \<turnstile>1 try e\<^sub>1 catch(C V) e\<^sub>2 :: T"

| WT1Nil: "P,E \<turnstile>1 [] [::] []"

| WT1Cons: "\<lbrakk> P,E \<turnstile>1 e :: T; P,E \<turnstile>1 es [::] Ts \<rbrakk> \<Longrightarrow> P,E \<turnstile>1 e#es [::] T#Ts"

declare WT1_WTs1.intros[intro!]
declare WT1Nil[iff]

inductive_cases WT1_WTs1_cases[elim!]:
  "P,E \<turnstile>1 Val v :: T"
  "P,E \<turnstile>1 Var i :: T"
  "P,E \<turnstile>1 Cast D e :: T"
  "P,E \<turnstile>1 e instanceof U :: T"
  "P,E \<turnstile>1 i:=e :: T"
  "P,E \<turnstile>1 {i:U=vo; e} :: T"
  "P,E \<turnstile>1 e1;;e2 :: T"
  "P,E \<turnstile>1 if (e) e1 else e2 :: T"
  "P,E \<turnstile>1 while (e) c :: T"
  "P,E \<turnstile>1 throw e :: T"
  "P,E \<turnstile>1 try e1 catch(C i) e2 :: T"
  "P,E \<turnstile>1 e\<bullet>F{D} :: T"
  "P,E \<turnstile>1 e1\<bullet>F{D}:=e2 :: T"
  "P,E \<turnstile>1 e\<bullet>compareAndSwap(D\<bullet>F, e', e'') :: T"
  "P,E \<turnstile>1 e1 \<guillemotleft>bop\<guillemotright> e2 :: T"
  "P,E \<turnstile>1 new C :: T"
  "P,E \<turnstile>1 newA T'\<lfloor>e\<rceil> :: T"
  "P,E \<turnstile>1 a\<lfloor>i\<rceil> := e :: T"
  "P,E \<turnstile>1 a\<lfloor>i\<rceil> :: T"
  "P,E \<turnstile>1 a\<bullet>length :: T"
  "P,E \<turnstile>1 e\<bullet>M(es) :: T"
  "P,E \<turnstile>1 sync\<^bsub>V\<^esub> (o') e :: T"
  "P,E \<turnstile>1 insync\<^bsub>V\<^esub> (a) e :: T"
  "P,E \<turnstile>1 [] [::] Ts"
  "P,E \<turnstile>1 e#es [::] Ts"

lemma WTs1_same_size: "P,E \<turnstile>1 es [::] Ts \<Longrightarrow> size es = size Ts"
by (induct es arbitrary: Ts) auto

lemma WTs1_snoc_cases:
  assumes wt: "P,E \<turnstile>1 es @ [e] [::] Ts"
  obtains T Ts' where "P,E \<turnstile>1 es [::] Ts'" "P,E \<turnstile>1 e :: T"
proof -
  from wt have "\<exists>T Ts'. P,E \<turnstile>1 es [::] Ts' \<and> P,E \<turnstile>1 e :: T"
    by(induct es arbitrary: Ts) auto
  thus thesis by(auto intro: that)
qed

lemma WTs1_append:
  assumes wt: "P,Env \<turnstile>1 es @ es' [::] Ts"
  obtains Ts' Ts'' where "P,Env \<turnstile>1 es [::] Ts'" "P,Env \<turnstile>1 es' [::] Ts''"
proof -
  from wt have "\<exists>Ts' Ts''. P,Env \<turnstile>1 es [::] Ts' \<and> P,Env \<turnstile>1 es' [::] Ts''"
    by(induct es arbitrary: Ts) auto
  thus ?thesis by(auto intro: that)
qed

lemma WT1_not_contains_insync: "P,E \<turnstile>1 e :: T \<Longrightarrow> \<not> contains_insync e"
  and WTs1_not_contains_insyncs: "P,E \<turnstile>1 es [::] Ts \<Longrightarrow> \<not> contains_insyncs es"
by(induct rule: WT1_WTs1.inducts) auto

lemma WT1_expr_locks: "P,E \<turnstile>1 e :: T \<Longrightarrow> expr_locks e = (\<lambda>a. 0)"
  and WTs1_expr_lockss: "P,E \<turnstile>1 es [::] Ts \<Longrightarrow> expr_lockss es = (\<lambda>a. 0)"
by(induct rule: WT1_WTs1.inducts)(auto)

lemma assumes wf: "wf_prog wfmd P"
  shows WT1_unique: "P,E \<turnstile>1 e :: T1 \<Longrightarrow> P,E \<turnstile>1 e :: T2 \<Longrightarrow> T1 = T2" 
  and WTs1_unique: "P,E \<turnstile>1 es [::] Ts1 \<Longrightarrow> P,E \<turnstile>1 es [::] Ts2 \<Longrightarrow> Ts1 = Ts2"
apply(induct arbitrary: T2 and Ts2 rule:WT1_WTs1.inducts)
apply blast
apply blast
apply blast
apply blast
apply clarsimp
apply blast
apply(blast dest: WT_binop_fun)
apply blast
apply blast
apply blast
apply blast
apply (blast dest:sees_field_idemp sees_field_fun)
apply (blast dest: sees_field_fun)
apply blast

apply(erule WT1_WTs1_cases)
apply(simp)
apply (blast dest:sees_method_idemp sees_method_fun)

apply blast
apply blast
apply blast
apply(blast dest: is_lub_unique[OF wf])
apply blast
apply blast
apply blast
apply blast
apply blast
done

lemma assumes wf: "wf_prog p P"
  shows WT1_is_type: "P,E \<turnstile>1 e :: T \<Longrightarrow> set E \<subseteq> types P \<Longrightarrow> is_type P T"
  and WTs1_is_type: "P,E \<turnstile>1 es [::] Ts \<Longrightarrow> set E \<subseteq> types P \<Longrightarrow> set Ts \<subseteq> types P"
apply(induct rule:WT1_WTs1.inducts)
apply simp
apply simp
apply simp
apply simp
apply (simp add:typeof_lit_is_type)
apply (fastforce intro:nth_mem)
apply(simp add: WT_binop_is_type)
apply(simp)
apply(simp del: is_type_array add: is_type_ArrayD)
apply(simp)
apply(simp)
apply (simp add:sees_field_is_type[OF _ wf])
apply simp
apply simp
apply(fastforce dest!: sees_wf_mdecl[OF wf] simp:wf_mdecl_def)
apply(simp)
apply(simp add: is_class_Object[OF wf])
apply simp
apply(blast dest: is_lub_is_type[OF wf])
apply simp
apply simp
apply simp
apply simp
apply(simp)
done

lemma blocks1_WT:
  "\<lbrakk> P,Env @ Ts \<turnstile>1 body :: T; set Ts \<subseteq> types P \<rbrakk> \<Longrightarrow> P,Env \<turnstile>1 blocks1 (length Env) Ts body :: T"
proof(induct n\<equiv>"length Env" Ts body arbitrary: Env rule: blocks1.induct)
  case 1 thus ?case by simp
next
  case (2 T' Ts e)
  note IH = \<open>\<And>Env'. \<lbrakk>Suc (length Env) = length Env'; P,Env' @ Ts \<turnstile>1 e :: T; set Ts \<subseteq> types P \<rbrakk>
              \<Longrightarrow> P,Env' \<turnstile>1 blocks1 (length Env') Ts e :: T\<close>
  from \<open>set (T' # Ts) \<subseteq> types P\<close> have "set Ts \<subseteq> types P" "is_type P T'" by(auto)
  moreover from \<open>P,Env @ T' # Ts \<turnstile>1 e :: T\<close> have "P,(Env @ [T']) @ Ts \<turnstile>1 e :: T" by simp
  note IH[OF _ this]
  ultimately show ?case by auto
qed

lemma WT1_fv: "\<lbrakk> P,E \<turnstile>1 e :: T; \<B> e (length E); syncvars e \<rbrakk> \<Longrightarrow> fv e \<subseteq> {0..<length E}"
  and WTs1_fvs: "\<lbrakk> P,E \<turnstile>1 es [::] Ts; \<B>s es (length E); syncvarss es \<rbrakk> \<Longrightarrow> fvs es \<subseteq> {0..<length E}"
proof(induct rule: WT1_WTs1.inducts)
  case (WT1Synchronized E e1 T e2 T' V)
  note IH1 = \<open>\<lbrakk>\<B> e1 (length E); syncvars e1\<rbrakk> \<Longrightarrow> fv e1 \<subseteq> {0..<length E}\<close>
  note IH2 = \<open>\<lbrakk>\<B> e2 (length (E @ [Class Object])); syncvars e2\<rbrakk> \<Longrightarrow> fv e2 \<subseteq> {0..<length (E @ [Class Object])}\<close>
  from \<open>\<B> (sync\<^bsub>V\<^esub> (e1) e2) (length E)\<close> have [simp]: "V = length E"
    and B1: "\<B> e1 (length E)" and B2: "\<B> e2 (Suc (length E))" by auto
  from \<open>syncvars (sync\<^bsub>V\<^esub> (e1) e2)\<close> have sync1: "syncvars e1" and sync2: "syncvars e2" and V: "V \<notin> fv e2" by auto
  have "fv e2 \<subseteq> {0..<length E}"
  proof
    fix x
    assume x: "x \<in> fv e2"
    with V have "x \<noteq> length E" by auto
    moreover from IH2 B2 sync2 have "fv e2 \<subseteq> {0..<Suc (length E)}" by auto
    with x have "x < Suc (length E)" by auto
    ultimately show "x \<in> {0..<length E}" by auto
  qed
  with IH1[OF B1 sync1] show ?case by(auto)
next
  case (WT1Cond E e e1 T1 e2 T2 T)
  thus ?case by(auto del: subsetI)
qed fastforce+

end
