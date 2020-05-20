(*  Title:      Jinja/Compiler/WellType1.thy

    Author:     Tobias Nipkow
    Copyright   2003 Technische Universitaet Muenchen
*)

section \<open>Well-Formedness of Intermediate Language\<close>

theory J1WellForm
imports "../J/JWellForm" J1
begin

subsection "Well-Typedness"

type_synonym 
  env\<^sub>1  = "ty list"   \<comment> \<open>type environment indexed by variable number\<close>

inductive
  WT\<^sub>1 :: "[J\<^sub>1_prog,env\<^sub>1, expr\<^sub>1     , ty     ] \<Rightarrow> bool"
         ("(_,_ \<turnstile>\<^sub>1/ _ :: _)"   [51,51,51]50)
  and WTs\<^sub>1 :: "[J\<^sub>1_prog,env\<^sub>1, expr\<^sub>1 list, ty list] \<Rightarrow> bool"
         ("(_,_ \<turnstile>\<^sub>1/ _ [::] _)" [51,51,51]50)
  for P :: J\<^sub>1_prog
where
  
  WTNew\<^sub>1:
  "is_class P C  \<Longrightarrow>
  P,E \<turnstile>\<^sub>1 new C :: Class C"

| WTCast\<^sub>1:
  "\<lbrakk> P,E \<turnstile>\<^sub>1 e :: Class D;  is_class P C;  P \<turnstile> C \<preceq>\<^sup>* D \<or> P \<turnstile> D \<preceq>\<^sup>* C \<rbrakk>
  \<Longrightarrow> P,E \<turnstile>\<^sub>1 Cast C e :: Class C"

| WTVal\<^sub>1:
  "typeof v = Some T \<Longrightarrow>
  P,E \<turnstile>\<^sub>1 Val v :: T"

| WTVar\<^sub>1:
  "\<lbrakk> E!i = T; i < size E \<rbrakk>
  \<Longrightarrow> P,E \<turnstile>\<^sub>1 Var i :: T"

| WTBinOp\<^sub>1:
  "\<lbrakk> P,E \<turnstile>\<^sub>1 e\<^sub>1 :: T\<^sub>1;  P,E \<turnstile>\<^sub>1 e\<^sub>2 :: T\<^sub>2;
     case bop of Eq \<Rightarrow> (P \<turnstile> T\<^sub>1 \<le> T\<^sub>2 \<or> P \<turnstile> T\<^sub>2 \<le> T\<^sub>1) \<and> T = Boolean
               | Add \<Rightarrow> T\<^sub>1 = Integer \<and> T\<^sub>2 = Integer \<and> T = Integer \<rbrakk>
  \<Longrightarrow> P,E \<turnstile>\<^sub>1 e\<^sub>1 \<guillemotleft>bop\<guillemotright> e\<^sub>2 :: T"

| WTLAss\<^sub>1:
  "\<lbrakk> E!i = T;  i < size E; P,E \<turnstile>\<^sub>1 e :: T';  P \<turnstile> T' \<le> T \<rbrakk>
  \<Longrightarrow> P,E \<turnstile>\<^sub>1 i:=e :: Void"

| WTFAcc\<^sub>1:
  "\<lbrakk> P,E \<turnstile>\<^sub>1 e :: Class C;  P \<turnstile> C sees F:T in D \<rbrakk>
  \<Longrightarrow> P,E \<turnstile>\<^sub>1 e\<bullet>F{D} :: T"

| WTFAss\<^sub>1:
  "\<lbrakk> P,E \<turnstile>\<^sub>1 e\<^sub>1 :: Class C;  P \<turnstile> C sees F:T in D;  P,E \<turnstile>\<^sub>1 e\<^sub>2 :: T';  P \<turnstile> T' \<le> T \<rbrakk>
  \<Longrightarrow> P,E \<turnstile>\<^sub>1 e\<^sub>1\<bullet>F{D} := e\<^sub>2 :: Void"

| WTCall\<^sub>1:
  "\<lbrakk> P,E \<turnstile>\<^sub>1 e :: Class C; P \<turnstile> C sees M:Ts' \<rightarrow> T = m in D;
    P,E \<turnstile>\<^sub>1 es [::] Ts;  P \<turnstile> Ts [\<le>] Ts' \<rbrakk>
  \<Longrightarrow> P,E \<turnstile>\<^sub>1 e\<bullet>M(es) :: T"

| WTBlock\<^sub>1:
  "\<lbrakk> is_type P T; P,E@[T] \<turnstile>\<^sub>1 e::T' \<rbrakk>
  \<Longrightarrow>  P,E \<turnstile>\<^sub>1 {i:T; e} :: T'"

| WTSeq\<^sub>1:
  "\<lbrakk> P,E \<turnstile>\<^sub>1 e\<^sub>1::T\<^sub>1;  P,E \<turnstile>\<^sub>1 e\<^sub>2::T\<^sub>2 \<rbrakk>
  \<Longrightarrow>  P,E \<turnstile>\<^sub>1 e\<^sub>1;;e\<^sub>2 :: T\<^sub>2"

| WTCond\<^sub>1:
  "\<lbrakk> P,E \<turnstile>\<^sub>1 e :: Boolean;  P,E \<turnstile>\<^sub>1 e\<^sub>1::T\<^sub>1;  P,E \<turnstile>\<^sub>1 e\<^sub>2::T\<^sub>2;
    P \<turnstile> T\<^sub>1 \<le> T\<^sub>2 \<or> P \<turnstile> T\<^sub>2 \<le> T\<^sub>1;  P \<turnstile> T\<^sub>1 \<le> T\<^sub>2 \<longrightarrow> T = T\<^sub>2; P \<turnstile> T\<^sub>2 \<le> T\<^sub>1 \<longrightarrow> T = T\<^sub>1 \<rbrakk>
  \<Longrightarrow> P,E \<turnstile>\<^sub>1 if (e) e\<^sub>1 else e\<^sub>2 :: T"

| WTWhile\<^sub>1:
  "\<lbrakk> P,E \<turnstile>\<^sub>1 e :: Boolean;  P,E \<turnstile>\<^sub>1 c::T \<rbrakk>
  \<Longrightarrow> P,E \<turnstile>\<^sub>1 while (e) c :: Void"

| WTThrow\<^sub>1:
  "P,E \<turnstile>\<^sub>1 e :: Class C  \<Longrightarrow>
  P,E \<turnstile>\<^sub>1 throw e :: Void"

| WTTry\<^sub>1:
  "\<lbrakk> P,E \<turnstile>\<^sub>1 e\<^sub>1 :: T;  P,E@[Class C] \<turnstile>\<^sub>1 e\<^sub>2 :: T; is_class P C \<rbrakk>
  \<Longrightarrow> P,E \<turnstile>\<^sub>1 try e\<^sub>1 catch(C i) e\<^sub>2 :: T"

| WTNil\<^sub>1:
  "P,E \<turnstile>\<^sub>1 [] [::] []"

| WTCons\<^sub>1:
  "\<lbrakk> P,E \<turnstile>\<^sub>1 e :: T;  P,E \<turnstile>\<^sub>1 es [::] Ts \<rbrakk>
  \<Longrightarrow>  P,E \<turnstile>\<^sub>1 e#es [::] T#Ts"

(*<*)
declare  WT\<^sub>1_WTs\<^sub>1.intros[intro!]
declare WTNil\<^sub>1[iff]

lemmas WT\<^sub>1_WTs\<^sub>1_induct = WT\<^sub>1_WTs\<^sub>1.induct [split_format (complete)]
  and WT\<^sub>1_WTs\<^sub>1_inducts = WT\<^sub>1_WTs\<^sub>1.inducts [split_format (complete)]

inductive_cases eee[elim!]:
  "P,E \<turnstile>\<^sub>1 Val v :: T"
  "P,E \<turnstile>\<^sub>1 Var i :: T"
  "P,E \<turnstile>\<^sub>1 Cast D e :: T"
  "P,E \<turnstile>\<^sub>1 i:=e :: T"
  "P,E \<turnstile>\<^sub>1 {i:U; e} :: T"
  "P,E \<turnstile>\<^sub>1 e\<^sub>1;;e\<^sub>2 :: T"
  "P,E \<turnstile>\<^sub>1 if (e) e\<^sub>1 else e\<^sub>2 :: T"
  "P,E \<turnstile>\<^sub>1 while (e) c :: T"
  "P,E \<turnstile>\<^sub>1 throw e :: T"
  "P,E \<turnstile>\<^sub>1 try e\<^sub>1 catch(C i) e\<^sub>2 :: T"
  "P,E \<turnstile>\<^sub>1 e\<bullet>F{D} :: T"
  "P,E \<turnstile>\<^sub>1 e\<^sub>1\<bullet>F{D}:=e\<^sub>2 :: T"
  "P,E \<turnstile>\<^sub>1 e\<^sub>1 \<guillemotleft>bop\<guillemotright> e\<^sub>2 :: T"
  "P,E \<turnstile>\<^sub>1 new C :: T"
  "P,E \<turnstile>\<^sub>1 e\<bullet>M(es) :: T"
  "P,E \<turnstile>\<^sub>1 [] [::] Ts"
  "P,E \<turnstile>\<^sub>1 e#es [::] Ts"
(*>*)

lemma WTs\<^sub>1_same_size: "\<And>Ts. P,E \<turnstile>\<^sub>1 es [::] Ts \<Longrightarrow> size es = size Ts"
(*<*)by (induct es type:list) auto(*>*)


lemma WT\<^sub>1_unique:
  "P,E \<turnstile>\<^sub>1 e :: T\<^sub>1 \<Longrightarrow> (\<And>T\<^sub>2. P,E \<turnstile>\<^sub>1 e :: T\<^sub>2 \<Longrightarrow> T\<^sub>1 = T\<^sub>2)" and
  "P,E \<turnstile>\<^sub>1 es [::] Ts\<^sub>1 \<Longrightarrow> (\<And>Ts\<^sub>2. P,E \<turnstile>\<^sub>1 es [::] Ts\<^sub>2 \<Longrightarrow> Ts\<^sub>1 = Ts\<^sub>2)"
(*<*)
apply(induct rule:WT\<^sub>1_WTs\<^sub>1.inducts)
apply blast
apply blast
apply clarsimp
apply blast
apply clarsimp
apply(case_tac bop)
apply clarsimp
apply clarsimp
apply blast
apply (blast dest:sees_field_idemp sees_field_fun)
apply blast
apply (blast dest:sees_method_idemp sees_method_fun)
apply blast
apply blast
apply blast
apply blast
apply clarify
apply blast
apply blast
apply blast
done
(*>*)


lemma assumes wf: "wf_prog p P"
shows WT\<^sub>1_is_type: "P,E \<turnstile>\<^sub>1 e :: T \<Longrightarrow> set E \<subseteq> types P \<Longrightarrow> is_type P T"
and "P,E \<turnstile>\<^sub>1 es [::] Ts \<Longrightarrow> True"
(*<*)
apply(induct rule:WT\<^sub>1_WTs\<^sub>1.inducts)
apply simp
apply simp
apply (simp add:typeof_lit_is_type)
apply (blast intro:nth_mem)
apply(simp split:bop.splits)
apply simp
apply (simp add:sees_field_is_type[OF _ wf])
apply simp
apply(fastforce dest!: sees_wf_mdecl[OF wf] simp:wf_mdecl_def)
apply simp
apply simp
apply blast
apply simp
apply simp
apply simp
apply simp
apply simp
done
(*>*)


subsection\<open>Well-formedness\<close>

\<comment> \<open>Indices in blocks increase by 1\<close>

primrec \<B> :: "expr\<^sub>1 \<Rightarrow> nat \<Rightarrow> bool"
  and \<B>s :: "expr\<^sub>1 list \<Rightarrow> nat \<Rightarrow> bool" where
"\<B> (new C) i = True" |
"\<B> (Cast C e) i = \<B> e i" |
"\<B> (Val v) i = True" |
"\<B> (e\<^sub>1 \<guillemotleft>bop\<guillemotright> e\<^sub>2) i = (\<B> e\<^sub>1 i \<and> \<B> e\<^sub>2 i)" |
"\<B> (Var j) i = True" |
"\<B> (e\<bullet>F{D}) i = \<B> e i" |
"\<B> (j:=e) i = \<B> e i" |
"\<B> (e\<^sub>1\<bullet>F{D} := e\<^sub>2) i = (\<B> e\<^sub>1 i \<and> \<B> e\<^sub>2 i)" |
"\<B> (e\<bullet>M(es)) i = (\<B> e i \<and> \<B>s es i)" |
"\<B> ({j:T ; e}) i = (i = j \<and> \<B> e (i+1))" |
"\<B> (e\<^sub>1;;e\<^sub>2) i = (\<B> e\<^sub>1 i \<and> \<B> e\<^sub>2 i)" |
"\<B> (if (e) e\<^sub>1 else e\<^sub>2) i = (\<B> e i \<and> \<B> e\<^sub>1 i \<and> \<B> e\<^sub>2 i)" |
"\<B> (throw e) i = \<B> e i" |
"\<B> (while (e) c) i = (\<B> e i \<and> \<B> c i)" |
"\<B> (try e\<^sub>1 catch(C j) e\<^sub>2) i = (\<B> e\<^sub>1 i \<and> i=j \<and> \<B> e\<^sub>2 (i+1))" |

"\<B>s [] i = True" |
"\<B>s (e#es) i = (\<B> e i \<and> \<B>s es i)"


definition wf_J\<^sub>1_mdecl :: "J\<^sub>1_prog \<Rightarrow> cname \<Rightarrow> expr\<^sub>1 mdecl \<Rightarrow> bool"
where
  "wf_J\<^sub>1_mdecl P C  \<equiv>  \<lambda>(M,Ts,T,body).
    (\<exists>T'. P,Class C#Ts \<turnstile>\<^sub>1 body :: T' \<and> P \<turnstile> T' \<le> T) \<and>
    \<D> body \<lfloor>{..size Ts}\<rfloor> \<and> \<B> body (size Ts + 1)"

lemma wf_J\<^sub>1_mdecl[simp]:
  "wf_J\<^sub>1_mdecl P C (M,Ts,T,body) \<equiv>
    ((\<exists>T'. P,Class C#Ts \<turnstile>\<^sub>1 body :: T' \<and> P \<turnstile> T' \<le> T) \<and>
     \<D> body \<lfloor>{..size Ts}\<rfloor> \<and> \<B> body (size Ts + 1))"
(*<*)by (simp add:wf_J\<^sub>1_mdecl_def)(*>*)

abbreviation "wf_J\<^sub>1_prog == wf_prog wf_J\<^sub>1_mdecl"

end
