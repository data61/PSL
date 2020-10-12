(*  Title:       CoreC++
    Author:      Daniel Wasserrab
    Maintainer:  Daniel Wasserrab <wasserra at fmi.uni-passau.de>

    Based on the Jinja theory J/WellTypeRT.thy by Tobias Nipkow 
*)

section \<open>Runtime Well-typedness\<close>

theory WellTypeRT imports WellType begin


subsection \<open>Run time types\<close>

primrec typeof_h :: "prog \<Rightarrow> heap \<Rightarrow> val \<Rightarrow> ty option" ("_ \<turnstile> typeof\<^bsub>_\<^esub>") where
  "P \<turnstile> typeof\<^bsub>h\<^esub> Unit     = Some Void"
| "P \<turnstile> typeof\<^bsub>h\<^esub> Null     = Some NT"
| "P \<turnstile> typeof\<^bsub>h\<^esub> (Bool b) = Some Boolean"
| "P \<turnstile> typeof\<^bsub>h\<^esub> (Intg i) = Some Integer"
| "P \<turnstile> typeof\<^bsub>h\<^esub> (Ref r)  = (case h (the_addr (Ref r)) of None \<Rightarrow> None 
                            | Some(C,S) \<Rightarrow> (if Subobjs P C (the_path(Ref r)) then
                                   Some(Class(last(the_path(Ref r))))
                                            else None))"


lemma type_eq_type: "typeof v = Some T \<Longrightarrow> P \<turnstile> typeof\<^bsub>h\<^esub> v = Some T"
by(induct v)auto

lemma typeof_Void [simp]: "P \<turnstile> typeof\<^bsub>h\<^esub> v = Some Void \<Longrightarrow> v = Unit"
by(induct v,auto split:if_split_asm)

lemma typeof_NT [simp]: "P \<turnstile> typeof\<^bsub>h\<^esub> v = Some NT \<Longrightarrow> v = Null"
by(induct v,auto split:if_split_asm)

lemma typeof_Boolean [simp]: "P \<turnstile> typeof\<^bsub>h\<^esub> v = Some Boolean \<Longrightarrow> \<exists>b. v = Bool b"
by(induct v,auto split:if_split_asm)

lemma typeof_Integer [simp]: "P \<turnstile> typeof\<^bsub>h\<^esub> v = Some Integer \<Longrightarrow> \<exists>i. v = Intg i"
by(induct v,auto split:if_split_asm)

lemma typeof_Class_Subo: 
"P \<turnstile> typeof\<^bsub>h\<^esub> v = Some (Class C) \<Longrightarrow> 
\<exists>a Cs D S. v = Ref(a,Cs) \<and> h a = Some(D,S) \<and> Subobjs P D Cs \<and> last Cs = C"
by(induct v,auto split:if_split_asm)

subsection \<open>The rules\<close>

inductive
  WTrt :: "[prog,env,heap,expr,     ty     ] \<Rightarrow> bool"
        ("_,_,_ \<turnstile> _ : _"   [51,51,51]50)
  and WTrts :: "[prog,env,heap,expr list,ty list] \<Rightarrow> bool"
        ("_,_,_ \<turnstile> _ [:] _" [51,51,51]50)
  for P :: prog
where
  
  WTrtNew:
  "is_class P C  \<Longrightarrow> 
  P,E,h \<turnstile> new C : Class C"

| WTrtDynCast:
  "\<lbrakk> P,E,h \<turnstile> e : T; is_refT T; is_class P C \<rbrakk>
  \<Longrightarrow> P,E,h \<turnstile> Cast C e : Class C"

| WTrtStaticCast:
  "\<lbrakk> P,E,h \<turnstile> e : T; is_refT T; is_class P C \<rbrakk>
  \<Longrightarrow> P,E,h \<turnstile> \<lparr>C\<rparr>e : Class C"

| WTrtVal:
  "P \<turnstile> typeof\<^bsub>h\<^esub> v = Some T \<Longrightarrow>
  P,E,h \<turnstile> Val v : T"

| WTrtVar:
  "E V = Some T \<Longrightarrow>
  P,E,h \<turnstile> Var V : T"

| WTrtBinOp:
  "\<lbrakk> P,E,h \<turnstile> e\<^sub>1 : T\<^sub>1;  P,E,h \<turnstile> e\<^sub>2 : T\<^sub>2;
     case bop of Eq \<Rightarrow> T = Boolean
               | Add \<Rightarrow> T\<^sub>1 = Integer \<and> T\<^sub>2 = Integer \<and> T = Integer \<rbrakk>
  \<Longrightarrow> P,E,h \<turnstile> e\<^sub>1 \<guillemotleft>bop\<guillemotright> e\<^sub>2 : T"

| WTrtLAss:
  "\<lbrakk> E V = Some T;  P,E,h \<turnstile> e : T'; P \<turnstile> T' \<le> T \<rbrakk>
  \<Longrightarrow> P,E,h \<turnstile> V:=e : T"

| WTrtFAcc:
"\<lbrakk>P,E,h \<turnstile> e : Class C; Cs \<noteq> []; P \<turnstile> C has least F:T via Cs \<rbrakk>
  \<Longrightarrow> P,E,h \<turnstile> e\<bullet>F{Cs} : T"

| WTrtFAccNT:
  "P,E,h \<turnstile> e : NT \<Longrightarrow> P,E,h \<turnstile> e\<bullet>F{Cs} : T"

| WTrtFAss:
"\<lbrakk>P,E,h \<turnstile> e\<^sub>1 : Class C; Cs \<noteq> [];
  P \<turnstile> C has least F:T via Cs; P,E,h \<turnstile> e\<^sub>2 : T'; P \<turnstile> T' \<le> T \<rbrakk>
  \<Longrightarrow> P,E,h \<turnstile> e\<^sub>1\<bullet>F{Cs}:=e\<^sub>2 : T"

| WTrtFAssNT:
  "\<lbrakk> P,E,h \<turnstile> e\<^sub>1 : NT; P,E,h \<turnstile> e\<^sub>2 : T'; P \<turnstile> T' \<le> T \<rbrakk>
  \<Longrightarrow> P,E,h \<turnstile> e\<^sub>1\<bullet>F{Cs}:=e\<^sub>2 : T"

| WTrtCall:
  "\<lbrakk> P,E,h \<turnstile> e : Class C;  P \<turnstile> C has least M = (Ts,T,m) via Cs;
     P,E,h \<turnstile> es [:] Ts'; P \<turnstile> Ts' [\<le>] Ts \<rbrakk>
  \<Longrightarrow> P,E,h \<turnstile> e\<bullet>M(es) : T" 

| WTrtStaticCall:
  "\<lbrakk> P,E,h \<turnstile> e : Class C'; P \<turnstile> Path C' to C unique;
     P \<turnstile> C has least M = (Ts,T,m) via Cs; 
     P,E,h \<turnstile> es [:] Ts'; P \<turnstile> Ts' [\<le>] Ts \<rbrakk>
  \<Longrightarrow> P,E,h \<turnstile> e\<bullet>(C::)M(es) : T"

| WTrtCallNT:
  "\<lbrakk>P,E,h \<turnstile> e : NT; P,E,h \<turnstile> es [:] Ts\<rbrakk> \<Longrightarrow> P,E,h \<turnstile> Call e Copt M es : T"

| WTrtBlock:
  "\<lbrakk>P,E(V\<mapsto>T),h \<turnstile> e : T'; is_type P T\<rbrakk> \<Longrightarrow> 
  P,E,h \<turnstile> {V:T; e} : T'"

| WTrtSeq:
  "\<lbrakk> P,E,h \<turnstile> e\<^sub>1 : T\<^sub>1;  P,E,h \<turnstile> e\<^sub>2 : T\<^sub>2 \<rbrakk>  \<Longrightarrow>  P,E,h \<turnstile> e\<^sub>1;;e\<^sub>2 : T\<^sub>2"

| WTrtCond:
  "\<lbrakk> P,E,h \<turnstile> e : Boolean;  P,E,h \<turnstile> e\<^sub>1 : T;  P,E,h \<turnstile> e\<^sub>2 : T \<rbrakk>
  \<Longrightarrow> P,E,h \<turnstile> if (e) e\<^sub>1 else e\<^sub>2 : T"

| WTrtWhile:
  "\<lbrakk> P,E,h \<turnstile> e : Boolean;  P,E,h \<turnstile> c : T \<rbrakk>
  \<Longrightarrow>  P,E,h \<turnstile> while(e) c : Void"

| WTrtThrow:
  "\<lbrakk>P,E,h \<turnstile> e : T'; is_refT T'\<rbrakk>  
 \<Longrightarrow>  P,E,h \<turnstile> throw e : T"


| WTrtNil:
"P,E,h \<turnstile> [] [:] []"

| WTrtCons:
 "\<lbrakk> P,E,h \<turnstile> e : T;  P,E,h \<turnstile> es [:] Ts \<rbrakk> \<Longrightarrow>  P,E,h \<turnstile> e#es [:] T#Ts"




declare
  WTrt_WTrts.intros[intro!]
  WTrtNil[iff]
declare
  WTrtFAcc[rule del] WTrtFAccNT[rule del]
  WTrtFAss[rule del] WTrtFAssNT[rule del]
  WTrtCall[rule del] WTrtCallNT[rule del]

lemmas WTrt_induct = WTrt_WTrts.induct [split_format (complete)]
  and WTrt_inducts = WTrt_WTrts.inducts [split_format (complete)]


subsection\<open>Easy consequences\<close>

inductive_simps [iff]:
  "P,E,h \<turnstile> [] [:] Ts"
  "P,E,h \<turnstile> e#es [:] T#Ts"
  "P,E,h \<turnstile> (e#es) [:] Ts"
  "P,E,h \<turnstile> Val v : T"
  "P,E,h \<turnstile> Var V : T"
  "P,E,h \<turnstile> e\<^sub>1;;e\<^sub>2 : T\<^sub>2"
  "P,E,h \<turnstile> {V:T; e} : T'"


lemma [simp]: "\<forall>Ts. (P,E,h \<turnstile> es\<^sub>1 @ es\<^sub>2 [:] Ts) =
  (\<exists>Ts\<^sub>1 Ts\<^sub>2. Ts = Ts\<^sub>1 @ Ts\<^sub>2 \<and> P,E,h \<turnstile> es\<^sub>1 [:] Ts\<^sub>1 & P,E,h \<turnstile> es\<^sub>2 [:] Ts\<^sub>2)"

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



inductive_cases WTrt_elim_cases[elim!]:
  "P,E,h \<turnstile> new C : T"
  "P,E,h \<turnstile> Cast C e : T"
  "P,E,h \<turnstile> \<lparr>C\<rparr>e : T"
  "P,E,h \<turnstile> e\<^sub>1 \<guillemotleft>bop\<guillemotright> e\<^sub>2 : T"
  "P,E,h \<turnstile> V:=e : T"
  "P,E,h \<turnstile> e\<bullet>F{Cs} : T"
  "P,E,h \<turnstile> e\<bullet>F{Cs} := v : T"
  "P,E,h \<turnstile> e\<bullet>M(es) : T"
  "P,E,h \<turnstile> e\<bullet>(C::)M(es) : T"
  "P,E,h \<turnstile> if (e) e\<^sub>1 else e\<^sub>2 : T"
  "P,E,h \<turnstile> while(e) c : T"
  "P,E,h \<turnstile> throw e : T"


subsection\<open>Some interesting lemmas\<close>


lemma WTrts_Val[simp]:
 "\<And>Ts. (P,E,h \<turnstile> map Val vs [:] Ts) = (map (\<lambda>v. (P \<turnstile> typeof\<^bsub>h\<^esub>) v) vs = map Some Ts)"

apply(induct vs)
 apply fastforce
apply(case_tac Ts)
 apply simp
apply simp
done



lemma WTrts_same_length: "\<And>Ts. P,E,h \<turnstile> es [:] Ts \<Longrightarrow> length es = length Ts"
by(induct es type:list)auto


lemma WTrt_env_mono:
  "P,E,h \<turnstile> e : T \<Longrightarrow> (\<And>E'. E \<subseteq>\<^sub>m E' \<Longrightarrow> P,E',h \<turnstile> e : T)" and
  "P,E,h \<turnstile> es [:] Ts \<Longrightarrow> (\<And>E'. E \<subseteq>\<^sub>m E' \<Longrightarrow> P,E',h \<turnstile> es [:] Ts)"

apply(induct rule: WTrt_inducts)
apply(simp add: WTrtNew)
apply(fastforce simp: WTrtDynCast)
apply(fastforce simp: WTrtStaticCast)
apply(fastforce simp: WTrtVal)
apply(simp add: WTrtVar map_le_def dom_def)
apply(fastforce simp add: WTrtBinOp)
apply (force simp:map_le_def)
apply(fastforce simp: WTrtFAcc)
apply(simp add: WTrtFAccNT)
apply(fastforce simp: WTrtFAss)
apply(fastforce simp: WTrtFAssNT)
apply(fastforce simp: WTrtCall)
apply(fastforce simp: WTrtStaticCall)
apply(fastforce simp: WTrtCallNT)
apply(fastforce simp: map_le_def)
apply(fastforce)
apply(fastforce simp: WTrtCond)
apply(fastforce simp: WTrtWhile)
apply(fastforce simp: WTrtThrow)
apply(simp add: WTrtNil)
apply(simp add: WTrtCons)
done


lemma WT_implies_WTrt: "P,E \<turnstile> e :: T \<Longrightarrow> P,E,h \<turnstile> e : T"
and WTs_implies_WTrts: "P,E \<turnstile> es [::] Ts \<Longrightarrow> P,E,h \<turnstile> es [:] Ts"

proof(induct rule: WT_WTs_inducts)
  case WTVal thus ?case by (fastforce dest:type_eq_type)
next
  case WTBinOp thus ?case by (fastforce split:bop.splits)
next
  case WTFAcc thus ?case
    by(fastforce intro!:WTrtFAcc dest:Subobjs_nonempty 
                  simp:LeastFieldDecl_def FieldDecls_def)
next
  case WTFAss thus ?case
    by(fastforce intro!:WTrtFAss dest:Subobjs_nonempty
                  simp:LeastFieldDecl_def FieldDecls_def)
next
  case WTCall thus ?case by (fastforce intro:WTrtCall)
qed (auto simp del:fun_upd_apply)


end
