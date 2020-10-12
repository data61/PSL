(*  Title:       CoreC++
    Author:      Daniel Wasserrab
    Maintainer:  Daniel Wasserrab <wasserra at fmi.uni-passau.de>

    Based on the Jinja theory Common/Conform.thy by David von Oheimb and Tobias Nipkow
*)

section \<open>Conformance Relations for Proofs\<close>

theory Conform
imports Exceptions WellTypeRT
begin

primrec conf :: "prog \<Rightarrow> heap \<Rightarrow> val \<Rightarrow> ty \<Rightarrow> bool"   ("_,_ \<turnstile> _ :\<le> _"  [51,51,51,51] 50) where
  "P,h \<turnstile> v :\<le> Void      = (P \<turnstile> typeof\<^bsub>h\<^esub> v = Some Void)"
| "P,h \<turnstile> v :\<le> Boolean   = (P \<turnstile> typeof\<^bsub>h\<^esub> v = Some Boolean)"
| "P,h \<turnstile> v :\<le> Integer   = (P \<turnstile> typeof\<^bsub>h\<^esub> v = Some Integer)"
| "P,h \<turnstile> v :\<le> NT        = (P \<turnstile> typeof\<^bsub>h\<^esub> v = Some NT)"
| "P,h \<turnstile> v :\<le> (Class C) = (P \<turnstile> typeof\<^bsub>h\<^esub> v = Some(Class C) \<or> P \<turnstile> typeof\<^bsub>h\<^esub> v = Some NT)"

definition fconf :: "prog \<Rightarrow> heap \<Rightarrow> ('a \<rightharpoonup> val) \<Rightarrow> ('a \<rightharpoonup> ty) \<Rightarrow> bool" ("_,_ \<turnstile> _ '(:\<le>') _" [51,51,51,51] 50) where
  "P,h \<turnstile> v\<^sub>m (:\<le>) T\<^sub>m  \<equiv>
  \<forall>FD T. T\<^sub>m FD = Some T \<longrightarrow> (\<exists>v. v\<^sub>m FD = Some v \<and> P,h \<turnstile> v :\<le> T)"

definition oconf :: "prog \<Rightarrow> heap \<Rightarrow> obj \<Rightarrow> bool"   ("_,_ \<turnstile> _ \<surd>" [51,51,51] 50) where
  "P,h \<turnstile> obj \<surd>  \<equiv> let (C,S) = obj in 
      (\<forall>Cs. Subobjs P C Cs \<longrightarrow> (\<exists>!fs'. (Cs,fs') \<in> S)) \<and> 
      (\<forall>Cs fs'. (Cs,fs') \<in> S \<longrightarrow> Subobjs P C Cs \<and> 
                    (\<exists>fs Bs ms. class P (last Cs) = Some (Bs,fs,ms) \<and> 
                                P,h \<turnstile> fs' (:\<le>) map_of fs))"  

definition hconf :: "prog \<Rightarrow> heap \<Rightarrow> bool"  ("_ \<turnstile> _ \<surd>" [51,51] 50) where
  "P \<turnstile> h \<surd>  \<equiv>
  (\<forall>a obj. h a = Some obj \<longrightarrow> P,h \<turnstile> obj \<surd>) \<and> preallocated h"

definition lconf :: "prog \<Rightarrow> heap \<Rightarrow> ('a \<rightharpoonup> val) \<Rightarrow> ('a \<rightharpoonup> ty) \<Rightarrow> bool"   ("_,_ \<turnstile> _ '(:\<le>')\<^sub>w _" [51,51,51,51] 50) where
  "P,h \<turnstile> v\<^sub>m (:\<le>)\<^sub>w T\<^sub>m  \<equiv>
  \<forall>V v. v\<^sub>m V = Some v \<longrightarrow> (\<exists>T. T\<^sub>m V = Some T \<and> P,h \<turnstile> v :\<le> T)"



abbreviation
  confs :: "prog \<Rightarrow> heap \<Rightarrow> val list \<Rightarrow> ty list \<Rightarrow> bool" 
           ("_,_ \<turnstile> _ [:\<le>] _" [51,51,51,51] 50) where
  "P,h \<turnstile> vs [:\<le>] Ts \<equiv> list_all2 (conf P h) vs Ts"


subsection\<open>Value conformance \<open>:\<le>\<close>\<close>

lemma conf_Null [simp]: "P,h \<turnstile> Null :\<le> T  =  P \<turnstile> NT \<le> T"
by(cases T) simp_all

lemma typeof_conf[simp]: "P \<turnstile> typeof\<^bsub>h\<^esub> v = Some T \<Longrightarrow> P,h \<turnstile> v :\<le> T"
by (cases T) auto

lemma typeof_lit_conf[simp]: "typeof v = Some T \<Longrightarrow> P,h \<turnstile> v :\<le> T"
by (rule typeof_conf[OF type_eq_type])

lemma defval_conf[simp]: "is_type P T \<Longrightarrow> P,h \<turnstile> default_val T :\<le> T"
by(cases T) auto


lemma typeof_notclass_heap:
  "\<forall>C. T \<noteq> Class C \<Longrightarrow> (P \<turnstile> typeof\<^bsub>h\<^esub> v = Some T) = (P \<turnstile> typeof\<^bsub>h'\<^esub> v = Some T)"
by(cases T)(auto dest:typeof_Void typeof_NT typeof_Boolean typeof_Integer)

lemma assumes h:"h a = Some(C,S)" 
  shows conf_upd_obj: "(P,h(a\<mapsto>(C,S')) \<turnstile> v :\<le> T) = (P,h \<turnstile> v :\<le> T)"

proof(cases T)
  case Void
  hence "(P \<turnstile> typeof\<^bsub>h(a\<mapsto>(C,S'))\<^esub> v = Some T) = (P \<turnstile> typeof\<^bsub>h\<^esub> v = Some T)"
    by(fastforce intro!:typeof_notclass_heap)
  with Void show ?thesis by simp
next
  case Boolean
  hence "(P \<turnstile> typeof\<^bsub>h(a\<mapsto>(C,S'))\<^esub> v = Some T) = (P \<turnstile> typeof\<^bsub>h\<^esub> v = Some T)"
    by(fastforce intro!:typeof_notclass_heap)
  with Boolean show ?thesis by simp
next
  case Integer
  hence "(P \<turnstile> typeof\<^bsub>h(a\<mapsto>(C,S'))\<^esub> v = Some T) = (P \<turnstile> typeof\<^bsub>h\<^esub> v = Some T)"
    by(fastforce intro!:typeof_notclass_heap)
  with Integer show ?thesis by simp
next
  case NT
  hence "(P \<turnstile> typeof\<^bsub>h(a\<mapsto>(C,S'))\<^esub> v = Some T) = (P \<turnstile> typeof\<^bsub>h\<^esub> v = Some T)"
    by(fastforce intro!:typeof_notclass_heap)
  with NT show ?thesis by simp
next
  case (Class C')
  { assume "P \<turnstile> typeof\<^bsub>h(a \<mapsto> (C, S'))\<^esub> v = Some(Class C')"
    with h have "P \<turnstile> typeof\<^bsub>h\<^esub> v = Some(Class C')"
      by (cases v) (auto split:if_split_asm)  }
  hence 1:"P \<turnstile> typeof\<^bsub>h(a \<mapsto> (C, S'))\<^esub> v = Some(Class C') \<Longrightarrow> 
           P \<turnstile> typeof\<^bsub>h\<^esub> v = Some(Class C')" by simp
  { assume type:"P \<turnstile> typeof\<^bsub>h(a \<mapsto> (C, S'))\<^esub> v = Some NT"
    and typenot:"P \<turnstile> typeof\<^bsub>h\<^esub> v \<noteq> Some NT"
    have "\<forall>C. NT \<noteq> Class C" by simp
    with type have "P \<turnstile> typeof\<^bsub>h\<^esub> v = Some NT" by(fastforce dest:typeof_notclass_heap)
    with typenot have "P \<turnstile> typeof\<^bsub>h\<^esub> v = Some(Class C')" by simp }
  hence 2:"\<lbrakk>P \<turnstile> typeof\<^bsub>h(a \<mapsto> (C, S'))\<^esub> v = Some NT; P \<turnstile> typeof\<^bsub>h\<^esub> v \<noteq> Some NT\<rbrakk> \<Longrightarrow>
    P \<turnstile> typeof\<^bsub>h\<^esub> v = Some(Class C')" by simp
  { assume "P \<turnstile> typeof\<^bsub>h\<^esub> v = Some(Class C')"
    with h have "P \<turnstile> typeof\<^bsub>h(a \<mapsto> (C, S'))\<^esub> v = Some(Class C')"
      by (cases v) (auto split:if_split_asm) }
  hence 3:"P \<turnstile> typeof\<^bsub>h\<^esub> v = Some(Class C') \<Longrightarrow> 
           P \<turnstile> typeof\<^bsub>h(a \<mapsto> (C, S'))\<^esub> v = Some(Class C')" by simp
  { assume typenot:"P \<turnstile> typeof\<^bsub>h(a \<mapsto> (C, S'))\<^esub> v \<noteq> Some NT"
    and type:"P \<turnstile> typeof\<^bsub>h\<^esub> v = Some NT"
    have "\<forall>C. NT \<noteq> Class C" by simp
    with type have "P \<turnstile> typeof\<^bsub>h(a \<mapsto> (C, S'))\<^esub> v = Some NT" 
      by(fastforce dest:typeof_notclass_heap)
    with typenot have "P \<turnstile> typeof\<^bsub>h(a \<mapsto> (C, S'))\<^esub> v = Some(Class C')" by simp }
  hence 4:"\<lbrakk>P \<turnstile> typeof\<^bsub>h(a \<mapsto> (C, S'))\<^esub> v \<noteq> Some NT; P \<turnstile> typeof\<^bsub>h\<^esub> v = Some NT\<rbrakk> \<Longrightarrow>
    P \<turnstile> typeof\<^bsub>h(a \<mapsto> (C, S'))\<^esub> v = Some(Class C')" by simp
  from Class show ?thesis by (auto intro:1 2 3 4)
qed


lemma conf_NT [iff]: "P,h \<turnstile> v :\<le> NT = (v = Null)"
by fastforce


subsection\<open>Value list conformance \<open>[:\<le>]\<close>\<close>

lemma confs_rev: "P,h \<turnstile> rev s [:\<le>] t = (P,h \<turnstile> s [:\<le>] rev t)"

  apply rule
  apply (rule subst [OF list_all2_rev])
  apply simp
  apply (rule subst [OF list_all2_rev])
  apply simp
  done



lemma confs_Cons2: "P,h \<turnstile> xs [:\<le>] y#ys = (\<exists>z zs. xs = z#zs \<and> P,h \<turnstile> z :\<le> y \<and> P,h \<turnstile> zs [:\<le>] ys)"
by (rule list_all2_Cons2)


subsection\<open>Field conformance \<open>(:\<le>)\<close>\<close>


lemma fconf_init_fields: 
"class P C = Some(Bs,fs,ms) \<Longrightarrow> P,h \<turnstile> init_class_fieldmap P C (:\<le>) map_of fs"

apply(unfold fconf_def init_class_fieldmap_def)
apply clarsimp
apply (rule exI)
apply (rule conjI)
apply (simp add:map_of_map)
apply(case_tac T)
apply simp_all
done



subsection\<open>Heap conformance\<close>

lemma hconfD: "\<lbrakk> P \<turnstile> h \<surd>; h a = Some obj \<rbrakk> \<Longrightarrow> P,h \<turnstile> obj \<surd>"

apply (unfold hconf_def)
apply (fast)
done


lemma hconf_Subobjs: 
"\<lbrakk>h a = Some(C,S); (Cs, fs) \<in> S; P \<turnstile> h \<surd>\<rbrakk> \<Longrightarrow> Subobjs P C Cs"

apply (unfold hconf_def)
apply clarsimp
apply (erule_tac x="a" in allE)
apply (erule_tac x="C" in allE)
apply (erule_tac x="S" in allE)
apply clarsimp
apply (unfold oconf_def)
apply fastforce
done



subsection \<open>Local variable conformance\<close>

lemma lconf_upd:
  "\<lbrakk> P,h \<turnstile> l (:\<le>)\<^sub>w E; P,h \<turnstile> v :\<le> T; E V = Some T \<rbrakk> \<Longrightarrow> P,h \<turnstile> l(V\<mapsto>v) (:\<le>)\<^sub>w E"

apply (unfold lconf_def)
apply auto
done


lemma lconf_empty[iff]: "P,h \<turnstile> Map.empty (:\<le>)\<^sub>w E"
by(simp add:lconf_def)

lemma lconf_upd2: "\<lbrakk>P,h \<turnstile> l (:\<le>)\<^sub>w E; P,h \<turnstile> v :\<le> T\<rbrakk> \<Longrightarrow> P,h \<turnstile> l(V\<mapsto>v) (:\<le>)\<^sub>w E(V\<mapsto>T)"
by(simp add:lconf_def)


subsection\<open>Environment conformance\<close>

definition envconf :: "prog \<Rightarrow> env \<Rightarrow> bool" ("_ \<turnstile> _ \<surd>" [51,51] 50) where
  "P \<turnstile> E \<surd> \<equiv> \<forall>V T. E V = Some T \<longrightarrow> is_type P T"

subsection\<open>Type conformance\<close>

primrec
  type_conf :: "prog \<Rightarrow> env \<Rightarrow> heap \<Rightarrow> expr \<Rightarrow> ty \<Rightarrow> bool"
    ("_,_,_ \<turnstile> _ :\<^bsub>NT\<^esub> _" [51,51,51]50) 
where
  type_conf_Void:      "P,E,h \<turnstile> e :\<^bsub>NT\<^esub> Void    \<longleftrightarrow> (P,E,h \<turnstile> e : Void)"
  | type_conf_Boolean: "P,E,h \<turnstile> e :\<^bsub>NT\<^esub> Boolean \<longleftrightarrow> (P,E,h \<turnstile> e : Boolean)"
  | type_conf_Integer: "P,E,h \<turnstile> e :\<^bsub>NT\<^esub> Integer \<longleftrightarrow> (P,E,h \<turnstile> e : Integer)"
  | type_conf_NT:      "P,E,h \<turnstile> e :\<^bsub>NT\<^esub> NT      \<longleftrightarrow> (P,E,h \<turnstile> e : NT)"
  | type_conf_Class:   "P,E,h \<turnstile> e :\<^bsub>NT\<^esub> Class C \<longleftrightarrow> 
                             (P,E,h \<turnstile> e : Class C \<or> P,E,h \<turnstile> e : NT)"

fun
  types_conf :: "prog \<Rightarrow> env \<Rightarrow> heap \<Rightarrow> expr list \<Rightarrow> ty list \<Rightarrow> bool" 
    ("_,_,_ \<turnstile> _ [:]\<^bsub>NT\<^esub> _"   [51,51,51]50)
where
  "P,E,h \<turnstile> [] [:]\<^bsub>NT\<^esub> [] \<longleftrightarrow> True"
  | "P,E,h \<turnstile> (e#es) [:]\<^bsub>NT\<^esub> (T#Ts) \<longleftrightarrow>
      (P,E,h \<turnstile> e:\<^bsub>NT\<^esub> T \<and> P,E,h \<turnstile> es [:]\<^bsub>NT\<^esub> Ts)"
  | "P,E,h \<turnstile> es [:]\<^bsub>NT\<^esub> Ts \<longleftrightarrow> False"

lemma wt_same_type_typeconf:
"P,E,h \<turnstile> e : T \<Longrightarrow> P,E,h \<turnstile> e :\<^bsub>NT\<^esub> T"
by(cases T) auto

lemma wts_same_types_typesconf:
  "P,E,h \<turnstile> es [:] Ts \<Longrightarrow> types_conf P E h es Ts"
proof(induct Ts arbitrary: es)
  case Nil thus ?case by (auto elim:WTrts.cases)
next
  case (Cons T' Ts')
  have wtes:"P,E,h \<turnstile> es [:] T'#Ts'"
    and IH:"\<And>es. P,E,h \<turnstile> es [:] Ts' \<Longrightarrow> types_conf P E h es Ts'" by fact+
  from wtes obtain e' es' where es:"es = e'#es'" by(cases es) auto
  with wtes have wte':"P,E,h \<turnstile> e' : T'" and wtes':"P,E,h \<turnstile> es' [:] Ts'"
    by simp_all
  from IH[OF wtes'] wte' es show ?case by (fastforce intro:wt_same_type_typeconf)
qed



lemma types_conf_smaller_types:
"\<And>es Ts. \<lbrakk>length es = length Ts'; types_conf P E h es Ts'; P \<turnstile> Ts' [\<le>] Ts \<rbrakk> 
  \<Longrightarrow> \<exists>Ts''. P,E,h \<turnstile> es [:] Ts'' \<and> P \<turnstile> Ts'' [\<le>] Ts"

proof(induct Ts')
  case Nil thus ?case by simp
next
  case (Cons S Ss)
  have length:"length es = length(S#Ss)"
    and types_conf:"types_conf P E h es (S#Ss)"
    and subs:"P \<turnstile> (S#Ss) [\<le>] Ts"
    and IH:"\<And>es Ts. \<lbrakk>length es = length Ss; types_conf P E h es Ss; P \<turnstile> Ss [\<le>] Ts\<rbrakk>
    \<Longrightarrow> \<exists>Ts''. P,E,h \<turnstile> es [:] Ts'' \<and> P \<turnstile> Ts'' [\<le>] Ts" by fact+
  from subs obtain U Us where Ts:"Ts = U#Us" by(cases Ts) auto
  from length obtain e' es' where es:"es = e'#es'" by(cases es) auto
  with types_conf have type:"P,E,h \<turnstile> e' :\<^bsub>NT\<^esub> S"
    and type':"types_conf P E h es' Ss" by simp_all
  from subs Ts have subs':"P \<turnstile> Ss [\<le>] Us" and sub:"P \<turnstile> S \<le> U" 
    by (simp_all add:fun_of_def)
  from sub type obtain T'' where step:"P,E,h \<turnstile> e' : T'' \<and> P \<turnstile> T'' \<le> U"
    by(cases S,auto,cases U,auto)
  from length es have "length es' = length Ss" by simp
  from IH[OF this type' subs'] obtain Ts'' 
    where "P,E,h \<turnstile> es' [:] Ts'' \<and> P \<turnstile> Ts'' [\<le>] Us"
    by auto
  with step have "P,E,h \<turnstile> (e'#es') [:] (T''#Ts'') \<and> P \<turnstile> (T''#Ts'') [\<le>] (U#Us)"
    by (auto simp:fun_of_def)
  with es Ts show ?case by blast
qed



end
