section \<open>After-execution security\<close> 

theory After_Execution
imports During_Execution
begin 


(* Note: For the paper, I will need the theorems as they are stated. *)

context PL_Indis
begin

subsection\<open>Setup for bisimilarities\<close>

(* Sbis: *)
lemma Sbis_transC[consumes 3, case_names Match]: 
assumes 0: "c \<approx>s d" and "s \<approx> t" and "(c,s) \<rightarrow>c (c',s')"
obtains d' t' where 
"(d,t) \<rightarrow>c (d',t')" and "s' \<approx> t'" and "c' \<approx>s d'"
using assms Sbis_matchC_C[OF 0] 
unfolding matchC_C_def by blast

lemma Sbis_transT[consumes 3, case_names Match]: 
assumes 0: "c \<approx>s d" and "s \<approx> t" and "(c,s) \<rightarrow>t s'"
obtains t' where "(d,t) \<rightarrow>t t'" and "s' \<approx> t'"
using assms Sbis_matchT_T[OF 0] 
unfolding matchT_T_def by blast

lemma Sbis_transC2[consumes 3, case_names Match]: 
assumes 0: "c \<approx>s d" and "s \<approx> t" and "(d,t) \<rightarrow>c (d',t')"
obtains c' s' where 
"(c,s) \<rightarrow>c (c',s')" and "s' \<approx> t'" and "c' \<approx>s d'"
using assms Sbis_matchC_C_rev[OF 0] Sbis_Sym
unfolding matchC_C_def2 by blast

lemma Sbis_transT2[consumes 3, case_names Match]: 
assumes 0: "c \<approx>s d" and "s \<approx> t" and "(d,t) \<rightarrow>t t'"
obtains s' where "(c,s) \<rightarrow>t s'" and "s' \<approx> t'"
using assms Sbis_matchT_T_rev[OF 0] Sbis_Sym
unfolding matchT_T_def2 by blast

(* ZObisT: *)
lemma ZObisT_transC[consumes 3, case_names Match MatchS]: 
assumes 0: "c \<approx>01T d" and "s \<approx> t" and "(c,s) \<rightarrow>c (c',s')"
and "\<And> d' t'. \<lbrakk>(d,t) \<rightarrow>c (d',t'); s' \<approx> t'; c' \<approx>01T d'\<rbrakk> \<Longrightarrow> thesis"
and "\<lbrakk>s' \<approx> t; c' \<approx>01T d\<rbrakk> \<Longrightarrow> thesis"
shows thesis
using assms ZObisT_matchC_ZOC[OF 0]
unfolding matchC_ZOC_def by blast

lemma ZObisT_transT[consumes 3, case_names Match]: 
assumes 0: "c \<approx>01T d" and "s \<approx> t" and "(c,s) \<rightarrow>t s'"
obtains t' where "(d,t) \<rightarrow>t t'" and "s' \<approx> t'"
using assms ZObisT_matchT_T[OF 0] 
unfolding matchT_T_def by blast

lemma ZObisT_transC2[consumes 3, case_names Match MatchS]: 
assumes 0: "c \<approx>01T d" and 2: "s \<approx> t" and 3: "(d,t) \<rightarrow>c (d',t')"
and 4: "\<And> c' s'. \<lbrakk>(c,s) \<rightarrow>c (c',s'); s' \<approx> t'; c' \<approx>01T d'\<rbrakk> \<Longrightarrow> thesis"
and 5: "\<lbrakk>s \<approx> t'; c \<approx>01T d'\<rbrakk> \<Longrightarrow> thesis"
shows thesis 
using assms ZObisT_matchC_ZOC_rev[OF 0] ZObisT_Sym
unfolding matchC_ZOC_def2 by blast

lemma ZObisT_transT2[consumes 3, case_names Match]: 
assumes 0: "c \<approx>01T d" and "s \<approx> t" and "(d,t) \<rightarrow>t t'"
obtains s' where "(c,s) \<rightarrow>t s'" and "s' \<approx> t'"
using assms ZObisT_matchT_T_rev[OF 0] ZObisT_Sym
unfolding matchT_T_def2 by blast

(* WbisT: *)
lemma WbisT_transC[consumes 3, case_names Match]: 
assumes 0: "c \<approx>wT d" and "s \<approx> t" and "(c,s) \<rightarrow>c (c',s')"
obtains d' t' where 
"(d,t) \<rightarrow>*c (d',t')" and "s' \<approx> t'" and "c' \<approx>wT d'"
using assms WbisT_matchC_MC[OF 0] 
unfolding matchC_MC_def by blast

lemma WbisT_transT[consumes 3, case_names Match]: 
assumes 0: "c \<approx>wT d" and "s \<approx> t" and "(c,s) \<rightarrow>t s'"
obtains t' where "(d,t) \<rightarrow>*t t'" and "s' \<approx> t'"
using assms WbisT_matchT_MT[OF 0] 
unfolding matchT_MT_def by blast

lemma WbisT_transC2[consumes 3, case_names Match]: 
assumes 0: "c \<approx>wT d" and "s \<approx> t" and "(d,t) \<rightarrow>c (d',t')"
obtains c' s' where 
"(c,s) \<rightarrow>*c (c',s')" and "s' \<approx> t'" and "c' \<approx>wT d'"
using assms WbisT_matchC_MC_rev[OF 0] WbisT_Sym
unfolding matchC_MC_def2 by blast

lemma WbisT_transT2[consumes 3, case_names Match]: 
assumes 0: "c \<approx>wT d" and "s \<approx> t" and "(d,t) \<rightarrow>t t'"
obtains s' where "(c,s) \<rightarrow>*t s'" and "s' \<approx> t'"
using assms WbisT_matchT_MT_rev[OF 0] WbisT_Sym
unfolding matchT_MT_def2 by blast

(*  *)
lemma WbisT_MtransC[consumes 3, case_names Match]: 
assumes 1: "c \<approx>wT d" and 2: "s \<approx> t" and 3: "(c,s) \<rightarrow>*c (c',s')"
obtains d' t' where 
"(d,t) \<rightarrow>*c (d',t')" and "s' \<approx> t'" and "c' \<approx>wT d'"
proof-
  have "(c,s) \<rightarrow>*c (c',s') \<Longrightarrow> 
        c \<approx>wT d \<Longrightarrow> s \<approx> t \<Longrightarrow> 
        (\<exists> d' t'. (d,t) \<rightarrow>*c (d',t') \<and> s' \<approx> t' \<and> c' \<approx>wT d')"
  proof (induct rule: MtransC_induct2)
    case (Trans c s c' s' c'' s'')
    then obtain d' t' where d: "(d, t) \<rightarrow>*c (d', t')" 
    and "s' \<approx> t'" and "c' \<approx>wT d'"
    and "(c', s') \<rightarrow>c (c'', s'')" by auto
    then obtain d'' t'' where "s'' \<approx> t''" and "c'' \<approx>wT d''" 
    and "(d', t') \<rightarrow>*c (d'', t'')" by (metis WbisT_transC)
    thus ?case using d by (metis MtransC_Trans) 
  qed (metis MtransC_Refl)
  thus thesis using that assms by auto
qed

lemma WbisT_MtransT[consumes 3, case_names Match]: 
assumes 1: "c \<approx>wT d" and 2: "s \<approx> t" and 3: "(c,s) \<rightarrow>*t s'"
obtains t' where "(d,t) \<rightarrow>*t t'" and "s' \<approx> t'"
proof-
  obtain c'' s'' where 4: "(c,s) \<rightarrow>*c (c'',s'')" 
  and 5: "(c'',s'') \<rightarrow>t s'" using 3 by (metis MtransT_invert2)
  then obtain d'' t'' where d: "(d,t) \<rightarrow>*c (d'',t'')" 
  and "s'' \<approx> t''" and "c'' \<approx>wT d''" using 1 2 4 WbisT_MtransC by blast
  then obtain t' where "s' \<approx> t'" and "(d'',t'') \<rightarrow>*t t'"
  by (metis 5 WbisT_transT) 
  thus thesis using d that by (metis MtransC_MtransT)
qed

lemma WbisT_MtransC2[consumes 3, case_names Match]: 
assumes "c \<approx>wT d" and "s \<approx> t" and 1: "(d,t) \<rightarrow>*c (d',t')"
obtains c' s' where 
"(c,s) \<rightarrow>*c (c',s')" and "s' \<approx> t'" and "c' \<approx>wT d'"
proof-
  have "d \<approx>wT c" and "t \<approx> s" 
  using assms by (metis WbisT_Sym indis_sym)+
  then obtain c' s' where 
  "(c,s) \<rightarrow>*c (c',s')" and "t' \<approx> s'" and "d' \<approx>wT c'"
  by (metis 1 WbisT_MtransC)
  thus ?thesis using that by (metis WbisT_Sym indis_sym)
qed

lemma WbisT_MtransT2[consumes 3, case_names Match]: 
assumes "c \<approx>wT d" and "s \<approx> t" and "(d,t) \<rightarrow>*t t'"
obtains s' where "(c,s) \<rightarrow>*t s'" and "s' \<approx> t'"
by (metis WbisT_MtransT WbisT_Sym assms indis_sym)

(* ZObis: *)
lemma ZObis_transC[consumes 3, case_names Match MatchO MatchS]: 
assumes 0: "c \<approx>01 d" and "s \<approx> t" and "(c,s) \<rightarrow>c (c',s')"
and "\<And> d' t'. \<lbrakk>(d,t) \<rightarrow>c (d',t'); s' \<approx> t'; c' \<approx>01 d'\<rbrakk> \<Longrightarrow> thesis" 
and "\<And> t'. \<lbrakk>(d,t) \<rightarrow>t t'; s' \<approx> t'; discr c'\<rbrakk> \<Longrightarrow> thesis"
and "\<lbrakk>s' \<approx> t; c' \<approx>01 d\<rbrakk> \<Longrightarrow> thesis"
shows thesis
using assms ZObis_matchC_ZO[OF 0] 
unfolding matchC_ZO_def by blast

lemma ZObis_transT[consumes 3, case_names Match MatchO MatchS]: 
assumes 0: "c \<approx>01 d" and "s \<approx> t" and "(c,s) \<rightarrow>t s'"
and "\<And> t'. \<lbrakk>(d,t) \<rightarrow>t t'; s' \<approx> t'\<rbrakk> \<Longrightarrow> thesis"
and "\<And> d' t'. \<lbrakk>(d,t) \<rightarrow>c (d',t'); s' \<approx> t'; discr d'\<rbrakk> \<Longrightarrow> thesis"
and "\<lbrakk>s' \<approx> t; discr d\<rbrakk> \<Longrightarrow> thesis"
shows thesis
using assms ZObis_matchT_ZO[OF 0] 
unfolding matchT_ZO_def by blast

lemma ZObis_transC2[consumes 3, case_names Match MatchO MatchS]: 
assumes 0: "c \<approx>01 d" and "s \<approx> t" and "(d,t) \<rightarrow>c (d',t')"
and "\<And> c' s'. \<lbrakk>(c,s) \<rightarrow>c (c',s'); s' \<approx> t'; c' \<approx>01 d'\<rbrakk> \<Longrightarrow> thesis"
and "\<And> s'. \<lbrakk>(c,s) \<rightarrow>t s'; s' \<approx> t'; discr d'\<rbrakk> \<Longrightarrow> thesis"
and "\<lbrakk>s \<approx> t'; c \<approx>01 d'\<rbrakk> \<Longrightarrow> thesis"
shows thesis 
using assms ZObis_matchC_ZO_rev[OF 0] ZObis_Sym
unfolding matchC_ZO_def2 by blast

lemma ZObis_transT2[consumes 3, case_names Match MatchO MatchS]: 
assumes 0: "c \<approx>01 d" and "s \<approx> t" and "(d,t) \<rightarrow>t t'"
and "\<And> s'. \<lbrakk>(c,s) \<rightarrow>t s'; s' \<approx> t'\<rbrakk> \<Longrightarrow> thesis"
and "\<And> c' s'. \<lbrakk>(c,s) \<rightarrow>c (c',s'); s' \<approx> t'; discr c'\<rbrakk> \<Longrightarrow> thesis"
and "\<lbrakk>s \<approx> t'; discr c\<rbrakk> \<Longrightarrow> thesis"
shows thesis
using assms ZObis_matchT_ZO_rev[OF 0] ZObis_Sym
unfolding matchT_ZO_def2 by blast

(* Wbis: *)
lemma Wbis_transC[consumes 3, case_names Match MatchO]: 
assumes 0: "c \<approx>w d" and "s \<approx> t" and "(c,s) \<rightarrow>c (c',s')"
and "\<And> d' t'. \<lbrakk>(d,t) \<rightarrow>*c (d',t'); s' \<approx> t'; c' \<approx>w d'\<rbrakk> \<Longrightarrow> thesis" 
and "\<And> t'. \<lbrakk>(d,t) \<rightarrow>*t t'; s' \<approx> t'; discr c'\<rbrakk> \<Longrightarrow> thesis"
shows thesis
using assms Wbis_matchC_M[OF 0] 
unfolding matchC_M_def by blast

lemma Wbis_transT[consumes 3, case_names Match MatchO]: 
assumes 0: "c \<approx>w d" and "s \<approx> t" and "(c,s) \<rightarrow>t s'"
and "\<And> t'. \<lbrakk>(d,t) \<rightarrow>*t t'; s' \<approx> t'\<rbrakk> \<Longrightarrow> thesis"
and "\<And> d' t'. \<lbrakk>(d,t) \<rightarrow>*c (d',t'); s' \<approx> t'; discr d'\<rbrakk> \<Longrightarrow> thesis"
shows thesis
using assms Wbis_matchT_M[OF 0] 
unfolding matchT_M_def by blast

lemma Wbis_transC2[consumes 3, case_names Match MatchO]: 
assumes 0: "c \<approx>w d" and "s \<approx> t" and "(d,t) \<rightarrow>c (d',t')"
and "\<And> c' s'. \<lbrakk>(c,s) \<rightarrow>*c (c',s'); s' \<approx> t'; c' \<approx>w d'\<rbrakk> \<Longrightarrow> thesis"
and "\<And> s'. \<lbrakk>(c,s) \<rightarrow>*t s'; s' \<approx> t'; discr d'\<rbrakk> \<Longrightarrow> thesis"
shows thesis 
using assms Wbis_matchC_M_rev[OF 0] Wbis_Sym
unfolding matchC_M_def2 by blast

lemma Wbis_transT2[consumes 3, case_names Match MatchO]: 
assumes 0: "c \<approx>w d" and "s \<approx> t" and "(d,t) \<rightarrow>t t'"
and "\<And> s'. \<lbrakk>(c,s) \<rightarrow>*t s'; s' \<approx> t'\<rbrakk> \<Longrightarrow> thesis"
and "\<And> c' s'. \<lbrakk>(c,s) \<rightarrow>*c (c',s'); s' \<approx> t'; discr c'\<rbrakk> \<Longrightarrow> thesis"
shows thesis
using assms Wbis_matchT_M_rev[OF 0] Wbis_Sym
unfolding matchT_M_def2 by blast

(*  *)
lemma Wbis_MtransC[consumes 3, case_names Match MatchO]: 
assumes "c \<approx>w d" and "s \<approx> t" and "(c,s) \<rightarrow>*c (c',s')"
and "\<And> d' t'. \<lbrakk>(d,t) \<rightarrow>*c (d',t'); s' \<approx> t'; c' \<approx>w d'\<rbrakk> \<Longrightarrow> thesis"
and "\<And> t'. \<lbrakk>(d,t) \<rightarrow>*t t'; s' \<approx> t'; discr c'\<rbrakk> \<Longrightarrow> thesis"
shows thesis
proof- 
  have "(c,s) \<rightarrow>*c (c',s') \<Longrightarrow> 
        c \<approx>w d \<Longrightarrow> s \<approx> t \<Longrightarrow> 
        (\<exists> d' t'. (d,t) \<rightarrow>*c (d',t') \<and> s' \<approx> t' \<and> c' \<approx>w d') \<or> 
        (\<exists> t'. (d,t) \<rightarrow>*t t' \<and> s' \<approx> t' \<and> discr c')"
  proof (induct rule: MtransC_induct2)
    case (Trans c s c' s' c'' s'')
    hence c's': "(c', s') \<rightarrow>c (c'', s'')"
    and  
    "(\<exists>d' t'. (d, t) \<rightarrow>*c (d', t') \<and> s' \<approx> t' \<and> c' \<approx>w d') \<or>
     (\<exists>t'. (d, t) \<rightarrow>*t t' \<and> s' \<approx> t' \<and> discr c')" by auto
    thus ?case (is "?A \<or> ?B")
    proof(elim disjE exE conjE)
      fix d' t'
      assume c'd': "c' \<approx>w d'" and s't': "s' \<approx> t'"
      and dt: "(d, t) \<rightarrow>*c (d', t')" 
      from c'd' s't' c's' show ?case
      apply (cases rule: Wbis_transC) 
      by (metis dt MtransC_Trans MtransC_MtransT)+
    next
      fix t'
      assume s't': "s' \<approx> t'" and c': "discr c'" 
      and dt: "(d, t) \<rightarrow>*t t'" 
      from c' s't' c's' show ?case
      by (metis discr.simps dt indis_sym indis_trans)
    qed
  qed auto
  thus thesis using assms by auto
qed

lemma Wbis_MtransT[consumes 3, case_names Match MatchO]: 
assumes c_d: "c \<approx>w d" and st: "s \<approx> t" and cs: "(c,s) \<rightarrow>*t s'" 
and 1: "\<And> t'. \<lbrakk>(d,t) \<rightarrow>*t t'; s' \<approx> t'\<rbrakk> \<Longrightarrow> thesis"
and 2: "\<And> d' t'. \<lbrakk>(d,t) \<rightarrow>*c (d',t'); s' \<approx> t'; discr d'\<rbrakk> \<Longrightarrow> thesis"
shows thesis
using cs proof(elim MtransT_invert2)
  fix c'' s'' assume cs: "(c,s) \<rightarrow>*c (c'',s'')" 
  and c''s'': "(c'',s'') \<rightarrow>t s'" 
  from c_d st cs show thesis
  proof (cases rule: Wbis_MtransC)
    fix d'' t'' 
    assume dt: "(d, t) \<rightarrow>*c (d'', t'')"
    and s''t'': "s'' \<approx> t''" and c''d'': "c'' \<approx>w d''"
    from c''d'' s''t'' c''s'' show thesis
    apply (cases rule: Wbis_transT)
    by (metis 1 2 dt MtransC_MtransT MtransC_Trans)+
  next
    case (MatchO t')
    thus ?thesis using 1 c''s''
    by (metis discr_MtransT indis_sym indis_trans transT_MtransT)
  qed
qed

lemma Wbis_MtransC2[consumes 3, case_names Match MatchO]: 
assumes "c \<approx>w d" and "s \<approx> t" and dt: "(d,t) \<rightarrow>*c (d',t')"
and 1: "\<And> c' s'. \<lbrakk>(c,s) \<rightarrow>*c (c',s'); s' \<approx> t'; c' \<approx>w d'\<rbrakk> \<Longrightarrow> thesis"
and 2: "\<And> s'. \<lbrakk>(c,s) \<rightarrow>*t s'; s' \<approx> t'; discr d'\<rbrakk> \<Longrightarrow> thesis"
shows thesis
proof-
  have dc: "d \<approx>w c" and ts: "t \<approx> s"
  by (metis assms Wbis_Sym indis_sym)+
  from dc ts dt show thesis
  apply(cases rule: Wbis_MtransC)
  by (metis 1 2 Wbis_Sym indis_sym)+
qed

lemma Wbis_MtransT2[consumes 3, case_names Match MatchO]: 
assumes "c \<approx>w d" and "s \<approx> t" and dt: "(d,t) \<rightarrow>*t t'"
and 1: "\<And> s'. \<lbrakk>(c,s) \<rightarrow>*t s'; s' \<approx> t'\<rbrakk> \<Longrightarrow> thesis"
and 2: "\<And> c' s'. \<lbrakk>(c,s) \<rightarrow>*c (c',s'); s' \<approx> t'; discr c'\<rbrakk> \<Longrightarrow> thesis"
shows thesis
proof-
  have dc: "d \<approx>w c" and ts: "t \<approx> s"
  by (metis assms Wbis_Sym indis_sym)+
  from dc ts dt show thesis
  apply(cases rule: Wbis_MtransT)
  by (metis 1 2 Wbis_Sym indis_sym)+
qed

(* BisT: *)
lemma BisT_transC[consumes 5, case_names Match]: 
assumes 0: "c \<approx>T d" 
and "mustT c s" and "mustT d t"
and "s \<approx> t" and "(c,s) \<rightarrow>c (c',s')"
obtains d' t' where 
"(d,t) \<rightarrow>*c (d',t')" and "s' \<approx> t'" and "c' \<approx>T d'"
using assms BisT_matchC_TMC[OF 0] 
unfolding matchC_TMC_def by blast

lemma BisT_transT[consumes 5, case_names Match]: 
assumes 0: "c \<approx>T d" 
and "mustT c s" and "mustT d t"
and "s \<approx> t" and "(c,s) \<rightarrow>t s'"
obtains t' where "(d,t) \<rightarrow>*t t'" and "s' \<approx> t'"
using assms BisT_matchT_TMT[OF 0] 
unfolding matchT_TMT_def by blast

lemma BisT_transC2[consumes 5, case_names Match]: 
assumes 0: "c \<approx>T d" 
and "mustT c s" and "mustT d t"
and "s \<approx> t" and "(d,t) \<rightarrow>c (d',t')"
obtains c' s' where 
"(c,s) \<rightarrow>*c (c',s')" and "s' \<approx> t'" and "c' \<approx>T d'"
using assms BisT_matchC_TMC_rev[OF 0] BisT_Sym
unfolding matchC_TMC_def2 by blast

lemma BisT_transT2[consumes 5, case_names Match]: 
assumes 0: "c \<approx>T d" 
and "mustT c s" and "mustT d t"
and "s \<approx> t" and "(d,t) \<rightarrow>t t'"
obtains s' where "(c,s) \<rightarrow>*t s'" and "s' \<approx> t'"
using assms BisT_matchT_TMT_rev[OF 0] BisT_Sym
unfolding matchT_TMT_def2 by blast

(*  *)
lemma BisT_MtransC[consumes 5, case_names Match]: 
assumes "c \<approx>T d" 
and "mustT c s" "mustT d t"
and "s \<approx> t" and "(c,s) \<rightarrow>*c (c',s')"
obtains d' t' where 
"(d,t) \<rightarrow>*c (d',t')" and "s' \<approx> t'" and "c' \<approx>T d'"
proof-
  have "(c,s) \<rightarrow>*c (c',s') \<Longrightarrow> 
        mustT c s \<Longrightarrow> mustT d t \<Longrightarrow> 
        c \<approx>T d \<Longrightarrow> s \<approx> t \<Longrightarrow> 
        (\<exists> d' t'. (d,t) \<rightarrow>*c (d',t') \<and> s' \<approx> t' \<and> c' \<approx>T d')"
  proof (induct rule: MtransC_induct2)
    case (Trans c s c' s' c'' s'')
    then obtain d' t' where d: "(d, t) \<rightarrow>*c (d', t')" 
    and "s' \<approx> t'" and "c' \<approx>T d'"
    and c's': "(c', s') \<rightarrow>c (c'', s'')" by auto
    moreover have "mustT c' s'" "mustT d' t'"
    by (metis Trans mustT_MtransC d)+
    ultimately obtain d'' t'' where "s'' \<approx> t''" and "c'' \<approx>T d''" 
    and "(d', t') \<rightarrow>*c (d'', t'')" by (metis BisT_transC)
    thus ?case using d by (metis MtransC_Trans) 
  qed (metis MtransC_Refl)
  thus thesis using that assms by auto
qed

lemma BisT_MtransT[consumes 5, case_names Match]: 
assumes 1: "c \<approx>T d" 
and ter: "mustT c s" "mustT d t"
and 2: "s \<approx> t" and 3: "(c,s) \<rightarrow>*t s'"
obtains t' where "(d,t) \<rightarrow>*t t'" and "s' \<approx> t'"
proof-
  obtain c'' s'' where 4: "(c,s) \<rightarrow>*c (c'',s'')" 
  and 5: "(c'',s'') \<rightarrow>t s'" using 3 by (metis MtransT_invert2)
  then obtain d'' t'' where d: "(d,t) \<rightarrow>*c (d'',t'')" 
  and "s'' \<approx> t''" and "c'' \<approx>T d''" using 1 2 ter 4 BisT_MtransC by blast
  moreover have "mustT c'' s''" "mustT d'' t''"
  by (metis d 4 assms mustT_MtransC)+
  ultimately obtain t' where "s' \<approx> t'" and "(d'',t'') \<rightarrow>*t t'"
  by (metis 5 ter BisT_transT) 
  thus thesis using d that by (metis MtransC_MtransT)
qed

lemma BisT_MtransC2[consumes 3, case_names Match]: 
assumes "c \<approx>T d" 
and ter: "mustT c s" "mustT d t"
and "s \<approx> t" and 1: "(d,t) \<rightarrow>*c (d',t')"
obtains c' s' where 
"(c,s) \<rightarrow>*c (c',s')" and "s' \<approx> t'" and "c' \<approx>T d'"
proof-
  have "d \<approx>T c" and "t \<approx> s" 
  using assms by (metis BisT_Sym indis_sym)+
  then obtain c' s' where 
  "(c,s) \<rightarrow>*c (c',s')" and "t' \<approx> s'" and "d' \<approx>T c'"
  by (metis 1 ter BisT_MtransC)
  thus ?thesis using that by (metis BisT_Sym indis_sym)
qed

lemma BisT_MtransT02[consumes 3, case_names Match]: 
assumes "c \<approx>T d" 
and ter: "mustT c s" "mustT d t"
and "s \<approx> t" and "(d,t) \<rightarrow>*t t'"
obtains s' where "(c,s) \<rightarrow>*t s'" and "s' \<approx> t'"
by (metis BisT_MtransT BisT_Sym assms indis_sym)


subsection \<open>Execution traces\<close>

(* Partial traces, modeled as lists of configurations *) 
primrec parTrace where
"parTrace [] \<longleftrightarrow> False" |
"parTrace (cf#cfl) \<longleftrightarrow> (cfl \<noteq> [] \<longrightarrow> parTrace cfl \<and> cf \<rightarrow>c hd cfl)"

lemma trans_Step2:
  "cf \<rightarrow>*c cf' \<Longrightarrow> cf' \<rightarrow>c cf'' \<Longrightarrow> cf \<rightarrow>*c cf''"
  using trans_Step[of "fst cf" "snd cf" "fst cf'" "snd cf'" "fst cf''" "snd cf''"]
  by simp

lemma parTrace_not_empty[simp]: "parTrace cfl \<Longrightarrow> cfl \<noteq> []"
  by (cases "cfl = []") simp

lemma parTrace_snoc[simp]:
  "parTrace (cfl@[cf]) \<longleftrightarrow> (cfl \<noteq> [] \<longrightarrow> parTrace cfl \<and> last cfl \<rightarrow>c cf)"
  by (induct cfl) auto

lemma MtransC_Ex_parTrace:
  assumes "cf \<rightarrow>*c cf'" shows "\<exists>cfl. parTrace cfl \<and> hd cfl = cf \<and> last cfl = cf'"
using assms
proof (induct rule: MtransC_induct)
  case (Refl cf) then show ?case
    by (auto intro!: exI[of _ "[cf]"])
next
  case (Trans cf cf' cf'')
  then obtain cfl where "parTrace cfl" "hd cfl = cf" "last cfl = cf'" by auto
  with \<open>cf' \<rightarrow>c cf''\<close> show ?case
    by (auto intro!: exI[of _ "cfl @ [cf'']"])
qed

lemma parTrace_imp_MtransC:
  assumes pT: "parTrace cfl"
  shows "(hd cfl) \<rightarrow>*c (last cfl)"
using pT proof (induct cfl rule: rev_induct)
  case (snoc cf cfl)
  with trans_Step2[of "hd cfl" "last cfl" cf]
  show ?case
    by auto
qed simp

(* Finite traces, modeled as pairs (partial trace, state): *)
fun finTrace where
"finTrace (cfl,s) \<longleftrightarrow>  
 parTrace cfl \<and> last cfl \<rightarrow>t s"

declare finTrace.simps[simp del]

(* The length of a finite trace *)
definition "lengthFT tr \<equiv> Suc (length (fst tr))"

(* The final state of a finite trace *)
definition "fstate tr \<equiv> snd tr"

(* The initial configuration of a finite trace *)
definition "iconfig tr \<equiv> hd (fst tr)"

lemma MtransT_Ex_finTrace:
  assumes "cf \<rightarrow>*t s" shows "\<exists>tr. finTrace tr \<and> iconfig tr = cf \<and> fstate tr = s"
proof -
  from \<open>cf \<rightarrow>*t s\<close> obtain cf' cfl where "parTrace cfl" "hd cfl = cf" "last cfl \<rightarrow>t s"
    by (auto simp: MtransT.simps dest!: MtransC_Ex_parTrace)
  then show ?thesis
    by (auto simp: finTrace.simps iconfig_def fstate_def
             intro!: exI[of _ "cfl"] exI[of _ s])
qed

lemma finTrace_imp_MtransT:
  "finTrace tr \<Longrightarrow> iconfig tr \<rightarrow>*t fstate tr"
  using parTrace_imp_MtransC[of "fst tr"]
  by (cases tr)
     (auto simp add: iconfig_def fstate_def finTrace.simps MtransT.simps
           simp del: split_paired_Ex)

subsection
\<open>Relationship between during-execution and after-execution security\<close>

(* For the termination-sensitive versions: *)

lemma WbisT_trace2:
  assumes bis: "c \<approx>wT d" "s \<approx> t" 
  and tr: "finTrace tr" "iconfig tr = (c,s)"
  shows "\<exists>tr'. finTrace tr' \<and> iconfig tr' = (d,t) \<and> fstate tr \<approx> fstate tr'"
proof -
  from tr finTrace_imp_MtransT[of tr]
  have "(c, s) \<rightarrow>*t fstate tr"
    by auto
  from WbisT_MtransT[OF bis this]
  obtain t' where "(d, t) \<rightarrow>*t t'" "fstate tr \<approx> t'"
    by auto
  from MtransT_Ex_finTrace[OF this(1)] this(2)
  show ?thesis by auto
qed

theorem WbisT_trace:
  assumes "c \<approx>wT c" and "s \<approx> t" 
  and "finTrace tr" and "iconfig tr = (c,s)"
  shows "\<exists>tr'. finTrace tr' \<and> iconfig tr' = (c,t) \<and> fstate tr \<approx> fstate tr'"
using WbisT_trace2[OF assms] .

theorem ZObisT_trace2:
  assumes bis: "c \<approx>01T d" "s \<approx> t" 
  and tr: "finTrace tr" "iconfig tr = (c,s)"
  shows "\<exists>tr'. finTrace tr' \<and> iconfig tr' = (d,t) \<and>
               fstate tr \<approx> fstate tr' \<and> lengthFT tr' \<le> lengthFT tr"
proof -
  obtain s' cfl where tr_eq: "tr = (cfl, s')" by (cases tr) auto
  with tr have cfl: "cfl \<noteq> []" "parTrace cfl" "last cfl \<rightarrow>t s'" "hd cfl = (c,s)"
    by (auto simp add: finTrace.simps iconfig_def)
  from this bis
  show ?thesis unfolding tr_eq fstate_def snd_conv
  proof (induct cfl arbitrary: c d s t rule: list_nonempty_induct)
    case (single cf)
    with ZObisT_transT[of c d s t s']
    obtain t' where "(d,t) \<rightarrow>t t'" "s' \<approx> t'" "cf = (c,s)"
      by auto
    then show ?case
      by (intro exI[of _ "([(d,t)], t')"])
         (simp add: finTrace.simps parTrace_def iconfig_def fstate_def lengthFT_def)
  next
    case (cons cf cfl)
    then have cfl: "parTrace cfl" "last cfl \<rightarrow>t s'"
      by auto

    from cons have "(c,s) \<rightarrow>c (fst (hd cfl), snd (hd cfl))"
      unfolding parTrace_def by (auto simp add: hd_conv_nth)
    with \<open>c \<approx>01T d\<close> \<open>s \<approx> t\<close> show ?case
    proof (cases rule: ZObisT_transC)
      case MatchS
      from cons(2)[OF cfl _ this(2,1)]
      show ?thesis
        by (auto simp: lengthFT_def le_Suc_eq)
    next
      case (Match d' t')
      from cons(2)[OF cfl _ Match(3,2)]
      obtain cfl' s where "finTrace (cfl', s)" "hd cfl' = (d', t')" "s' \<approx> s" "length cfl' \<le> length cfl"
        by (auto simp: iconfig_def lengthFT_def)
      with Match(1) show ?thesis
        by (intro exI[of _ "((d,t)#cfl', s)"])
           (auto simp: iconfig_def lengthFT_def finTrace.simps)
    qed
  qed
qed

theorem ZObisT_trace:
  assumes "c \<approx>01T c" "s \<approx> t"
  and "finTrace tr" "iconfig tr = (c,s)"
  shows "\<exists>tr'. finTrace tr' \<and> iconfig tr' = (c,t) \<and>
               fstate tr \<approx> fstate tr' \<and> lengthFT tr' \<le> lengthFT tr"
  using ZObisT_trace2[OF assms] .

theorem Sbis_trace:
  assumes bis: "c \<approx>s d" "s \<approx> t"
  and tr: "finTrace tr" "iconfig tr = (c,s)"
  shows "\<exists>tr'. finTrace tr' \<and> iconfig tr' = (d,t) \<and> fstate tr \<approx> fstate tr' \<and>
               lengthFT tr' = lengthFT tr"
proof -
  obtain s' cfl where tr_eq: "tr = (cfl, s')" by (cases tr) auto
  with tr have cfl: "cfl \<noteq> []" "parTrace cfl" "last cfl \<rightarrow>t s'" "hd cfl = (c,s)"
    by (auto simp add: finTrace.simps iconfig_def)
  from this bis
  show ?thesis unfolding tr_eq fstate_def snd_conv
  proof (induct cfl arbitrary: c d s t rule: list_nonempty_induct)
    case (single cf)
    with Sbis_transT[of c d s t s']
    obtain t' where "(d,t) \<rightarrow>t t'" "s' \<approx> t'" "cf = (c,s)"
      by auto
    with single show ?case
      by (intro exI[of _ "([(d,t)], t')"])
         (simp add: lengthFT_def iconfig_def indis_refl finTrace.simps)
  next
    case (cons cf cfl)
    with Sbis_transC[of c d s t "fst (hd cfl)" "snd (hd cfl)"]
    obtain d' t' where *: "(d,t) \<rightarrow>c (d',t')" "snd (hd cfl) \<approx> t'" "fst (hd cfl) \<approx>s d'"
      by auto
    moreover
    with cons(2)[of "fst (hd cfl)" "snd (hd cfl)" d' t'] cons(1,3,4)
    obtain cfl' s where "finTrace (cfl', s)" "hd cfl' = (d', t')" "s' \<approx> s" "length cfl' = length cfl"
      by (auto simp: iconfig_def lengthFT_def)
    ultimately show ?case
      by (intro exI[of _ "((d,t)#cfl', s)"])
         (auto simp: finTrace.simps lengthFT_def iconfig_def)
  qed
qed

corollary siso_trace:
assumes "siso c" and "s \<approx> t" 
and "finTrace tr" and "iconfig tr = (c,s)"
shows 
"\<exists> tr'. finTrace tr' \<and> iconfig tr' = (c,t) \<and> fstate tr \<approx> fstate tr'
        \<and> lengthFT tr' = lengthFT tr"
apply(rule Sbis_trace)
using assms by auto

(* For the termination-insensitive versions: *)
theorem Wbis_trace:
  assumes T: "\<And>s. mustT c s"
  and bis: "c \<approx>w c" "s \<approx> t"
  and tr: "finTrace tr" "iconfig tr = (c,s)"
  shows "\<exists>tr'. finTrace tr' \<and> iconfig tr' = (c,t) \<and> fstate tr \<approx> fstate tr'"
proof -
  from tr finTrace_imp_MtransT[of tr]
  have "(c, s) \<rightarrow>*t fstate tr"
    by auto
  from bis this
  show ?thesis
  proof (cases rule: Wbis_MtransT)
    case (Match t')
    from MtransT_Ex_finTrace[OF this(1)] this(2)
    show ?thesis by auto
  next
    case (MatchO d' t')
    from T[THEN mustT_MtransC, OF MatchO(1)] have "mustT d' t'" .
    from this[THEN mustT_MtransT] obtain s' where "(d', t') \<rightarrow>*t s'" ..
    from MatchO(1) \<open>(d', t') \<rightarrow>*t s'\<close> have "(c, t) \<rightarrow>*t s'" by (rule MtransC_MtransT)
    note MtransT_Ex_finTrace[OF this]
    moreover
    from \<open>discr d'\<close> \<open>(d', t') \<rightarrow>*t s'\<close> have "t' \<approx> s'" by (rule discr_MtransT)
    with \<open>fstate tr \<approx> t'\<close>have "fstate tr \<approx> s'" by (rule indis_trans)
    ultimately show ?thesis
      by auto
  qed
qed

corollary ZObis_trace:
  assumes T: "\<And>s. mustT c s"
  and ZObis: "c \<approx>01 c" and indis: "s \<approx> t"
  and tr: "finTrace tr" "iconfig tr = (c,s)"
  shows "\<exists>tr'. finTrace tr' \<and> iconfig tr' = (c,t) \<and> fstate tr \<approx> fstate tr'"
  by (rule Wbis_trace[OF T bis_imp(4)[OF ZObis] indis tr])

(* For the mustT-interactive notion: *)

theorem BisT_trace:
  assumes bis: "c \<approx>T c" "s \<approx> t"
  and T: "mustT c s" "mustT c t"
  and tr: "finTrace tr" "iconfig tr = (c,s)"
  shows "\<exists>tr'. finTrace tr' \<and> iconfig tr' = (c,t) \<and> fstate tr \<approx> fstate tr'"
proof -
  from tr finTrace_imp_MtransT[of tr]
  have "(c, s) \<rightarrow>*t fstate tr"
    by auto
  from BisT_MtransT[OF bis(1) T bis(2) this]
  obtain t' where "(c,t) \<rightarrow>*t t'" "fstate tr \<approx> t'" .
  from MtransT_Ex_finTrace[OF this(1)] this(2)
  show ?thesis
    by auto
qed

end 
(* context PL_Indis  *)


end
